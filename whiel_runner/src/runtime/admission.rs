//! Run-scoped admission for solver processes and CPU-heavy workers.

use std::collections::VecDeque;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

use tokio::sync::{Notify, OwnedSemaphorePermit, Semaphore};

use crate::failure::FailureReport;

use super::CancellationToken;

const QUEUED: u8 = 0;
const GRANTED: u8 = 1;
const CANCELLED: u8 = 2;
const CLOSED: u8 = 3;
const MAX_BYPASS_GRANTS: usize = 8;

// ------------------------------------------------------------
// Resolved Resource Policy
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeResourcePolicy {
    max_vampire_processes: usize,
    cex_reserved_vampire_processes: usize,
    max_inv_vampire_processes: usize,
    max_cpu_workers: usize,
}

impl RuntimeResourcePolicy {
    pub fn default_symbolic() -> Self {
        let parallelism = std::thread::available_parallelism()
            .map(usize::from)
            .unwrap_or(1);
        let max_vampire_processes = parallelism.max(4);
        Self {
            max_vampire_processes,
            cex_reserved_vampire_processes: 2,
            max_inv_vampire_processes: max_vampire_processes - 2,
            max_cpu_workers: parallelism,
        }
    }

    pub fn symbolic(
        max_vampire_processes: usize,
        max_inv_vampire_processes: usize,
        max_cpu_workers: usize,
    ) -> Result<Self, ResourcePolicyError> {
        if max_vampire_processes < 4 {
            return Err(ResourcePolicyError::SymbolicProcessCapacity);
        }
        if !(2..=max_vampire_processes).contains(&max_inv_vampire_processes) {
            return Err(ResourcePolicyError::InvProcessCapacity);
        }
        if max_cpu_workers == 0 {
            return Err(ResourcePolicyError::CpuWorkerCapacity);
        }
        Ok(Self {
            max_vampire_processes,
            cex_reserved_vampire_processes: 2,
            max_inv_vampire_processes,
            max_cpu_workers,
        })
    }

    pub fn agent_only(
        max_vampire_processes: usize,
        max_cpu_workers: usize,
    ) -> Result<Self, ResourcePolicyError> {
        if max_vampire_processes == 0 {
            return Err(ResourcePolicyError::VampireProcessCapacity);
        }
        if max_cpu_workers == 0 {
            return Err(ResourcePolicyError::CpuWorkerCapacity);
        }
        Ok(Self {
            max_vampire_processes,
            cex_reserved_vampire_processes: 0,
            max_inv_vampire_processes: 0,
            max_cpu_workers,
        })
    }

    pub fn max_vampire_processes(self) -> usize {
        self.max_vampire_processes
    }

    pub fn cex_reserved_vampire_processes(self) -> usize {
        self.cex_reserved_vampire_processes
    }

    pub fn max_inv_vampire_processes(self) -> usize {
        self.max_inv_vampire_processes
    }

    pub fn max_cpu_workers(self) -> usize {
        self.max_cpu_workers
    }

    fn shared_vampire_processes(self) -> usize {
        self.max_vampire_processes - self.cex_reserved_vampire_processes
    }
}

impl Default for RuntimeResourcePolicy {
    fn default() -> Self {
        Self::default_symbolic()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourcePolicyError {
    VampireProcessCapacity,
    SymbolicProcessCapacity,
    InvProcessCapacity,
    CpuWorkerCapacity,
    WrongProfile,
}

impl fmt::Display for ResourcePolicyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let detail = match self {
            Self::VampireProcessCapacity => "max Vampire process count must be positive",
            Self::SymbolicProcessCapacity => {
                "a symbolic profile requires at least four Vampire process slots"
            }
            Self::InvProcessCapacity => {
                "a symbolic INV cap must be between two and the total process count"
            }
            Self::CpuWorkerCapacity => "max CPU worker count must be positive",
            Self::WrongProfile => {
                "the resource policy does not match the requested admission class"
            }
        };
        formatter.write_str(detail)
    }
}

impl std::error::Error for ResourcePolicyError {}

// ------------------------------------------------------------
// Shared Admission Handles
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolverAdmissionClass {
    Inv,
    Cex,
    General,
}

#[derive(Clone)]
pub struct SolverAdmission {
    controller: Arc<AdmissionController>,
    class: SolverAdmissionClass,
}

impl fmt::Debug for SolverAdmission {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SolverAdmission")
            .field("policy", &self.controller.policy)
            .field("class", &self.class)
            .finish_non_exhaustive()
    }
}

impl SolverAdmission {
    pub fn policy(&self) -> RuntimeResourcePolicy {
        self.controller.policy
    }

    pub fn class(&self) -> SolverAdmissionClass {
        self.class
    }

    /// Whether two lane handles belong to the same run-scoped authority.
    pub(crate) fn shares_controller_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.controller, &other.controller)
    }

    pub async fn acquire_cpu_worker(
        &self,
        cancellation: &CancellationToken,
    ) -> Result<CpuWorkerPermit, AdmissionError> {
        if let Some(report) = self.controller.failure() {
            return Err(AdmissionError::Closed(report));
        }
        let acquire = Arc::clone(&self.controller.cpu).acquire_owned();
        let closed = self.controller.closed.notified();
        tokio::pin!(acquire);
        tokio::pin!(closed);
        closed.as_mut().enable();
        if let Some(report) = self.controller.failure() {
            return Err(AdmissionError::Closed(report));
        }
        let permit = tokio::select! {
            biased;
            _ = &mut closed => {
                return Err(AdmissionError::Closed(
                    self.controller
                        .failure()
                        .expect("admission closure publishes its failure before notification"),
                ));
            }
            _ = cancellation.cancelled() => return Err(AdmissionError::Cancelled),
            permit = &mut acquire => permit.expect("the private CPU semaphore is never closed"),
        };
        if cancellation.is_cancelled() {
            drop(permit);
            return Err(AdmissionError::Cancelled);
        }
        if let Some(report) = self.controller.failure() {
            drop(permit);
            return Err(AdmissionError::Closed(report));
        }
        Ok(CpuWorkerPermit { _permit: permit })
    }

    pub(crate) fn can_ever_admit(&self, slots: usize, locally_bounded: bool) -> bool {
        if slots == 0 {
            return false;
        }
        let policy = self.controller.policy;
        match self.class {
            SolverAdmissionClass::Cex => {
                slots <= policy.cex_reserved_vampire_processes
                    && slots <= policy.max_vampire_processes
            }
            SolverAdmissionClass::Inv => {
                slots <= policy.max_inv_vampire_processes
                    && slots
                        <= if locally_bounded {
                            policy.max_vampire_processes
                        } else {
                            policy.shared_vampire_processes()
                        }
            }
            SolverAdmissionClass::General => {
                slots
                    <= if locally_bounded {
                        policy.max_vampire_processes
                    } else {
                        policy.shared_vampire_processes()
                    }
            }
        }
    }

    pub(crate) fn poison(&self, report: FailureReport) {
        self.controller.poison(report);
    }

    /// The most solver leases this run ever held at one instant.
    ///
    /// A check takes a fresh lease per solver invocation, so across a retry
    /// ladder it holds several in sequence, and a run mixing one-slot and
    /// two-slot requests can hold more leases than it has checks. Under a
    /// uniform lane policy, where every request takes the same number of slots,
    /// this is the observed maximum of simultaneous checks.
    pub fn max_simultaneous_solver_grants(&self) -> usize {
        self.controller
            .max_live_solver_permits
            .load(Ordering::Acquire)
    }

    /// Wait until every admitted solver lease has been released.
    ///
    /// Blocking Vampire workers retain their lease even if an async
    /// supervisor is dropped. A run owner can therefore join detached
    /// process cleanup without retaining each Tokio task handle.
    pub(crate) async fn wait_for_solver_idle(&self) {
        loop {
            let changed = self.controller.solver_permit_changed.notified();
            tokio::pin!(changed);
            changed.as_mut().enable();
            if self.controller.live_solver_permits.load(Ordering::Acquire) == 0 {
                return;
            }
            changed.await;
        }
    }

    pub(crate) async fn acquire_solver(
        &self,
        slots: usize,
        locally_bounded: bool,
        cancellation: &CancellationToken,
    ) -> Result<SolverPermit, AdmissionError> {
        if !self.can_ever_admit(slots, locally_bounded) {
            return Err(AdmissionError::InsufficientCapacity);
        }
        let waiter = Arc::new(Waiter {
            class: self.class,
            slots,
            locally_bounded,
            status: AtomicU8::new(QUEUED),
            bypass_grants: AtomicUsize::new(0),
            notified: Notify::new(),
        });
        self.controller.enqueue(Arc::clone(&waiter));
        let mut queue_guard = QueuedWaiterGuard {
            controller: Arc::clone(&self.controller),
            waiter: Arc::clone(&waiter),
            armed: true,
        };

        loop {
            let status = waiter.status.load(Ordering::Acquire);
            if status == GRANTED {
                if let Some(report) = self.controller.failure() {
                    return Err(AdmissionError::Closed(report));
                }
                if cancellation.is_cancelled() {
                    return Err(AdmissionError::Cancelled);
                }
                queue_guard.armed = false;
                let live = self
                    .controller
                    .live_solver_permits
                    .fetch_add(1, Ordering::AcqRel)
                    + 1;
                self.controller
                    .max_live_solver_permits
                    .fetch_max(live, Ordering::AcqRel);
                return Ok(SolverPermit {
                    controller: Arc::clone(&self.controller),
                    class: self.class,
                    slots,
                });
            }
            if status == CLOSED {
                return Err(AdmissionError::Closed(
                    self.controller
                        .failure()
                        .expect("a closed waiter retains the controller failure"),
                ));
            }
            if cancellation.is_cancelled() {
                return Err(AdmissionError::Cancelled);
            }

            let notified = waiter.notified.notified();
            let closed = self.controller.closed.notified();
            tokio::pin!(notified);
            tokio::pin!(closed);
            notified.as_mut().enable();
            closed.as_mut().enable();
            if waiter.status.load(Ordering::Acquire) != QUEUED
                || cancellation.is_cancelled()
                || self.controller.failure().is_some()
            {
                continue;
            }
            tokio::select! {
                biased;
                _ = &mut closed => {},
                _ = cancellation.cancelled() => {},
                _ = &mut notified => {},
            }
        }
    }
}

pub fn create_symbolic_solver_admissions(
    policy: RuntimeResourcePolicy,
) -> Result<(SolverAdmission, SolverAdmission), ResourcePolicyError> {
    if policy.cex_reserved_vampire_processes != 2 || policy.max_inv_vampire_processes < 2 {
        return Err(ResourcePolicyError::WrongProfile);
    }
    let controller = Arc::new(AdmissionController::new(policy));
    Ok((
        SolverAdmission {
            controller: Arc::clone(&controller),
            class: SolverAdmissionClass::Inv,
        },
        SolverAdmission {
            controller,
            class: SolverAdmissionClass::Cex,
        },
    ))
}

pub fn create_general_solver_admission(
    policy: RuntimeResourcePolicy,
) -> Result<SolverAdmission, ResourcePolicyError> {
    if policy.cex_reserved_vampire_processes != 0 || policy.max_inv_vampire_processes != 0 {
        return Err(ResourcePolicyError::WrongProfile);
    }
    Ok(SolverAdmission {
        controller: Arc::new(AdmissionController::new(policy)),
        class: SolverAdmissionClass::General,
    })
}

#[derive(Clone, Debug)]
pub enum AdmissionError {
    Cancelled,
    InsufficientCapacity,
    Closed(FailureReport),
}

impl fmt::Display for AdmissionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Cancelled => "resource admission was cancelled",
            Self::InsufficientCapacity => "the requested work exceeds its admission capacity",
            Self::Closed(_) => "the shared resource admission controller is closed",
        })
    }
}

impl std::error::Error for AdmissionError {}

pub struct CpuWorkerPermit {
    _permit: OwnedSemaphorePermit,
}

pub(crate) struct SolverPermit {
    controller: Arc<AdmissionController>,
    class: SolverAdmissionClass,
    slots: usize,
}

impl SolverPermit {
    pub(crate) fn poison(&self, report: FailureReport) {
        self.controller.poison(report);
    }
}

struct QueuedWaiterGuard {
    controller: Arc<AdmissionController>,
    waiter: Arc<Waiter>,
    armed: bool,
}

impl Drop for QueuedWaiterGuard {
    fn drop(&mut self) {
        if self.armed {
            self.controller.abandon(&self.waiter);
        }
    }
}

impl Drop for SolverPermit {
    fn drop(&mut self) {
        self.controller.release(self.class, self.slots);
        self.controller
            .live_solver_permits
            .fetch_sub(1, Ordering::AcqRel);
        self.controller.solver_permit_changed.notify_waiters();
    }
}

// ------------------------------------------------------------
// Weighted Solver Controller
// ------------------------------------------------------------

struct Waiter {
    class: SolverAdmissionClass,
    slots: usize,
    locally_bounded: bool,
    status: AtomicU8,
    bypass_grants: AtomicUsize,
    notified: Notify,
}

struct AdmissionController {
    policy: RuntimeResourcePolicy,
    state: Mutex<AdmissionState>,
    cpu: Arc<Semaphore>,
    closed: Notify,
    live_solver_permits: AtomicUsize,
    /// High-water mark of simultaneously held solver leases: the run's own
    /// observation of the concurrency it reached, against the concurrency its
    /// budgets configured.
    max_live_solver_permits: AtomicUsize,
    solver_permit_changed: Notify,
}

struct AdmissionStateGuard<'a> {
    controller: &'a AdmissionController,
    state: MutexGuard<'a, AdmissionState>,
}

impl Deref for AdmissionStateGuard<'_> {
    type Target = AdmissionState;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

impl DerefMut for AdmissionStateGuard<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.state
    }
}

impl Drop for AdmissionStateGuard<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.controller
                .fail_closed_after_authority_panic(&mut self.state);
        }
    }
}

#[derive(Default)]
struct AdmissionState {
    active_total: usize,
    active_inv: usize,
    active_cex: usize,
    ordinary_queue: VecDeque<Arc<Waiter>>,
    cex_queue: VecDeque<Arc<Waiter>>,
    failure: Option<FailureReport>,
}

impl AdmissionController {
    fn new(policy: RuntimeResourcePolicy) -> Self {
        Self {
            policy,
            state: Mutex::new(AdmissionState::default()),
            cpu: Arc::new(Semaphore::new(policy.max_cpu_workers)),
            closed: Notify::new(),
            live_solver_permits: AtomicUsize::new(0),
            max_live_solver_permits: AtomicUsize::new(0),
            solver_permit_changed: Notify::new(),
        }
    }

    fn enqueue(&self, waiter: Arc<Waiter>) {
        let notifications = {
            let mut state = self.lock_state();
            if state.failure.is_some() {
                waiter.status.store(CLOSED, Ordering::Release);
                return waiter.notified.notify_one();
            }
            match waiter.class {
                SolverAdmissionClass::Cex => state.cex_queue.push_back(waiter),
                SolverAdmissionClass::Inv | SolverAdmissionClass::General => {
                    state.ordinary_queue.push_back(waiter)
                }
            }
            self.schedule(&mut state)
        };
        notify(notifications);
    }

    fn abandon(&self, waiter: &Arc<Waiter>) {
        let notifications = {
            let mut state = self.lock_state();
            match waiter.status.swap(CANCELLED, Ordering::AcqRel) {
                QUEUED => {
                    let queue = match waiter.class {
                        SolverAdmissionClass::Cex => &mut state.cex_queue,
                        SolverAdmissionClass::Inv | SolverAdmissionClass::General => {
                            &mut state.ordinary_queue
                        }
                    };
                    queue.retain(|queued| !Arc::ptr_eq(queued, waiter));
                }
                GRANTED => {
                    if state.failure.is_none() {
                        release_counts(&mut state, waiter.class, waiter.slots);
                    }
                }
                CANCELLED => {}
                CLOSED => {}
                status => {
                    panic!("unknown solver waiter status {status}")
                }
            }
            self.schedule(&mut state)
        };
        notify(notifications);
    }

    fn release(&self, class: SolverAdmissionClass, slots: usize) {
        let notifications = {
            let mut state = self.lock_state();
            if state.failure.is_some() {
                return;
            }
            release_counts(&mut state, class, slots);
            self.schedule(&mut state)
        };
        notify(notifications);
    }

    fn schedule(&self, state: &mut AdmissionState) -> Vec<Arc<Waiter>> {
        let mut notifications = Vec::new();
        if state.failure.is_some() {
            return notifications;
        }
        loop {
            discard_cancelled(&mut state.cex_queue);
            discard_cancelled(&mut state.ordinary_queue);

            if state
                .cex_queue
                .front()
                .is_some_and(|waiter| self.can_grant(state, waiter))
            {
                let waiter = state.cex_queue.pop_front().expect("CEX queue front exists");
                grant(state, &waiter);
                notifications.push(waiter);
                continue;
            }
            if let Some(index) = self.oldest_admissible_ordinary(state) {
                let waiter = state
                    .ordinary_queue
                    .remove(index)
                    .expect("indexed waiter exists");
                for bypassed in state.ordinary_queue.iter().take(index) {
                    bypassed.bypass_grants.fetch_add(1, Ordering::AcqRel);
                }
                grant(state, &waiter);
                notifications.push(waiter);
                continue;
            }
            break;
        }
        notifications
    }

    fn oldest_admissible_ordinary(&self, state: &AdmissionState) -> Option<usize> {
        for (index, waiter) in state.ordinary_queue.iter().enumerate() {
            if self.can_grant(state, waiter) {
                return Some(index);
            }
            if waiter.bypass_grants.load(Ordering::Acquire) >= MAX_BYPASS_GRANTS {
                // Stop backfilling until this older weighted request can run.
                // Cancellation removes it and lets later work proceed.
                return None;
            }
        }
        None
    }

    fn can_grant(&self, state: &AdmissionState, waiter: &Waiter) -> bool {
        let Some(next_total) = state.active_total.checked_add(waiter.slots) else {
            return false;
        };
        if next_total > self.policy.max_vampire_processes {
            return false;
        }
        match waiter.class {
            SolverAdmissionClass::Cex => {
                state.active_cex + waiter.slots <= self.policy.cex_reserved_vampire_processes
            }
            SolverAdmissionClass::Inv => {
                state.active_inv + waiter.slots <= self.policy.max_inv_vampire_processes
                    && self.non_cex_capacity_available(state, waiter)
            }
            SolverAdmissionClass::General => self.non_cex_capacity_available(state, waiter),
        }
    }

    fn non_cex_capacity_available(&self, state: &AdmissionState, waiter: &Waiter) -> bool {
        let non_cex_active = state.active_total - state.active_cex;
        non_cex_active + waiter.slots <= self.policy.shared_vampire_processes()
            || (waiter.locally_bounded && state.cex_queue.is_empty())
    }

    fn poison(&self, report: FailureReport) {
        debug_assert_eq!(report.scope(), crate::FailureScope::RunGlobal);
        let notifications = {
            let mut state = self.lock_state();
            if state.failure.is_some() {
                return;
            }
            state.failure = Some(report);
            let mut notifications = state.cex_queue.drain(..).collect::<Vec<_>>();
            notifications.extend(state.ordinary_queue.drain(..));
            for waiter in &notifications {
                waiter.status.store(CLOSED, Ordering::Release);
            }
            notifications
        };
        notify(notifications);
        self.closed.notify_waiters();
    }

    fn failure(&self) -> Option<FailureReport> {
        self.lock_state().failure.clone()
    }

    fn lock_state(&self) -> AdmissionStateGuard<'_> {
        let mut state = match self.state.lock() {
            Ok(state) => state,
            Err(poisoned) => {
                let mut state = poisoned.into_inner();
                self.fail_closed_after_authority_panic(&mut state);
                state
            }
        };
        if state.failure.is_some() {
            // Keep a recovered poison quarantined even if a later refactor
            // reaches this boundary through a new controller method.
            self.close_queued(&mut state);
        }
        AdmissionStateGuard {
            controller: self,
            state,
        }
    }

    fn fail_closed_after_authority_panic(&self, state: &mut AdmissionState) {
        if state.failure.is_none() {
            state.failure = Some(FailureReport::admission_authority(
                "runtime admission authority panicked while holding shared state",
            ));
        }
        self.close_queued(state);
        self.closed.notify_waiters();
    }

    fn close_queued(&self, state: &mut AdmissionState) {
        let mut waiters = state.cex_queue.drain(..).collect::<Vec<_>>();
        waiters.extend(state.ordinary_queue.drain(..));
        for waiter in waiters {
            waiter.status.store(CLOSED, Ordering::Release);
            waiter.notified.notify_one();
        }
    }

    #[cfg(test)]
    fn inject_authority_panic(&self) {
        let _state = self.lock_state();
        panic!("inject admission-authority panic");
    }

    #[cfg(test)]
    fn state(&self) -> TestState {
        let state = self.lock_state();
        TestState {
            active_total: state.active_total,
            active_inv: state.active_inv,
            active_cex: state.active_cex,
            queued_ordinary: state.ordinary_queue.len(),
            queued_cex: state.cex_queue.len(),
            closed: state.failure.is_some(),
        }
    }
}

#[cfg(test)]
struct TestState {
    active_total: usize,
    active_inv: usize,
    active_cex: usize,
    queued_ordinary: usize,
    queued_cex: usize,
    closed: bool,
}

fn discard_cancelled(queue: &mut VecDeque<Arc<Waiter>>) {
    while queue
        .front()
        .is_some_and(|waiter| matches!(waiter.status.load(Ordering::Acquire), CANCELLED | CLOSED))
    {
        queue.pop_front();
    }
}

fn grant(state: &mut AdmissionState, waiter: &Waiter) {
    state.active_total += waiter.slots;
    match waiter.class {
        SolverAdmissionClass::Inv => state.active_inv += waiter.slots,
        SolverAdmissionClass::Cex => state.active_cex += waiter.slots,
        SolverAdmissionClass::General => {}
    }
    waiter.status.store(GRANTED, Ordering::Release);
}

fn release_counts(state: &mut AdmissionState, class: SolverAdmissionClass, slots: usize) {
    state.active_total = state
        .active_total
        .checked_sub(slots)
        .expect("solver permit accounting underflow");
    match class {
        SolverAdmissionClass::Inv => {
            state.active_inv = state
                .active_inv
                .checked_sub(slots)
                .expect("INV permit accounting underflow");
        }
        SolverAdmissionClass::Cex => {
            state.active_cex = state
                .active_cex
                .checked_sub(slots)
                .expect("CEX permit accounting underflow");
        }
        SolverAdmissionClass::General => {}
    }
}

fn notify(waiters: Vec<Arc<Waiter>>) {
    for waiter in waiters {
        waiter.notified.notify_one();
    }
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    use crate::failure::{FailureKind, FailureOrigin, FailureScope};

    #[test]
    fn rejects_invalid_profiles() {
        assert_eq!(
            RuntimeResourcePolicy::symbolic(3, 2, 1),
            Err(ResourcePolicyError::SymbolicProcessCapacity)
        );
        assert_eq!(
            RuntimeResourcePolicy::agent_only(0, 1),
            Err(ResourcePolicyError::VampireProcessCapacity)
        );
    }

    #[tokio::test]
    async fn cpu_admission_is_shared_across_handles() {
        let policy = RuntimeResourcePolicy::symbolic(4, 2, 1).unwrap();
        let (inv, cex) = create_symbolic_solver_admissions(policy).unwrap();
        let cancellation = CancellationToken::new();
        let first = inv.acquire_cpu_worker(&cancellation).await.unwrap();
        let waiting = tokio::time::timeout(
            std::time::Duration::from_millis(20),
            cex.acquire_cpu_worker(&cancellation),
        )
        .await;
        assert!(waiting.is_err());
        drop(first);
        cex.acquire_cpu_worker(&cancellation).await.unwrap();
    }

    #[tokio::test]
    async fn run_owner_waits_for_live_solver_leases_even_after_poison() {
        let policy = RuntimeResourcePolicy::symbolic(4, 2, 1).unwrap();
        let (inv, cex) = create_symbolic_solver_admissions(policy).unwrap();
        let permit = inv
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();
        inv.poison(FailureReport::admission_authority("test poison"));

        let waiting = tokio::spawn(async move {
            cex.wait_for_solver_idle().await;
        });
        tokio::time::sleep(Duration::from_millis(10)).await;
        assert!(!waiting.is_finished());

        drop(permit);
        tokio::time::timeout(Duration::from_secs(1), waiting)
            .await
            .expect("run owner did not observe solver cleanup")
            .unwrap();
        assert_eq!(
            inv.controller.live_solver_permits.load(Ordering::Acquire),
            0
        );
    }

    #[tokio::test]
    async fn paired_grant_is_atomic_and_queued_cancellation_leaks_nothing() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let running = admission
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();
        let cancellation = CancellationToken::new();
        let waiting_admission = admission.clone();
        let waiting_cancellation = cancellation.clone();
        let waiting = tokio::spawn(async move {
            waiting_admission
                .acquire_solver(2, true, &waiting_cancellation)
                .await
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;
        assert_eq!(admission.controller.state().active_total, 1);
        cancellation.cancel();
        assert!(matches!(
            waiting.await.unwrap(),
            Err(AdmissionError::Cancelled)
        ));
        assert_eq!(admission.controller.state().active_total, 1);
        drop(running);
        assert_eq!(admission.controller.state().active_total, 0);
    }

    #[tokio::test]
    async fn dropping_a_queued_acquisition_releases_a_later_grant() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let running = admission
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();

        let waiting_admission = admission.clone();
        let waiting = tokio::spawn(async move {
            waiting_admission
                .acquire_solver(2, true, &CancellationToken::new())
                .await
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;
        waiting.abort();
        assert!(matches!(waiting.await, Err(error) if error.is_cancelled()));
        assert_eq!(admission.controller.state().queued_ordinary, 0);
        assert_eq!(admission.controller.state().active_total, 1);

        drop(running);
        let successor = tokio::time::timeout(
            Duration::from_secs(1),
            admission.acquire_solver(2, true, &CancellationToken::new()),
        )
        .await
        .expect("a dropped waiter must not block its successor")
        .unwrap();
        drop(successor);
        assert_eq!(admission.controller.state().active_total, 0);
    }

    #[tokio::test]
    async fn oldest_admissible_request_backfills_idle_capacity() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let holder = admission
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();

        let pair_admission = admission.clone();
        let pair = tokio::spawn(async move {
            pair_admission
                .acquire_solver(2, true, &CancellationToken::new())
                .await
                .unwrap()
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;

        let single_admission = admission.clone();
        let single = tokio::spawn(async move {
            single_admission
                .acquire_solver(1, true, &CancellationToken::new())
                .await
                .unwrap()
        });
        let single_permit = tokio::time::timeout(Duration::from_secs(1), single)
            .await
            .expect("an admissible request must use the idle slot")
            .unwrap();
        assert!(!pair.is_finished());

        drop(holder);
        drop(single_permit);
        let pair_permit = tokio::time::timeout(Duration::from_secs(1), pair)
            .await
            .expect("the older pair must run after complete capacity is free")
            .unwrap();
        drop(pair_permit);
        assert_eq!(admission.controller.state().active_total, 0);
    }

    #[tokio::test]
    async fn finite_work_can_borrow_behind_an_unbounded_shared_capacity_waiter() {
        let policy = RuntimeResourcePolicy::symbolic(4, 4, 1).unwrap();
        let (inv, _cex) = create_symbolic_solver_admissions(policy).unwrap();
        let shared = inv
            .acquire_solver(2, false, &CancellationToken::new())
            .await
            .unwrap();

        let unbounded_admission = inv.clone();
        let unbounded = tokio::spawn(async move {
            unbounded_admission
                .acquire_solver(1, false, &CancellationToken::new())
                .await
                .unwrap()
        });
        wait_for_queue(&inv, SolverAdmissionClass::Inv, 1).await;

        let bounded_admission = inv.clone();
        let bounded = tokio::spawn(async move {
            bounded_admission
                .acquire_solver(1, true, &CancellationToken::new())
                .await
                .unwrap()
        });
        let bounded_permit = tokio::time::timeout(Duration::from_secs(1), bounded)
            .await
            .expect("bounded work must borrow otherwise-idle reserved capacity")
            .unwrap();
        assert!(!unbounded.is_finished());

        drop(shared);
        let unbounded_permit = tokio::time::timeout(Duration::from_secs(1), unbounded)
            .await
            .expect("the older unbounded request must run after shared capacity is free")
            .unwrap();
        drop(unbounded_permit);
        drop(bounded_permit);
        assert_eq!(inv.controller.state().active_total, 0);
    }

    #[tokio::test]
    async fn bounded_bypass_reserves_capacity_for_an_older_weighted_request() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let holder = admission
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();

        let pair_admission = admission.clone();
        let pair = tokio::spawn(async move {
            pair_admission
                .acquire_solver(2, true, &CancellationToken::new())
                .await
                .unwrap()
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;

        for _ in 0..MAX_BYPASS_GRANTS {
            let single = admission
                .acquire_solver(1, true, &CancellationToken::new())
                .await
                .unwrap();
            drop(single);
        }
        let blocked_admission = admission.clone();
        let blocked_single = tokio::spawn(async move {
            blocked_admission
                .acquire_solver(1, true, &CancellationToken::new())
                .await
                .unwrap()
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 2).await;
        assert!(!pair.is_finished());
        assert!(!blocked_single.is_finished());

        drop(holder);
        let pair_permit = tokio::time::timeout(Duration::from_secs(1), pair)
            .await
            .expect("bounded bypass must let the older pair reserve released capacity")
            .unwrap();
        assert!(!blocked_single.is_finished());
        drop(pair_permit);
        let single_permit = tokio::time::timeout(Duration::from_secs(1), blocked_single)
            .await
            .expect("later work must resume after the older pair")
            .unwrap();
        drop(single_permit);
        assert_eq!(admission.controller.state().active_total, 0);
    }

    #[tokio::test]
    async fn queued_cex_receives_the_next_complete_borrowed_pair() {
        let policy = RuntimeResourcePolicy::symbolic(4, 4, 1).unwrap();
        let (inv, cex) = create_symbolic_solver_admissions(policy).unwrap();
        let cancellation = CancellationToken::new();
        let shared = inv.acquire_solver(2, false, &cancellation).await.unwrap();
        let borrowed_one = inv.acquire_solver(1, true, &cancellation).await.unwrap();
        let borrowed_two = inv.acquire_solver(1, true, &cancellation).await.unwrap();

        let queued_cex = cex.clone();
        let cex_cancellation = cancellation.clone();
        let cex_task = tokio::spawn(async move {
            queued_cex
                .acquire_solver(2, true, &cex_cancellation)
                .await
                .unwrap()
        });
        wait_for_queue(&cex, SolverAdmissionClass::Cex, 1).await;

        let later_inv = inv.clone();
        let inv_cancellation = cancellation.clone();
        let later_task = tokio::spawn(async move {
            later_inv
                .acquire_solver(1, true, &inv_cancellation)
                .await
                .unwrap()
        });
        wait_for_queue(&inv, SolverAdmissionClass::Inv, 1).await;

        drop(borrowed_one);
        tokio::time::sleep(Duration::from_millis(10)).await;
        assert_eq!(inv.controller.state().active_total, 3);
        assert!(!cex_task.is_finished());
        assert!(!later_task.is_finished());

        drop(borrowed_two);
        let cex_permit = tokio::time::timeout(Duration::from_secs(1), cex_task)
            .await
            .expect("CEX pair must receive the released reservation")
            .unwrap();
        assert_eq!(inv.controller.state().active_cex, 2);
        assert!(!later_task.is_finished());

        drop(cex_permit);
        drop(shared);
        let later_permit = tokio::time::timeout(Duration::from_secs(1), later_task)
            .await
            .expect("later borrower must eventually run")
            .unwrap();
        drop(later_permit);
        assert_eq!(inv.controller.state().active_total, 0);
    }

    #[tokio::test]
    async fn inv_cap_and_unbounded_non_borrowing_preserve_cex_capacity() {
        let policy = RuntimeResourcePolicy::symbolic(4, 2, 1).unwrap();
        let (inv, cex) = create_symbolic_solver_admissions(policy).unwrap();
        let cancellation = CancellationToken::new();
        let inv_pair = inv.acquire_solver(2, false, &cancellation).await.unwrap();

        let later_inv = inv.clone();
        let later_cancellation = cancellation.clone();
        let waiting = tokio::spawn(async move {
            later_inv
                .acquire_solver(1, false, &later_cancellation)
                .await
                .unwrap()
        });
        wait_for_queue(&inv, SolverAdmissionClass::Inv, 1).await;
        assert_eq!(inv.controller.state().active_inv, 2);

        let cex_pair = cex.acquire_solver(2, true, &cancellation).await.unwrap();
        assert_eq!(inv.controller.state().active_total, 4);
        assert!(!waiting.is_finished());

        drop(inv_pair);
        let later_permit = tokio::time::timeout(Duration::from_secs(1), waiting)
            .await
            .expect("INV work must run after the configured INV cap is released")
            .unwrap();
        drop(later_permit);
        drop(cex_pair);
        assert_eq!(inv.controller.state().active_total, 0);
    }

    #[tokio::test]
    async fn cancellation_and_drop_stress_preserves_admission_accounting() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        for iteration in 0..100 {
            let holder = admission
                .acquire_solver(1, false, &CancellationToken::new())
                .await
                .unwrap();
            let cancellation = CancellationToken::new();
            let queued_admission = admission.clone();
            let queued_cancellation = cancellation.clone();
            let queued = tokio::spawn(async move {
                queued_admission
                    .acquire_solver(2, true, &queued_cancellation)
                    .await
            });
            wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;
            if iteration % 2 == 0 {
                cancellation.cancel();
                assert!(matches!(
                    queued.await.unwrap(),
                    Err(AdmissionError::Cancelled)
                ));
            } else {
                queued.abort();
                assert!(matches!(queued.await, Err(error) if error.is_cancelled()));
            }
            drop(holder);

            let successor = admission
                .acquire_solver(2, true, &CancellationToken::new())
                .await
                .unwrap();
            drop(successor);
            let state = admission.controller.state();
            assert_eq!(state.active_total, 0);
            assert_eq!(state.queued_ordinary, 0);
        }
    }

    #[tokio::test]
    async fn run_global_failure_closes_admission_and_quarantines_capacity() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let running = admission
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();

        let queued_admission = admission.clone();
        let queued = tokio::spawn(async move {
            queued_admission
                .acquire_solver(2, true, &CancellationToken::new())
                .await
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;

        running.poison(run_global_failure());
        let Err(AdmissionError::Closed(report)) = queued.await.unwrap() else {
            panic!("queued work must receive the admission's fatal report")
        };
        assert_eq!(report.origin(), FailureOrigin::VampireProofSearch);
        drop(running);

        let state = admission.controller.state();
        assert!(state.closed);
        assert_eq!(state.active_total, 1);
        assert_eq!(state.queued_ordinary, 0);
        assert!(matches!(
            admission
                .acquire_solver(1, true, &CancellationToken::new())
                .await,
            Err(AdmissionError::Closed(_))
        ));
        assert!(matches!(
            admission
                .acquire_cpu_worker(&CancellationToken::new())
                .await,
            Err(AdmissionError::Closed(_))
        ));
    }

    #[tokio::test]
    async fn poisoning_a_granted_unobserved_waiter_prevents_post_fatal_launch() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let holder = admission
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();

        let waiting_admission = admission.clone();
        let waiting = tokio::spawn(async move {
            waiting_admission
                .acquire_solver(2, true, &CancellationToken::new())
                .await
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;

        // Releasing the holder synchronously grants the pair. Poison before
        // yielding, so the granted future cannot observe its status first.
        drop(holder);
        admission.poison(run_global_failure());
        let Err(AdmissionError::Closed(report)) = waiting.await.unwrap() else {
            panic!("a granted but unobserved waiter must not cross admission closure")
        };
        assert_eq!(report.origin(), FailureOrigin::VampireProofSearch);
        let state = admission.controller.state();
        assert!(state.closed);
        assert_eq!(state.active_total, 2);
        assert_eq!(state.queued_ordinary, 0);
    }

    #[tokio::test]
    async fn poisoned_admission_authority_fails_closed_and_wakes_waiters() {
        let policy = RuntimeResourcePolicy::agent_only(2, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let holder = admission
            .acquire_solver(1, false, &CancellationToken::new())
            .await
            .unwrap();

        let waiting_admission = admission.clone();
        let waiting = tokio::spawn(async move {
            waiting_admission
                .acquire_solver(2, true, &CancellationToken::new())
                .await
        });
        wait_for_queue(&admission, SolverAdmissionClass::General, 1).await;

        let controller = Arc::clone(&admission.controller);
        assert!(
            std::thread::spawn(move || {
                controller.inject_authority_panic();
            })
            .join()
            .is_err()
        );

        let Err(AdmissionError::Closed(report)) = waiting.await.unwrap() else {
            panic!("a poisoned admission authority must wake queued work")
        };
        assert_eq!(report.origin(), FailureOrigin::RunControl);
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(report.scope(), FailureScope::RunGlobal);

        drop(holder);
        let state = admission.controller.state();
        assert!(state.closed);
        assert_eq!(state.active_total, 1);
        assert_eq!(state.queued_ordinary, 0);
        assert!(matches!(
            admission
                .acquire_solver(1, true, &CancellationToken::new())
                .await,
            Err(AdmissionError::Closed(_))
        ));
    }

    fn run_global_failure() -> FailureReport {
        FailureReport::try_new(
            FailureOrigin::VampireProofSearch,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            Some("owned Vampire descendants survived cleanup".to_string()),
            Vec::new(),
        )
        .unwrap()
    }

    async fn wait_for_queue(
        admission: &SolverAdmission,
        class: SolverAdmissionClass,
        count: usize,
    ) {
        tokio::time::timeout(Duration::from_secs(1), async {
            loop {
                let state = admission.controller.state();
                let observed = match class {
                    SolverAdmissionClass::Cex => state.queued_cex,
                    SolverAdmissionClass::Inv | SolverAdmissionClass::General => {
                        state.queued_ordinary
                    }
                };
                if observed == count {
                    return;
                }
                tokio::task::yield_now().await;
            }
        })
        .await
        .expect("waiter must enter its admission queue");
    }
}

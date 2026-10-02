//! Persistent symbolic CEX state and exact W-check boundaries.
//!
//! Phase 4B owns construction, one-attempt recording, and refutation
//! resolution. Phase 4C adds the fair two-axis scheduler and the serial CEX
//! lane over those exact boundaries.

use std::collections::{BTreeMap, HashSet, VecDeque};
use std::sync::Arc;
use std::time::Duration;

use serde_json::json;

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore, AttemptId, BackendId, ScopeTag};
use crate::encoding::{
    EncodingError, PreparedWLayerBundle, SolverBodySource, SolverEncodingContext,
};
use crate::entailment::{
    EmptyCheckEvidence, Entailment, EntailmentCheckResult, EntailmentCounterexample,
    EntailmentInvocationOutcome, assemble_entailment, check_entailment_detailed,
    resolve_entailment_counterexample,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::{
    CertificationInstance, CertificationRuntime, CertifiedInvalidity, CertifiedValidity,
    InvalidityCertificationOutcome, SearchFeedback, VerificationParameters, certify_invalid,
};
use crate::runtime::{
    AdmissionError, CancellationToken, CpuJobError, SolverAdmission, SolverAdmissionClass,
};
use crate::task::SynthesisTask;
use crate::telemetry::{TelemetryHandle, qf_formula_shape};
use crate::vampire::{
    FmbContourStrategy, FmbOptions, FmbSize, VampireMode, VampireProof, VampireSearchBudget,
    VampireWorkerCommand,
};

use super::inv::SymbolicLaneOutcome;
use super::w_channel::{ProvedWEntry, WProofSender, WPublicationOutcome};

// ------------------------------------------------------------
// Caller-Owned Policy
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WLimitGrowth {
    Linear(Duration),
    Geometric(u64),
}

impl WLimitGrowth {
    pub fn geometric(factor: u64) -> Result<Self, &'static str> {
        if factor < 2 {
            return Err("geometric W-limit growth must be at least two");
        }
        Ok(Self::Geometric(factor))
    }

    pub fn apply(self, limit: Duration) -> Option<Duration> {
        match self {
            Self::Linear(increment) => limit.checked_add(increment),
            Self::Geometric(factor) => limit.checked_mul(u32::try_from(factor).ok()?),
        }
    }

    fn is_valid(self) -> bool {
        match self {
            Self::Linear(increment) => !increment.is_zero(),
            Self::Geometric(factor) => (2..=u64::from(u32::MAX)).contains(&factor),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WSearchSchedule {
    fresh_batch_size: usize,
    retry_batch_size: usize,
    initial_limit: Duration,
    limit_growth: WLimitGrowth,
}

impl WSearchSchedule {
    pub fn new(
        fresh_batch_size: usize,
        retry_batch_size: usize,
        initial_limit: Duration,
        limit_growth: WLimitGrowth,
    ) -> Result<Self, &'static str> {
        if fresh_batch_size == 0 || retry_batch_size == 0 {
            return Err("W-search batch sizes must be positive");
        }
        if initial_limit.is_zero() {
            return Err("the initial W-search limit must be positive");
        }
        if !limit_growth.is_valid() {
            return Err("W-search limit growth must be positive and unbounded");
        }
        Ok(Self {
            fresh_batch_size,
            retry_batch_size,
            initial_limit,
            limit_growth,
        })
    }

    pub fn fresh_batch_size(&self) -> usize {
        self.fresh_batch_size
    }

    pub fn retry_batch_size(&self) -> usize {
        self.retry_batch_size
    }

    pub fn initial_limit(&self) -> Duration {
        self.initial_limit
    }

    pub fn limit_growth(&self) -> WLimitGrowth {
        self.limit_growth
    }
}

impl Default for WSearchSchedule {
    fn default() -> Self {
        Self::new(10, 10, Duration::from_secs(30), WLimitGrowth::Geometric(2))
            .expect("the approved W-search defaults are valid")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolicHoudiniPolicy {
    admit_higher_w_layers: bool,
    w_search: WSearchSchedule,
}

impl SymbolicHoudiniPolicy {
    pub fn new(admit_higher_w_layers: bool, w_search: WSearchSchedule) -> Self {
        Self {
            admit_higher_w_layers,
            w_search,
        }
    }

    pub fn admit_higher_w_layers(&self) -> bool {
        self.admit_higher_w_layers
    }

    pub fn w_search(&self) -> &WSearchSchedule {
        &self.w_search
    }
}

impl Default for SymbolicHoudiniPolicy {
    fn default() -> Self {
        Self::new(false, WSearchSchedule::default())
    }
}

// ------------------------------------------------------------
// Runtime And Public Results
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct SymbolicCexRuntime {
    vampire: VampireWorkerCommand,
    certification: CertificationRuntime,
}

impl SymbolicCexRuntime {
    pub fn new(vampire: VampireWorkerCommand, certification: CertificationRuntime) -> Self {
        Self {
            vampire,
            certification,
        }
    }
}

#[derive(Clone, Debug)]
pub enum CertifiedSynthesisResult {
    Valid(CertifiedValidity),
    Invalid(CertifiedInvalidity),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WSearchAttempt {
    index: u64,
    start_size: FmbSize,
    limit: Duration,
}

impl WSearchAttempt {
    pub fn new(index: u64, start_size: FmbSize, limit: Duration) -> Result<Self, &'static str> {
        if limit.is_zero() {
            return Err("a W-search attempt limit must be positive");
        }
        Ok(Self {
            index,
            start_size,
            limit,
        })
    }

    pub fn index(self) -> u64 {
        self.index
    }

    pub fn start_size(self) -> FmbSize {
        self.start_size
    }

    pub fn limit(self) -> Duration {
        self.limit
    }
}

#[derive(Clone, Debug)]
pub enum WSearchResult {
    Proved {
        proof: VampireProof,
        empty_evidence: EmptyCheckEvidence,
    },
    Refuted(EntailmentCounterexample),
    TimedOut {
        next_start_size: FmbSize,
        peer_failure: Option<FailureReport>,
    },
    Failure {
        report: FailureReport,
        next_start_size: FmbSize,
    },
}

impl WSearchResult {
    fn is_conclusive(&self) -> bool {
        matches!(self, Self::Proved { .. } | Self::Refuted(_))
    }

    fn next_start_size(&self, fallback: FmbSize) -> FmbSize {
        match self {
            Self::TimedOut {
                next_start_size, ..
            }
            | Self::Failure {
                next_start_size, ..
            } => (*next_start_size).max(fallback),
            Self::Proved { .. } | Self::Refuted(_) => fallback,
        }
    }
}

#[derive(Clone, Debug)]
pub enum WInitializationInvocationOutcome {
    Result(Box<CheckedWInitialization>),
    Cancelled,
    RunFatal(FailureReport),
}

/// One W initialization result inseparably bound to the exact checked query.
///
/// Construction is private. A caller can inspect this value, but only
/// `check_w_initialization` can produce one for `record_w_initialization`.
#[derive(Clone, Debug)]
pub struct CheckedWInitialization {
    attempt: WSearchAttempt,
    context_id: Arc<str>,
    backend_id: BackendId,
    bundle_identity: Arc<str>,
    entailment_identity: Option<Arc<str>>,
    attempt_id: Option<AttemptId>,
    terminal_artifact: Option<ArtifactRef>,
    result: WSearchResult,
}

impl CheckedWInitialization {
    pub fn attempt(&self) -> WSearchAttempt {
        self.attempt
    }

    pub fn result(&self) -> &WSearchResult {
        &self.result
    }

    pub fn attempt_id(&self) -> Option<AttemptId> {
        self.attempt_id
    }

    pub fn terminal_artifact(&self) -> Option<ArtifactRef> {
        self.terminal_artifact
    }
}

/// Compact, durable reference to one completed W initialization attempt.
#[derive(Clone, Debug)]
pub struct WAttemptRecord {
    attempt: WSearchAttempt,
    bundle_identity: Arc<str>,
    entailment_identity: Option<Arc<str>>,
    attempt_id: Option<AttemptId>,
    terminal_artifact: Option<ArtifactRef>,
}

impl WAttemptRecord {
    pub fn attempt(&self) -> WSearchAttempt {
        self.attempt
    }

    pub fn bundle_identity(&self) -> &str {
        &self.bundle_identity
    }

    pub fn entailment_identity(&self) -> Option<&str> {
        self.entailment_identity.as_deref()
    }

    pub fn attempt_id(&self) -> Option<AttemptId> {
        self.attempt_id
    }

    pub fn terminal_artifact(&self) -> Option<ArtifactRef> {
        self.terminal_artifact
    }
}

#[derive(Clone, Debug)]
pub enum CounterexampleResolutionOutcome {
    Rejected(SearchFeedback),
    Failure(FailureReport),
}

#[derive(Clone, Debug)]
pub enum WRefutationResolutionOutcome {
    Certified(CertifiedInvalidity),
    Recorded,
    Cancelled,
    RunFatal(FailureReport),
}

// ------------------------------------------------------------
// Persistent CEX State
// ------------------------------------------------------------

#[derive(Debug)]
struct CounterexampleResolutionRecord {
    input: Option<CertificationInstance>,
    outcome: Option<CounterexampleResolutionOutcome>,
    attempt_count: u64,
    retry_in_flight: bool,
}

#[derive(Debug)]
struct WSearchEntry {
    bundle: Option<Arc<PreparedWLayerBundle>>,
    initialization_entailment: Option<Entailment>,
    entailment_identity: Option<Arc<str>>,
    result: Option<WSearchResult>,
    initialization_evidence: Option<ArtifactRef>,
    last_attempt: Option<WSearchAttempt>,
    attempt_history: Vec<WAttemptRecord>,
    next_start_size: FmbSize,
    first_attempt_complete: bool,
    resolution: Option<CounterexampleResolutionRecord>,
}

impl Default for WSearchEntry {
    fn default() -> Self {
        Self {
            bundle: None,
            initialization_entailment: None,
            entailment_identity: None,
            result: None,
            initialization_evidence: None,
            last_attempt: None,
            attempt_history: Vec::new(),
            next_start_size: FmbSize::ONE,
            first_attempt_complete: false,
            resolution: None,
        }
    }
}

#[derive(Debug, Default)]
struct ResolutionRetryQueue {
    ready: VecDeque<u64>,
    queued: HashSet<u64>,
}

impl ResolutionRetryQueue {
    fn record_failure(&mut self, index: u64, report: &FailureReport) {
        if report.scope() == FailureScope::LaneLocal
            && report.retryable()
            && self.queued.insert(index)
        {
            self.ready.push_back(index);
        }
    }

    fn next(&mut self) -> Option<u64> {
        let index = self.ready.pop_front()?;
        self.queued.remove(&index);
        Some(index)
    }

    fn restore(&mut self, index: u64) {
        if self.queued.insert(index) {
            self.ready.push_front(index);
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum WSchedulePhase {
    #[default]
    Bootstrap,
    Fresh,
    Retry,
}

/// Opaque scheduling ledger for the approved fresh/retry alternation.
///
/// `eligible_before_fresh` snapshots the retry frontier when a fresh cycle
/// begins. Results from that fresh cycle become eligible only in a later
/// cycle. Each selected retry rotates to the FIFO tail, so no index can occur
/// twice in one retry round.
#[derive(Debug, Default)]
struct WAttemptScheduler {
    phase: WSchedulePhase,
    fresh_completed: usize,
    retry_ready: VecDeque<u64>,
    retry_queued: HashSet<u64>,
    eligible_before_fresh: usize,
    retry_remaining: usize,
}

impl WAttemptScheduler {
    fn retryable(result: &WSearchResult) -> bool {
        matches!(result, WSearchResult::TimedOut { .. })
            || matches!(
                result,
                WSearchResult::Failure { report, .. }
                    if report.scope() == FailureScope::LaneLocal
            )
    }

    fn select(
        &self,
        next_w_index: u64,
        entries: &BTreeMap<u64, WSearchEntry>,
        schedule: &WSearchSchedule,
    ) -> Result<WSearchAttempt, FailureReport> {
        match self.phase {
            WSchedulePhase::Bootstrap | WSchedulePhase::Fresh => {
                WSearchAttempt::new(next_w_index, FmbSize::ONE, schedule.initial_limit())
                    .map_err(cex_state_failure)
            }
            WSchedulePhase::Retry => {
                let index = *self
                    .retry_ready
                    .front()
                    .ok_or_else(|| cex_state_failure("the W retry phase has no eligible retry"))?;
                let entry = entries.get(&index).ok_or_else(|| {
                    cex_state_failure("the W retry queue refers to a missing search entry")
                })?;
                let prior = entry.last_attempt.ok_or_else(|| {
                    cex_state_failure("the W retry queue refers to an unattempted index")
                })?;
                let limit = schedule
                    .limit_growth()
                    .apply(prior.limit())
                    .ok_or_else(|| {
                        cex_state_failure(
                            "the W retry time limit exceeded its runtime representation",
                        )
                    })?;
                WSearchAttempt::new(index, entry.next_start_size, limit).map_err(cex_state_failure)
            }
        }
    }

    fn record_completion(
        &mut self,
        attempt: WSearchAttempt,
        first_attempt: bool,
        result: &WSearchResult,
        schedule: &WSearchSchedule,
    ) -> Result<(), FailureReport> {
        if first_attempt {
            if self.phase == WSchedulePhase::Bootstrap {
                if attempt.index() != 0 {
                    return Err(cex_state_failure(
                        "the W scheduler bootstrap completed a nonzero index",
                    ));
                }
                self.update_retry_eligibility(attempt.index(), result);
                self.begin_fresh_cycle();
                return Ok(());
            }
            if self.phase != WSchedulePhase::Fresh {
                return Err(cex_state_failure(
                    "a fresh W result completed during the retry phase",
                ));
            }
            let fresh_completed = self.fresh_completed.checked_add(1).ok_or_else(|| {
                cex_state_failure("the W fresh-cycle counter exceeded its runtime representation")
            })?;
            self.update_retry_eligibility(attempt.index(), result);
            self.fresh_completed = fresh_completed;
            if self.fresh_completed == schedule.fresh_batch_size() {
                self.fresh_completed = 0;
                self.retry_remaining = self
                    .eligible_before_fresh
                    .min(self.retry_ready.len())
                    .min(schedule.retry_batch_size());
                if self.retry_remaining == 0 {
                    self.begin_fresh_cycle();
                } else {
                    self.phase = WSchedulePhase::Retry;
                }
            }
            return Ok(());
        }

        if self.phase == WSchedulePhase::Retry
            && self.retry_ready.front().copied() == Some(attempt.index())
        {
            self.retry_ready.pop_front();
            self.retry_queued.remove(&attempt.index());
            if Self::retryable(result) {
                self.enqueue_retry(attempt.index());
            }
            self.retry_remaining = self.retry_remaining.saturating_sub(1);
            if self.retry_remaining == 0 {
                self.begin_fresh_cycle();
            }
        } else {
            self.update_retry_eligibility(attempt.index(), result);
        }
        Ok(())
    }

    fn begin_fresh_cycle(&mut self) {
        self.phase = WSchedulePhase::Fresh;
        self.fresh_completed = 0;
        self.eligible_before_fresh = self.retry_ready.len();
        self.retry_remaining = 0;
    }

    fn update_retry_eligibility(&mut self, index: u64, result: &WSearchResult) {
        if Self::retryable(result) {
            self.enqueue_retry(index);
        } else {
            self.remove_retry(index);
        }
    }

    fn enqueue_retry(&mut self, index: u64) {
        if self.retry_queued.insert(index) {
            self.retry_ready.push_back(index);
        }
    }

    fn remove_retry(&mut self, index: u64) {
        if self.retry_queued.remove(&index) {
            self.retry_ready.retain(|queued| *queued != index);
        }
    }
}

#[derive(Debug, Default)]
struct WSearchProgress {
    entries: BTreeMap<u64, WSearchEntry>,
    attempts: WAttemptScheduler,
    resolution_retries: ResolutionRetryQueue,
    w_zero_proved: bool,
    proved_unpublished: BTreeMap<u64, ()>,
    publication_complete: HashSet<u64>,
    run_fatal: Option<FailureReport>,
}

impl WSearchProgress {
    fn latch_run_fatal(&mut self, report: FailureReport) {
        if self.run_fatal.is_none() {
            self.run_fatal = Some(report);
        }
    }

    fn next_resolution_retry(&mut self) -> Option<u64> {
        if self.run_fatal.is_some() {
            return None;
        }
        self.resolution_retries.next()
    }

    fn commit_attempt(
        &mut self,
        next_w_index: &mut u64,
        attempt: WSearchAttempt,
        result: WSearchResult,
        initialization_evidence: Option<ArtifactRef>,
        attempt_record: WAttemptRecord,
        policy: &SymbolicHoudiniPolicy,
    ) -> Result<(), FailureReport> {
        let first_attempt = !self
            .entries
            .get(&attempt.index())
            .is_some_and(|entry| entry.first_attempt_complete);
        let advanced_index = if first_attempt {
            Some(next_w_index.checked_add(1).ok_or_else(|| {
                cex_state_failure("the W-index space was exhausted while recording an attempt")
            })?)
        } else {
            None
        };
        let next_start_size = result.next_start_size(attempt.start_size());
        let run_fatal = match &result {
            WSearchResult::Failure { report, .. } if report.scope() == FailureScope::RunGlobal => {
                Some(report.clone())
            }
            _ => None,
        };
        let proved = matches!(&result, WSearchResult::Proved { .. });
        let proves_w_zero = attempt.index() == 0 && proved;
        self.attempts
            .record_completion(attempt, first_attempt, &result, policy.w_search())?;
        let entry = self.entries.entry(attempt.index()).or_default();
        entry.result = Some(result);
        entry.initialization_evidence = initialization_evidence;
        entry.last_attempt = Some(attempt);
        entry.attempt_history.push(attempt_record);
        entry.next_start_size = next_start_size;
        entry.first_attempt_complete = true;
        if let Some(index) = advanced_index {
            *next_w_index = index;
        }
        if proved && (attempt.index() == 0 || policy.admit_higher_w_layers()) {
            self.proved_unpublished.insert(attempt.index(), ());
        }
        self.w_zero_proved |= proves_w_zero;
        if self.run_fatal.is_none() {
            self.run_fatal = run_fatal;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct SymbolicCexState {
    verification: VerificationParameters,
    admission: SolverAdmission,
    policy: SymbolicHoudiniPolicy,
    encoding_context: SolverEncodingContext,
    next_w_index: u64,
    search: WSearchProgress,
    certified_invalid: Option<CertifiedSynthesisResult>,
    artifacts: ArtifactStore,
    telemetry: TelemetryHandle,
}

impl SymbolicCexState {
    pub fn verification(&self) -> &VerificationParameters {
        &self.verification
    }

    pub fn admission(&self) -> &SolverAdmission {
        &self.admission
    }

    pub fn policy(&self) -> &SymbolicHoudiniPolicy {
        &self.policy
    }

    pub fn encoding_context(&self) -> &SolverEncodingContext {
        &self.encoding_context
    }

    pub fn next_w_index(&self) -> u64 {
        self.next_w_index
    }

    pub fn certified_invalid(&self) -> Option<&CertifiedSynthesisResult> {
        self.certified_invalid.as_ref()
    }

    pub fn artifacts(&self) -> &ArtifactStore {
        &self.artifacts
    }

    /// Attach one observational run telemetry handle before the lane starts.
    pub fn attach_telemetry(&mut self, telemetry: TelemetryHandle) {
        self.telemetry = telemetry;
    }

    pub fn w_bundle(&self, index: u64) -> Option<&Arc<PreparedWLayerBundle>> {
        self.search
            .entries
            .get(&index)
            .and_then(|entry| entry.bundle.as_ref())
    }

    pub fn w_result(&self, index: u64) -> Option<&WSearchResult> {
        self.search
            .entries
            .get(&index)
            .and_then(|entry| entry.result.as_ref())
    }

    pub fn w_initialization_evidence(&self, index: u64) -> Option<ArtifactRef> {
        self.search
            .entries
            .get(&index)
            .and_then(|entry| entry.initialization_evidence)
    }

    pub fn w_attempt_history(&self, index: u64) -> &[WAttemptRecord] {
        self.search
            .entries
            .get(&index)
            .map_or(&[], |entry| entry.attempt_history.as_slice())
    }

    pub fn next_w_start_size(&self, index: u64) -> FmbSize {
        self.search
            .entries
            .get(&index)
            .map_or(FmbSize::ONE, |entry| entry.next_start_size)
    }

    pub fn run_fatal(&self) -> Option<&FailureReport> {
        self.search.run_fatal.as_ref()
    }

    pub fn w_was_published(&self, index: u64) -> bool {
        self.search.publication_complete.contains(&index)
    }

    /// Record one complete W attempt. Publication evidence is committed before
    /// the in-memory conclusive result becomes visible.
    pub fn record_w_initialization(
        &mut self,
        checked: Box<CheckedWInitialization>,
    ) -> Result<WSearchResult, FailureReport> {
        let recorded = self.try_record_w_initialization(*checked);
        if let Err(report) = &recorded
            && report.scope() == FailureScope::RunGlobal
        {
            self.latch_run_fatal(report.clone());
        }
        recorded
    }

    fn try_record_w_initialization(
        &mut self,
        checked: CheckedWInitialization,
    ) -> Result<WSearchResult, FailureReport> {
        let CheckedWInitialization {
            attempt,
            context_id,
            backend_id,
            bundle_identity,
            entailment_identity,
            attempt_id,
            terminal_artifact,
            result,
        } = checked;
        self.validate_recordable_attempt(attempt, false)?;
        if context_id.as_ref() != self.encoding_context.context_id()
            || backend_id != self.artifacts.backend_id()
        {
            return Err(cex_state_failure(
                "a checked W result belongs to another encoding context or artifact backend",
            ));
        }
        let entry = self
            .search
            .entries
            .get(&attempt.index())
            .expect("recordable W attempt has a prepared entry");
        let expected_bundle_identity = entry
            .bundle
            .as_ref()
            .expect("recordable W attempt has a prepared bundle")
            .identity();
        if expected_bundle_identity != bundle_identity.as_ref() {
            return Err(cex_state_failure(
                "a checked W result belongs to another prepared W bundle",
            ));
        }
        match (
            entry.entailment_identity.as_deref(),
            entailment_identity.as_deref(),
        ) {
            (Some(expected), Some(actual)) if expected == actual => {}
            (Some(_), None) | (None, None) => {}
            _ => {
                return Err(cex_state_failure(
                    "a checked W result belongs to another initialization entailment",
                ));
            }
        }
        if terminal_artifact
            .is_some_and(|reference| reference.backend_id() != self.artifacts.backend_id())
        {
            return Err(cex_state_failure(
                "a W attempt summary belongs to another artifact backend",
            ));
        }
        if result.is_conclusive() {
            let expected_identity = entailment_identity.as_deref().ok_or_else(|| {
                cex_state_failure("conclusive W evidence requires an assembled entailment")
            })?;
            let actual_identity = result_entailment_identity(&result).ok_or_else(|| {
                cex_state_failure("conclusive W evidence has inconsistent logical identities")
            })?;
            if actual_identity != expected_identity {
                return Err(cex_state_failure(
                    "a W result belongs to another initialization entailment",
                ));
            }
        }
        if let Some(existing) = self
            .w_result(attempt.index())
            .filter(|result| result.is_conclusive())
        {
            return Ok(existing.clone());
        }

        let initialization_evidence = match &result {
            WSearchResult::Proved {
                proof,
                empty_evidence,
            } => Some(publish_w_initialization_evidence(
                &self.artifacts,
                attempt.index(),
                proof,
                empty_evidence,
            )?),
            _ => None,
        };
        let attempt_record = WAttemptRecord {
            attempt,
            bundle_identity,
            entailment_identity,
            attempt_id,
            terminal_artifact,
        };
        let run_fatal = match &result {
            WSearchResult::Failure { report, .. } if report.scope() == FailureScope::RunGlobal => {
                Some(report.clone())
            }
            _ => None,
        };
        let policy = self.policy.clone();
        self.search.commit_attempt(
            &mut self.next_w_index,
            attempt,
            result.clone(),
            initialization_evidence,
            attempt_record,
            &policy,
        )?;
        match run_fatal {
            Some(report) => Err(report),
            None => Ok(result),
        }
    }

    fn bind_w_initialization_entailment(
        &mut self,
        index: u64,
        entailment: Entailment,
    ) -> Result<(), FailureReport> {
        let entry = self.search.entries.get_mut(&index).ok_or_else(|| {
            cex_state_failure("a W initialization entailment requires its prepared bundle")
        })?;
        let identity = entailment.identity_arc();
        match entry.entailment_identity.as_deref() {
            Some(expected) if expected != identity.as_ref() => Err(cex_state_failure(
                "reassembled W initialization changed its logical identity",
            )),
            Some(_) => {
                if entry.initialization_entailment.is_none() {
                    entry.initialization_entailment = Some(entailment);
                }
                Ok(())
            }
            None => {
                entry.entailment_identity = Some(identity);
                entry.initialization_entailment = Some(entailment);
                Ok(())
            }
        }
    }

    /// Select one retained transient resolution retry. This does not select or
    /// launch W entailment work, and every completed retryable failure returns
    /// to the FIFO behind its peers.
    pub fn next_counterexample_resolution(&mut self) -> Option<(u64, EntailmentCounterexample)> {
        if self.search.run_fatal.is_some() || self.certified_invalid.is_some() {
            return None;
        }
        while let Some(index) = self.search.next_resolution_retry() {
            let Some(entry) = self.search.entries.get_mut(&index) else {
                continue;
            };
            let Some(WSearchResult::Refuted(counterexample)) = &entry.result else {
                continue;
            };
            let Some(record) = &entry.resolution else {
                continue;
            };
            if !record.retry_in_flight
                && matches!(
                    record.outcome,
                    Some(CounterexampleResolutionOutcome::Failure(ref report))
                        if report.scope() == FailureScope::LaneLocal && report.retryable()
                )
            {
                let counterexample = counterexample.clone();
                entry
                    .resolution
                    .as_mut()
                    .expect("the selected retry has resolution progress")
                    .retry_in_flight = true;
                return Some((index, counterexample));
            }
        }
        None
    }

    pub fn record_counterexample_resolution(
        &mut self,
        index: u64,
        counterexample: &EntailmentCounterexample,
        input: Option<CertificationInstance>,
        outcome: CounterexampleResolutionOutcome,
    ) -> Result<(), FailureReport> {
        if let Err(report) = self.validate_counterexample(index, counterexample) {
            self.latch_run_fatal(report.clone());
            return Err(report);
        }
        if let CounterexampleResolutionOutcome::Failure(report) = &outcome
            && report.scope() == FailureScope::RunGlobal
        {
            let report = report.clone();
            self.latch_run_fatal(report.clone());
            return Err(report);
        }
        let entry = self
            .search
            .entries
            .get_mut(&index)
            .expect("counterexample validation requires the indexed entry");
        if let Some(record) = &entry.resolution
            && record.attempt_count > 0
            && !record.retry_in_flight
        {
            let report = cex_state_failure(
                "a counterexample-resolution retry was not selected by the retry ledger",
            );
            self.latch_run_fatal(report.clone());
            return Err(report);
        }
        let attempt_count = entry
            .resolution
            .as_ref()
            .map_or(1, |record| record.attempt_count.saturating_add(1));
        let retained_input = input.or_else(|| {
            entry
                .resolution
                .as_ref()
                .and_then(|record| record.input.clone())
        });
        entry.resolution = Some(CounterexampleResolutionRecord {
            input: retained_input,
            outcome: Some(outcome.clone()),
            attempt_count,
            retry_in_flight: false,
        });
        if let CounterexampleResolutionOutcome::Failure(report) = &outcome {
            self.search.resolution_retries.record_failure(index, report);
        }
        Ok(())
    }

    fn restore_counterexample_resolution_retry(&mut self, index: u64) {
        let Some(entry) = self.search.entries.get_mut(&index) else {
            return;
        };
        let Some(record) = entry.resolution.as_mut() else {
            return;
        };
        if record.retry_in_flight {
            record.retry_in_flight = false;
            self.search.resolution_retries.restore(index);
        }
    }

    fn validate_recordable_attempt(
        &self,
        attempt: WSearchAttempt,
        require_scheduled: bool,
    ) -> Result<(), FailureReport> {
        if self.search.run_fatal.is_some() || self.certified_invalid.is_some() {
            return Err(cex_state_failure(
                "a stopped symbolic CEX state cannot record another W attempt",
            ));
        }
        let entry = self.search.entries.get(&attempt.index()).ok_or_else(|| {
            cex_state_failure("a W attempt requires its complete prepared bundle")
        })?;
        if entry.bundle.is_none()
            || attempt.start_size() != entry.next_start_size
            || attempt.index() > self.next_w_index
            || (!entry.first_attempt_complete && attempt.index() != self.next_w_index)
            || entry
                .last_attempt
                .is_some_and(|prior| attempt.limit() <= prior.limit())
        {
            return Err(cex_state_failure(
                "a W attempt differs from the durable index, frontier, or effort state",
            ));
        }
        if require_scheduled {
            let expected = self.search.attempts.select(
                self.next_w_index,
                &self.search.entries,
                self.policy.w_search(),
            )?;
            if expected != attempt {
                return Err(cex_state_failure(
                    "a W attempt was not selected by the current fair scheduler state",
                ));
            }
        }
        Ok(())
    }

    fn validate_counterexample(
        &self,
        index: u64,
        counterexample: &EntailmentCounterexample,
    ) -> Result<(), FailureReport> {
        match self.w_result(index) {
            Some(WSearchResult::Refuted(retained))
                if retained.entailment_identity() == counterexample.entailment_identity() =>
            {
                Ok(())
            }
            _ => Err(cex_state_failure(
                "counterexample resolution does not match the retained W refutation",
            )),
        }
    }

    fn retained_certification_input(&self, index: u64) -> Option<CertificationInstance> {
        self.search
            .entries
            .get(&index)
            .and_then(|entry| entry.resolution.as_ref())
            .and_then(|record| record.input.clone())
    }

    fn retain_certification_input(&mut self, index: u64, input: CertificationInstance) {
        let entry = self
            .search
            .entries
            .get_mut(&index)
            .expect("validated counterexample has an indexed entry");
        match &mut entry.resolution {
            Some(record) => record.input = Some(input),
            None => {
                // A complete decode precedes the first certification outcome.
                entry.resolution = Some(CounterexampleResolutionRecord {
                    input: Some(input),
                    outcome: None,
                    attempt_count: 0,
                    retry_in_flight: false,
                });
            }
        }
    }

    fn latch_run_fatal(&mut self, report: FailureReport) {
        self.search.latch_run_fatal(report);
    }

    fn retain_run_fatal_attempt(
        &mut self,
        attempt: WSearchAttempt,
        bundle_identity: Arc<str>,
        entailment_identity: Arc<str>,
        attempt_id: Option<AttemptId>,
        terminal_artifact: Option<ArtifactRef>,
    ) {
        let Some(entry) = self.search.entries.get_mut(&attempt.index()) else {
            return;
        };
        entry.last_attempt = Some(attempt);
        entry.attempt_history.push(WAttemptRecord {
            attempt,
            bundle_identity,
            entailment_identity: Some(entailment_identity),
            attempt_id,
            terminal_artifact,
        });
    }
}

pub fn new_symbolic_cex_state(
    task: &SynthesisTask,
    encoding_context: SolverEncodingContext,
    artifacts: &ArtifactStore,
    verification: VerificationParameters,
    admission: SolverAdmission,
    policy: SymbolicHoudiniPolicy,
) -> Result<SymbolicCexState, FailureReport> {
    if admission.class() != SolverAdmissionClass::Cex
        || admission.policy() != verification.resources()
        || encoding_context.task_identity() != task.identity()
        || encoding_context.artifact_store().backend_id() != artifacts.backend_id()
        || artifacts.task_identity() != task.identity()
    {
        return Err(cex_state_failure(
            "symbolic CEX inputs do not share one task, backend, and CEX admission authority",
        ));
    }
    Ok(SymbolicCexState {
        verification,
        admission,
        policy,
        encoding_context,
        next_w_index: 0,
        search: WSearchProgress::default(),
        certified_invalid: None,
        artifacts: artifacts.scoped(ScopeTag::Cex),
        telemetry: TelemetryHandle::disabled(),
    })
}

// ------------------------------------------------------------
// W Construction And Initialization
// ------------------------------------------------------------

pub async fn ensure_w_layer_bundle(
    task: &SynthesisTask,
    state: &mut SymbolicCexState,
    index: u64,
    cancellation: &CancellationToken,
) -> Result<Arc<PreparedWLayerBundle>, EncodingError> {
    if state.encoding_context.task_identity() != task.identity()
        || state.artifacts.task_identity() != task.identity()
    {
        let report = cex_state_failure("W construction uses a different task authority");
        state.latch_run_fatal(report.clone());
        return Err(EncodingError::Failure(report));
    }
    if let Some(bundle) = state.w_bundle(index) {
        return Ok(Arc::clone(bundle));
    }
    let bundle = state
        .encoding_context
        .ensure_w_layer_bundle(&state.admission, index, cancellation)
        .await;
    let bundle = match bundle {
        Ok(bundle) => bundle,
        Err(EncodingError::Failure(report)) => {
            if report.scope() == FailureScope::RunGlobal {
                state.latch_run_fatal(report.clone());
            }
            return Err(EncodingError::Failure(report));
        }
        Err(EncodingError::Cancelled) => return Err(EncodingError::Cancelled),
    };
    if bundle.index() != index
        || bundle.formula_body().context_id() != state.encoding_context.context_id()
        || bundle.maintenance_wp_body().context_id() != state.encoding_context.context_id()
    {
        let report = cex_state_failure(
            "the prepared W bundle differs from its requested index or encoding context",
        );
        state.latch_run_fatal(report.clone());
        return Err(EncodingError::Failure(report));
    }
    if state.telemetry.is_enabled() {
        let relation_arities = task
            .solver_relations()
            .iter()
            .map(|relation| (relation.key().as_str().to_string(), relation.arity()))
            .collect::<BTreeMap<_, _>>();
        match qf_formula_shape(bundle.identity(), &relation_arities) {
            Some(shape) => state.telemetry.record_w_attempt_formula(index, shape),
            None => state
                .telemetry
                .record_error("could not extract an attempted W-formula shape"),
        }
        state.telemetry.increment("cex.w_bundles_prepared", 1);
    }
    state.search.entries.entry(index).or_default().bundle = Some(Arc::clone(&bundle));
    Ok(bundle)
}

pub async fn check_w_initialization(
    task: &SynthesisTask,
    state: &mut SymbolicCexState,
    attempt: WSearchAttempt,
    runtime: &SymbolicCexRuntime,
    cancellation: &CancellationToken,
) -> WInitializationInvocationOutcome {
    if let Some(report) = state.run_fatal().cloned() {
        return WInitializationInvocationOutcome::RunFatal(report);
    }
    if cancellation.is_cancelled() {
        return WInitializationInvocationOutcome::Cancelled;
    }
    if state.encoding_context.task_identity() != task.identity()
        || state.artifacts.task_identity() != task.identity()
    {
        return latch_w_run_fatal(
            state,
            cex_state_failure("W initialization uses a different task authority"),
        );
    }
    if let Err(report) = state.validate_recordable_attempt(attempt, false) {
        return latch_w_run_fatal(state, report);
    }
    let bundle = Arc::clone(
        state
            .w_bundle(attempt.index())
            .expect("validated W attempt has a complete bundle"),
    );
    let attempt_artifacts = state
        .artifacts
        .scoped(ScopeTag::named(format!("w:{}", attempt.index())));
    let entailment = match state
        .search
        .entries
        .get(&attempt.index())
        .and_then(|entry| entry.initialization_entailment.clone())
    {
        Some(entailment) => entailment,
        None => {
            let pre_body = match state
                .encoding_context
                .prepare_solver_bodies(
                    &state.admission,
                    &attempt_artifacts,
                    vec![SolverBodySource::Assert(
                        task.preprocessed_pre_solver().clone(),
                    )],
                    cancellation,
                )
                .await
            {
                Ok(mut bodies) => bodies.remove(0),
                Err(EncodingError::Cancelled) => {
                    return WInitializationInvocationOutcome::Cancelled;
                }
                Err(EncodingError::Failure(report)) => {
                    return w_preparation_failure(state, attempt, &bundle, report);
                }
            };
            let assembled = match assemble_entailment(
                &state.encoding_context,
                &state.admission,
                &attempt_artifacts,
                vec![pre_body],
                vec![bundle.formula_body().clone()],
                cancellation,
            )
            .await
            {
                Ok(entailment) => entailment,
                Err(EncodingError::Cancelled) => {
                    return WInitializationInvocationOutcome::Cancelled;
                }
                Err(EncodingError::Failure(report)) => {
                    return w_preparation_failure(state, attempt, &bundle, report);
                }
            };
            if let Err(report) =
                state.bind_w_initialization_entailment(attempt.index(), assembled.clone())
            {
                return latch_w_run_fatal(state, report);
            }
            assembled
        }
    };
    let entailment_identity = entailment.identity_arc();
    let initial_limit = state
        .search
        .entries
        .get(&attempt.index())
        .and_then(|entry| entry.attempt_history.first())
        .map_or(attempt.limit(), |record| record.attempt().limit());
    let checked = check_entailment_detailed(
        &entailment,
        &attempt_artifacts,
        VampireSearchBudget::cumulative(initial_limit, attempt.limit()),
        VampireMode::ProofAndFmb(FmbOptions {
            start_size: attempt.start_size(),
            contour_strategy: FmbContourStrategy::SingleSortedComplete,
        }),
        runtime.vampire.clone(),
        state.admission.clone(),
        cancellation.clone(),
    )
    .await;
    let attempt_id = checked.attempt_id();
    let terminal_artifact = checked.terminal_artifact();
    match checked.into_outcome() {
        EntailmentInvocationOutcome::Result(result) => {
            WInitializationInvocationOutcome::Result(Box::new(CheckedWInitialization {
                attempt,
                context_id: Arc::from(state.encoding_context.context_id()),
                backend_id: state.artifacts.backend_id(),
                bundle_identity: Arc::from(bundle.identity()),
                entailment_identity: Some(entailment_identity),
                attempt_id,
                terminal_artifact,
                result: map_entailment_result(result, attempt.start_size()),
            }))
        }
        EntailmentInvocationOutcome::Cancelled(_) => WInitializationInvocationOutcome::Cancelled,
        EntailmentInvocationOutcome::RunFailure(report) => {
            state.retain_run_fatal_attempt(
                attempt,
                Arc::from(bundle.identity()),
                entailment_identity,
                attempt_id,
                terminal_artifact,
            );
            latch_w_run_fatal(state, report)
        }
    }
}

async fn check_scheduled_w_initialization(
    task: &SynthesisTask,
    state: &mut SymbolicCexState,
    attempt: WSearchAttempt,
    runtime: &SymbolicCexRuntime,
    cancellation: &CancellationToken,
) -> WInitializationInvocationOutcome {
    if let Err(report) = state.validate_recordable_attempt(attempt, true) {
        return latch_w_run_fatal(state, report);
    }
    check_w_initialization(task, state, attempt, runtime, cancellation).await
}

fn w_preparation_failure(
    state: &mut SymbolicCexState,
    attempt: WSearchAttempt,
    bundle: &PreparedWLayerBundle,
    report: FailureReport,
) -> WInitializationInvocationOutcome {
    if report.scope() == FailureScope::RunGlobal {
        latch_w_run_fatal(state, report)
    } else {
        WInitializationInvocationOutcome::Result(Box::new(checked_w_preparation_failure(
            attempt, bundle, state, report,
        )))
    }
}

fn checked_w_preparation_failure(
    attempt: WSearchAttempt,
    bundle: &PreparedWLayerBundle,
    state: &SymbolicCexState,
    report: FailureReport,
) -> CheckedWInitialization {
    CheckedWInitialization {
        attempt,
        context_id: Arc::from(state.encoding_context.context_id()),
        backend_id: state.artifacts.backend_id(),
        bundle_identity: Arc::from(bundle.identity()),
        entailment_identity: None,
        attempt_id: None,
        terminal_artifact: None,
        result: WSearchResult::Failure {
            report,
            next_start_size: attempt.start_size(),
        },
    }
}

fn latch_w_run_fatal(
    state: &mut SymbolicCexState,
    report: FailureReport,
) -> WInitializationInvocationOutcome {
    state.latch_run_fatal(report.clone());
    WInitializationInvocationOutcome::RunFatal(report)
}

fn result_entailment_identity(result: &WSearchResult) -> Option<&str> {
    match result {
        WSearchResult::Proved {
            proof,
            empty_evidence,
        } if proof.problem_identity() == empty_evidence.entailment_identity() => {
            Some(proof.problem_identity())
        }
        WSearchResult::Proved { .. } => None,
        WSearchResult::Refuted(counterexample) => Some(counterexample.entailment_identity()),
        WSearchResult::TimedOut { .. } | WSearchResult::Failure { .. } => None,
    }
}

fn map_entailment_result(result: EntailmentCheckResult, fallback: FmbSize) -> WSearchResult {
    match result {
        EntailmentCheckResult::Proved {
            proof,
            empty_evidence,
        } => WSearchResult::Proved {
            proof,
            empty_evidence,
        },
        EntailmentCheckResult::Refuted(counterexample) => WSearchResult::Refuted(counterexample),
        EntailmentCheckResult::TimedOut {
            next_fmb_start_size,
            peer_failure,
        } => WSearchResult::TimedOut {
            next_start_size: next_fmb_start_size.unwrap_or(fallback).max(fallback),
            peer_failure,
        },
        EntailmentCheckResult::Failure {
            report,
            next_fmb_start_size,
        } => WSearchResult::Failure {
            report,
            next_start_size: next_fmb_start_size.unwrap_or(fallback).max(fallback),
        },
    }
}

// ------------------------------------------------------------
// Refutation Resolution And Certification
// ------------------------------------------------------------

pub async fn resolve_w_refutation(
    task: &SynthesisTask,
    state: &mut SymbolicCexState,
    index: u64,
    counterexample: &EntailmentCounterexample,
    runtime: &SymbolicCexRuntime,
    cancellation: &CancellationToken,
) -> WRefutationResolutionOutcome {
    if let Some(report) = state.run_fatal() {
        return WRefutationResolutionOutcome::RunFatal(report.clone());
    }
    if let Err(report) = state.validate_counterexample(index, counterexample) {
        state.latch_run_fatal(report.clone());
        return WRefutationResolutionOutcome::RunFatal(report);
    }
    let input = match state.retained_certification_input(index) {
        Some(input) => input,
        None => {
            let source_task = task.clone();
            let artifacts = state.artifacts.clone();
            let retained_counterexample = counterexample.clone();
            let decoded = state
                .encoding_context
                .run_cpu_job(&state.admission, cancellation, move |job_cancellation| {
                    if job_cancellation.is_cancelled() {
                        return Err(CpuJobError::Cancelled);
                    }
                    let decoded = resolve_entailment_counterexample(
                        &source_task,
                        &artifacts,
                        &retained_counterexample,
                    )
                    .map_err(CpuJobError::Failure)?;
                    if job_cancellation.is_cancelled() {
                        return Err(CpuJobError::Cancelled);
                    }
                    CertificationInstance::from_decoded(&source_task, &decoded).map_err(|error| {
                        CpuJobError::Failure(model_failure(
                            FailureKind::MalformedResult,
                            false,
                            format!("convert decoded Vampire model to source Instance: {error}"),
                        ))
                    })
                })
                .await;
            let input = match decoded {
                Ok(input) => input,
                Err(CpuJobError::Cancelled)
                | Err(CpuJobError::Admission(AdmissionError::Cancelled)) => {
                    state.restore_counterexample_resolution_retry(index);
                    return WRefutationResolutionOutcome::Cancelled;
                }
                Err(CpuJobError::Failure(report))
                | Err(CpuJobError::Admission(AdmissionError::Closed(report))) => {
                    return record_resolution_failure(state, index, counterexample, None, report);
                }
                Err(error) => {
                    return record_resolution_failure(
                        state,
                        index,
                        counterexample,
                        None,
                        cex_state_failure(format!(
                            "admitted counterexample decoding failed: {error}"
                        )),
                    );
                }
            };
            state.retain_certification_input(index, input.clone());
            input
        }
    };
    state.telemetry.increment("cex.certification_attempts", 1);
    let certification_started = state.telemetry.start_span();
    let certification = certify_invalid(
        task,
        &state.verification,
        &state.artifacts,
        &input,
        &runtime.certification,
        cancellation,
    )
    .await;
    state
        .telemetry
        .finish_span("cex.certification", certification_started);
    match certification {
        InvalidityCertificationOutcome::Certified(mut certified) => {
            certified.source_w_index = Some(index);
            state.certified_invalid = Some(CertifiedSynthesisResult::Invalid(certified.clone()));
            WRefutationResolutionOutcome::Certified(certified)
        }
        InvalidityCertificationOutcome::Rejected(feedback) => {
            match state.record_counterexample_resolution(
                index,
                counterexample,
                Some(input),
                CounterexampleResolutionOutcome::Rejected(feedback),
            ) {
                Ok(()) => WRefutationResolutionOutcome::Recorded,
                Err(report) => {
                    state.latch_run_fatal(report.clone());
                    WRefutationResolutionOutcome::RunFatal(report)
                }
            }
        }
        InvalidityCertificationOutcome::Failure(report) => {
            record_resolution_failure(state, index, counterexample, Some(input), report)
        }
        InvalidityCertificationOutcome::Cancelled => {
            state.restore_counterexample_resolution_retry(index);
            WRefutationResolutionOutcome::Cancelled
        }
    }
}

// ------------------------------------------------------------
// Fair W Scheduling, Publication, And CEX Lane
// ------------------------------------------------------------

/// Select the next fresh or retry W attempt without mutating durable state.
pub fn select_next_w_attempt(state: &SymbolicCexState) -> Result<WSearchAttempt, FailureReport> {
    if let Some(report) = state.run_fatal() {
        return Err(report.clone());
    }
    if state.certified_invalid().is_some() {
        return Err(cex_state_failure(
            "a terminal symbolic CEX state has no next W attempt",
        ));
    }
    state.search.attempts.select(
        state.next_w_index,
        &state.search.entries,
        state.policy.w_search(),
    )
}

/// Publish every policy-authorized durable W proof which has not completed its
/// handoff bookkeeping. The default path probes W(0) only and allocates no
/// batch when that entry is absent or already complete.
pub fn publish_available_w_proofs(
    task: &SynthesisTask,
    state: &mut SymbolicCexState,
    sender: &WProofSender,
) -> Result<(), FailureReport> {
    if state.encoding_context.task_identity() != task.identity()
        || state.artifacts.task_identity() != task.identity()
        || !sender.matches_authority(task.identity(), state.artifacts.backend_id())
    {
        let report = cex_state_failure(
            "proved W publication does not share one task and artifact authority",
        );
        state.latch_run_fatal(report.clone());
        return Err(report);
    }

    let indices = if state.policy.admit_higher_w_layers() {
        state
            .search
            .proved_unpublished
            .keys()
            .copied()
            .collect::<Vec<_>>()
    } else if state.search.w_zero_proved && !state.search.publication_complete.contains(&0) {
        vec![0]
    } else {
        return Ok(());
    };
    if indices.is_empty() {
        return Ok(());
    }

    let mut publications = Vec::with_capacity(indices.len());
    for index in &indices {
        let entry = state.search.entries.get(index).ok_or_else(|| {
            cex_state_failure("proved W publication refers to a missing search entry")
        })?;
        let bundle = entry.bundle.as_ref().ok_or_else(|| {
            cex_state_failure("proved W publication requires its exact prepared bundle")
        })?;
        let evidence = entry.initialization_evidence.ok_or_else(|| {
            cex_state_failure("proved W publication requires initialization evidence")
        })?;
        publications.push(
            ProvedWEntry::from_bundle(Arc::clone(bundle), evidence).map_err(cex_state_failure)?,
        );
    }

    let outcome = sender
        .publish_batch(publications)
        .map_err(|detail| cex_state_failure(format!("publish proved W batch: {detail}")));
    let outcome = match outcome {
        Ok(outcome) => outcome,
        Err(report) => {
            state.latch_run_fatal(report.clone());
            return Err(report);
        }
    };
    match outcome {
        WPublicationOutcome::Published { .. }
        | WPublicationOutcome::NoChange
        | WPublicationOutcome::ReceiverClosed => {
            // Exact duplicate publication is safe after a publication-before-
            // bookkeeping interruption. A closed receiver permanently retires
            // this run's handoff work without discarding CEX-owned evidence.
            for index in indices {
                state.search.proved_unpublished.remove(&index);
                state.search.publication_complete.insert(index);
            }
            Ok(())
        }
    }
}

/// Run the serial symbolic CEX search until certification, fatal failure,
/// lane-local bundle failure, or external cancellation.
pub async fn search_w_counterexamples(
    task: &SynthesisTask,
    state: &mut SymbolicCexState,
    sender: &WProofSender,
    runtime: &SymbolicCexRuntime,
    cancellation: &CancellationToken,
) -> SymbolicLaneOutcome {
    if state.encoding_context.task_identity() != task.identity()
        || state.artifacts.task_identity() != task.identity()
        || !sender.matches_authority(task.identity(), state.artifacts.backend_id())
    {
        let report = cex_state_failure(
            "symbolic CEX search does not share one task and publication authority",
        );
        state.latch_run_fatal(report.clone());
        return SymbolicLaneOutcome::RunFatal(report);
    }
    loop {
        state.telemetry.increment("cex.search_cycles", 1);
        if cancellation.is_cancelled() {
            return SymbolicLaneOutcome::Cancelled;
        }
        if let Some(certified) = state.certified_invalid().cloned() {
            return SymbolicLaneOutcome::Terminal(certified);
        }
        if let Some(report) = state.run_fatal().cloned() {
            return SymbolicLaneOutcome::RunFatal(report);
        }

        if let Some((index, counterexample)) = state.next_counterexample_resolution() {
            let resolution_span = state.telemetry.span("cex.counterexample_resolution");
            match resolve_w_refutation(task, state, index, &counterexample, runtime, cancellation)
                .await
            {
                WRefutationResolutionOutcome::Certified(certificate) => {
                    return SymbolicLaneOutcome::Terminal(CertifiedSynthesisResult::Invalid(
                        certificate,
                    ));
                }
                WRefutationResolutionOutcome::Recorded => {}
                WRefutationResolutionOutcome::Cancelled => {
                    return SymbolicLaneOutcome::Cancelled;
                }
                WRefutationResolutionOutcome::RunFatal(report) => {
                    return SymbolicLaneOutcome::RunFatal(report);
                }
            }
            drop(resolution_span);
        }

        let attempt = match select_next_w_attempt(state) {
            Ok(attempt) => attempt,
            Err(report) => {
                state.latch_run_fatal(report.clone());
                return SymbolicLaneOutcome::RunFatal(report);
            }
        };
        state
            .telemetry
            .observe_max("cex.highest_w_index", attempt.index());
        state
            .telemetry
            .observe_max("cex.highest_fmb_start_size", attempt.start_size().get());
        if !state.w_attempt_history(attempt.index()).is_empty() {
            state.telemetry.increment("cex.retries", 1);
        }
        state.telemetry.event_with("w_attempt_started", || {
            serde_json::json!({
                "w_index": attempt.index(),
                "fmb_start_size": attempt.start_size().get(),
                "limit_nanoseconds": attempt.limit().as_nanos(),
                "retry": !state.w_attempt_history(attempt.index()).is_empty(),
            })
        });
        let preparation_span = state.telemetry.span("cex.w_bundle_preparation");
        match ensure_w_layer_bundle(task, state, attempt.index(), cancellation).await {
            Ok(_) => {}
            Err(EncodingError::Cancelled) => return SymbolicLaneOutcome::Cancelled,
            Err(EncodingError::Failure(report)) if report.scope() == FailureScope::RunGlobal => {
                return SymbolicLaneOutcome::RunFatal(report);
            }
            Err(EncodingError::Failure(report)) => {
                return SymbolicLaneOutcome::Inconclusive(report);
            }
        }
        drop(preparation_span);

        let attempt_span = state.telemetry.span("cex.vampire_paired_attempt");
        state.telemetry.increment("cex.w_attempts", 1);
        let checked =
            match check_scheduled_w_initialization(task, state, attempt, runtime, cancellation)
                .await
            {
                WInitializationInvocationOutcome::Result(checked) => checked,
                WInitializationInvocationOutcome::Cancelled => {
                    return SymbolicLaneOutcome::Cancelled;
                }
                WInitializationInvocationOutcome::RunFatal(report) => {
                    return SymbolicLaneOutcome::RunFatal(report);
                }
            };
        let attempt_elapsed = attempt_span
            .and_then(crate::telemetry::TelemetrySpan::finish)
            .unwrap_or_default();
        let result = match state.record_w_initialization(checked) {
            Ok(result) => result,
            Err(report) => return SymbolicLaneOutcome::RunFatal(report),
        };
        let result_name = match &result {
            WSearchResult::Proved { .. } => "proved",
            WSearchResult::Refuted(_) => "refuted",
            WSearchResult::TimedOut { .. } => "timeout",
            WSearchResult::Failure { .. } => "failure",
        };
        state
            .telemetry
            .increment(format!("cex.w_result.{result_name}"), 1);
        match &result {
            WSearchResult::TimedOut {
                next_start_size, ..
            }
            | WSearchResult::Failure {
                next_start_size, ..
            } => state
                .telemetry
                .observe_max("cex.highest_safe_fmb_frontier", next_start_size.get()),
            WSearchResult::Proved { .. } | WSearchResult::Refuted(_) => {}
        }
        state.telemetry.event_with("w_attempt_completed", || {
            serde_json::json!({
                "w_index": attempt.index(),
                "fmb_start_size": attempt.start_size().get(),
                "limit_nanoseconds": attempt.limit().as_nanos(),
                "elapsed_nanoseconds": attempt_elapsed.as_nanos(),
                "result": result_name,
                "next_safe_fmb_start_size": match &result {
                    WSearchResult::TimedOut { next_start_size, .. }
                    | WSearchResult::Failure { next_start_size, .. } =>
                        Some(next_start_size.get()),
                    _ => None,
                },
            })
        });
        match result {
            WSearchResult::Proved { .. } => {
                if let Err(report) = publish_available_w_proofs(task, state, sender) {
                    return SymbolicLaneOutcome::RunFatal(report);
                }
            }
            WSearchResult::Refuted(counterexample) => {
                let resolution_span = state.telemetry.span("cex.counterexample_resolution");
                match resolve_w_refutation(
                    task,
                    state,
                    attempt.index(),
                    &counterexample,
                    runtime,
                    cancellation,
                )
                .await
                {
                    WRefutationResolutionOutcome::Certified(certificate) => {
                        return SymbolicLaneOutcome::Terminal(CertifiedSynthesisResult::Invalid(
                            certificate,
                        ));
                    }
                    WRefutationResolutionOutcome::Recorded => {}
                    WRefutationResolutionOutcome::Cancelled => {
                        return SymbolicLaneOutcome::Cancelled;
                    }
                    WRefutationResolutionOutcome::RunFatal(report) => {
                        return SymbolicLaneOutcome::RunFatal(report);
                    }
                }
                drop(resolution_span);
            }
            WSearchResult::TimedOut { .. } => {}
            WSearchResult::Failure { report, .. } if report.scope() == FailureScope::RunGlobal => {
                return SymbolicLaneOutcome::RunFatal(report);
            }
            WSearchResult::Failure { .. } => {}
        }
    }
}

/// Own the CEX state and close proof publication after every ordinary exit.
pub async fn run_cex_lane(
    task: &SynthesisTask,
    mut state: SymbolicCexState,
    sender: WProofSender,
    runtime: &SymbolicCexRuntime,
    cancellation: &CancellationToken,
) -> SymbolicLaneOutcome {
    state.telemetry.increment("lane.cex.starts", 1);
    let _lane_span = state.telemetry.span("lane.cex.activity");
    let outcome = search_w_counterexamples(task, &mut state, &sender, runtime, cancellation).await;
    sender.close();
    outcome
}

fn record_resolution_failure(
    state: &mut SymbolicCexState,
    index: u64,
    counterexample: &EntailmentCounterexample,
    input: Option<CertificationInstance>,
    report: FailureReport,
) -> WRefutationResolutionOutcome {
    if report.scope() == FailureScope::RunGlobal {
        state.latch_run_fatal(report.clone());
        return WRefutationResolutionOutcome::RunFatal(report);
    }
    match state.record_counterexample_resolution(
        index,
        counterexample,
        input,
        CounterexampleResolutionOutcome::Failure(report),
    ) {
        Ok(()) => WRefutationResolutionOutcome::Recorded,
        Err(report) => {
            state.latch_run_fatal(report.clone());
            WRefutationResolutionOutcome::RunFatal(report)
        }
    }
}

// ------------------------------------------------------------
// Evidence And Failure Helpers
// ------------------------------------------------------------

fn publish_w_initialization_evidence(
    artifacts: &ArtifactStore,
    index: u64,
    proof: &VampireProof,
    empty_evidence: &EmptyCheckEvidence,
) -> Result<ArtifactRef, FailureReport> {
    if proof.problem_identity() != empty_evidence.entailment_identity()
        || proof.output().backend_id() != artifacts.backend_id()
        || empty_evidence.artifact().backend_id() != artifacts.backend_id()
    {
        return Err(cex_state_failure(
            "W proof and empty-instance evidence do not share one entailment backend",
        ));
    }
    let Some(query) = proof.query_artifact() else {
        return Err(cex_state_failure(
            "a source-linked W initialization proof requires its query artifact",
        ));
    };
    let payload = json!({
        "kind": "initialization_check",
        "check": "w-layer",
        "w_index": index,
        "outcome": "proved",
        "entailment_identity": proof.problem_identity(),
        "references": [artifact_json(query), artifact_json(proof.output()), artifact_json(empty_evidence.artifact())],
    });
    artifacts.publish(
        ArtifactKind::InitializationCheck,
        payload.to_string().into_bytes().into_boxed_slice(),
    )
}

fn artifact_json(reference: ArtifactRef) -> serde_json::Value {
    json!({
        "backend_id": reference.backend_id().to_string(),
        "local_id": reference.local_id(),
        "kind": reference.kind(),
    })
}

fn cex_state_failure(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::InitializationExecution,
        FailureKind::StateInvariantViolation,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("symbolic CEX state failures use a permitted classification")
}

fn model_failure(kind: FailureKind, retryable: bool, detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::ModelDecoding,
        kind,
        retryable,
        FailureScope::LaneLocal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("symbolic model-resolution failures use a permitted classification")
}

// ------------------------------------------------------------
// Focused Ledger Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::artifact::{ArtifactKind, ArtifactStoreConfig, new_artifact_store};
    use crate::certification::CertificationBridgeCommand;
    use crate::encoding::{
        EncodingWorkerCommand, EncodingWorkerPoolConfig, new_solver_encoding_context,
    };
    use crate::runtime::{RuntimeResourcePolicy, create_symbolic_solver_admissions};
    use crate::vampire::VampireModel;

    use super::*;

    fn test_task() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version": 3,
              "semantic_version": 1,
              "encoding_version": 1,
              "identity": {
                "canonical_id": "Example0012",
                "module": "Benchmark.Example0012.Input",
                "namespace": "Whiel.Benchmark.Example0012",
                "source_sha256": "6fe56e9493eefa68d69085d1602adda3a0d522d964f1a8bf6ef3996f08cd3195"
              },
              "schema": {"expression":"Whiel.Benchmark.Example0012.programSchema","display":"{R (arity: 2)}"},
              "original": {
                "pre":{"expression":"Whiel.Benchmark.Example0012.inputPre","display":"true"},
                "command":{"expression":"Whiel.Benchmark.Example0012.inputCmd","display":"SKIP"},
                "post":{"expression":"Whiel.Benchmark.Example0012.inputPost","display":"true"}
              },
              "preprocessed": {
                "pre":{"expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre","display":"true"},
                "command":{"expression":"Whiel.Benchmark.Example0012.inputPreproc.loopCmd","display":"WHILE true DO SKIP END"},
                "post":{"expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost","display":"true"}
              },
              "preprocessing_evidence":{"expression":"Whiel.Benchmark.Example0012.inputPreproc"},
              "solver": {
                "schema_relations": [
                  {"key":"rel:E:0","arity":2},
                  {"key":"rel:T:0","arity":2},
                  {"key":"rel:T:1","arity":2},
                  {"key":"rel:TBound:0","arity":2}
                ],
                "task_constants": [],
                "preprocessed_pre": {
                  "source_id":"task.preprocessed_pre",
                  "expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre",
                  "no_bound_expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre_noBound",
                  "constants":[],
                  "relations":["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"]
                },
                "preprocessed_post": {
                  "source_id":"task.preprocessed_post",
                  "expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost",
                  "no_bound_expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost_noBound",
                  "constants":[],
                  "relations":["rel:E:0", "rel:T:0", "rel:TBound:0"]
                },
                "loop_guard": {
                  "source_id":"task.loop_guard",
                  "constants":[],
                  "relations":["rel:T:0", "rel:T:1"]
                },
                "negated_loop_guard": {
                  "source_id":"task.negated_loop_guard",
                  "constants":[],
                  "relations":["rel:T:0", "rel:T:1"]
                }
              }
            }"#,
        )
        .expect("test task")
    }

    fn attempt_record(attempt: WSearchAttempt) -> WAttemptRecord {
        WAttemptRecord {
            attempt,
            bundle_identity: Arc::from("test-w-bundle"),
            entailment_identity: Some(Arc::from("test-w-entailment")),
            attempt_id: None,
            terminal_artifact: None,
        }
    }

    fn transient_failure() -> FailureReport {
        model_failure(
            FailureKind::ProcessFailure,
            true,
            "transient model artifact read",
        )
    }

    fn deterministic_failure() -> FailureReport {
        model_failure(
            FailureKind::MalformedResult,
            false,
            "deterministically malformed model",
        )
    }

    #[test]
    fn safe_frontier_is_retained_without_increment() {
        let result = map_entailment_result(
            EntailmentCheckResult::TimedOut {
                next_fmb_start_size: Some(FmbSize::new(7).unwrap()),
                peer_failure: None,
            },
            FmbSize::new(3).unwrap(),
        );
        assert!(matches!(
            result,
            WSearchResult::TimedOut { next_start_size, .. } if next_start_size.get() == 7
        ));
    }

    #[test]
    fn missing_frontier_falls_back_to_attempt_start() {
        let result = map_entailment_result(
            EntailmentCheckResult::TimedOut {
                next_fmb_start_size: None,
                peer_failure: None,
            },
            FmbSize::new(5).unwrap(),
        );
        assert!(matches!(
            result,
            WSearchResult::TimedOut { next_start_size, .. } if next_start_size.get() == 5
        ));
    }

    #[test]
    fn recording_advances_fresh_index_once_and_persists_retry_frontier() {
        let mut progress = WSearchProgress::default();
        progress.entries.insert(0, WSearchEntry::default());
        let mut next_w_index = 0;
        let first = WSearchAttempt::new(0, FmbSize::ONE, Duration::from_secs(30)).unwrap();
        progress
            .commit_attempt(
                &mut next_w_index,
                first,
                WSearchResult::TimedOut {
                    next_start_size: FmbSize::new(7).unwrap(),
                    peer_failure: None,
                },
                None,
                attempt_record(first),
                &SymbolicHoudiniPolicy::default(),
            )
            .unwrap();
        assert_eq!(next_w_index, 1);
        assert_eq!(progress.entries[&0].next_start_size.get(), 7);

        let retry =
            WSearchAttempt::new(0, FmbSize::new(7).unwrap(), Duration::from_secs(60)).unwrap();
        progress
            .commit_attempt(
                &mut next_w_index,
                retry,
                WSearchResult::TimedOut {
                    next_start_size: FmbSize::new(11).unwrap(),
                    peer_failure: None,
                },
                None,
                attempt_record(retry),
                &SymbolicHoudiniPolicy::default(),
            )
            .unwrap();
        assert_eq!(next_w_index, 1);
        assert_eq!(progress.entries[&0].next_start_size.get(), 11);
    }

    #[test]
    fn run_global_attempt_failure_stops_later_launches() {
        let mut progress = WSearchProgress::default();
        progress.entries.insert(0, WSearchEntry::default());
        let mut next_w_index = 0;
        progress
            .commit_attempt(
                &mut next_w_index,
                WSearchAttempt::new(0, FmbSize::ONE, Duration::from_secs(30)).unwrap(),
                WSearchResult::Failure {
                    report: cex_state_failure("shared backend stopped"),
                    next_start_size: FmbSize::ONE,
                },
                None,
                attempt_record(
                    WSearchAttempt::new(0, FmbSize::ONE, Duration::from_secs(30)).unwrap(),
                ),
                &SymbolicHoudiniPolicy::default(),
            )
            .unwrap();
        assert_eq!(next_w_index, 1);
        assert_eq!(
            progress.run_fatal.as_ref().map(FailureReport::scope),
            Some(FailureScope::RunGlobal)
        );
    }

    #[test]
    fn transient_resolution_failures_return_to_the_fifo() {
        let mut queue = ResolutionRetryQueue::default();
        queue.record_failure(8, &transient_failure());
        queue.record_failure(8, &transient_failure());
        assert_eq!(queue.next(), Some(8));
        assert_eq!(queue.next(), None);

        queue.record_failure(8, &transient_failure());
        assert_eq!(queue.next(), Some(8));
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn repeated_transient_resolution_failures_are_fair_through_the_state_ledger() {
        let task = test_task();
        let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("target/phase4c-resolution-fairness")
            .join(std::process::id().to_string());
        let _ = std::fs::remove_dir_all(&directory);
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(directory.join("artifacts")))
                .expect("artifact store");
        let context = new_solver_encoding_context(
            &task,
            &artifacts,
            EncodingWorkerPoolConfig::new(
                EncodingWorkerCommand::new("/usr/bin/false", env!("CARGO_MANIFEST_DIR")),
                1,
            )
            .unwrap(),
        )
        .unwrap();
        let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).unwrap();
        let (_inv, cex) = create_symbolic_solver_admissions(resources).unwrap();
        let verification = VerificationParameters::new(Duration::from_secs(1), resources).unwrap();
        let mut state = new_symbolic_cex_state(
            &task,
            context.clone(),
            &artifacts,
            verification,
            cex,
            SymbolicHoudiniPolicy::default(),
        )
        .unwrap();

        for index in 0..=1 {
            let output = artifacts
                .publish(
                    ArtifactKind::Model,
                    format!("fixture model {index}").into_bytes().into(),
                )
                .unwrap();
            let model = VampireModel::for_test(
                format!("phase4c-resolution-{index}"),
                artifacts.next_attempt_id().unwrap(),
                output,
            );
            let counterexample = EntailmentCounterexample::model_for_test(context.clone(), model);
            state.search.entries.insert(
                index,
                WSearchEntry {
                    result: Some(WSearchResult::Refuted(counterexample.clone())),
                    ..WSearchEntry::default()
                },
            );
            state
                .record_counterexample_resolution(
                    index,
                    &counterexample,
                    None,
                    CounterexampleResolutionOutcome::Failure(transient_failure()),
                )
                .unwrap();
        }

        let (first, first_counterexample) =
            state.next_counterexample_resolution().expect("first retry");
        assert_eq!(first, 0);
        state
            .record_counterexample_resolution(
                first,
                &first_counterexample,
                None,
                CounterexampleResolutionOutcome::Failure(transient_failure()),
            )
            .unwrap();

        let (second, second_counterexample) =
            state.next_counterexample_resolution().expect("peer retry");
        assert_eq!(second, 1);
        state
            .record_counterexample_resolution(
                second,
                &second_counterexample,
                None,
                CounterexampleResolutionOutcome::Failure(transient_failure()),
            )
            .unwrap();

        assert_eq!(
            state
                .next_counterexample_resolution()
                .map(|(index, _)| index),
            Some(0)
        );

        context.shutdown().await.expect("encoding worker shutdown");
        drop(state);
        drop(context);
        drop(artifacts);
        owner.settle().expect("artifact settlement");
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn cancelled_selected_resolution_restores_the_same_fifo_retry() {
        let mut queue = ResolutionRetryQueue::default();
        queue.record_failure(8, &transient_failure());
        assert_eq!(queue.next(), Some(8));
        queue.restore(8);
        assert_eq!(queue.next(), Some(8));
        assert_eq!(queue.next(), None);
    }

    #[test]
    fn deterministic_and_run_global_failures_never_enter_retry_fifo() {
        let mut queue = ResolutionRetryQueue::default();
        queue.record_failure(3, &deterministic_failure());
        queue.record_failure(4, &cex_state_failure("fatal backend mismatch"));
        assert_eq!(queue.next(), None);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn real_run_global_decode_failures_latch_immediately_and_after_a_queued_retry() {
        for queued in [false, true] {
            let task = test_task();
            let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("target/phase4b-poisoned-model-cache")
                .join(format!("{}_{}", std::process::id(), u8::from(queued)));
            let _ = std::fs::remove_dir_all(&directory);
            let (owner, artifacts) =
                new_artifact_store(&task, ArtifactStoreConfig::new(directory.join("artifacts")))
                    .expect("artifact store");
            let context = new_solver_encoding_context(
                &task,
                &artifacts,
                EncodingWorkerPoolConfig::new(
                    EncodingWorkerCommand::new("/usr/bin/false", env!("CARGO_MANIFEST_DIR")),
                    1,
                )
                .unwrap(),
            )
            .unwrap();
            let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).unwrap();
            let (_inv, cex) = create_symbolic_solver_admissions(resources).unwrap();
            let verification = VerificationParameters::new(Duration::from_secs(1), resources)
                .unwrap()
                .with_final_certification_limit(Some(Duration::from_secs(1)))
                .unwrap();
            let mut state = new_symbolic_cex_state(
                &task,
                context.clone(),
                &artifacts,
                verification,
                cex,
                SymbolicHoudiniPolicy::default(),
            )
            .unwrap();

            let output = artifacts
                .publish(ArtifactKind::Model, b"fixture model".as_slice().into())
                .unwrap();
            let model = VampireModel::for_test(
                "phase4b.poisoned-model-entailment",
                artifacts.next_attempt_id().unwrap(),
                output,
            );
            let counterexample = EntailmentCounterexample::model_for_test(context.clone(), model);
            counterexample.poison_decoded_model_cache();
            let entry = WSearchEntry {
                result: Some(WSearchResult::Refuted(counterexample.clone())),
                ..WSearchEntry::default()
            };
            state.search.entries.insert(0, entry);
            let retained = if queued {
                assert!(matches!(
                    record_resolution_failure(
                        &mut state,
                        0,
                        &counterexample,
                        None,
                        transient_failure(),
                    ),
                    WRefutationResolutionOutcome::Recorded
                ));
                let (index, selected) = state
                    .next_counterexample_resolution()
                    .expect("one transient failure must become a queued retry");
                assert_eq!(index, 0);
                selected
            } else {
                counterexample.clone()
            };
            let runtime = SymbolicCexRuntime::new(
                VampireWorkerCommand::new("/usr/bin/false"),
                CertificationRuntime::new(
                    CertificationBridgeCommand::new("/usr/bin/false", env!("CARGO_MANIFEST_DIR")),
                    directory.join("certification-work"),
                    directory.join("solution"),
                ),
            );
            assert!(matches!(
                resolve_w_refutation(
                    &task,
                    &mut state,
                    0,
                    &retained,
                    &runtime,
                    &CancellationToken::new(),
                )
                .await,
                WRefutationResolutionOutcome::RunFatal(ref report)
                    if report.origin() == FailureOrigin::ModelDecoding
                        && report.kind() == FailureKind::InfrastructureFailure
                        && report.scope() == FailureScope::RunGlobal
            ));
            assert!(state.run_fatal().is_some());
            assert!(state.next_counterexample_resolution().is_none());

            assert!(matches!(
                check_w_initialization(
                    &task,
                    &mut state,
                    WSearchAttempt::new(1, FmbSize::ONE, Duration::from_secs(1)).unwrap(),
                    &runtime,
                    &CancellationToken::new(),
                )
                .await,
                WInitializationInvocationOutcome::RunFatal(_)
            ));

            let Err(EncodingError::Failure(shutdown_report)) = context.shutdown().await else {
                panic!("the retained run-global decode failure must fail context shutdown")
            };
            assert_eq!(shutdown_report.origin(), FailureOrigin::ModelDecoding);
            assert_eq!(shutdown_report.scope(), FailureScope::RunGlobal);
            drop(state);
            drop(context);
            drop(artifacts);
            let settlement = owner
                .settle()
                .expect_err("run-global decode failure must fail artifact settlement");
            assert_eq!(settlement.origin(), FailureOrigin::ArtifactSettlement);
            assert_eq!(settlement.scope(), FailureScope::RunGlobal);
            std::fs::remove_dir_all(directory).unwrap();
        }
    }

    #[test]
    fn approved_policy_defaults_are_stable() {
        let policy = SymbolicHoudiniPolicy::default();
        assert!(!policy.admit_higher_w_layers());
        assert_eq!(policy.w_search().fresh_batch_size(), 10);
        assert_eq!(policy.w_search().retry_batch_size(), 10);
        assert_eq!(policy.w_search().initial_limit(), Duration::from_secs(30));
        assert_eq!(policy.w_search().limit_growth(), WLimitGrowth::Geometric(2));
        assert!(
            WSearchSchedule::new(
                1,
                1,
                Duration::from_secs(1),
                WLimitGrowth::Linear(Duration::ZERO),
            )
            .is_err()
        );
    }

    fn record_timeout(
        progress: &mut WSearchProgress,
        next_w_index: &mut u64,
        attempt: WSearchAttempt,
        next_start_size: u64,
        schedule: &WSearchSchedule,
    ) {
        progress.entries.entry(attempt.index()).or_default().bundle = None;
        progress
            .commit_attempt(
                next_w_index,
                attempt,
                WSearchResult::TimedOut {
                    next_start_size: FmbSize::new(next_start_size).unwrap(),
                    peer_failure: None,
                },
                None,
                attempt_record(attempt),
                &SymbolicHoudiniPolicy::new(false, schedule.clone()),
            )
            .unwrap();
    }

    #[test]
    fn scheduler_only_retries_indices_from_earlier_fresh_cycles() {
        let schedule = WSearchSchedule::default();
        let mut progress = WSearchProgress::default();
        let mut next_w_index = 0;

        let bootstrap = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        assert_eq!(bootstrap.index(), 0);
        assert_eq!(bootstrap.start_size(), FmbSize::ONE);
        assert_eq!(bootstrap.limit(), Duration::from_secs(30));
        record_timeout(&mut progress, &mut next_w_index, bootstrap, 7, &schedule);

        for expected in 1..=10 {
            let attempt = progress
                .attempts
                .select(next_w_index, &progress.entries, &schedule)
                .unwrap();
            assert_eq!(attempt.index(), expected);
            assert_eq!(attempt.limit(), Duration::from_secs(30));
            record_timeout(
                &mut progress,
                &mut next_w_index,
                attempt,
                expected + 10,
                &schedule,
            );
        }

        let retry0 = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        assert_eq!(retry0.index(), 0);
        assert_eq!(retry0.limit(), Duration::from_secs(60));
        assert_eq!(retry0.start_size().get(), 7);
        record_timeout(&mut progress, &mut next_w_index, retry0, 8, &schedule);

        for expected in 11..=20 {
            let attempt = progress
                .attempts
                .select(next_w_index, &progress.entries, &schedule)
                .unwrap();
            assert_eq!(attempt.index(), expected);
            record_timeout(
                &mut progress,
                &mut next_w_index,
                attempt,
                expected + 20,
                &schedule,
            );
        }

        for expected in 1..=10 {
            let attempt = progress
                .attempts
                .select(next_w_index, &progress.entries, &schedule)
                .unwrap();
            assert_eq!(attempt.index(), expected);
            assert_eq!(attempt.limit(), Duration::from_secs(60));
            assert_eq!(attempt.start_size().get(), expected + 10);
            record_timeout(
                &mut progress,
                &mut next_w_index,
                attempt,
                attempt.start_size().get() + 1,
                &schedule,
            );
        }

        let next_fresh = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        assert_eq!(next_fresh.index(), 21);
    }

    #[test]
    fn scheduler_doubles_each_index_independently() {
        let schedule =
            WSearchSchedule::new(1, 1, Duration::from_secs(30), WLimitGrowth::Geometric(2))
                .unwrap();
        let mut progress = WSearchProgress::default();
        let mut next_w_index = 0;

        let w0 = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        record_timeout(&mut progress, &mut next_w_index, w0, 9, &schedule);
        let w1 = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        record_timeout(&mut progress, &mut next_w_index, w1, 11, &schedule);

        let retry0 = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        assert_eq!(
            (retry0.index(), retry0.limit()),
            (0, Duration::from_secs(60))
        );
        record_timeout(&mut progress, &mut next_w_index, retry0, 13, &schedule);
        let w2 = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        record_timeout(&mut progress, &mut next_w_index, w2, 17, &schedule);

        let retry1 = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        assert_eq!(retry1.index(), 1);
        record_timeout(&mut progress, &mut next_w_index, retry1, 15, &schedule);
        let w3 = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        record_timeout(&mut progress, &mut next_w_index, w3, 19, &schedule);
        let retry0_again = progress
            .attempts
            .select(next_w_index, &progress.entries, &schedule)
            .unwrap();
        assert_eq!(
            (
                retry0_again.index(),
                retry0_again.limit(),
                retry0_again.start_size().get()
            ),
            (0, Duration::from_secs(120), 13)
        );
    }

    #[test]
    fn reported_fmb_frontier_never_regresses() {
        let result = map_entailment_result(
            EntailmentCheckResult::TimedOut {
                next_fmb_start_size: Some(FmbSize::new(3).unwrap()),
                peer_failure: None,
            },
            FmbSize::new(8).unwrap(),
        );
        assert!(matches!(
            result,
            WSearchResult::TimedOut { next_start_size, .. } if next_start_size.get() == 8
        ));
    }
}

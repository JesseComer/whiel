//! Every concurrency budget one campaign uses, derived in one place.
//!
//! `--workers N` is the only knob, and it means N concurrent clause checks.
//! Each other budget follows from N, the number of solver lanes a single
//! check occupies at once, and the machine's own parallelism. Deriving them
//! anywhere else would let two of them drift apart, so nothing outside this
//! module computes one: the resolved value is recorded verbatim with the
//! run, and every consumer reads it from there.

use std::num::NonZeroUsize;

use crate::encoding::LEAN_WORKER_THREADS;
use crate::vampire::{VAMPIRE_MEMORY_LIMIT_MB, VAMPIRE_PLANNED_FOOTPRINT_MB};

/// Vampire slots one check occupies at once. A campaign races a proof lane
/// against a finite-model lane, and the race takes both slots atomically, so a
/// check takes two. Deriving the Vampire budget as `checks × lanes` is what
/// keeps the lane policy from silently halving the concurrency the operator
/// asked for: `--workers N` is N concurrent checks at either lane count.
pub const CAMPAIGN_CHECK_LANES: usize = 2;

/// Whether a campaign check races a finite-model lane against the proof lane.
/// It always does: a production check configuration cannot be built without
/// the lane, so a clause that is not inductive comes back refuted with a
/// Lean-validated countermodel rather than merely unproved.
pub const CAMPAIGN_FINITE_MODEL_LANE: bool = true;

// The lane is not optional, so the Vampire budget must fund it. Narrowing the
// lane count here would leave a check asking for two slots and holding one,
// which the race runs in turn instead of concurrently.
const _: () = assert!(
    CAMPAIGN_CHECK_LANES >= 2,
    "a campaign check races two lanes and takes both Vampire slots at once"
);

/// The default checks ceiling, and the Lean-worker ceiling besides: the
/// verifier is fast relative to the proposer, so concurrency beyond a few
/// checks buys little measurable throughput and mostly adds queueing, and a
/// default must never claim a large machine on the operator's behalf. Each
/// Lean worker beyond this is also a whole extra process for no measurable
/// gain, since obligation preparation is not the throughput gate.
const DEFAULT_CHECKS_CEILING: usize = 4;

/// The campaign's async runtime never runs below this, however small the
/// machine: the controller and the interrupt relay both need to make progress.
const MINIMUM_RUNTIME_THREADS: usize = 2;

const BYTES_PER_MB: u64 = 1024 * 1024;

/// The resolved budgets of one campaign run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CampaignBudgets {
    host_parallelism: NonZeroUsize,
    /// Physical memory the machine reported, `None` when it could not be read.
    host_memory_bytes: Option<u64>,
    /// Concurrent checks the machine's memory is estimated to hold, given the
    /// limit each Vampire process runs under and the lanes a check occupies.
    /// `None` when memory could not be read, in which case nothing is warned.
    memory_estimate_checks: Option<NonZeroUsize>,
    /// Whether the effective checks (default or explicit) exceed that
    /// estimate. Reported only: memory bounds nothing here.
    exceeds_memory_estimate: bool,
    /// Whether `checks × lanes` exceeds the machine's own parallelism.
    /// Reported only: an explicit `--workers` and the default both stand as
    /// given, whatever this machine can actually run at once.
    exceeds_host_parallelism: bool,
    checks: NonZeroUsize,
    lanes: NonZeroUsize,
    vampire_processes: NonZeroUsize,
    lean_workers: NonZeroUsize,
    lean_worker_threads: NonZeroUsize,
    cpu_permits: NonZeroUsize,
    runtime_worker_threads: NonZeroUsize,
    certification_jobs: NonZeroUsize,
}

fn positive(value: usize) -> NonZeroUsize {
    NonZeroUsize::new(value.max(1)).expect("a floor of one is positive")
}

impl CampaignBudgets {
    /// Resolve the budgets of a run on this machine. `requested` is the
    /// operator's `--workers N`, absent when the default applies.
    pub fn for_host(requested: Option<NonZeroUsize>) -> Self {
        Self::derive_with_memory(
            requested,
            host_parallelism(),
            host_memory_bytes(),
            CAMPAIGN_CHECK_LANES,
        )
    }

    /// The core-count derivation, with memory left out of it. Used where the
    /// machine's memory is not part of what is being tested.
    pub fn derive(requested: Option<NonZeroUsize>, cores: usize, lanes: usize) -> Self {
        Self::derive_with_memory(requested, cores, None, lanes)
    }

    /// The one derivation. `cores` is the machine's parallelism, `memory` its
    /// physical memory in bytes when that could be read, and `lanes` the solver
    /// lanes a single check occupies; `cores` and `lanes` are floored at one.
    ///
    /// Default checks are `floor(cores / 2)`, at least one and at most
    /// [`DEFAULT_CHECKS_CEILING`]: the verifier is fast relative to the
    /// proposer, so a default must not claim a large machine, whatever `lanes`
    /// or the machine's memory happen to be. An explicit `--workers` is always
    /// honoured, whatever it is. Neither the memory estimate nor the core
    /// count caps either one; both are reported instead, so the operator
    /// hears about a check that this machine cannot actually run at once
    /// without the run being narrowed on their behalf.
    pub fn derive_with_memory(
        requested: Option<NonZeroUsize>,
        cores: usize,
        memory: Option<u64>,
        lanes: usize,
    ) -> Self {
        let host_parallelism = positive(cores);
        let lanes = positive(lanes);
        // What the machine's memory is estimated to hold: one Vampire process
        // per lane, each occupying its planned footprint. The hard limit every
        // process runs under is far above any real footprint by design, so it
        // is the wrong number to divide by — dividing by it would flag every
        // ordinary machine as exceeding a one-check estimate.
        let memory_estimate_checks = memory.map(|bytes| {
            let per_check_mb = VAMPIRE_PLANNED_FOOTPRINT_MB.saturating_mul(lanes.get() as u64);
            let holds = (bytes / BYTES_PER_MB) / per_check_mb.max(1);
            positive(usize::try_from(holds).unwrap_or(usize::MAX))
        });
        let by_cores = positive(host_parallelism.get() / 2).min(positive(DEFAULT_CHECKS_CEILING));
        let checks = requested.unwrap_or(by_cores);
        // Both bounds are reported against the settled figure, whichever
        // path produced it: a default that happens to exceed either is just
        // as worth knowing about as an explicit request that does.
        let exceeds_memory_estimate =
            memory_estimate_checks.is_some_and(|estimate| checks > estimate);
        let exceeds_host_parallelism =
            checks.get().saturating_mul(lanes.get()) > host_parallelism.get();
        Self {
            host_parallelism,
            host_memory_bytes: memory,
            memory_estimate_checks,
            exceeds_memory_estimate,
            exceeds_host_parallelism,
            checks,
            lanes,
            vampire_processes: positive(checks.get().saturating_mul(lanes.get())),
            lean_workers: positive(checks.get().min(DEFAULT_CHECKS_CEILING)),
            lean_worker_threads: positive(LEAN_WORKER_THREADS),
            // CPU permits bound the run's own CPU-heavy jobs, not its Lean
            // exchanges, so the machine is their measure.
            cpu_permits: host_parallelism,
            runtime_worker_threads: positive(host_parallelism.get().max(MINIMUM_RUNTIME_THREADS)),
            // Certification runs after the search, one Lean module at a time
            // within an input, so this bounds the solver and packaging
            // fan-out of the input being certified.
            certification_jobs: checks,
        }
    }

    pub fn host_parallelism(self) -> NonZeroUsize {
        self.host_parallelism
    }

    /// Concurrent checks the machine's memory is estimated to hold.
    pub fn memory_estimate_checks(self) -> Option<NonZeroUsize> {
        self.memory_estimate_checks
    }

    /// Whether the effective checks (default or explicit) exceed what memory
    /// is estimated to hold. Reported, never enforced.
    pub fn exceeds_memory_estimate(self) -> bool {
        self.exceeds_memory_estimate
    }

    /// Whether `checks × lanes` exceeds the machine's own logical CPU count.
    /// Reported, never enforced: a small machine still runs its default, or
    /// an explicit request, at the cost of contention rather than a refusal.
    pub fn exceeds_host_parallelism(self) -> bool {
        self.exceeds_host_parallelism
    }

    /// The memory limit each Vampire process is launched under, in MB.
    pub fn vampire_memory_limit_mb(self) -> u64 {
        VAMPIRE_MEMORY_LIMIT_MB
    }

    /// What one Vampire process is planned to occupy, in MB. The memory
    /// estimate divides by this, not by the hard limit.
    pub fn vampire_planned_footprint_mb(self) -> u64 {
        VAMPIRE_PLANNED_FOOTPRINT_MB
    }

    /// Clause checks the run may have in flight at once: `--workers N`.
    pub fn checks(self) -> NonZeroUsize {
        self.checks
    }

    pub fn lanes(self) -> NonZeroUsize {
        self.lanes
    }

    /// Whether a check races a finite-model lane against the proof lane. The
    /// same number that widens the Vampire budget decides the lane, so the two
    /// cannot disagree.
    pub fn finite_model_lane(self) -> bool {
        self.lanes.get() >= 2
    }

    pub fn vampire_processes(self) -> NonZeroUsize {
        self.vampire_processes
    }

    pub fn lean_workers(self) -> NonZeroUsize {
        self.lean_workers
    }

    pub fn lean_worker_threads(self) -> NonZeroUsize {
        self.lean_worker_threads
    }

    pub fn cpu_permits(self) -> NonZeroUsize {
        self.cpu_permits
    }

    pub fn runtime_worker_threads(self) -> NonZeroUsize {
        self.runtime_worker_threads
    }

    pub fn certification_jobs(self) -> NonZeroUsize {
        self.certification_jobs
    }

    /// The record written with the run, so two runs can be compared by their
    /// settings alone rather than by the machines they happened to use.
    pub fn record(self) -> serde_json::Value {
        serde_json::json!({
            "host_parallelism": self.host_parallelism.get(),
            "host_memory_bytes": self.host_memory_bytes,
            "vampire_memory_limit_mb": VAMPIRE_MEMORY_LIMIT_MB,
            "vampire_planned_footprint_mb": VAMPIRE_PLANNED_FOOTPRINT_MB,
            "memory_estimate_checks": self.memory_estimate_checks.map(NonZeroUsize::get),
            "exceeds_memory_estimate": self.exceeds_memory_estimate,
            "exceeds_host_parallelism": self.exceeds_host_parallelism,
            "lean_round_trip_timeout_seconds":
                crate::encoding::FIXED_AMBIENT_ROUND_TRIP_TIMEOUT.as_secs(),
            "checks": self.checks.get(),
            "lanes": self.lanes.get(),
            "finite_model_lane": self.finite_model_lane(),
            "vampire_processes": self.vampire_processes.get(),
            "lean_workers": self.lean_workers.get(),
            "lean_worker_threads": self.lean_worker_threads.get(),
            "cpu_permits": self.cpu_permits.get(),
            "runtime_worker_threads": self.runtime_worker_threads.get(),
            "certification_jobs": self.certification_jobs.get(),
        })
    }
}

/// The machine's parallelism, one when it cannot be determined.
pub fn host_parallelism() -> usize {
    std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1)
}

/// The machine's physical memory in bytes, `None` when it cannot be read.
/// A machine that will not say how much memory it has is reported on nothing:
/// the core rule stands alone rather than a guess standing in for a
/// measurement.
pub fn host_memory_bytes() -> Option<u64> {
    #[cfg(target_os = "macos")]
    {
        let mut bytes: u64 = 0;
        let mut size = std::mem::size_of::<u64>();
        let name = c"hw.memsize";
        // SAFETY: `name` is a NUL-terminated C string, and the output buffer
        // and its length describe the same `u64`.
        let read = unsafe {
            libc::sysctlbyname(
                name.as_ptr(),
                (&raw mut bytes).cast(),
                &raw mut size,
                std::ptr::null_mut(),
                0,
            )
        };
        (read == 0 && bytes > 0).then_some(bytes)
    }
    #[cfg(target_os = "linux")]
    {
        let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
        let total = meminfo
            .lines()
            .find_map(|line| line.strip_prefix("MemTotal:"))?;
        let kilobytes: u64 = total.split_whitespace().next()?.parse().ok()?;
        kilobytes.checked_mul(1024).filter(|bytes| *bytes > 0)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn count(value: usize) -> NonZeroUsize {
        NonZeroUsize::new(value).unwrap()
    }

    /// `(cores, checks, vampire, lean, cpu, runtime, certification)` under the
    /// campaign's own lane count.
    fn row(cores: usize) -> (usize, usize, usize, usize, usize, usize, usize) {
        let budgets = CampaignBudgets::derive(None, cores, CAMPAIGN_CHECK_LANES);
        (
            budgets.host_parallelism().get(),
            budgets.checks().get(),
            budgets.vampire_processes().get(),
            budgets.lean_workers().get(),
            budgets.cpu_permits().get(),
            budgets.runtime_worker_threads().get(),
            budgets.certification_jobs().get(),
        )
    }

    #[test]
    fn the_default_is_half_the_cores_capped_at_four() {
        assert_eq!(CAMPAIGN_CHECK_LANES, 2);
        assert_eq!(CAMPAIGN_FINITE_MODEL_LANE, CAMPAIGN_CHECK_LANES >= 2);
        assert_eq!(row(1), (1, 1, 2, 1, 1, 2, 1));
        assert_eq!(row(2), (2, 1, 2, 1, 2, 2, 1));
        assert_eq!(row(4), (4, 2, 4, 2, 4, 4, 2));
        assert_eq!(row(10), (10, 4, 8, 4, 10, 10, 4));
        assert_eq!(row(64), (64, 4, 8, 4, 64, 64, 4));
    }

    /// Even one check must be able to race both lanes, so the smallest Vampire
    /// budget a campaign ever derives is two slots — including on a one-core
    /// machine, where that already exceeds the machine's own parallelism.
    #[test]
    fn one_check_still_gets_a_slot_for_each_lane() {
        for cores in [1, 2, 3] {
            let budgets = CampaignBudgets::derive(None, cores, CAMPAIGN_CHECK_LANES);
            assert_eq!(budgets.checks().get(), 1);
            assert_eq!(budgets.vampire_processes().get(), 2);
        }
        let one_core = CampaignBudgets::derive(None, 1, CAMPAIGN_CHECK_LANES);
        assert!(one_core.exceeds_host_parallelism());
        let explicit = CampaignBudgets::derive(Some(count(1)), 64, CAMPAIGN_CHECK_LANES);
        assert_eq!(explicit.vampire_processes().get(), 2);
        assert!(!explicit.exceeds_host_parallelism());
    }

    #[test]
    fn an_explicit_count_is_honoured_whatever_the_machine_offers() {
        let budgets = CampaignBudgets::derive(Some(count(6)), 2, CAMPAIGN_CHECK_LANES);
        assert_eq!(budgets.checks().get(), 6);
        assert_eq!(budgets.vampire_processes().get(), 12);
        assert_eq!(budgets.lean_workers().get(), 4);
        assert_eq!(budgets.certification_jobs().get(), 6);
        // The machine, not the request, measures the derived host budgets.
        assert_eq!(budgets.cpu_permits().get(), 2);
        assert_eq!(budgets.runtime_worker_threads().get(), 2);
        // 6 checks at 2 lanes is 12 processes on a 2-core machine: reported.
        assert!(budgets.exceeds_host_parallelism());
    }

    /// The lane count scales the Vampire budget it multiplies, but no longer
    /// the default itself: the default is a fixed function of the cores
    /// alone, so widening the lane count only widens what is reported against
    /// the machine's own parallelism.
    #[test]
    fn the_lane_count_scales_the_vampire_budget_but_not_the_default() {
        let single = CampaignBudgets::derive(None, 10, 1);
        assert_eq!(single.checks().get(), 4);
        assert_eq!(single.vampire_processes().get(), 4);
        assert!(!single.record()["finite_model_lane"].as_bool().unwrap());
        let double = CampaignBudgets::derive(None, 10, 2);
        assert_eq!(double.checks().get(), 4);
        assert_eq!(double.vampire_processes().get(), 8);
        assert!(double.record()["finite_model_lane"].as_bool().unwrap());
        let explicit = CampaignBudgets::derive(Some(count(3)), 10, 2);
        assert_eq!(explicit.checks().get(), 3);
        assert_eq!(explicit.vampire_processes().get(), 6);
    }

    #[test]
    fn an_unusable_machine_report_still_yields_a_working_run() {
        let budgets = CampaignBudgets::derive(None, 0, 0);
        assert_eq!(budgets.host_parallelism().get(), 1);
        assert_eq!(budgets.lanes().get(), 1);
        assert_eq!(budgets.checks().get(), 1);
        assert_eq!(budgets.vampire_processes().get(), 1);
    }

    /// A gibibyte, as the memory tests count it.
    const GB: u64 = 1024 * 1024 * 1024;

    #[test]
    fn memory_no_longer_caps_the_default_but_is_reported() {
        let per_check_gb = (VAMPIRE_PLANNED_FOOTPRINT_MB * CAMPAIGN_CHECK_LANES as u64) / 1024;
        // Room for only one check's memory, on a machine whose core rule
        // derives four: the default no longer defers to the estimate, so it
        // stands as the core rule gives it, flagged rather than narrowed.
        let cramped = CampaignBudgets::derive_with_memory(
            None,
            64,
            Some(per_check_gb * GB),
            CAMPAIGN_CHECK_LANES,
        );
        assert_eq!(
            cramped.memory_estimate_checks().map(NonZeroUsize::get),
            Some(1)
        );
        assert_eq!(
            cramped.checks().get(),
            4,
            "the default is not memory-bounded"
        );
        assert!(cramped.exceeds_memory_estimate());
        // Plenty of memory: nothing to report.
        let roomy = CampaignBudgets::derive_with_memory(
            None,
            64,
            Some(99 * per_check_gb * GB),
            CAMPAIGN_CHECK_LANES,
        );
        assert_eq!(roomy.checks().get(), 4);
        assert!(!roomy.exceeds_memory_estimate());
    }

    #[test]
    fn an_unreadable_memory_size_reports_nothing() {
        let budgets = CampaignBudgets::derive_with_memory(None, 10, None, CAMPAIGN_CHECK_LANES);
        assert_eq!(budgets.checks().get(), 4, "the core rule stands alone");
        assert_eq!(budgets.memory_estimate_checks(), None);
        assert!(!budgets.exceeds_memory_estimate());
        let record = budgets.record();
        assert!(record["host_memory_bytes"].is_null());
        assert!(record["memory_estimate_checks"].is_null());
    }

    #[test]
    fn an_explicit_count_above_the_memory_estimate_is_honoured_and_flagged() {
        let per_check_gb = (VAMPIRE_PLANNED_FOOTPRINT_MB * CAMPAIGN_CHECK_LANES as u64) / 1024;
        let budgets = CampaignBudgets::derive_with_memory(
            Some(count(12)),
            64,
            Some(2 * per_check_gb * GB),
            CAMPAIGN_CHECK_LANES,
        );
        assert_eq!(budgets.checks().get(), 12, "the request is honoured");
        assert!(budgets.exceeds_memory_estimate());
        // At or below the estimate there is nothing to warn about.
        let within = CampaignBudgets::derive_with_memory(
            Some(count(2)),
            64,
            Some(2 * per_check_gb * GB),
            CAMPAIGN_CHECK_LANES,
        );
        assert!(!within.exceeds_memory_estimate());
    }

    #[test]
    fn checks_times_lanes_beyond_the_core_count_is_reported_not_refused() {
        let budgets = CampaignBudgets::derive(Some(count(5)), 4, CAMPAIGN_CHECK_LANES);
        assert_eq!(budgets.vampire_processes().get(), 10);
        assert!(budgets.exceeds_host_parallelism());
        let fits = CampaignBudgets::derive(Some(count(2)), 4, CAMPAIGN_CHECK_LANES);
        assert!(!fits.exceeds_host_parallelism());
    }

    #[test]
    fn the_record_carries_every_derived_budget() {
        let record = CampaignBudgets::derive(Some(count(3)), 8, CAMPAIGN_CHECK_LANES).record();
        let object = record.as_object().unwrap();
        let mut keys = object.keys().map(String::as_str).collect::<Vec<_>>();
        keys.sort_unstable();
        assert_eq!(
            keys,
            [
                "certification_jobs",
                "checks",
                "cpu_permits",
                "exceeds_host_parallelism",
                "exceeds_memory_estimate",
                "finite_model_lane",
                "host_memory_bytes",
                "host_parallelism",
                "lanes",
                "lean_round_trip_timeout_seconds",
                "lean_worker_threads",
                "lean_workers",
                "memory_estimate_checks",
                "runtime_worker_threads",
                "vampire_memory_limit_mb",
                "vampire_planned_footprint_mb",
                "vampire_processes",
            ]
        );
        assert_eq!(record["checks"], 3);
        assert_eq!(record["lanes"], 2);
        assert_eq!(record["finite_model_lane"], true);
        assert_eq!(record["vampire_processes"], 6);
        assert_eq!(record["lean_workers"], 3);
        assert_eq!(record["lean_worker_threads"], 1);
        assert_eq!(record["cpu_permits"], 8);
        assert_eq!(record["runtime_worker_threads"], 8);
        assert_eq!(record["certification_jobs"], 3);
        assert_eq!(record["vampire_memory_limit_mb"], VAMPIRE_MEMORY_LIMIT_MB);
        assert_eq!(
            record["vampire_planned_footprint_mb"],
            VAMPIRE_PLANNED_FOOTPRINT_MB
        );
        // The estimate divides by the planning figure, never by the hard
        // limit: a machine with room for several checks must be told so.
        assert_eq!(
            record["memory_estimate_checks"],
            serde_json::Value::Null,
            "this row derives without a memory reading"
        );
        assert_eq!(record["lean_round_trip_timeout_seconds"], 300);
    }
}

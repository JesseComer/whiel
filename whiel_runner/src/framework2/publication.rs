//! Publication of one provider-neutral AgentHoudini result.
//!
//! Pass 7.5f left a *private* checked aggregate candidate: a frozen Core
//! whose `2N+1` conditions were all re-proved, packaged, compiled, and
//! audited, living under a caller-supplied private root and removed on
//! drop. Pass 7.5e left an `Invalid` outcome carrying a frozen
//! counterexample record and no durable form for it. This module closes
//! both lifecycles into the two results a run may publish, under one rule:
//!
//! **No source authorizes a result until it has been revalidated.** A tree
//! that was built by this run, cached from an earlier stage of it, or
//! already checked in is put back through
//! [`revalidate_certificate_tree`]: a fresh Lean build of every module from
//! source, `Check.lean` regenerated and elaborated at the exact immutable
//! `Input.lean` declaration type, and an audit of the theorem's axiom
//! closure to exactly std3. Only then is anything published, and
//! publication is **one** rename of a complete tree into a destination that
//! must not already exist. One rename, on every path: there is no
//! cross-filesystem copy fallback, because a copy followed by a removal has
//! a window in which a partial tree stands where a complete one is claimed
//! to be. A caller whose staging is on another filesystem is refused before
//! anything is built or written.
//!
//! For an `Invalid` result the durable record `Counterexample.json` is
//! written beside the input first, and the certificate tree is renamed
//! last. The record is evidence, never authority: it names an instance,
//! its Lean-issued identity, the fuel that instance consumed, the run's
//! fuel policy, and the task and scope it was validated against, and every
//! consumer of it — this module's own `Invalid` publication and the
//! certificate CLI's `--counterexample` mode alike — sends it back through
//! Lean's `admitFrozen` re-decode and re-check before a certificate is
//! emitted from it. A crash between record installation and the tree rename
//! therefore leaves a record with no certificate, which authorizes nothing.
//!
//! [`settle_search_outcome`] is where a run enters all of this: it takes a
//! terminal search outcome and the run's own resources, certifies and
//! publishes (`Valid`), records and publishes (`Invalid`), or publishes
//! nothing (`Failure`), and then shuts the solver pool down and settles the
//! artifact backend. It is the production exit from the search, so a
//! campaign needs no publication logic of its own.
//!
//! The run configuration record ([`RunConfiguration`]) is the other half of
//! the lifecycle: the run's `compress_core`, optional level
//! bound `l_max`, retry policy, enabled tool set, and artifact retention
//! mode, bound into the artifact store's run identity at construction and
//! rechecked on every later entry, so an in-process resume or a
//! manifest-driven reopen under a different policy fails closed instead of
//! continuing under a policy the earlier work was not done under. There is
//! no cross-process search resume in this milestone.

use std::collections::BTreeSet;
use std::fmt;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::Deserialize;
use serde_json::{Value, json};

use crate::artifact::{ArtifactBackendOwner, Retention};
use crate::encoding::bytes_sha256;
use crate::failure::FailureReport;
use crate::runtime::owned_path::{OwnedDirectory, PathLease, entry_exists, rename_noreplace};
use crate::runtime::phase::{PhaseCancellation, PhaseStop};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::TaskIdentity;

use super::admission::FrameworkIIAdmissionContext;
use super::agent::{AgentConsultationBinding, AgentProvider};
use super::aggregate::{
    AggregateCertificationError, CertifyFrozenCoreRequest, CheckedAggregateCandidate,
    certify_frozen_core,
};
use super::certificate::CORE_RECORD_NAME;
#[cfg(feature = "test-hooks")]
use super::certificate::CertificateBuildHooks;
use super::certificate::{
    CertificateBuildError, CertificateBuildReceipt, CertificateRevalidation,
    CertificateRevalidationRequest, InvalidCertificateBuildRequest,
    build_invalid_certificate_in_owned_directory, revalidate_certificate_tree,
};
use super::certificate_ops::CertificateBundleShape;
use super::counterexample::{CounterexampleProvenance, FrozenCounterexampleRecord};
use super::freeze::CoreFreezeError;
use super::leancheck::PinnedLeancheckVampire;
use super::production::{CascPortfolioPolicy, FrameworkIIRetryPolicy};
use super::search::PreCertificateAgentHoudiniOutcome;
use super::solver::FrameworkIISolverContext;
use super::stabilization::FrameworkIIChecker;
use super::tools::{AgentTool, AgentToolPolicy};
use crate::entailment::PremiseRole;

/// Wire tag of the persisted run configuration record.
pub const RUN_CONFIGURATION_KIND: &str = "whiel_framework_ii_run_configuration";
/// Wire version of the persisted run configuration record.
///
/// v2 (Milestone 7.5 review, finding 5) added the required `casc_portfolio`
/// member. There is no v1 reader: a v1 record states no CASC portfolio
/// policy at all, and reading it as one that names none would bind a run to
/// a policy it was not run under, which is the very thing this record
/// exists to prevent.
///
/// v4 adds the required `retry_premise_role` member on the same argument:
/// the role a retry launch writes its premises under decides which
/// conditions the search reaches, so two searches that disagree on it are
/// not the same run. A record written before the member existed does state
/// one behaviour — every launch of such a run wrote premises as axioms —
/// but it is still refused rather than read as that, because the record
/// has exactly one canonical form: a reader that rewrote an older record
/// into the current one would make the persisted bytes and the record
/// disagree, and a resume of such a store recomputes its policy anyway and
/// would report drift a moment later. Failing closed on the version says
/// so directly.
pub const RUN_CONFIGURATION_VERSION: u64 = 4;
/// Wire tag of the durable counterexample record.
pub const COUNTEREXAMPLE_RECORD_KIND: &str = "whiel_framework_ii_counterexample";
/// Wire version of the durable counterexample record.
pub const COUNTEREXAMPLE_RECORD_VERSION: u64 = 1;
/// File name of the durable counterexample record, written beside the
/// benchmark's own `Input.lean`.
pub const COUNTEREXAMPLE_RECORD_FILE: &str = "Counterexample.json";
/// Directory a `Valid` settlement's evidence is kept under, beside the run's
/// other payloads in the input's own run directory (`staging`, `private`,
/// the published `Certificate`), when [`Retention::All`] asks for it. Never
/// inside `private` (the candidate's own tree, which `publish_valid` renames
/// away and then requires to be empty) and never inside the published
/// `Certificate` tree.
pub const VALID_EVIDENCE_DIRECTORY: &str = "CertificateEvidence";

// ------------------------------------------------------------
// Run Configuration Record
// ------------------------------------------------------------

/// The run policy every later entry into a run is checked against.
///
/// The fixed-ambient framework had no persisted run configuration before Pass 7.5g. These
/// fields are each read from the live authority that actually applies them
/// rather than from a caller's claim about them: `compress_core` and
/// the level bound from the controller state, the retry policy from the
/// checker, the tool set from the controller state's tool policy, and the
/// retention mode from the artifact store itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunConfiguration {
    compress_core: bool,
    level_bound: Option<u64>,
    /// Held as the exact wire value rather than as a [`Duration`]. The wire
    /// carries whole nanoseconds in a `u64`, a `Duration` counts them in a
    /// `u128`, and a record must never state a limit other than the one the
    /// run applies — so the conversion happens once, at construction, where
    /// a duration that does not fit is refused
    /// ([`RunConfigurationError::UnrepresentableDuration`]) instead of
    /// silently saturating on the way out.
    retry_baseline_nanos: u64,
    retry_allowance_nanos: Vec<u64>,
    /// Whether this run may run and certify the `casc_2025` portfolio, read
    /// from the checker's own retry policy. It decides which conditions the
    /// search can reach at all, so two runs are comparable only when it
    /// matches; see [`CascPortfolioPolicy`].
    casc_portfolio: CascPortfolioPolicy,
    /// The TPTP role a *retry* launch writes this run's premises under,
    /// read from the checker that applies it. A first launch always writes
    /// them as axioms; the role decides which conditions a retry reaches,
    /// so it belongs in the run's identity beside the ladder it retries on.
    retry_premise_role: PremiseRole,
    tools: Vec<&'static str>,
    retention: Retention,
}

impl RunConfiguration {
    /// Build the record from the run's own authorities.
    ///
    /// Fails closed on a retry duration that cannot be stated exactly in
    /// the record's `u64` nanoseconds; every realistic policy is many
    /// centuries short of that bound, and a record that cannot state its
    /// own policy exactly is worse than no record.
    pub fn new(
        compress_core: bool,
        level_bound: Option<u64>,
        retry: Option<&FrameworkIIRetryPolicy>,
        retry_premise_role: Option<PremiseRole>,
        tools: &AgentToolPolicy,
        retention: Retention,
    ) -> Result<Self, RunConfigurationError> {
        let retry_baseline_nanos = exact_nanos(
            retry
                .map(FrameworkIIRetryPolicy::baseline)
                .unwrap_or_default(),
            "retry baseline",
        )?;
        let mut retry_allowance_nanos = Vec::new();
        for allowance in retry
            .map(|policy| policy.allowances().to_vec())
            .unwrap_or_default()
        {
            retry_allowance_nanos.push(exact_nanos(allowance, "retry allowance")?);
        }
        Ok(Self {
            compress_core,
            level_bound,
            retry_baseline_nanos,
            retry_allowance_nanos,
            casc_portfolio: retry
                .map(FrameworkIIRetryPolicy::casc_portfolio)
                .unwrap_or_default(),
            // A checker that declares no retry policy performs no retry, so
            // the default is the role every first launch uses.
            retry_premise_role: retry_premise_role.unwrap_or_default(),
            tools: tools.enabled().iter().map(|tool| tool.name()).collect(),
            retention,
        })
    }

    /// Whether this run may run and certify the `casc_2025` portfolio.
    pub fn casc_portfolio(&self) -> CascPortfolioPolicy {
        self.casc_portfolio
    }

    /// The TPTP role a retry launch writes this run's premises under.
    pub fn retry_premise_role(&self) -> PremiseRole {
        self.retry_premise_role
    }

    pub fn compress_core(&self) -> bool {
        self.compress_core
    }

    pub fn level_bound(&self) -> Option<u64> {
        self.level_bound
    }

    /// The retry policy's direct-search baseline, or zero when the run's
    /// checker declares no retry policy at all.
    pub fn retry_baseline(&self) -> Duration {
        Duration::from_nanos(self.retry_baseline_nanos)
    }

    /// The retry policy's solver allowances, empty when the run's checker
    /// declares no retry policy at all.
    pub fn retry_allowances(&self) -> Vec<Duration> {
        self.retry_allowance_nanos
            .iter()
            .copied()
            .map(Duration::from_nanos)
            .collect()
    }

    pub fn tools(&self) -> &[&'static str] {
        &self.tools
    }

    pub fn retention(&self) -> Retention {
        self.retention
    }

    /// The canonical persisted form.
    pub fn to_json(&self) -> Value {
        json!({
            "kind": RUN_CONFIGURATION_KIND,
            "version": RUN_CONFIGURATION_VERSION,
            "compress_core": self.compress_core,
            "level_bound": self.level_bound,
            "retry_policy": {
                "baseline_nanos": self.retry_baseline_nanos,
                "allowance_nanos": self.retry_allowance_nanos,
            },
            "casc_portfolio": self.casc_portfolio.name(),
            "retry_premise_role": self.retry_premise_role.name(),
            "tools": self.tools,
            "retention": retention_name(self.retention),
        })
    }

    /// Decode one persisted record strictly. An unknown kind or version, an
    /// unknown member, an unknown tool or retention name, and
    /// a tool list that is not in canonical order without duplicates are all
    /// refused: a stale host fails closed rather than reading a record it
    /// only partly understands.
    pub fn from_json(value: &Value) -> Result<Self, RunConfigurationError> {
        let wire: WireRunConfiguration = serde_json::from_value(value.clone())
            .map_err(|error| RunConfigurationError::Malformed(error.to_string()))?;
        if wire.kind != RUN_CONFIGURATION_KIND {
            return Err(RunConfigurationError::Malformed(format!(
                "run configuration has kind {:?}, not {RUN_CONFIGURATION_KIND}",
                wire.kind
            )));
        }
        if wire.version != RUN_CONFIGURATION_VERSION {
            return Err(RunConfigurationError::UnsupportedVersion(wire.version));
        }
        let casc_portfolio = CascPortfolioPolicy::from_name(wire.casc_portfolio.as_str())
            .ok_or_else(|| {
                RunConfigurationError::Malformed(format!(
                    "unknown CASC portfolio policy {:?}",
                    wire.casc_portfolio
                ))
            })?;
        let retry_premise_role = PremiseRole::from_name(wire.retry_premise_role.as_str())
            .ok_or_else(|| {
                RunConfigurationError::Malformed(format!(
                    "unknown retry premise role {:?}",
                    wire.retry_premise_role
                ))
            })?;
        let retention = match wire.retention.as_str() {
            "all" => Retention::All,
            "certificate_only" => Retention::CertificateOnly,
            other => {
                return Err(RunConfigurationError::Malformed(format!(
                    "unknown retention mode {other:?}"
                )));
            }
        };
        let level_bound = match &wire.level_bound {
            Value::Null => None,
            Value::Number(number) => Some(number.as_u64().ok_or_else(|| {
                RunConfigurationError::Malformed(format!(
                    "level bound {number} is not a whole number"
                ))
            })?),
            other => {
                return Err(RunConfigurationError::Malformed(format!(
                    "level bound {other} is neither null nor a whole number"
                )));
            }
        };
        let mut tools = Vec::with_capacity(wire.tools.len());
        for name in &wire.tools {
            let tool = AgentTool::ALL
                .into_iter()
                .find(|tool| tool.name() == name)
                .ok_or_else(|| {
                    RunConfigurationError::Malformed(format!("unknown agent tool {name:?}"))
                })?;
            tools.push(tool);
        }
        let canonical: BTreeSet<AgentTool> = tools.iter().copied().collect();
        if canonical.len() != tools.len() || canonical.iter().copied().collect::<Vec<_>>() != tools
        {
            return Err(RunConfigurationError::Malformed(
                "the run configuration's tool list is not in canonical order without duplicates"
                    .to_string(),
            ));
        }
        Ok(Self {
            compress_core: wire.compress_core,
            level_bound,
            retry_baseline_nanos: wire.retry_policy.baseline_nanos,
            retry_allowance_nanos: wire.retry_policy.allowance_nanos,
            casc_portfolio,
            retry_premise_role,
            tools: tools.into_iter().map(AgentTool::name).collect(),
            retention,
        })
    }

    /// The digest the artifact store's run identity carries.
    pub fn digest(&self) -> String {
        bytes_sha256(
            serde_json::to_vec(&self.to_json())
                .expect("run configuration JSON is always serializable")
                .as_slice(),
        )
    }

    /// Compare this configuration with one already bound to a run.
    pub fn check_drift(&self, bound: &Self) -> Result<(), RunConfigurationError> {
        if self == bound {
            return Ok(());
        }
        Err(RunConfigurationError::Drift {
            bound: bound.digest(),
            found: self.digest(),
        })
    }
}

/// The exact whole nanoseconds of one recorded duration.
///
/// Every duration these records carry is stated in a `u64` of nanoseconds
/// on the wire. A `Duration` counts nanoseconds in a `u128`, so the two
/// ranges differ above roughly 584 years, and a record that saturated there
/// would state a limit other than the one that was applied. Records fail
/// closed on that instead.
fn exact_nanos(duration: Duration, what: &'static str) -> Result<u64, RunConfigurationError> {
    u64::try_from(duration.as_nanos())
        .map_err(|_| RunConfigurationError::UnrepresentableDuration { what, duration })
}

fn retention_name(retention: Retention) -> &'static str {
    match retention {
        Retention::All => "all",
        Retention::CertificateOnly => "certificate_only",
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireRunConfiguration {
    kind: String,
    version: u64,
    compress_core: bool,
    /// Read as a value rather than an `Option<u64>`: serde defaults a
    /// missing `Option` field to `None`, which would silently read a
    /// record that never stated a level bound as one that states there is
    /// none. The member is required and must be null or a whole number.
    level_bound: Value,
    retry_policy: WireRetryPolicy,
    /// Required, and deliberately not defaulted: a record that does not
    /// state its CASC portfolio policy is a v1 record, which the version
    /// check has already refused.
    casc_portfolio: String,
    /// Required for the same reason: a record that does not state the role
    /// its retries rendered under predates the member, and the version
    /// check has already refused it.
    retry_premise_role: String,
    tools: Vec<String>,
    retention: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireRetryPolicy {
    baseline_nanos: u64,
    allowance_nanos: Vec<u64>,
}

/// Why a run configuration was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunConfigurationError {
    /// The persisted record is not a well-formed current record.
    Malformed(String),
    /// The record was written by a version this host does not understand.
    UnsupportedVersion(u64),
    /// The run's configuration disagrees with the one already bound to it.
    Drift { bound: String, found: String },
    /// One of the run's durations cannot be stated exactly in the record's
    /// `u64` nanoseconds, so no record is written for it.
    UnrepresentableDuration {
        what: &'static str,
        duration: Duration,
    },
}

impl fmt::Display for RunConfigurationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(detail) => write!(formatter, "malformed run configuration: {detail}"),
            Self::UnsupportedVersion(version) => write!(
                formatter,
                "run configuration version {version} is not {RUN_CONFIGURATION_VERSION}"
            ),
            Self::Drift { bound, found } => write!(
                formatter,
                "the run configuration changed: this run declares {found}, \
                 the artifact store is bound to {bound}"
            ),
            Self::UnrepresentableDuration { what, duration } => write!(
                formatter,
                "the run's {what} of {duration:?} cannot be stated exactly in whole \
                 nanoseconds, so no run configuration record can name it"
            ),
        }
    }
}

impl std::error::Error for RunConfigurationError {}

// ------------------------------------------------------------
// Durable Counterexample Record
// ------------------------------------------------------------

/// The durable form of one validated counterexample: `Counterexample.json`,
/// written beside the benchmark's `Input.lean`.
///
/// It is a record, not authority. Everything it carries is either Lean's
/// own (the canonical instance, its identity, the fuel it consumed) or the
/// run's identity for the thing that was refuted (the task and scope), plus
/// the run's fuel policy so a reader can see under what regime the replay
/// ran. Rebuilding a certificate from it goes back through Lean.
#[derive(Clone, Debug)]
pub struct DurableCounterexampleRecord {
    record: FrozenCounterexampleRecord,
    fuel_policy: CounterexampleFuelPolicy,
}

/// The run's fuel policy for counterexample validation.
///
/// There is no host fuel bound to record: Lean replays the raw command
/// under its own unreachable structural fuel and the host's call-local
/// wall-clock limit is the only guard, whose expiry is a `timeout`
/// rejection of the call and never a verdict on the instance. Recording
/// both facts explicitly is what makes the record readable years later.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CounterexampleFuelPolicy {
    /// The wire value, for the same reason [`RunConfiguration`] holds its
    /// durations that way: the record must state the limit that was applied,
    /// exactly, and a duration that does not fit whole `u64` nanoseconds is
    /// refused at construction rather than saturated on the way out.
    validation_limit_nanos: u64,
}

impl CounterexampleFuelPolicy {
    /// The policy for one validation limit, refusing a limit that cannot be
    /// stated exactly in the record's whole `u64` nanoseconds.
    pub fn new(validation_limit: Duration) -> Result<Self, DurableCounterexampleError> {
        Ok(Self {
            validation_limit_nanos: u64::try_from(validation_limit.as_nanos()).map_err(|_| {
                DurableCounterexampleError::UnrepresentableValidationLimit(validation_limit)
            })?,
        })
    }

    fn from_nanos(validation_limit_nanos: u64) -> Self {
        Self {
            validation_limit_nanos,
        }
    }

    /// The call-local wall-clock limit one validation ran under.
    pub fn validation_limit(&self) -> Duration {
        Duration::from_nanos(self.validation_limit_nanos)
    }

    fn to_json(self) -> Value {
        json!({
            "kind": "structural_replay",
            "host_fuel_bound": Value::Null,
            "validation_limit_nanos": self.validation_limit_nanos,
        })
    }
}

impl DurableCounterexampleRecord {
    pub fn new(record: FrozenCounterexampleRecord, fuel_policy: CounterexampleFuelPolicy) -> Self {
        Self {
            record,
            fuel_policy,
        }
    }

    pub fn frozen(&self) -> &FrozenCounterexampleRecord {
        &self.record
    }

    pub fn fuel_policy(&self) -> CounterexampleFuelPolicy {
        self.fuel_policy
    }

    /// The canonical persisted form.
    pub fn to_json(&self) -> Value {
        let identity = self.record.task_identity();
        let provenance = match self.record.provenance() {
            CounterexampleProvenance::Consultation(binding) => json!({
                "kind": "consultation",
                "task_digest": binding.task_digest(),
                "scope_digest": binding.scope_digest(),
                "run_digest": binding.run_digest(),
                "consultation_digest": binding.consultation_digest(),
                "state_snapshot_digest": binding.state_snapshot_digest(),
                "validation_manifest_digest": binding.validation_manifest_digest(),
                "request_digest": binding.request_digest(),
                "validation_ordinal": binding.validation_ordinal(),
            }),
            CounterexampleProvenance::RecordedWitness { source } => json!({
                "kind": "recorded_witness",
                "source": source.as_ref(),
            }),
        };
        json!({
            "kind": COUNTEREXAMPLE_RECORD_KIND,
            "version": COUNTEREXAMPLE_RECORD_VERSION,
            "task": {
                "canonical_id": identity.canonical_id(),
                "module": identity.module(),
                "namespace": identity.namespace(),
                "source_sha256": identity.source_digest().as_str(),
                "semantic_version": identity.semantic_version(),
                "encoding_version": identity.encoding_version(),
            },
            "scope_identity_sha256": self.record.scope_identity_sha256(),
            "instance_identity": self.record.instance_identity(),
            "fuel_consumed": self.record.fuel_consumed(),
            "fuel_policy": self.fuel_policy.to_json(),
            "provenance": provenance,
            "instance": self.record.instance(),
        })
    }

    /// Decode one durable record strictly against the task identity the
    /// reading run is bound to.
    ///
    /// The identity check is the point: a record is only ever readable back
    /// into the run whose exact input source, scope, and encoding it was
    /// written against. It still authorizes nothing — Lean re-decodes and
    /// re-checks the instance before any certificate comes out of it.
    pub fn from_json(
        value: &Value,
        task_identity: &TaskIdentity,
        scope_identity_sha256: &str,
    ) -> Result<Self, DurableCounterexampleError> {
        let wire: WireCounterexampleRecord = serde_json::from_value(value.clone())
            .map_err(|error| DurableCounterexampleError::Malformed(error.to_string()))?;
        if wire.kind != COUNTEREXAMPLE_RECORD_KIND {
            return Err(DurableCounterexampleError::Malformed(format!(
                "counterexample record has kind {:?}, not {COUNTEREXAMPLE_RECORD_KIND}",
                wire.kind
            )));
        }
        if wire.version != COUNTEREXAMPLE_RECORD_VERSION {
            return Err(DurableCounterexampleError::UnsupportedVersion(wire.version));
        }
        if wire.task.canonical_id != task_identity.canonical_id()
            || wire.task.module != task_identity.module()
            || wire.task.namespace != task_identity.namespace()
            || wire.task.source_sha256 != task_identity.source_digest().as_str()
            || wire.task.semantic_version != task_identity.semantic_version()
            || wire.task.encoding_version != task_identity.encoding_version()
        {
            return Err(DurableCounterexampleError::TaskMismatch {
                found: wire.task.canonical_id,
                expected: task_identity.canonical_id().to_string(),
            });
        }
        if wire.scope_identity_sha256 != scope_identity_sha256 {
            return Err(DurableCounterexampleError::ScopeMismatch {
                found: wire.scope_identity_sha256,
                expected: scope_identity_sha256.to_string(),
            });
        }
        if wire.fuel_policy.kind != "structural_replay"
            || !wire.fuel_policy.host_fuel_bound.is_null()
        {
            return Err(DurableCounterexampleError::Malformed(
                "counterexample records carry the structural-replay fuel policy and no host bound"
                    .to_string(),
            ));
        }
        if wire.instance.is_null() {
            return Err(DurableCounterexampleError::Malformed(
                "counterexample record carries no canonical instance".to_string(),
            ));
        }
        // The instance identity is a Lean-issued sha256. Consumers name
        // staging directories after a prefix of it, so a record carrying
        // anything else — a short string, upper case, non-hex, a multi-byte
        // character whose boundary a byte slice would split — is refused
        // here rather than reaching a slice that could panic on it.
        if !is_sha256_hex(&wire.instance_identity) {
            return Err(DurableCounterexampleError::Malformed(format!(
                "counterexample instance identity {:?} is not 64 lowercase hex digits",
                wire.instance_identity
            )));
        }
        let provenance = match wire.provenance {
            WireProvenance::Consultation {
                task_digest,
                scope_digest,
                run_digest,
                consultation_digest,
                state_snapshot_digest,
                validation_manifest_digest,
                request_digest,
                validation_ordinal,
            } => CounterexampleProvenance::Consultation(Box::new(
                AgentConsultationBinding::from_parts(
                    task_digest,
                    scope_digest,
                    run_digest,
                    consultation_digest,
                    state_snapshot_digest,
                    validation_manifest_digest,
                    request_digest,
                    validation_ordinal,
                ),
            )),
            WireProvenance::RecordedWitness { source } => {
                CounterexampleProvenance::RecordedWitness {
                    source: source.into(),
                }
            }
        };
        Ok(Self {
            record: FrozenCounterexampleRecord::rehydrate(
                wire.instance,
                wire.instance_identity,
                wire.fuel_consumed,
                task_identity.clone(),
                scope_identity_sha256,
                provenance,
            ),
            fuel_policy: CounterexampleFuelPolicy::from_nanos(
                wire.fuel_policy.validation_limit_nanos,
            ),
        })
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireCounterexampleRecord {
    kind: String,
    version: u64,
    task: WireTaskIdentity,
    scope_identity_sha256: String,
    instance_identity: String,
    fuel_consumed: u64,
    fuel_policy: WireFuelPolicy,
    provenance: WireProvenance,
    instance: Value,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireTaskIdentity {
    canonical_id: String,
    module: String,
    namespace: String,
    source_sha256: String,
    semantic_version: u64,
    encoding_version: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireFuelPolicy {
    kind: String,
    host_fuel_bound: Value,
    validation_limit_nanos: u64,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum WireProvenance {
    Consultation {
        task_digest: String,
        scope_digest: String,
        run_digest: String,
        consultation_digest: String,
        state_snapshot_digest: String,
        validation_manifest_digest: String,
        request_digest: String,
        validation_ordinal: usize,
    },
    RecordedWitness {
        source: String,
    },
}

/// Whether one string is exactly 64 lowercase hexadecimal digits.
fn is_sha256_hex(candidate: &str) -> bool {
    candidate.len() == 64
        && candidate
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Why a durable counterexample record was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DurableCounterexampleError {
    Malformed(String),
    UnsupportedVersion(u64),
    TaskMismatch {
        found: String,
        expected: String,
    },
    ScopeMismatch {
        found: String,
        expected: String,
    },
    /// The run's validation limit cannot be stated exactly in the record's
    /// whole `u64` nanoseconds.
    UnrepresentableValidationLimit(Duration),
}

impl fmt::Display for DurableCounterexampleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(detail) => {
                write!(formatter, "malformed counterexample record: {detail}")
            }
            Self::UnsupportedVersion(version) => write!(
                formatter,
                "counterexample record version {version} is not {COUNTEREXAMPLE_RECORD_VERSION}"
            ),
            Self::TaskMismatch { found, expected } => write!(
                formatter,
                "counterexample record names task {found}, not {expected}"
            ),
            Self::ScopeMismatch { found, expected } => write!(
                formatter,
                "counterexample record names scope {found}, not {expected}"
            ),
            Self::UnrepresentableValidationLimit(limit) => write!(
                formatter,
                "a counterexample validation limit of {limit:?} cannot be stated exactly in \
                 whole nanoseconds, so no record can name it"
            ),
        }
    }
}

impl std::error::Error for DurableCounterexampleError {}

// ------------------------------------------------------------
// Published Results
// ------------------------------------------------------------

/// What one published result left on disk.
#[derive(Clone, Debug)]
pub struct PublishedValid {
    certificate: PathBuf,
    receipt: CertificateBuildReceipt,
    revalidation: CertificateRevalidation,
}

impl PublishedValid {
    /// The published `Certificate/` tree.
    pub fn certificate(&self) -> &Path {
        &self.certificate
    }

    /// The certification's own durable evidence for the `2N+1` batch.
    pub fn receipt(&self) -> &CertificateBuildReceipt {
        &self.receipt
    }

    /// The fresh Lean build, exact type check, and std3 audit that
    /// authorized this publication.
    pub fn revalidation(&self) -> &CertificateRevalidation {
        &self.revalidation
    }
}

/// What one published `Invalid` result left on disk.
#[derive(Clone, Debug)]
pub struct PublishedInvalid {
    certificate: PathBuf,
    record: PathBuf,
    receipt: CertificateBuildReceipt,
    revalidation: CertificateRevalidation,
}

impl PublishedInvalid {
    /// The published `Certificate/` tree.
    pub fn certificate(&self) -> &Path {
        &self.certificate
    }

    /// The durable `Counterexample.json` beside the input.
    pub fn record(&self) -> &Path {
        &self.record
    }

    pub fn receipt(&self) -> &CertificateBuildReceipt {
        &self.receipt
    }

    pub fn revalidation(&self) -> &CertificateRevalidation {
        &self.revalidation
    }
}

/// One request to publish a checked aggregate candidate as `Valid`.
pub struct PublishValidRequest<'a> {
    pub space_guard: Option<&'a std::sync::Arc<super::resource_limits::SpaceGuard>>,
    /// The private candidate. It is consumed: publication either takes its
    /// tree over or leaves it to be removed on drop.
    pub candidate: CheckedAggregateCandidate,
    /// The canonical id of the benchmark being published.
    pub canonical_id: &'a str,
    /// The `Input.lean` declaration namespace the theorem must elaborate
    /// over.
    pub input_namespace: &'a str,
    pub repository_root: PathBuf,
    /// Parent directory for the revalidation's own staging tree.
    pub staging_root: PathBuf,
    /// Where the published `Certificate/` tree goes. Must not exist.
    pub destination: PathBuf,
}

/// One request to publish a frozen counterexample record as `Invalid`.
pub struct PublishInvalidRequest<'a> {
    pub space_guard: Option<&'a std::sync::Arc<super::resource_limits::SpaceGuard>>,
    pub solver: &'a FrameworkIISolverContext,
    pub admission: &'a SolverAdmission,
    /// The record the search froze, or a durable record already re-read.
    pub record: &'a DurableCounterexampleRecord,
    /// The `Input.lean` declaration namespace the negated theorem must
    /// elaborate over.
    pub input_namespace: &'a str,
    pub repository_root: PathBuf,
    /// Parent directory for the build's and the revalidation's own staging
    /// trees.
    pub staging_root: PathBuf,
    /// Directory holding the benchmark's `Input.lean`. `Counterexample.json`
    /// is written here and `Certificate/` is published under it.
    pub input_directory: PathBuf,
    /// Where the published `Certificate/` tree goes. Must not exist.
    pub destination: PathBuf,
    /// The cancellation this publication runs under, independent of search
    /// cancellation. [`publish_invalid`] opens its own phase on it, so it
    /// must be a deadline-free root; a caller that already owns a phase
    /// passes that phase's own token to [`publish_invalid_in_phase`].
    pub external_cancellation: &'a CancellationToken,
    /// One allowance through generation and revalidation. Campaign settlement
    /// always supplies Some; None preserves standalone certificate publication.
    /// Under an already-open phase this states the allowance the caller bound
    /// there, so an expiry is reported against the limit that caused it.
    pub certification_limit: Option<Duration>,
    #[cfg(feature = "test-hooks")]
    pub hooks: CertificateBuildHooks,
}

/// Why a publication was refused.
#[derive(Debug)]
pub enum PublicationError {
    DeadlineExpired(Duration),
    Interrupted,
    PhaseControl(String),
    /// The candidate or record could not be revalidated: its sources did
    /// not build, did not elaborate at the exact input type, or did not
    /// audit to exactly std3.
    Revalidation(Box<CertificateBuildError>),
    /// The `Invalid` certificate could not be built from the record.
    Build(Box<CertificateBuildError>),
    /// A publication destination already exists.
    DestinationExists(PathBuf),
    /// A durable record is already beside the input and its bytes are not
    /// the ones this publication would write.
    ///
    /// Distinct from [`Self::DestinationExists`] on purpose: the path is not
    /// a destination this publication is claiming, it is a record whose
    /// content disagrees with the result being published, and the two
    /// failures call for different answers.
    RecordConflict {
        path: PathBuf,
        existing: String,
    },
    /// The staging tree and its publication destination are on different
    /// filesystems, so publication could not be one rename.
    ///
    /// Publication is atomic or it does not happen. There is no copy
    /// fallback: a copy followed by a removal has an interruption window in
    /// which a half-written tree stands where a complete one is claimed to
    /// be.
    CrossesFilesystems {
        staging: PathBuf,
        destination: PathBuf,
    },
    /// A filesystem operation failed.
    Io(String),
}

impl fmt::Display for PublicationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DeadlineExpired(limit) => {
                write!(formatter, "certification allowance of {limit:?} expired")
            }
            Self::Interrupted => write!(formatter, "certification was externally interrupted"),
            Self::PhaseControl(detail) => {
                write!(formatter, "certification phase control failed: {detail}")
            }
            Self::Revalidation(error) => write!(
                formatter,
                "the certificate source was not revalidated: {error}"
            ),
            Self::Build(error) => {
                write!(formatter, "the Invalid certificate build failed: {error}")
            }
            Self::DestinationExists(path) => write!(
                formatter,
                "publication destination already exists: {}",
                path.display()
            ),
            Self::RecordConflict { path, existing } => write!(
                formatter,
                "the durable record at {} is not the one this result would write \
                 (it names instance {existing}); a result is never published over \
                 another result's record",
                path.display()
            ),
            Self::CrossesFilesystems {
                staging,
                destination,
            } => write!(
                formatter,
                "the staging tree {} and the publication destination {} are on different \
                 filesystems, so publication cannot be one rename; stage on the \
                 destination's own filesystem (the certificate CLI's default staging root \
                 is a sibling of the destination for exactly this reason)",
                staging.display(),
                destination.display()
            ),
            Self::Io(detail) => write!(formatter, "publication I/O failed: {detail}"),
        }
    }
}

impl std::error::Error for PublicationError {}

/// Publish one checked aggregate candidate as the run's `Valid` result.
///
/// The candidate's tree is revalidated first — a fresh Lean build of every
/// module from source, `Check.lean` elaborated at
/// `Whiel.HoareValid inputPre inputCmd inputPost` over the immutable
/// `Input.lean` namespace, and an exact-std3 axiom audit — and only then
/// renamed into place. The candidate's certification receipt is evidence
/// that the batch was proved; it is never the thing that authorizes the
/// publication.
pub async fn publish_valid(
    request: PublishValidRequest<'_>,
) -> Result<PublishedValid, PublicationError> {
    let PublishValidRequest {
        space_guard,
        mut candidate,
        canonical_id,
        input_namespace,
        repository_root,
        staging_root,
        destination,
    } = request;
    let (phase, limit) = candidate
        .take_certification_phase()
        .map_err(|error| PublicationError::PhaseControl(error.to_string()))?;
    let tree = candidate.private_tree().join("Certificate");
    let checked = async {
        let destination_lease = publication_lease(&destination)?;
        if publication_entry_exists(&destination)? {
            return Err(PublicationError::DestinationExists(destination.clone()));
        }
        // Before any Lean runs: publication is one rename, and one rename only
        // works within a filesystem. A caller who staged elsewhere is told so
        // now rather than after a full revalidation.
        ensure_same_filesystem(&tree, &destination)?;
        let revalidation = revalidate_certificate_tree(CertificateRevalidationRequest {
            tree: &tree,
            canonical_id,
            input_namespace,
            certificate_module: &candidate.receipt().certificate_module,
            certificate_theorem: &candidate.receipt().certificate_theorem,
            shape: CertificateBundleShape::Valid,
            repository_root,
            staging_root,
            cancellation: phase.token(),
        })
        .await
        .map_err(|error| publication_build_error(error, &phase, Some(limit), true))?;
        Ok((revalidation, destination_lease))
    }
    .await;
    let (revalidation, _destination_lease) =
        finish_publication_phase(phase, Some(limit), checked, |token| {
            publication_space_check(space_guard, token)
        })
        .await?;

    // The frozen Core record goes beside the input first and the tree is
    // renamed last, so no crash point leaves a certificate without the
    // record it was built from.
    publish_core_record(candidate.private_tree(), &destination)?;
    // Publication proper: one rename of a complete, revalidated tree. The
    // candidate is retained only once the rename has succeeded, so a
    // failure here still removes the private tree rather than leaking it.
    publish_tree(&tree, &destination)?;
    candidate.retain();
    // The candidate's own `aggregate-<digest>` directory is empty now that
    // its `Certificate` subtree has been renamed away. It is removed rather
    // than left standing: `prepare_private_tree` refuses a private root
    // entry that already exists, so an empty leftover would block a later
    // certification of the same frozen Core.
    remove_emptied_private_tree(candidate.private_tree());
    let receipt = candidate.receipt().clone();
    Ok(PublishedValid {
        certificate: destination,
        receipt,
        revalidation,
    })
}

/// Publish one frozen counterexample record as the run's `Invalid` result.
///
/// The record goes back through Lean: `emit_invalid_certificate` re-decodes
/// the canonical instance, re-checks that the frozen fuel still refutes the
/// immutable input triple, and emits the zero-job bundle. The built tree is
/// then revalidated exactly as a `Valid` tree is, at the negated target,
/// before anything is published. `Counterexample.json` is written beside
/// the input first and the certificate tree is renamed last, so no crash
/// point leaves a certificate without the record it was built from.
pub async fn publish_invalid(
    request: PublishInvalidRequest<'_>,
) -> Result<PublishedInvalid, PublicationError> {
    let limit = request.certification_limit;
    let space_guard = request.space_guard;
    let phase = open_certification_phase(request.external_cancellation, limit)?;
    let staged = stage_invalid_publication(request, &phase).await;
    finish_publication_phase(phase, limit, staged, |token| {
        publication_space_check(space_guard, token)
    })
    .await?
    .publish()
}

/// Publish one frozen counterexample record as `Invalid` under a
/// certification phase the caller has already opened and will finish.
///
/// The deferred entry points — `campaign certify`, and the certificate CLI's
/// own `--counterexample` and `--witness` modes — wrap a whole build in one
/// phase and carry its allowance on that phase. A phase never nests on
/// another phase's child, so such a caller runs the publication body under
/// the phase it owns instead of asking for a second one. `phase` is the
/// authority here: `request.external_cancellation` is that phase's own
/// token and `request.certification_limit` the allowance already bound to
/// it, stated so a stop is reported against the limit that caused it.
/// Nothing is bound and no relay is joined here.
pub(crate) async fn publish_invalid_in_phase(
    request: PublishInvalidRequest<'_>,
    phase: &PhaseCancellation,
) -> Result<PublishedInvalid, PublicationError> {
    let limit = request.certification_limit;
    let space_guard = request.space_guard;
    let staged = stage_invalid_publication(request, phase).await;
    check_publication_step(phase, limit, staged, |token| {
        publication_space_check(space_guard, token)
    })
    .await?
    .publish()
}

/// Open the phase an `Invalid` publication owns, carrying its allowance as
/// an absolute deadline on the phase's own child token.
fn open_certification_phase(
    external: &CancellationToken,
    limit: Option<Duration>,
) -> Result<PhaseCancellation, PublicationError> {
    let started_at = tokio::time::Instant::now();
    let deadline = limit
        .map(|limit| {
            started_at.checked_add(limit).ok_or_else(|| {
                PublicationError::PhaseControl(
                    "certification allowance overflows the monotonic clock".into(),
                )
            })
        })
        .transpose()?;
    let phase = PhaseCancellation::new(external).map_err(|_| {
        PublicationError::PhaseControl(
            "certification requires a deadline-free external root".into(),
        )
    })?;
    if let Some(deadline) = deadline {
        assert!(phase.token().bind_absolute_deadline(deadline));
    }
    Ok(phase)
}

/// One `Invalid` result built, revalidated and recorded under a live
/// certification phase, with only its final rename left to perform.
struct StagedInvalid {
    built: PathBuf,
    /// The owned attempt parent; only it remains once the tree is promoted.
    guard: OwnedDirectory,
    receipt: CertificateBuildReceipt,
    revalidation: CertificateRevalidation,
    record_path: PathBuf,
    destination: PathBuf,
    /// Ownership of the destination and of the durable record outlives the
    /// rename that publishes the tree.
    _destination_lease: PathLease,
    _record_lease: PathLease,
}

impl StagedInvalid {
    /// The record first, the certificate last. A record without a
    /// certificate authorizes nothing; a certificate is never present
    /// without the record it was built from.
    fn publish(self) -> Result<PublishedInvalid, PublicationError> {
        publish_tree(&self.built, &self.destination)?;
        drop(self.guard);
        Ok(PublishedInvalid {
            certificate: self.destination,
            record: self.record_path,
            receipt: self.receipt,
            revalidation: self.revalidation,
        })
    }
}

/// Build, revalidate and record one `Invalid` result under `phase`.
///
/// Every await runs on the phase's own token, so the allowance bound to it
/// and any external interruption reach the Lean work already in flight.
async fn stage_invalid_publication(
    request: PublishInvalidRequest<'_>,
    phase: &PhaseCancellation,
) -> Result<StagedInvalid, PublicationError> {
    let PublishInvalidRequest {
        space_guard,
        solver,
        admission,
        record,
        input_namespace,
        repository_root,
        staging_root,
        input_directory,
        destination,
        external_cancellation: _,
        certification_limit: limit,
        #[cfg(feature = "test-hooks")]
        hooks,
    } = request;
    let destination_lease = publication_lease(&destination)?;
    if publication_entry_exists(&destination)? {
        return Err(PublicationError::DestinationExists(destination.clone()));
    }
    let record_path = input_directory.join(COUNTEREXAMPLE_RECORD_FILE);
    // Byte-identical to what the acceptance record wrote for the same
    // result (`acceptance::durable_counterexample_bytes`): the check
    // below compares bytes, not parsed values, so any change to how
    // either side serialises this record has to change both.
    let record_bytes = serde_json::to_vec_pretty(&record.to_json())
        .expect("counterexample record JSON is always serializable");
    // A record already beside the input is only acceptable if it is the
    // one this publication would write: republishing an `Invalid` result
    // from its own durable record is ordinary, replacing one record's
    // certificate with another record's is not. That is a content conflict,
    // not an occupied destination, and it is reported as one.
    // Different certificate destinations may share this record. Keep its
    // ownership across every await and the final certificate rename.
    let record_lease = publication_lease(&record_path)?;
    check_existing_record(&record_path, &record_bytes)?;
    std::fs::create_dir_all(&staging_root).map_err(|error| {
        PublicationError::Io(format!("create {}: {error}", staging_root.display()))
    })?;
    // Before Lean runs and before the record is written: the built tree is
    // published by one rename out of the staging root, which only works
    // within a filesystem.
    ensure_same_filesystem(&staging_root, &destination)?;
    let guard = prepare_invalid_staging(&staging_root, record.frozen().instance_identity())?;
    // The parent is exclusively owned; the builder receives its absent child.
    let built = guard.path().join("Certificate");
    let receipt = build_invalid_certificate_in_owned_directory(
        InvalidCertificateBuildRequest {
            solver,
            admission,
            record: record.frozen(),
            repository_root: repository_root.clone(),
            staging_root: staging_root.clone(),
            destination: built.clone(),
            cancellation: phase.token(),
            #[cfg(feature = "test-hooks")]
            hooks,
        },
        &guard,
    )
    .await
    .map_err(|error| publication_build_error(error, phase, limit, false))?;

    let revalidation = revalidate_certificate_tree(CertificateRevalidationRequest {
        tree: &built,
        canonical_id: record.frozen().task_identity().canonical_id(),
        input_namespace,
        certificate_module: &receipt.certificate_module,
        certificate_theorem: &receipt.certificate_theorem,
        shape: CertificateBundleShape::Invalid,
        repository_root,
        staging_root,
        cancellation: phase.token(),
    })
    .await
    .map_err(|error| publication_build_error(error, phase, limit, true))?;
    // Keep both storage observations and the durable record write inside
    // the live certification phase. A record alone authorizes nothing.
    publication_space_check(space_guard, phase.token().clone())
        .await
        .map_err(|error| publication_space_error(error, phase, limit))?;
    write_record_atomically(&record_path, &record_bytes)?;
    Ok(StagedInvalid {
        built,
        guard,
        receipt,
        revalidation,
        record_path,
        destination,
        _destination_lease: destination_lease,
        _record_lease: record_lease,
    })
}

fn publication_stop_error(phase: &PhaseCancellation, limit: Option<Duration>) -> PublicationError {
    match phase.stop_reason() {
        Some(PhaseStop::DeadlineExpired) => deadline_publication_error(limit),
        Some(PhaseStop::Interrupted) => PublicationError::Interrupted,
        None => PublicationError::PhaseControl(
            "certificate operation cancelled without an external or deadline signal".into(),
        ),
    }
}

fn deadline_publication_error(limit: Option<Duration>) -> PublicationError {
    match limit {
        Some(limit) => PublicationError::DeadlineExpired(limit),
        None => PublicationError::PhaseControl(
            "an unbounded certificate phase acquired a deadline".into(),
        ),
    }
}

fn publication_build_error(
    error: CertificateBuildError,
    phase: &PhaseCancellation,
    limit: Option<Duration>,
    revalidation: bool,
) -> PublicationError {
    match error {
        CertificateBuildError::Cancelled => publication_stop_error(phase, limit),
        error if revalidation => PublicationError::Revalidation(Box::new(error)),
        error => PublicationError::Build(Box::new(error)),
    }
}

async fn finish_publication_phase<T, F, Fut>(
    phase: PhaseCancellation,
    limit: Option<Duration>,
    result: Result<T, PublicationError>,
    final_check: F,
) -> Result<T, PublicationError>
where
    F: FnOnce(CancellationToken) -> Fut,
    Fut: std::future::Future<Output = Result<(), String>>,
{
    // The joined storage scan remains under the same deadline and external
    // cancellation relay as revalidation. Only the synchronous rename follows
    // phase completion; no potentially long await may follow that boundary.
    let result = apply_publication_check(&phase, limit, result, final_check).await;
    let completed = phase.finish().await;
    // A real non-cancellation failure keeps precedence through cleanup. A
    // successful audit must also have a timely boundary and a joined relay.
    let value = result?;
    let completed = completed.map_err(|error| PublicationError::PhaseControl(error.to_string()))?;
    publication_stop_outcome(completed.stop, limit).map(|()| value)
}

/// The same final storage check and stop classification, under a phase the
/// caller owns and will finish at its own boundary. The relay is left
/// running: joining it here would end a phase this publication is only one
/// step of, and the owner's own completion is what classifies the outcome.
async fn check_publication_step<T, F, Fut>(
    phase: &PhaseCancellation,
    limit: Option<Duration>,
    result: Result<T, PublicationError>,
    final_check: F,
) -> Result<T, PublicationError>
where
    F: FnOnce(CancellationToken) -> Fut,
    Fut: std::future::Future<Output = Result<(), String>>,
{
    let value = apply_publication_check(phase, limit, result, final_check).await?;
    publication_stop_outcome(phase.stop_reason(), limit).map(|()| value)
}

async fn apply_publication_check<T, F, Fut>(
    phase: &PhaseCancellation,
    limit: Option<Duration>,
    result: Result<T, PublicationError>,
    final_check: F,
) -> Result<T, PublicationError>
where
    F: FnOnce(CancellationToken) -> Fut,
    Fut: std::future::Future<Output = Result<(), String>>,
{
    match result {
        Ok(value) => final_check(phase.token().clone())
            .await
            .map(|()| value)
            .map_err(|error| publication_space_error(error, phase, limit)),
        Err(error) => Err(error),
    }
}

fn publication_stop_outcome(
    stop: Option<PhaseStop>,
    limit: Option<Duration>,
) -> Result<(), PublicationError> {
    match stop {
        Some(PhaseStop::DeadlineExpired) => Err(deadline_publication_error(limit)),
        Some(PhaseStop::Interrupted) => Err(PublicationError::Interrupted),
        None => Ok(()),
    }
}

fn publication_space_error(
    error: String,
    phase: &PhaseCancellation,
    limit: Option<Duration>,
) -> PublicationError {
    if !error.starts_with("resource_exhausted:") && phase.stop_reason().is_some() {
        publication_stop_error(phase, limit)
    } else {
        PublicationError::Io(error)
    }
}

async fn publication_space_check(
    guard: Option<&std::sync::Arc<super::resource_limits::SpaceGuard>>,
    cancellation: CancellationToken,
) -> Result<(), String> {
    if let Some(guard) = guard {
        guard.checkpoint_with_cancellation(&cancellation).await?;
    }
    Ok(())
}

/// Publish one complete tree with exactly one rename.
///
/// There is no copy fallback. A copy followed by a removal is not one
/// step: between them a partial tree stands where a complete one is
/// claimed to be, and an interruption leaves either a half-written
/// certificate in the published location or the same tree in two places
/// with nothing saying which is authoritative. A caller whose staging is on
/// another filesystem is refused with
/// [`PublicationError::CrossesFilesystems`] and told to stage on the
/// destination's own filesystem.
/// Move the certificate build's `Core.json` from beside the private tree to
/// beside the published one. A record already there with the same rows is
/// left alone; a different one is a conflict, never replaced.
fn publish_core_record(private_tree: &Path, destination: &Path) -> Result<(), PublicationError> {
    let source = private_tree.join(CORE_RECORD_NAME);
    if !publication_entry_exists(&source)? {
        return Err(PublicationError::Io(format!(
            "the certificate build left no {CORE_RECORD_NAME} beside {}",
            private_tree.display()
        )));
    }
    let Some(parent) = destination.parent() else {
        return Ok(());
    };
    let target = parent.join(CORE_RECORD_NAME);
    let text = std::fs::read_to_string(&source)
        .map_err(|error| PublicationError::Io(format!("read {}: {error}", source.display())))?;
    if publication_entry_exists(&target)? {
        let existing = std::fs::read_to_string(&target)
            .map_err(|error| PublicationError::Io(format!("read {}: {error}", target.display())))?;
        let same = serde_json::from_str::<serde_json::Value>(&existing).ok()
            == serde_json::from_str::<serde_json::Value>(&text).ok();
        if !same {
            return Err(PublicationError::Io(format!(
                "{} already holds a different Core record; it is not replaced",
                target.display()
            )));
        }
        std::fs::remove_file(&source).map_err(|error| {
            PublicationError::Io(format!("remove {}: {error}", source.display()))
        })?;
        return Ok(());
    }
    std::fs::create_dir_all(parent)
        .map_err(|error| PublicationError::Io(format!("create {}: {error}", parent.display())))?;
    rename_noreplace(&source, &target)
        .map_err(|error| PublicationError::Io(format!("publish {}: {error}", target.display())))
}

fn publish_tree(from: &Path, to: &Path) -> Result<(), PublicationError> {
    if publication_entry_exists(to)? {
        return Err(PublicationError::DestinationExists(to.to_path_buf()));
    }
    if let Some(parent) = to.parent() {
        std::fs::create_dir_all(parent).map_err(|error| {
            PublicationError::Io(format!("create {}: {error}", parent.display()))
        })?;
    }
    if forced_cross_filesystem() {
        return Err(PublicationError::CrossesFilesystems {
            staging: from.to_path_buf(),
            destination: to.to_path_buf(),
        });
    }
    match rename_noreplace(from, to) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            Err(PublicationError::DestinationExists(to.to_path_buf()))
        }
        Err(error) if error.kind() == std::io::ErrorKind::CrossesDevices => {
            Err(PublicationError::CrossesFilesystems {
                staging: from.to_path_buf(),
                destination: to.to_path_buf(),
            })
        }
        Err(error) => Err(PublicationError::Io(format!(
            "publish {} to {}: {error}",
            from.display(),
            to.display()
        ))),
    }
}

/// Refuse a staging tree that cannot be renamed into its destination,
/// before anything at all is built or written.
///
/// The check is on the two filesystems, not on the rename: a publication
/// that would end in [`PublicationError::CrossesFilesystems`] is worth
/// refusing before a Lean build and, for the `Invalid` result, before the
/// durable record is written beside the input. Neither path exists yet in
/// general, so each is resolved to its nearest existing ancestor.
fn ensure_same_filesystem(staging: &Path, destination: &Path) -> Result<(), PublicationError> {
    let refuse = || PublicationError::CrossesFilesystems {
        staging: staging.to_path_buf(),
        destination: destination.to_path_buf(),
    };
    if forced_cross_filesystem() {
        return Err(refuse());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let device = |path: &Path| -> Result<u64, PublicationError> {
            let existing = nearest_existing(path).ok_or_else(|| {
                PublicationError::Io(format!(
                    "no existing ancestor of {} to resolve its filesystem",
                    path.display()
                ))
            })?;
            std::fs::metadata(&existing)
                .map(|metadata| metadata.dev())
                .map_err(|error| {
                    PublicationError::Io(format!("stat {}: {error}", existing.display()))
                })
        };
        if device(staging)? != device(destination)? {
            return Err(refuse());
        }
    }
    Ok(())
}

/// The nearest ancestor of `path` — `path` itself included — that exists.
fn nearest_existing(path: &Path) -> Option<PathBuf> {
    let mut candidate = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().ok()?.join(path)
    };
    loop {
        if candidate.exists() {
            return Some(candidate);
        }
        if !candidate.pop() {
            return None;
        }
    }
}

/// Whether a test has asked publication to behave as if its staging and
/// destination were on different filesystems.
///
/// A second filesystem cannot be assumed on a developer machine or in CI,
/// and creating one is not this crate's business, so the refusal path is
/// exercised by making the two devices disagree on demand. Outside `cfg
/// (test)` there is no such switch and this is a constant `false`.
#[cfg(test)]
fn forced_cross_filesystem() -> bool {
    FORCED_CROSS_FILESYSTEM.with(std::cell::Cell::get)
}

#[cfg(not(test))]
fn forced_cross_filesystem() -> bool {
    false
}

#[cfg(test)]
thread_local! {
    static FORCED_CROSS_FILESYSTEM: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Remove the private certification directory a published `Valid` tree has
/// just been renamed out of.
///
/// Best effort by design: the tree is published either way, and a
/// publication that succeeded is never reported as a failure because an
/// emptied directory could not be removed. It is still worth removing —
/// `prepare_private_tree` refuses a private-root entry that already exists,
/// so a leftover would block a later certification of the same frozen Core
/// — and worth saying so when it cannot be.
fn remove_emptied_private_tree(private_tree: &Path) {
    match std::fs::remove_dir(private_tree) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => eprintln!(
            "warning: the published certificate's private certification directory {} could not \
             be removed ({error}); a later certification of the same frozen Core will refuse it",
            private_tree.display()
        ),
    }
}

/// Reserve an attempt parent without touching any existing staging tree.
fn prepare_invalid_staging(
    staging_root: &Path,
    instance_identity: &str,
) -> Result<OwnedDirectory, PublicationError> {
    let short: String = instance_identity.chars().take(16).collect();
    OwnedDirectory::fresh(staging_root, &format!("invalid-{short}"))
        .map_err(|error| PublicationError::Io(format!("reserve invalid staging: {error}")))
}

/// Acquire ownership before checks or asynchronous work. Locks are nonblocking;
/// a caller can retry after the active writer completes or is cancelled.
fn publication_lease(path: &Path) -> Result<PathLease, PublicationError> {
    PathLease::acquire(path).map_err(|error| {
        PublicationError::Io(format!(
            "acquire publication ownership of {}: {error}",
            path.display()
        ))
    })
}

fn publication_entry_exists(path: &Path) -> Result<bool, PublicationError> {
    entry_exists(path)
        .map_err(|error| PublicationError::Io(format!("inspect {}: {error}", path.display())))
}

/// Matching durable evidence can be reused; differing bytes are never replaced.
fn check_existing_record(path: &Path, bytes: &[u8]) -> Result<bool, PublicationError> {
    match std::fs::read(path) {
        Ok(existing) if existing == bytes => Ok(true),
        Ok(existing) => Err(PublicationError::RecordConflict {
            existing: existing_record_instance(&existing),
            path: path.to_path_buf(),
        }),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            // A dangling symlink is occupied, not permission to replace it.
            if publication_entry_exists(path)? {
                Err(PublicationError::Io(format!(
                    "record {} is an unreadable entry",
                    path.display()
                )))
            } else {
                Ok(false)
            }
        }
        Err(error) => Err(PublicationError::Io(format!(
            "read {}: {error}",
            path.display()
        ))),
    }
}

/// The instance identity an existing record on disk names, for a conflict
/// message. Unreadable bytes are reported as such rather than guessed at.
fn existing_record_instance(bytes: &[u8]) -> String {
    serde_json::from_slice::<Value>(bytes)
        .ok()
        .and_then(|value| {
            value
                .get("instance_identity")
                .and_then(Value::as_str)
                .map(str::to_string)
        })
        .unwrap_or_else(|| "an unreadable record".to_string())
}

/// Install fully written evidence without replacing an existing record. A
/// private sibling directory owns the temporary file; hard-link installation
/// is atomic and refuses an entry created even by a writer without our lease.
pub(super) fn write_record_atomically(path: &Path, bytes: &[u8]) -> Result<(), PublicationError> {
    if check_existing_record(path, bytes)? {
        return Ok(());
    }
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let staging = OwnedDirectory::fresh(parent, ".record-write")
        .map_err(|error| PublicationError::Io(format!("reserve record staging: {error}")))?;
    let temporary = staging.path().join("record");
    std::fs::write(&temporary, bytes)
        .map_err(|error| PublicationError::Io(format!("write {}: {error}", temporary.display())))?;
    install_record(&temporary, path, bytes)
}

/// The atomic installation boundary is deliberately separate from the early
/// conflict check: an entry appearing during the build still cannot be replaced.
fn install_record(temporary: &Path, path: &Path, bytes: &[u8]) -> Result<(), PublicationError> {
    match std::fs::hard_link(temporary, path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            check_existing_record(path, bytes).and_then(|present| {
                if present {
                    Ok(())
                } else {
                    Err(PublicationError::Io(format!(
                        "record {} disappeared during installation",
                        path.display()
                    )))
                }
            })
        }
        Err(error) => Err(PublicationError::Io(format!(
            "install record {}: {error}",
            path.display()
        ))),
    }
}

// ------------------------------------------------------------
// Settlement Of One Search Outcome
// ------------------------------------------------------------

/// What one settled run left behind.
///
/// Every terminal outcome of the search has exactly one of these: a
/// published `Valid` tree, a published `Invalid` record and tree, or a
/// failure report with nothing to publish. In all three the run's solver
/// pool is shut down and its artifact backend settled.
#[derive(Debug)]
pub enum SettledSearchOutcome {
    Valid(Box<PublishedValid>),
    Invalid(Box<PublishedInvalid>),
    /// The search reached no publishable result. Nothing is published, and
    /// the run's resources are settled all the same.
    Failure(FailureReport),
}

/// Why a settlement did not reach a published result.
#[derive(Debug)]
pub enum SettlementError {
    /// The proved Core could not be frozen.
    Freeze(CoreFreezeError),
    /// The frozen Core's `2N+1` batch did not certify.
    Certification(Box<AggregateCertificationError>),
    /// The certified candidate or the rebuilt record did not publish.
    Publication(Box<PublicationError>),
    /// The run's solver pool did not shut down cleanly. Raised only when
    /// the result itself was otherwise reached, so a shutdown failure never
    /// masks a real publication failure; on a settled failure the shutdown
    /// error is appended to that failure's own detail instead.
    Shutdown(String),
    /// The run's artifact backend did not settle.
    Settlement(FailureReport),
}

impl fmt::Display for SettlementError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Freeze(error) => write!(formatter, "the proved Core did not freeze: {error}"),
            Self::Certification(error) => {
                write!(formatter, "the frozen Core did not certify: {error}")
            }
            Self::Publication(error) => write!(formatter, "{error}"),
            Self::Shutdown(detail) => {
                write!(
                    formatter,
                    "the run's solver pool did not shut down: {detail}"
                )
            }
            Self::Settlement(report) => write!(
                formatter,
                "the run's artifact backend did not settle: {}",
                report.detail().unwrap_or("no detail")
            ),
        }
    }
}

impl std::error::Error for SettlementError {}

/// The run-owned resources one settlement consumes.
///
/// Both are taken by value: settlement is the end of the run, and the two
/// authorities that must not outlive it are the worker pool and the
/// artifact backend's unique owner.
pub struct SettlementResources {
    /// The run's solver context. Shut down after the result is published.
    pub solver: FrameworkIISolverContext,
    /// The run's unique artifact-backend owner. Settled last, so the
    /// manifest it freezes describes a run whose work has stopped.
    pub artifacts: ArtifactBackendOwner,
}

/// Everything a settlement needs beyond the outcome and the resources.
pub struct SettlementPolicy<'a> {
    pub space_guard: Option<&'a std::sync::Arc<super::resource_limits::SpaceGuard>>,
    /// The live bound admission context the frozen clauses are re-admitted
    /// through (`Valid` only).
    pub admission: &'a FrameworkIIAdmissionContext,
    pub solver_admission: &'a SolverAdmission,
    /// The pinned leancheck Vampire every `Valid` job is re-proved with.
    pub pinned: &'a PinnedLeancheckVampire,
    /// The benchmark being published.
    pub canonical_id: &'a str,
    /// The immutable `Input.lean` declaration namespace both shapes
    /// elaborate over.
    pub input_namespace: &'a str,
    pub repository_root: PathBuf,
    /// Staging parent for certification and for both revalidations. It must
    /// be on the destination's filesystem: publication is one rename.
    pub staging_root: PathBuf,
    /// Private root the `Valid` candidate is certified under.
    pub private_root: PathBuf,
    /// This run's own directory for the input being settled — the
    /// campaign's fresh per-input directory, not the checked-in benchmark
    /// directory the bound Lean worker reads `Input.lean` from. An
    /// `Invalid` result writes `Counterexample.json` here; under
    /// [`Retention::All`] a `Valid` result's certification evidence is
    /// kept under `input_directory`/[`VALID_EVIDENCE_DIRECTORY`] here too.
    pub input_directory: PathBuf,
    /// Where the published `Certificate/` tree goes. Must not exist.
    pub destination: PathBuf,
    /// Per-job leancheck deadline (`Valid` only).
    pub time_limit_seconds: u64,
    /// One independent certification allowance for both Valid and Invalid,
    /// including re-admission/generation and revalidation.
    pub certification_limit: Duration,
    /// How many `Valid` jobs may be solved at once.
    pub concurrency: NonZeroUsize,
    /// The run's fuel policy for counterexample validation, read from the
    /// same live authority the search applied (`Invalid` only).
    pub fuel_policy: CounterexampleFuelPolicy,
    /// The run's own artifact retention (`Valid` only): under
    /// [`Retention::All`] the certification's solver evidence is kept at
    /// `input_directory`/[`VALID_EVIDENCE_DIRECTORY`]; under
    /// [`Retention::CertificateOnly`] it is dropped. An `Invalid` result
    /// never had evidence to retain.
    pub retention: Retention,
    /// External root with no search deadline bound to it.
    pub external_cancellation: &'a CancellationToken,
    #[cfg(feature = "test-hooks")]
    pub hooks: CertificateBuildHooks,
}

/// Settle one terminal search outcome: certify or record it, publish it
/// atomically, and shut the run's resources down.
///
/// This is the production exit from [`PreCertificateAgentHoudiniSearch`],
/// and the only one. Each of the search's three terminal outcomes has
/// exactly one path through it:
///
/// - `Valid`: freeze the proved Core, certify its exact `2N+1` batch under
///   the pinned leancheck Vampire, and publish the checked candidate with
///   [`publish_valid`] — a revalidation and then one rename.
/// - `Invalid`: bind the frozen counterexample to the run's own fuel policy
///   as a [`DurableCounterexampleRecord`] and publish it with
///   [`publish_invalid`] — Lean's re-decode and re-check, a revalidation at
///   the negated target, the record beside the input, and then one rename.
/// - `Failure`: nothing is published.
///
/// In all three the solver pool is shut down and the artifact backend
/// settled before this returns, in that order. A shutdown or settlement
/// failure is reported only when the result itself was reached, so it never
/// masks the reason a publication failed.
///
/// [`PreCertificateAgentHoudiniSearch`]: super::search::PreCertificateAgentHoudiniSearch
pub async fn settle_search_outcome<S, C>(
    outcome: PreCertificateAgentHoudiniOutcome<S, C>,
    policy: SettlementPolicy<'_>,
    resources: SettlementResources,
) -> Result<SettledSearchOutcome, SettlementError>
where
    S: AgentProvider,
    C: FrameworkIIChecker,
{
    let SettlementResources { solver, artifacts } = resources;
    let settled = settle_outcome_before_shutdown(outcome, policy, &solver).await;
    // Resource shutdown and settlement happen on every path, including the
    // failed ones: a run that could not publish still owns a worker pool
    // and an artifact backend, and both stop here.
    let shutdown = solver.shutdown().await;
    let backend = artifacts.settle();
    let settled = settled?;
    // A settled failure is the run's own account of what went wrong, and a
    // shutdown error is very often that same failure replayed by the pool
    // it latched in. Reporting the shutdown instead would replace a search
    // failure with an infrastructure one and lose the record's own status.
    // The shutdown error is not dropped, though: a pool that could not be
    // shut down may be a solver tree that could not be reaped, which is a
    // fact about the machine and not about this input, so it is carried
    // into the failure's own detail where an operator reading the record
    // finds it.
    if let SettledSearchOutcome::Failure(report) = settled {
        let report = match shutdown {
            Ok(()) => report,
            Err(error) => report
                .with_appended_detail(&format!("the run's solver pool did not shut down: {error}")),
        };
        backend.map_err(SettlementError::Settlement)?;
        return Ok(SettledSearchOutcome::Failure(report));
    }
    if let Err(error) = shutdown {
        return Err(SettlementError::Shutdown(error.to_string()));
    }
    backend.map_err(SettlementError::Settlement)?;
    Ok(settled)
}

async fn settle_outcome_before_shutdown<S, C>(
    outcome: PreCertificateAgentHoudiniOutcome<S, C>,
    policy: SettlementPolicy<'_>,
    solver: &FrameworkIISolverContext,
) -> Result<SettledSearchOutcome, SettlementError>
where
    S: AgentProvider,
    C: FrameworkIIChecker,
{
    match outcome {
        PreCertificateAgentHoudiniOutcome::Failure(report) => {
            Ok(SettledSearchOutcome::Failure(report))
        }
        PreCertificateAgentHoudiniOutcome::Valid(mut handoff) => {
            let frozen = handoff.freeze_core().map_err(SettlementError::Freeze)?;
            // `--retention all` keeps the batch's solver evidence beside the
            // run's other payloads, under the input's own directory, never
            // inside the private candidate tree `publish_valid` renames away
            // and then requires empty, and never inside the published
            // `Certificate` tree itself. `certificate-only` drops it, the
            // same as every other payload settlement does not retain.
            let evidence_destination = match policy.retention {
                Retention::All => Some(policy.input_directory.join(VALID_EVIDENCE_DIRECTORY)),
                Retention::CertificateOnly => None,
            };
            let candidate = certify_frozen_core(CertifyFrozenCoreRequest {
                frozen: &frozen,
                admission: policy.admission,
                solver,
                solver_admission: policy.solver_admission,
                catalog: handoff.catalog(),
                pinned: policy.pinned,
                time_limit_seconds: policy.time_limit_seconds,
                certification_limit: policy.certification_limit,
                concurrency: policy.concurrency,
                repository_root: policy.repository_root.clone(),
                staging_root: policy.staging_root.clone(),
                private_root: policy.private_root.clone(),
                evidence_destination,
                cancellation: policy.external_cancellation,
                #[cfg(feature = "test-hooks")]
                hooks: policy.hooks,
            })
            .await
            .map_err(|error| SettlementError::Certification(Box::new(error)))?;
            // The live search is done with: the candidate is a complete
            // private tree and publication reads nothing else from the run.
            drop(handoff);
            let published = publish_valid(PublishValidRequest {
                space_guard: policy.space_guard,
                candidate,
                canonical_id: policy.canonical_id,
                input_namespace: policy.input_namespace,
                repository_root: policy.repository_root.clone(),
                staging_root: policy.staging_root.clone(),
                destination: policy.destination.clone(),
            })
            .await
            .map_err(|error| SettlementError::Publication(Box::new(error)))?;
            Ok(SettledSearchOutcome::Valid(Box::new(published)))
        }
        PreCertificateAgentHoudiniOutcome::Invalid(record) => {
            let durable = DurableCounterexampleRecord::new(*record, policy.fuel_policy);
            let published = publish_invalid(PublishInvalidRequest {
                space_guard: policy.space_guard,
                solver,
                admission: policy.solver_admission,
                record: &durable,
                input_namespace: policy.input_namespace,
                repository_root: policy.repository_root.clone(),
                staging_root: policy.staging_root.clone(),
                input_directory: policy.input_directory.clone(),
                destination: policy.destination.clone(),
                external_cancellation: policy.external_cancellation,
                certification_limit: Some(policy.certification_limit),
                #[cfg(feature = "test-hooks")]
                hooks: policy.hooks,
            })
            .await
            .map_err(|error| SettlementError::Publication(Box::new(error)))?;
            Ok(SettledSearchOutcome::Invalid(Box::new(published)))
        }
    }
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    #[tokio::test]
    async fn workspace_failure_prevents_the_publication_rename() {
        let root = std::env::temp_dir().join(format!(
            "whiel-publication-space-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&root).unwrap();
        let tree = root.join("private");
        std::fs::create_dir(&tree).unwrap();
        std::fs::write(tree.join("evidence"), b"12345").unwrap();
        let guard = super::super::resource_limits::SpaceGuard::new(
            &super::super::resource_limits::CampaignResourceLimits {
                workspace_bytes: 4,
                minimum_free_bytes: 1,
                ..Default::default()
            },
            root.clone(),
            crate::runtime::CancellationToken::new(),
        );
        let destination = root.join("Certificate");
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        let error = finish_publication_phase(phase, None, Ok(()), |token| {
            publication_space_check(Some(&guard), token)
        })
        .await
        .and_then(|()| publish_tree(&tree, &destination))
        .unwrap_err();
        assert!(error.to_string().contains("resource_exhausted"));
        assert!(!destination.exists());
        assert!(tree.join("evidence").exists());
        std::fs::remove_dir_all(root).unwrap();
    }

    async fn stopped_final_space_scan_cannot_publish(deadline: bool) {
        let scratch =
            OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-publication-delayed-scan").unwrap();
        let root = scratch.path().to_path_buf();
        let tree = root.join("private");
        std::fs::create_dir(&tree).unwrap();
        std::fs::write(tree.join("evidence"), b"checked proof").unwrap();
        let destination = root.join("Certificate");
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        let limit = deadline.then_some(Duration::from_millis(20));
        if let Some(limit) = limit {
            assert!(
                phase
                    .token()
                    .bind_absolute_deadline(tokio::time::Instant::now() + limit)
            );
        }
        let (started, wait_started) = tokio::sync::oneshot::channel();
        let cancel = external.clone();
        let interrupter = tokio::spawn(async move {
            wait_started.await.unwrap();
            if !deadline {
                cancel.cancel();
            }
        });
        let completed = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let observed = completed.clone();
        let error = tokio::time::timeout(
            Duration::from_secs(2),
            finish_publication_phase(phase, limit, Ok(()), move |token| async move {
                started.send(()).unwrap();
                // Inject a scan that finishes successfully only after its
                // phase stops. The completion boundary must still reject it,
                // and must join the check before returning to the rename.
                token.cancelled().await;
                observed.store(true, std::sync::atomic::Ordering::SeqCst);
                Ok(())
            }),
        )
        .await
        .expect("the delayed check and cancellation relay must join")
        .and_then(|()| publish_tree(&tree, &destination))
        .unwrap_err();
        interrupter.await.unwrap();
        assert!(completed.load(std::sync::atomic::Ordering::SeqCst));
        if deadline {
            assert!(matches!(error, PublicationError::DeadlineExpired(_)));
        } else {
            assert!(matches!(error, PublicationError::Interrupted));
        }
        assert!(!destination.exists());
        assert_eq!(
            std::fs::read(tree.join("evidence")).unwrap(),
            b"checked proof"
        );
        std::fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn certification_deadline_during_final_space_scan_prevents_publication() {
        stopped_final_space_scan_cannot_publish(true).await;
    }

    #[tokio::test]
    async fn external_cancellation_during_final_space_scan_prevents_publication() {
        stopped_final_space_scan_cannot_publish(false).await;
    }

    /// The deferred entry points wrap a whole build in one phase and bind
    /// its allowance there, so the `Invalid` body runs under that phase
    /// instead of opening a second one. The runtime's refusal of a phase
    /// nested on another phase's child stays exactly where it is: it is the
    /// publication's own phase step that moves.
    #[tokio::test]
    async fn the_invalid_body_runs_under_a_phase_its_caller_already_owns() {
        let external = CancellationToken::new();
        let owned = open_certification_phase(&external, Some(Duration::from_secs(600)))
            .expect("a deadline-free root opens one phase");
        // What the deferred path used to ask for, and is still refused.
        let nested = open_certification_phase(owned.token(), Some(Duration::from_secs(600)));
        assert!(
            matches!(&nested, Err(PublicationError::PhaseControl(detail))
                if detail.contains("deadline-free external root")),
            "a phase never nests on another phase's child"
        );
        // The body's own step runs under the caller's live phase, checks
        // storage on its token, and leaves the relay for its owner to join.
        let checked = check_publication_step(
            &owned,
            Some(Duration::from_secs(600)),
            Ok("built"),
            |token| async move {
                assert!(!token.is_cancelled());
                Ok(())
            },
        )
        .await
        .expect("a live phase lets the publication finish its work");
        assert_eq!(checked, "built");
        let completed = owned
            .finish()
            .await
            .expect("the owner joins the relay it started");
        assert!(completed.stop.is_none());
    }

    /// A stop on the caller's phase still ends the publication, and says
    /// which stop it was: the allowance the caller bound is the allowance a
    /// deadline expiry is reported against.
    #[tokio::test]
    async fn a_stopped_caller_phase_refuses_the_invalid_publication_step() {
        let limit = Duration::from_millis(20);
        for interrupt in [false, true] {
            let external = CancellationToken::new();
            let owned = open_certification_phase(&external, Some(limit))
                .expect("a deadline-free root opens one phase");
            if interrupt {
                external.cancel();
            } else {
                tokio::time::sleep(limit * 2).await;
            }
            let refused = check_publication_step(&owned, Some(limit), Ok(()), |_| async { Ok(()) })
                .await
                .expect_err("a stopped phase publishes nothing");
            if interrupt {
                assert!(
                    matches!(&refused, PublicationError::Interrupted),
                    "{refused}"
                );
            } else {
                assert!(
                    matches!(&refused, PublicationError::DeadlineExpired(reported)
                        if *reported == limit),
                    "{refused}"
                );
            }
            owned.finish().await.expect("the owner joins its own relay");
        }
    }

    use super::*;
    use crate::framework2::tests::fixed_ambient_task;
    use crate::task::SynthesisTask;
    use serde_json::json;

    fn tool_policy() -> AgentToolPolicy {
        AgentToolPolicy::new([AgentTool::Countermodel, AgentTool::Ledger])
    }

    fn configuration() -> RunConfiguration {
        RunConfiguration::new(
            true,
            Some(3),
            Some(
                &FrameworkIIRetryPolicy::new([Duration::from_secs(5), Duration::from_secs(10)])
                    .expect("a strictly increasing ladder"),
            ),
            Some(PremiseRole::NegatedConjecture),
            &tool_policy(),
            Retention::CertificateOnly,
        )
        .expect("every duration of this policy is exactly representable")
    }

    /// The whole run policy survives its persisted form exactly, and the
    /// digest is a function of that form alone.
    #[test]
    fn the_run_configuration_round_trips_through_its_persisted_form() {
        let configuration = configuration();
        let persisted = configuration.to_json();
        let decoded = RunConfiguration::from_json(&persisted).expect("its own form decodes");
        assert_eq!(decoded, configuration);
        assert_eq!(decoded.digest(), configuration.digest());
        assert!(decoded.compress_core());
        assert_eq!(decoded.level_bound(), Some(3));
        assert_eq!(decoded.retry_baseline(), Duration::from_secs(5));
        assert_eq!(
            decoded.retry_allowances(),
            [Duration::from_secs(5), Duration::from_secs(10)]
        );
        assert_eq!(decoded.tools(), ["countermodel", "ledger"]);
        assert_eq!(decoded.retention(), Retention::CertificateOnly);
        assert_eq!(persisted["kind"], json!(RUN_CONFIGURATION_KIND));
        assert_eq!(persisted["version"], json!(RUN_CONFIGURATION_VERSION));
        assert!(persisted.get("session_mode").is_none());

        // Milestone 7.5 review, finding 5: the CASC portfolio policy is read
        // from the checker's own retry policy and is disabled by default,
        // and an enabled run records that instead.
        assert_eq!(decoded.casc_portfolio(), CascPortfolioPolicy::Disabled);
        assert_eq!(persisted["casc_portfolio"], json!("disabled"));
        let enabled = RunConfiguration::new(
            true,
            Some(3),
            Some(
                &FrameworkIIRetryPolicy::new([Duration::from_secs(5), Duration::from_secs(10)])
                    .expect("a strictly increasing ladder")
                    .with_casc_portfolio(CascPortfolioPolicy::Enabled),
            ),
            None,
            &tool_policy(),
            Retention::CertificateOnly,
        )
        .expect("every duration of this policy is exactly representable");
        assert_eq!(enabled.casc_portfolio(), CascPortfolioPolicy::Enabled);
        assert_eq!(enabled.to_json()["casc_portfolio"], json!("enabled"));
        assert_ne!(
            enabled.digest(),
            configuration.digest(),
            "the portfolio policy is part of the run's recorded identity"
        );
        assert_eq!(
            RunConfiguration::from_json(&enabled.to_json()).unwrap(),
            enabled
        );
    }

    /// The retry premise role is part of the run's identity: two searches
    /// that render their retries differently are not one run, and a record
    /// that predates the member is refused rather than read as either.
    #[test]
    fn the_retry_premise_role_is_bound_and_an_older_record_is_refused() {
        let goal_tagged = configuration();
        assert_eq!(
            goal_tagged.retry_premise_role(),
            PremiseRole::NegatedConjecture
        );
        assert_eq!(
            goal_tagged.to_json()["retry_premise_role"],
            json!("negated_conjecture")
        );
        let axiom_tagged = RunConfiguration::new(
            true,
            Some(3),
            Some(
                &FrameworkIIRetryPolicy::new([Duration::from_secs(5), Duration::from_secs(10)])
                    .expect("a strictly increasing ladder"),
            ),
            Some(PremiseRole::Axiom),
            &tool_policy(),
            Retention::CertificateOnly,
        )
        .expect("every duration of this policy is exactly representable");
        assert_ne!(axiom_tagged, goal_tagged);
        assert_ne!(axiom_tagged.digest(), goal_tagged.digest());
        assert!(matches!(
            axiom_tagged.check_drift(&goal_tagged),
            Err(RunConfigurationError::Drift { .. })
        ));

        // The same record without the member is the form written before
        // the role existed. It is refused rather than read as one role or
        // the other — as a record that states no role, exactly as a record
        // that stated no portfolio policy before it.
        let mut older = goal_tagged.to_json();
        let object = older.as_object_mut().expect("a record is an object");
        object.remove("retry_premise_role");
        object.insert("version".to_string(), json!(RUN_CONFIGURATION_VERSION - 1));
        assert!(RunConfiguration::from_json(&older).is_err());
        // A record that is otherwise current but names an earlier version
        // is refused on the version itself.
        let mut renumbered = goal_tagged.to_json();
        renumbered["version"] = json!(RUN_CONFIGURATION_VERSION - 1);
        assert!(matches!(
            RunConfiguration::from_json(&renumbered),
            Err(RunConfigurationError::UnsupportedVersion(version))
                if version == RUN_CONFIGURATION_VERSION - 1
        ));

        // And a current record that omits it, or names a role that is not
        // one, is malformed rather than defaulted.
        let mut missing = goal_tagged.to_json();
        missing
            .as_object_mut()
            .expect("a record is an object")
            .remove("retry_premise_role");
        assert!(matches!(
            RunConfiguration::from_json(&missing),
            Err(RunConfigurationError::Malformed(_))
        ));
        let mut unknown = goal_tagged.to_json();
        unknown["retry_premise_role"] = json!("conjecture");
        assert!(matches!(
            RunConfiguration::from_json(&unknown),
            Err(RunConfigurationError::Malformed(_))
        ));
    }

    /// A checker that declares no retry policy contributes an empty ladder
    /// rather than a fabricated one.
    #[test]
    fn a_run_without_a_retry_policy_records_an_empty_ladder() {
        let configuration = RunConfiguration::new(
            false,
            None,
            None,
            None,
            &AgentToolPolicy::none_enabled(),
            Retention::All,
        )
        .expect("an empty ladder is exactly representable");
        assert_eq!(configuration.retry_allowances(), []);
        assert_eq!(configuration.retry_baseline(), Duration::ZERO);
        // A run that performs no retry states the role every first launch
        // uses, rather than one it would never have reached.
        assert_eq!(configuration.retry_premise_role(), PremiseRole::Axiom);
        assert!(configuration.tools().is_empty());
        assert_eq!(
            RunConfiguration::from_json(&configuration.to_json()).unwrap(),
            configuration
        );
    }

    /// Every way a persisted record can fail to be a current record is
    /// refused, so a stale host fails closed instead of reading a record it
    /// only partly understands.
    #[test]
    fn the_run_configuration_decoder_refuses_every_stale_or_malformed_record() {
        let base = configuration().to_json();
        let mutate = |mutation: &dyn Fn(&mut Value)| {
            let mut value = base.clone();
            mutation(&mut value);
            value
        };
        let cases: Vec<Value> = vec![
            mutate(&|value| value["kind"] = json!("whiel_framework_ii_something_else")),
            mutate(&|value| value["version"] = json!(RUN_CONFIGURATION_VERSION + 1)),
            mutate(&|value| value["version"] = json!(2)),
            mutate(&|value| {
                value["version"] = json!(2);
                value["session_mode"] = json!("fresh");
            }),
            mutate(&|value| {
                value
                    .as_object_mut()
                    .unwrap()
                    .insert("extra".to_string(), json!(1));
            }),
            mutate(&|value| value["session_mode"] = json!("resumed")),
            mutate(&|value| value["retention"] = json!("some")),
            mutate(&|value| value["tools"] = json!(["countermodel", "no_such_tool"])),
            // Not canonical order.
            mutate(&|value| value["tools"] = json!(["ledger", "countermodel"])),
            // A duplicate.
            mutate(&|value| value["tools"] = json!(["countermodel", "countermodel"])),
            mutate(&|value| {
                value["retry_policy"]
                    .as_object_mut()
                    .unwrap()
                    .insert("extra".to_string(), json!(1));
            }),
            mutate(&|value| {
                value.as_object_mut().unwrap().remove("level_bound");
            }),
            // Milestone 7.5 review, finding 5: the CASC portfolio policy is
            // a required member with two names, and a v1 record — which
            // states none at all — is refused by the version check rather
            // than read as a run bound to no portfolio policy.
            mutate(&|value| value["casc_portfolio"] = json!("sometimes")),
            mutate(&|value| {
                value.as_object_mut().unwrap().remove("casc_portfolio");
            }),
            mutate(&|value| {
                value["version"] = json!(1);
                value.as_object_mut().unwrap().remove("casc_portfolio");
            }),
        ];
        for case in cases {
            assert!(
                RunConfiguration::from_json(&case).is_err(),
                "this record must be refused: {case}"
            );
        }
        assert_eq!(
            RunConfiguration::from_json(&mutate(&|value| {
                value["version"] = json!(RUN_CONFIGURATION_VERSION + 1)
            })),
            Err(RunConfigurationError::UnsupportedVersion(
                RUN_CONFIGURATION_VERSION + 1
            ))
        );
    }

    /// Drift is reported with both digests, so a failure says what changed
    /// against what.
    #[test]
    fn a_changed_run_configuration_is_drift_against_the_bound_one() {
        let bound = configuration();
        assert_eq!(bound.check_drift(&bound), Ok(()));
        let moved = RunConfiguration::new(
            true,
            Some(4),
            Some(
                &FrameworkIIRetryPolicy::new([Duration::from_secs(5), Duration::from_secs(10)])
                    .unwrap(),
            ),
            None,
            &tool_policy(),
            Retention::CertificateOnly,
        )
        .expect("every duration of this policy is exactly representable");
        assert_eq!(
            moved.check_drift(&bound),
            Err(RunConfigurationError::Drift {
                bound: bound.digest(),
                found: moved.digest(),
            })
        );
    }

    fn durable_record(task: &SynthesisTask) -> DurableCounterexampleRecord {
        let record = FrozenCounterexampleRecord::rehydrate(
            json!({"relations": [{"name": "p::E", "rows": [["num:0", "num:1"]]}]}),
            "c".repeat(64),
            6,
            task.identity().clone(),
            "d".repeat(64),
            CounterexampleProvenance::RecordedWitness {
                source: "Benchmark/Fixture/Metadata.json".into(),
            },
        );
        DurableCounterexampleRecord::new(record, fuel_policy())
    }

    fn fuel_policy() -> CounterexampleFuelPolicy {
        CounterexampleFuelPolicy::new(Duration::from_secs(30))
            .expect("thirty seconds is exactly representable")
    }

    /// The durable record survives its own persisted form, including the
    /// instance Lean issued, which is never rewritten on the way through.
    #[test]
    fn the_durable_counterexample_record_round_trips_against_its_own_task() {
        let task = fixed_ambient_task();
        let record = durable_record(&task);
        let persisted = record.to_json();
        let decoded =
            DurableCounterexampleRecord::from_json(&persisted, task.identity(), &"d".repeat(64))
                .expect("its own form decodes");
        assert_eq!(decoded.frozen().instance(), record.frozen().instance());
        assert_eq!(decoded.frozen().instance_identity(), &"c".repeat(64));
        assert_eq!(decoded.frozen().fuel_consumed(), 6);
        assert_eq!(decoded.frozen().task_identity(), task.identity());
        assert_eq!(decoded.frozen().scope_identity_sha256(), &"d".repeat(64));
        assert_eq!(
            decoded.frozen().provenance(),
            &CounterexampleProvenance::RecordedWitness {
                source: "Benchmark/Fixture/Metadata.json".into(),
            }
        );
        assert!(decoded.frozen().consultation().is_none());
        assert_eq!(decoded.fuel_policy(), record.fuel_policy());
        // The fuel policy says what it is: a structural replay with no host
        // bound, guarded only by the call-local limit.
        assert_eq!(persisted["fuel_policy"]["kind"], json!("structural_replay"));
        assert_eq!(persisted["fuel_policy"]["host_fuel_bound"], Value::Null);
    }

    /// A consultation-provenance record keeps the exact binding digests.
    #[test]
    fn a_consulted_record_keeps_its_consultation_binding() {
        let task = fixed_ambient_task();
        let record = DurableCounterexampleRecord::new(
            FrozenCounterexampleRecord::rehydrate(
                json!({"relations": []}),
                "c".repeat(64),
                2,
                task.identity().clone(),
                "d".repeat(64),
                CounterexampleProvenance::Consultation(Box::new(
                    super::super::agent::AgentConsultationBinding::for_test(&"e".repeat(64), 7),
                )),
            ),
            fuel_policy(),
        );
        let decoded = DurableCounterexampleRecord::from_json(
            &record.to_json(),
            task.identity(),
            &"d".repeat(64),
        )
        .unwrap();
        let binding = decoded
            .frozen()
            .consultation()
            .expect("a consulted record keeps its binding");
        assert_eq!(binding.consultation_digest(), &"e".repeat(64));
        assert_eq!(binding.validation_ordinal(), 7);
    }

    /// A record is only readable back into the run whose exact input
    /// source, scope, and record version it was written against.
    #[test]
    fn the_durable_counterexample_decoder_refuses_another_task_scope_or_version() {
        let task = fixed_ambient_task();
        let scope = "d".repeat(64);
        let base = durable_record(&task).to_json();

        let mut other_task = base.clone();
        other_task["task"]["canonical_id"] = json!("SomeOtherTask");
        assert!(matches!(
            DurableCounterexampleRecord::from_json(&other_task, task.identity(), &scope),
            Err(DurableCounterexampleError::TaskMismatch { .. })
        ));

        let mut other_source = base.clone();
        other_source["task"]["source_sha256"] = json!("b".repeat(64));
        assert!(matches!(
            DurableCounterexampleRecord::from_json(&other_source, task.identity(), &scope),
            Err(DurableCounterexampleError::TaskMismatch { .. })
        ));

        let mut other_scope = base.clone();
        other_scope["scope_identity_sha256"] = json!("e".repeat(64));
        assert!(matches!(
            DurableCounterexampleRecord::from_json(&other_scope, task.identity(), &scope),
            Err(DurableCounterexampleError::ScopeMismatch { .. })
        ));

        let mut later = base.clone();
        later["version"] = json!(COUNTEREXAMPLE_RECORD_VERSION + 1);
        assert!(matches!(
            DurableCounterexampleRecord::from_json(&later, task.identity(), &scope),
            Err(DurableCounterexampleError::UnsupportedVersion(version))
                if version == COUNTEREXAMPLE_RECORD_VERSION + 1
        ));

        let mutations: [&dyn Fn(&mut Value); 6] = [
            &|value: &mut Value| value["kind"] = json!("whiel_framework_ii_core_rows"),
            &|value: &mut Value| {
                value.as_object_mut().unwrap().insert("x".into(), json!(1));
            },
            &|value: &mut Value| value["instance"] = Value::Null,
            &|value: &mut Value| value["fuel_policy"]["kind"] = json!("bounded"),
            &|value: &mut Value| value["fuel_policy"]["host_fuel_bound"] = json!(4096),
            &|value: &mut Value| value["provenance"]["kind"] = json!("guessed"),
        ];
        for mutation in mutations {
            let mut value = base.clone();
            mutation(&mut value);
            assert!(
                DurableCounterexampleRecord::from_json(&value, task.identity(), &scope).is_err(),
                "this record must be refused: {value}"
            );
        }
    }

    /// Pass 7.5g review, finding 8: the instance identity is a Lean-issued
    /// sha256 and is checked to look like one. Consumers name staging
    /// directories after a prefix of it, so a record whose identity is
    /// short, upper case, non-hex, or multi-byte is refused here rather
    /// than reaching a slice that could split a character boundary.
    #[test]
    fn the_durable_counterexample_decoder_refuses_a_malformed_instance_identity() {
        let task = fixed_ambient_task();
        let scope = "d".repeat(64);
        let base = durable_record(&task).to_json();
        for identity in [
            String::new(),
            "c".repeat(63),
            "c".repeat(65),
            "C".repeat(64),
            format!("{}g", "c".repeat(63)),
            // Sixteen bytes of this string do not end on a character
            // boundary, which is exactly what a byte slice would panic on.
            "é".repeat(32),
        ] {
            let mut value = base.clone();
            value["instance_identity"] = json!(identity);
            let error = DurableCounterexampleRecord::from_json(&value, task.identity(), &scope)
                .expect_err("a malformed instance identity is refused");
            assert!(
                matches!(&error, DurableCounterexampleError::Malformed(detail)
                    if detail.contains("64 lowercase hex")),
                "{error}"
            );
        }
        assert!(is_sha256_hex(&"c".repeat(64)));
        assert!(is_sha256_hex("0123456789abcdef".repeat(4).as_str()));
    }

    #[test]
    fn concurrent_record_writes_never_replace_different_evidence() {
        use std::sync::{Arc, Barrier};
        let root = Scratch::new("record-overlap");
        let record = root.path().join(COUNTEREXAMPLE_RECORD_FILE);
        let old_part = record.with_extension("part");
        std::fs::write(&old_part, b"foreign temporary file").unwrap();
        let barrier = Arc::new(Barrier::new(2));
        let threads: Vec<_> = [b"first record".as_slice(), b"second record".as_slice()]
            .into_iter()
            .map(|bytes| {
                let record = record.clone();
                let barrier = barrier.clone();
                std::thread::spawn(move || {
                    barrier.wait();
                    (bytes, write_record_atomically(&record, bytes))
                })
            })
            .collect();
        let results: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        assert_eq!(results.iter().filter(|r| r.1.is_ok()).count(), 1);
        let winner = results.iter().find(|r| r.1.is_ok()).unwrap();
        let loser = results.iter().find(|r| r.1.is_err()).unwrap();
        assert!(matches!(
            loser.1,
            Err(PublicationError::RecordConflict { .. })
        ));
        assert_eq!(std::fs::read(&record).unwrap(), winner.0);
        write_record_atomically(&record, winner.0).unwrap(); // Same-record replay.
        assert!(matches!(
            write_record_atomically(&record, loser.0),
            Err(PublicationError::RecordConflict { .. })
        ));
        assert_eq!(std::fs::read(old_part).unwrap(), b"foreign temporary file");
        assert_eq!(
            std::fs::read_dir(root.path()).unwrap().count(),
            2,
            "temporary attempt directories were removed"
        );
    }

    #[test]
    fn a_record_appearing_after_the_early_check_is_never_replaced() {
        let root = Scratch::new("record-late-conflict");
        let path = root.path().join(COUNTEREXAMPLE_RECORD_FILE);
        assert!(!check_existing_record(&path, b"this attempt").unwrap());
        let attempt = OwnedDirectory::fresh(root.path(), "attempt").unwrap();
        let temporary = attempt.path().join("record");
        std::fs::write(&temporary, b"this attempt").unwrap();
        std::fs::write(&path, b"another writer").unwrap();
        assert!(matches!(
            install_record(&temporary, &path, b"this attempt"),
            Err(PublicationError::RecordConflict { .. })
        ));
        assert_eq!(std::fs::read(&path).unwrap(), b"another writer");
        assert_eq!(std::fs::read(&temporary).unwrap(), b"this attempt");
        drop(attempt);
        assert_eq!(std::fs::read_dir(root.path()).unwrap().count(), 1);
    }

    #[tokio::test]
    async fn shared_record_lease_spans_awaits_even_for_distinct_destinations() {
        let root = Scratch::new("record-leases");
        let record = root.path().join(COUNTEREXAMPLE_RECORD_FILE);
        let destination = root.path().join("Certificate");
        let other = root.path().join("OtherCertificate");
        let first = publication_lease(&destination).unwrap();
        let record_owner = publication_lease(&record).unwrap();
        tokio::task::yield_now().await;
        let second = publication_lease(&other).unwrap(); // Independent outputs proceed.
        assert!(publication_lease(&record).is_err()); // Shared evidence is still owned.
        drop((first, record_owner));
        let retry = publication_lease(&record).unwrap();
        write_record_atomically(&record, b"reusable evidence").unwrap();
        drop((retry, second));
        let repeat = publication_lease(&record).unwrap();
        write_record_atomically(&record, b"reusable evidence").unwrap();
        drop(repeat);
    }

    #[tokio::test]
    async fn failed_final_check_releases_leases_and_owned_invalid_staging() {
        let root = Scratch::new("publication-failed-cleanup");
        let destination = root.path().join("Certificate");
        let record = root.path().join(COUNTEREXAMPLE_RECORD_FILE);
        let lease = publication_lease(&destination).unwrap();
        let record_lease = publication_lease(&record).unwrap();
        let staging = prepare_invalid_staging(root.path(), &"a".repeat(64)).unwrap();
        let attempt = staging.path().to_path_buf();
        std::fs::write(attempt.join("proof"), b"private").unwrap();
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        let result =
            finish_publication_phase(phase, None, Ok((lease, record_lease, staging)), |_| async {
                Err("injected final storage failure".into())
            })
            .await;
        assert!(result.is_err());
        assert!(!attempt.exists());
        assert!(!destination.exists());
        drop(publication_lease(&destination).unwrap());
        drop(publication_lease(&record).unwrap());
    }

    /// Pass 7.5g review, finding 9: a duration that cannot be stated
    /// exactly in the record's whole `u64` nanoseconds is refused at
    /// construction rather than saturated on the way out, so no record ever
    /// states a limit other than the one that was applied.
    #[test]
    fn a_duration_that_no_record_can_state_exactly_is_refused_at_construction() {
        let unrepresentable = Duration::from_secs(u64::MAX / 1_000_000);
        assert!(u64::try_from(unrepresentable.as_nanos()).is_err());

        assert_eq!(
            CounterexampleFuelPolicy::new(unrepresentable),
            Err(DurableCounterexampleError::UnrepresentableValidationLimit(
                unrepresentable
            ))
        );
        // The whole representable range round-trips exactly, including the
        // largest value there is.
        let largest = Duration::from_nanos(u64::MAX);
        let policy = CounterexampleFuelPolicy::new(largest).expect("u64 nanos are representable");
        assert_eq!(policy.validation_limit(), largest);
        assert_eq!(policy.to_json()["validation_limit_nanos"], json!(u64::MAX));

        let ladder = FrameworkIIRetryPolicy::new([unrepresentable])
            .expect("a one-rung ladder is strictly increasing");
        let refused = RunConfiguration::new(
            false,
            None,
            Some(&ladder),
            None,
            &AgentToolPolicy::none_enabled(),
            Retention::All,
        )
        .expect_err("a policy no record can state exactly is refused");
        assert!(
            matches!(
                &refused,
                RunConfigurationError::UnrepresentableDuration { .. }
            ),
            "{refused}"
        );
    }

    // ------------------------------------------------------------
    // Publication Mechanics
    // ------------------------------------------------------------

    struct Scratch(PathBuf);

    impl Scratch {
        fn new(label: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "whiel-publication-{label}-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .expect("the clock is after the epoch")
                    .as_nanos()
            ));
            std::fs::create_dir_all(&path).expect("create the scratch directory");
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn with_forced_cross_filesystem<T>(body: impl FnOnce() -> T) -> T {
        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(true));
        let outcome = body();
        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(false));
        outcome
    }

    /// Pass 7.5g review, finding 2: publication is one rename or it is
    /// refused. There is no copy fallback, and the refusal comes before
    /// anything is written — which is why `ensure_same_filesystem` is a
    /// separate check the publishers run before Lean does anything.
    ///
    /// A second filesystem cannot be assumed on a developer machine, so the
    /// two devices are made to disagree on demand; the same switch drives
    /// the rename path itself, so both halves of the refusal are covered.
    #[test]
    fn a_publication_across_filesystems_is_refused_and_never_copies() {
        let scratch = Scratch::new("cross-device");
        let staging = scratch.path().join("staging");
        let tree = staging.join("Certificate");
        std::fs::create_dir_all(&tree).expect("create the staged tree");
        std::fs::write(tree.join("Valid.lean"), b"-- valid\n").expect("write a module");
        let destination = scratch.path().join("published/Certificate");

        // Same filesystem: the precheck passes and the rename publishes.
        assert!(ensure_same_filesystem(&tree, &destination).is_ok());

        let refused = with_forced_cross_filesystem(|| {
            ensure_same_filesystem(&tree, &destination)
                .expect_err("a staging root on another filesystem is refused")
        });
        assert!(
            matches!(&refused, PublicationError::CrossesFilesystems { .. }),
            "{refused}"
        );
        // The message tells the caller what to do about it.
        let message = refused.to_string();
        assert!(message.contains("one rename"), "{message}");
        assert!(
            message.contains("stage on the destination's own filesystem"),
            "{message}"
        );

        // The rename path refuses the same way, and copies nothing: the
        // staged tree is still whole and the destination was never made.
        let refused = with_forced_cross_filesystem(|| {
            publish_tree(&tree, &destination).expect_err("no copy fallback exists")
        });
        assert!(
            matches!(&refused, PublicationError::CrossesFilesystems { .. }),
            "{refused}"
        );
        assert!(tree.join("Valid.lean").is_file());
        assert!(!destination.exists());

        // Unforced, the same call publishes with one rename.
        publish_tree(&tree, &destination).expect("one rename publishes");
        assert!(!tree.exists());
        assert!(destination.join("Valid.lean").is_file());
    }

    /// Pass 7.5g review, finding 7: the private certification directory a
    /// published tree was renamed out of is removed, so a later
    /// certification of the same frozen Core is not refused by an empty
    /// leftover.
    #[test]
    fn the_emptied_private_certification_directory_is_removed() {
        let scratch = Scratch::new("private-tree");
        let private = scratch.path().join("aggregate-0123456789abcdef");
        let tree = private.join("Certificate");
        std::fs::create_dir_all(&tree).expect("create the private tree");
        std::fs::write(tree.join("Valid.lean"), b"-- valid\n").expect("write a module");
        let destination = scratch.path().join("published/Certificate");

        publish_tree(&tree, &destination).expect("one rename publishes");
        remove_emptied_private_tree(&private);
        assert!(!private.exists(), "the emptied directory is removed");
        // Removing it again is not an error: it is best effort by design.
        remove_emptied_private_tree(&private);
    }

    #[test]
    fn invalid_staging_is_owned_and_never_reuses_or_deletes_an_existing_tree() {
        let scratch = Scratch::new("invalid-staging");
        let identity = "c".repeat(64);
        let first = prepare_invalid_staging(scratch.path(), &identity).unwrap();
        let first_path = first.path().to_path_buf();
        std::fs::write(first.path().join("sentinel"), b"first").unwrap();
        let retained = first.retain();
        let second = prepare_invalid_staging(scratch.path(), &identity).unwrap();
        assert_ne!(second.path(), retained);
        assert!(second.path().is_dir());
        assert!(!second.path().join("Certificate").exists());
        let second_path = second.path().to_path_buf();
        drop(second);
        assert!(!second_path.exists());
        assert_eq!(
            std::fs::read(first_path.join("sentinel")).unwrap(),
            b"first"
        );
    }

    /// Pass 7.5g review, finding 9: a record already beside the input whose
    /// bytes are not this result's is a content conflict, and says so —
    /// naming the instance the standing record belongs to — rather than
    /// reporting an occupied destination.
    #[test]
    fn a_byte_different_standing_record_is_a_content_conflict() {
        let path = PathBuf::from("/benchmark/Example0013/Counterexample.json");
        let conflict = PublicationError::RecordConflict {
            existing: existing_record_instance(
                serde_json::to_vec_pretty(&json!({"instance_identity": "a".repeat(64)}))
                    .expect("serializable")
                    .as_slice(),
            ),
            path: path.clone(),
        };
        let message = conflict.to_string();
        assert!(message.contains("Counterexample.json"), "{message}");
        assert!(message.contains(&"a".repeat(64)), "{message}");
        assert!(
            !message.contains("destination already exists"),
            "a content conflict is not an occupied destination: {message}"
        );
        assert_eq!(
            existing_record_instance(b"not json at all"),
            "an unreadable record"
        );
        assert_eq!(
            PublicationError::DestinationExists(path).to_string(),
            "publication destination already exists: \
             /benchmark/Example0013/Counterexample.json"
        );
    }
}

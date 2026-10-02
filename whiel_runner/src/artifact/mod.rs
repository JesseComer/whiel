//! Run-scoped required artifacts and optional cold-history policy.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::mpsc::{self, Receiver, SyncSender, TrySendError};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::thread::{self, JoinHandle};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::Serialize;
use tokio::sync::{Notify, watch};

use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::task::{SynthesisTask, TaskIdentity};

/*
  One backend owns all required artifacts for one synthesis run.
  Cloneable scoped handles add provenance without copying payloads.
  Only the non-cloneable owner can settle the backend.
*/

// ------------------------------------------------------------
// Artifact Identity And Kinds
// ------------------------------------------------------------

const OPEN: u8 = 0;
const SETTLING: u8 = 1;
const SETTLED: u8 = 2;
const SETTLEMENT_FAILED: u8 = 3;

const HISTORY_DORMANT: u8 = 0;
const HISTORY_RUNNING: u8 = 1;
const HISTORY_FAILED: u8 = 2;
const HISTORY_STOPPED: u8 = 3;

static NEXT_BACKEND_SEQUENCE: IdAllocator = IdAllocator::new(0);
static BACKEND_PREFIX: OnceLock<u64> = OnceLock::new();

const DEFAULT_HISTORY_QUEUE_CAPACITY: usize = 1_024;
const MAX_HISTORY_PAGE_SIZE: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BackendId(u128);

impl fmt::Display for BackendId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:032x}", self.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ArtifactId(u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AttemptId(u64);

impl AttemptId {
    pub fn get(self) -> u64 {
        self.0
    }

    /// Reconstruct an `AttemptId` from a caller-supplied scalar (Pass 7.5c:
    /// the AgentHoudini `countermodel`/`validate_clauses` tool bodies decode
    /// an agent-supplied `u64` and must look it up against the dictionary's
    /// own `AttemptId`-keyed map). `pub(crate)` rather than `pub`: only the
    /// crate's own dictionary lookups reconstruct an `AttemptId` this way: no
    /// artifact backend accepts a caller-forged one.
    pub(crate) fn from_u64(value: u64) -> Self {
        Self(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ArtifactKind {
    Query,
    Proof,
    Model,
    EmptyInstanceCheck,
    InitializationCheck,
    Certificate,
    /// Required authority-acceptance record which precedes certificate
    /// import. Terminal results reference it, so it outlives every
    /// retention policy, unlike the run-progress `RuntimeTrace` records.
    AcceptanceRecord,
    Witness,
    FailureDiagnostic,
    RuntimeTrace,
}

impl ArtifactKind {
    /// Payloads every retention policy keeps on disk: the payloads that
    /// back a terminal result by construction.
    ///
    /// `Witness` and `FailureDiagnostic` are deliberately absent — many are
    /// published per run and only the ones a terminal result references
    /// survive certificate-only settlement (see `settle_retaining`).
    fn certificate_only_durable(self) -> bool {
        matches!(self, Self::Certificate | Self::AcceptanceRecord)
    }

    /// Provenance no one consults outside detailed diagnostics.
    ///
    /// Under `Retention::CertificateOnly` these publish as manifest records
    /// with no payload file at all. Skipping the file — not writing and
    /// deleting it — is what keeps a long run from flooding filesystem
    /// watchers such as a cloud-sync engine: a file that is written and
    /// immediately deleted still costs two bookkeeping records.
    fn certificate_only_record_only(self) -> bool {
        matches!(
            self,
            Self::RuntimeTrace | Self::EmptyInstanceCheck | Self::InitializationCheck
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArtifactRef {
    backend: BackendId,
    artifact: ArtifactId,
    kind: ArtifactKind,
}

impl ArtifactRef {
    pub fn backend_id(self) -> BackendId {
        self.backend
    }

    pub fn kind(self) -> ArtifactKind {
        self.kind
    }

    /// Return the backend-local stable identifier used in artifact manifests.
    pub fn local_id(self) -> u64 {
        self.artifact.0
    }

    /// Return this required payload's deterministic path below an artifact
    /// root.  A terminal synthesis result exposes this path only after the
    /// owning backend has settled successfully.
    pub fn retained_path(self, artifact_root: &Path) -> PathBuf {
        artifact_root
            .join(format!("run-{}", self.backend))
            .join("required")
            .join(format!("artifact-{:020}.bin", self.artifact.0))
    }
}

/// Why a staged set could not be published whole, and what it had promoted.
///
/// `published` is empty whenever the refusal happened while staging, which is
/// where the byte and file budgets refuse. It is nonempty only if an atomic
/// promotion failed part way through the set, and then it names exactly the
/// references a report must account for.
#[derive(Debug)]
pub struct PublishSetFailure {
    published: Vec<ArtifactRef>,
    report: FailureReport,
}

impl PublishSetFailure {
    pub fn published(&self) -> &[ArtifactRef] {
        &self.published
    }

    pub fn report(&self) -> &FailureReport {
        &self.report
    }

    pub fn into_report(self) -> FailureReport {
        self.report
    }
}

// ------------------------------------------------------------
// Store Configuration And Scope
// ------------------------------------------------------------

/// Which required payloads survive a run.
///
/// Runtime proofs are never read back — outcomes are stdout-authoritative
/// and certification re-runs Vampire from scratch — so outside detailed
/// diagnostics they are provenance no one consults. Discarding them as each
/// job finishes bounds *peak* disk use, which pruning at settlement cannot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Retention {
    /// Keep every payload. Required for debugging runtime issues such as a
    /// support edge skipping a call that was never actually proven.
    All,
    /// Keep only what backs the terminal result.
    ///
    /// Three complementary behaviors, in publication order:
    /// - pure-provenance kinds (`certificate_only_record_only`) publish as
    ///   manifest records with no payload file at all;
    /// - payloads consumed mid-run (queries Vampire reads, models the
    ///   decoder reads, streamed solver output) are written and discarded
    ///   as their consumer finishes with them;
    /// - settlement removes every remaining payload the terminal result
    ///   does not reference (`settle_retaining`), leaving certificates,
    ///   acceptance records, terminal-referenced witnesses/diagnostics,
    ///   and the manifest.
    CertificateOnly,
}

/// The file one run's bound configuration is persisted as, in the run root.
///
/// It is written the moment the configuration is bound rather than at
/// settlement, so a manifest-driven reopen of an unsettled run can still
/// read back exactly what that run is bound to. The settled `manifest.json`
/// carries the same object.
pub const RUN_CONFIGURATION_FILE: &str = "run-configuration.json";

/// Wire version of the frozen run manifest.
///
/// 1 -> 2 in Pass 7.5g: the manifest gained `run_configuration`, the run
/// policy the run was bound to. A reader that does not understand the
/// policy a run was bound to fails closed on the version rather than
/// reading the rest of the manifest as if no policy had been bound — and a
/// reader of a *later* manifest fails closed for the mirror-image reason,
/// since it cannot know what a later version moved or redefined.
pub const MANIFEST_FORMAT_VERSION: u64 = 2;

/// What binding a run configuration did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunConfigurationBinding {
    /// This declaration was the run's first, and was persisted.
    Bound,
    /// The run was already bound to exactly this configuration.
    Unchanged,
}

/// Read one run's bound configuration back from its run root.
///
/// This is the manifest-driven reopen path: it prefers the settled
/// `manifest.json`'s own `run_configuration` and falls back to the eagerly
/// written [`RUN_CONFIGURATION_FILE`] for a run that has not settled.
/// `Ok(None)` means the run declared no configuration, which is different
/// from a run whose record could not be read.
///
/// The manifest's own `format_version` is checked first and must be exactly
/// [`MANIFEST_FORMAT_VERSION`]. A version this host does not understand —
/// an older one that predates `run_configuration`, a newer one that may
/// have moved or redefined it, or none at all — is refused rather than read
/// for whatever member happens to be there: a v1 manifest carries no
/// `run_configuration` member, so reading it leniently would answer
/// "this run declared no policy" for a run whose policy simply had nowhere
/// to be written.
pub fn read_run_configuration(run_root: &Path) -> Result<Option<serde_json::Value>, FailureReport> {
    let manifest_path = run_root.join("manifest.json");
    if manifest_path.is_file() {
        let bytes = fs::read(&manifest_path).map_err(|error| {
            FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("read {}: {error}", manifest_path.display()),
            )
        })?;
        let manifest: serde_json::Value = serde_json::from_slice(&bytes).map_err(|error| {
            FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("parse {}: {error}", manifest_path.display()),
            )
        })?;
        let format_version = manifest
            .get("format_version")
            .and_then(|value| value.as_u64());
        if format_version != Some(MANIFEST_FORMAT_VERSION) {
            let found = match manifest.get("format_version") {
                None => "no format_version".to_string(),
                Some(value) => format!("format_version {value}"),
            };
            return Err(FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!(
                    "{} carries {found}, not {MANIFEST_FORMAT_VERSION}; this host cannot read \
                     the run policy out of it",
                    manifest_path.display()
                ),
            ));
        }
        return Ok(match manifest.get("run_configuration") {
            None | Some(serde_json::Value::Null) => None,
            Some(record) => Some(record.clone()),
        });
    }
    let record_path = run_root.join(RUN_CONFIGURATION_FILE);
    if !record_path.is_file() {
        return Ok(None);
    }
    let bytes = fs::read(&record_path).map_err(|error| {
        FailureReport::artifact(
            FailureKind::ManifestFailure,
            FailureScope::RunGlobal,
            format!("read {}: {error}", record_path.display()),
        )
    })?;
    serde_json::from_slice(&bytes).map(Some).map_err(|error| {
        FailureReport::artifact(
            FailureKind::ManifestFailure,
            FailureScope::RunGlobal,
            format!("parse {}: {error}", record_path.display()),
        )
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HistoryMode {
    Disabled,
    BestEffort,
    Strict,
}

#[derive(Clone, Debug)]
pub struct ArtifactStoreConfig {
    root: PathBuf,
    log_maintenance_history: bool,
    fail_on_history_log_error: bool,
    history_queue_capacity: usize,
    payload_budget_bytes: Option<u64>,
    payload_file_budget: Option<u64>,
    retention: Retention,
}

impl ArtifactStoreConfig {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self {
            root: root.into(),
            log_maintenance_history: false,
            fail_on_history_log_error: false,
            history_queue_capacity: DEFAULT_HISTORY_QUEUE_CAPACITY,
            payload_budget_bytes: None,
            payload_file_budget: None,
            retention: Retention::All,
        }
    }

    /// Choose which payloads survive the run.
    pub fn retention(mut self, retention: Retention) -> Self {
        self.retention = retention;
        self
    }

    /// Cap the total bytes of required payloads one run may publish.
    ///
    /// A run that exceeds its budget fails with a `PublicationFailure`
    /// instead of consuming the volume it is writing to. `None` keeps the
    /// historical unbounded behavior.
    pub fn payload_budget(mut self, bytes: Option<u64>) -> Self {
        self.payload_budget_bytes = bytes;
        self
    }

    /// Cap the number of payload files one run may create on disk.
    ///
    /// File *count* is the number bytes cannot stand in for: filesystem
    /// watchers such as a cloud-sync engine track one record per file, so
    /// a flood of small payloads can wedge them where the same bytes in a
    /// few files would not. The counter charges every staged payload file
    /// at creation and never decrements — discarding a payload does not
    /// refund its bookkeeping cost. Exceeding the budget fails with a
    /// `PublicationFailure`; `None` leaves it unbounded.
    pub fn payload_file_budget(mut self, files: Option<u64>) -> Self {
        self.payload_file_budget = files;
        self
    }

    pub fn maintenance_history(mut self, enabled: bool, strict: bool) -> Self {
        self.log_maintenance_history = enabled;
        self.fail_on_history_log_error = strict;
        self
    }

    /// Set the maximum number of optional-history commands awaiting one writer.
    pub fn maintenance_history_queue_capacity(mut self, capacity: usize) -> Self {
        self.history_queue_capacity = capacity;
        self
    }

    fn history_mode(&self) -> HistoryMode {
        match (self.log_maintenance_history, self.fail_on_history_log_error) {
            (false, _) => HistoryMode::Disabled,
            (true, false) => HistoryMode::BestEffort,
            (true, true) => HistoryMode::Strict,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScopeTag {
    Root,
    Inv,
    Cex,
    Houdini,
    AgentNaive,
    AgentHoudini,
    Attempt(AttemptId),
    Catalog(u64),
    Clause(u64),
    Generation(u64),
    Track(u64),
    VerificationStage(Arc<str>),
    Solver(Arc<str>),
    Named(Arc<str>),
}

impl ScopeTag {
    pub fn solver(name: impl Into<Arc<str>>) -> Self {
        Self::Solver(name.into())
    }

    pub fn named(name: impl Into<Arc<str>>) -> Self {
        Self::Named(name.into())
    }

    pub fn verification_stage(name: impl Into<Arc<str>>) -> Self {
        Self::VerificationStage(name.into())
    }

    fn display(&self) -> String {
        match self {
            Self::Root => "root".to_string(),
            Self::Inv => "inv".to_string(),
            Self::Cex => "cex".to_string(),
            Self::Houdini => "houdini".to_string(),
            Self::AgentNaive => "agent-naive".to_string(),
            Self::AgentHoudini => "agent-houdini".to_string(),
            Self::Attempt(id) => format!("entailment-attempt:{}", id.get()),
            Self::Catalog(id) => format!("catalog:{id}"),
            Self::Clause(id) => format!("clause:{id}"),
            Self::Generation(id) => format!("generation:{id}"),
            Self::Track(id) => format!("track:{id}"),
            Self::VerificationStage(name) => format!("stage:{name}"),
            Self::Solver(name) => format!("solver:{name}"),
            Self::Named(name) => name.to_string(),
        }
    }
}

#[derive(Debug)]
struct ScopeNode {
    parent: Option<Arc<ScopeNode>>,
    tag: ScopeTag,
}

impl ScopeNode {
    fn path(&self) -> Vec<String> {
        let mut reversed = Vec::new();
        let mut cursor = Some(self);
        while let Some(node) = cursor {
            reversed.push(node.tag.display());
            cursor = node.parent.as_deref();
        }
        reversed.reverse();
        reversed
    }

    fn tags(&self) -> Vec<ScopeTag> {
        let mut reversed = Vec::new();
        let mut cursor = Some(self);
        while let Some(node) = cursor {
            reversed.push(node.tag.clone());
            cursor = node.parent.as_deref();
        }
        reversed.reverse();
        reversed
    }
}

// ------------------------------------------------------------
// Resolved Artifacts And Diagnostics
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct ResolvedArtifact {
    path: PathBuf,
    kind: ArtifactKind,
    byte_len: u64,
    scope: Vec<String>,
}

impl ResolvedArtifact {
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn kind(&self) -> ArtifactKind {
        self.kind
    }

    pub fn byte_len(&self) -> u64 {
        self.byte_len
    }

    pub fn scope(&self) -> &[String] {
        &self.scope
    }
}

#[derive(Clone, Debug)]
pub struct ArtifactBackendDiagnostics {
    pub backend_id: BackendId,
    pub history_mode: HistoryMode,
    pub history_sink_initialized: bool,
    pub history_records_constructed: u64,
    pub history_path_exists: bool,
    pub history_queue_capacity: usize,
    pub history_queue_depth: usize,
    pub history_queue_high_water: usize,
    pub history_records_written: u64,
    pub history_worker_state: HistoryWorkerState,
    pub required_payloads_published: u64,
    pub required_payload_files_created: u64,
    pub ready_query_artifacts: usize,
    pub in_flight_query_payload_bytes: usize,
    pub active_publications: usize,
    pub settled: bool,
    pub settlement_failed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HistoryWorkerState {
    Disabled,
    Dormant,
    Running,
    Failed,
    Stopped,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MaintenanceHistoryCursor(u64);

impl MaintenanceHistoryCursor {
    pub fn start() -> Self {
        Self(0)
    }

    pub fn get(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Debug)]
pub struct MaintenanceHistoryPage {
    pub records: Vec<serde_json::Value>,
    pub next_cursor: Option<MaintenanceHistoryCursor>,
}

// ------------------------------------------------------------
// Shared Artifact Store Handle
// ------------------------------------------------------------

#[derive(Clone)]
pub struct ArtifactStore {
    backend: Arc<Backend>,
    scope: Arc<ScopeNode>,
}

impl fmt::Debug for ArtifactStore {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ArtifactStore")
            .field("backend_id", &self.backend.id)
            .field("scope", &self.scope.path())
            .finish()
    }
}

impl ArtifactStore {
    pub fn backend_id(&self) -> BackendId {
        self.backend.id
    }

    /// Create an O(1)-sized child view with immutable provenance.
    pub fn scoped(&self, tag: ScopeTag) -> Self {
        Self {
            backend: Arc::clone(&self.backend),
            scope: Arc::new(ScopeNode {
                parent: Some(Arc::clone(&self.scope)),
                tag,
            }),
        }
    }

    /// Allocate a run-unique attempt identity, independent of history logging.
    pub fn next_attempt_id(&self) -> Result<AttemptId, FailureReport> {
        if self.backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "cannot allocate an attempt after artifact settlement begins",
            ));
        }
        let attempt = self
            .backend
            .next_attempt_id
            .allocate()
            .map(AttemptId)
            .ok_or_else(|| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "attempt identity space exhausted",
                )
            })?;
        if self.backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact backend began settlement during attempt allocation",
            ));
        }
        Ok(attempt)
    }

    /// Publish one complete required payload exactly once.
    pub fn publish(
        &self,
        kind: ArtifactKind,
        payload: Box<[u8]>,
    ) -> Result<ArtifactRef, FailureReport> {
        self.publish_bytes(kind, &payload)
    }

    /// Build and publish one required payload on the same retained worker.
    ///
    /// The builder can perform CPU-heavy serialization without occupying an
    /// async executor thread or materializing its payload before admission.
    pub(crate) async fn publish_required_deferred_async<F>(
        &self,
        kind: ArtifactKind,
        build: F,
    ) -> Result<ArtifactRef, FailureReport>
    where
        F: FnOnce() -> Result<Arc<[u8]>, FailureReport> + Send + 'static,
    {
        let store = self.clone();
        let registration = self.register_owned_work()?;
        tokio::task::spawn_blocking(move || {
            let _completion = OwnedWorkCompletion::new(registration);
            let payload = build()?;
            store.publish_bytes(kind, &payload)
        })
        .await
        .map_err(|error| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                format!("required-artifact publication worker failed: {error}"),
            )
        })?
    }

    /// Publish several payloads of one kind as a single staged set.
    ///
    /// Every payload is written into staging before any of them is promoted,
    /// so a byte-budget, file-budget or staging refusal anywhere in the set
    /// promotes nothing: the refusals that actually bound a recording are all
    /// or nothing. Promotion is still a sequence of atomic renames, so a
    /// failure there reports the references it had already promoted rather
    /// than leaving a caller to guess at a prefix.
    pub fn publish_set(
        &self,
        kind: ArtifactKind,
        payloads: &[Vec<u8>],
    ) -> Result<Vec<ArtifactRef>, PublishSetFailure> {
        let mut published = Vec::with_capacity(payloads.len());
        if let Some(report) = self.backend.resource_failure() {
            return Err(PublishSetFailure { published, report });
        }
        if self.backend.retention == Retention::CertificateOnly
            && kind.certificate_only_record_only()
        {
            for payload in payloads {
                match self.record_without_payload(kind, payload.len() as u64) {
                    Ok(reference) => published.push(reference),
                    Err(report) => return Err(PublishSetFailure { published, report }),
                }
            }
            return Ok(published);
        }
        let mut staged = Vec::with_capacity(payloads.len());
        for payload in payloads {
            match self.stage_payload(payload) {
                Ok(entry) => staged.push(entry),
                Err(report) => return Err(PublishSetFailure { published, report }),
            }
        }
        for entry in staged {
            match entry.commit(kind) {
                Ok(reference) => published.push(reference),
                Err(report) => return Err(PublishSetFailure { published, report }),
            }
        }
        Ok(published)
    }

    fn publish_bytes(
        &self,
        kind: ArtifactKind,
        payload: &[u8],
    ) -> Result<ArtifactRef, FailureReport> {
        if let Some(report) = self.backend.resource_failure() {
            return Err(report);
        }
        if self.backend.retention == Retention::CertificateOnly
            && kind.certificate_only_record_only()
        {
            return self.record_without_payload(kind, payload.len() as u64);
        }
        self.stage_payload(payload)?.commit(kind)
    }

    /// Write one complete payload into staging, leaving it unpromoted.
    fn stage_payload(&self, payload: &[u8]) -> Result<StagedArtifact, FailureReport> {
        if let Some(report) = self.backend.resource_failure() {
            return Err(report);
        }
        let (staged, mut writer) = self.begin_staged_payload()?;
        writer.write_all(payload).map_err(|error| {
            self.backend.resource_failure().unwrap_or_else(|| {
                FailureReport::artifact(
                    FailureKind::PublicationFailure,
                    FailureScope::LaneLocal,
                    format!("write staged required artifact: {error}"),
                )
            })
        })?;
        writer.flush().map_err(|error| {
            FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::LaneLocal,
                format!("flush staged required artifact: {error}"),
            )
        })?;
        drop(writer);
        Ok(staged)
    }

    /// Publish a manifest record whose payload never touches disk.
    ///
    /// Certificate-only retention routes pure-provenance kinds here: the
    /// index gains a normal record — same identity space, `retained: false`
    /// from birth — so reports can still say what existed, while the
    /// filesystem sees nothing. Byte and file budgets are deliberately not
    /// charged; they protect the volume, and no volume is consumed.
    fn record_without_payload(
        &self,
        kind: ArtifactKind,
        byte_len: u64,
    ) -> Result<ArtifactRef, FailureReport> {
        let backend = &self.backend;
        if backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "artifact backend is not open",
            ));
        }
        // Mirror StagedArtifact::begin: join the active set, then recheck,
        // so settlement cannot slip between the check and the record insert.
        backend.active_publications.fetch_add(1, Ordering::AcqRel);
        if backend.state.load(Ordering::Acquire) != OPEN {
            backend.active_publications.fetch_sub(1, Ordering::AcqRel);
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "artifact backend is settling",
            ));
        }
        let result = (|| {
            let id = backend.next_artifact_id.allocate().ok_or_else(|| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "artifact identity space exhausted",
                )
            })?;
            let artifact = ArtifactId(id);
            let mut records = backend.records.lock().map_err(|_| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "artifact index lock was poisoned",
                )
            })?;
            records.insert(
                artifact,
                ArtifactRecord {
                    id,
                    kind,
                    relative_path: format!("required/artifact-{id:020}.bin"),
                    byte_len,
                    scope: self.scope.path(),
                    retained: false,
                },
            );
            backend
                .required_payloads_published
                .fetch_add(1, Ordering::Relaxed);
            Ok(ArtifactRef {
                backend: backend.id,
                artifact,
                kind,
            })
        })();
        backend.active_publications.fetch_sub(1, Ordering::AcqRel);
        result
    }

    /// Publish or reuse one immutable query selected by its content identity.
    ///
    /// The backend coalesces concurrent misses. The shared index lock is held
    /// only while selecting a publication slot, never while writing files.
    /// Ready entries retain only a domain-separated SHA-256 digest, byte
    /// length, and reference. This operational identity assumes SHA-256
    /// collision resistance; the referenced durable payload remains exact.
    /// A failed publication exposes no reference and removes its slot so a
    /// later caller can retry the same content identity.
    pub(crate) async fn publish_query(
        &self,
        content_identity: Arc<str>,
        payload: Arc<[u8]>,
    ) -> Result<ArtifactRef, FailureReport> {
        let fingerprint = QueryFingerprint {
            digest: content_identity,
            byte_len: u64::try_from(payload.len()).map_err(|_| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "query payload length exceeds the artifact identity range",
                )
            })?,
        };
        match self.backend.select_query(fingerprint, payload)? {
            QuerySelection::Reuse(reference) => Ok(reference),
            QuerySelection::Wait(publication) => publication.wait().await,
            QuerySelection::Publish(publication) => {
                let query_store = self.canonical_query_store();
                let guard = self.begin_query_publication_work(Arc::clone(&publication))?;
                let worker = tokio::task::spawn_blocking(move || {
                    run_query_publication_worker(query_store, publication, guard)
                });
                // A dropped initiating caller does not own publication. The
                // retained blocking closure above publishes the terminal cache
                // state and discharges backend work independently.
                worker.await.map_err(|error| {
                    FailureReport::artifact(
                        FailureKind::InfrastructureFailure,
                        FailureScope::RunGlobal,
                        format!("query publication worker failed: {error}"),
                    )
                })?
            }
        }
    }

    fn begin_query_publication_work(
        &self,
        publication: Arc<QueryPublication>,
    ) -> Result<QueryPublicationWorkGuard, FailureReport> {
        match self.register_owned_work() {
            Ok(registration) => Ok(QueryPublicationWorkGuard {
                backend: Arc::clone(&self.backend),
                publication,
                registration: Some(registration),
                finished: false,
            }),
            Err(report) => {
                let result = Err(report.clone());
                self.backend
                    .finish_query_publication(&publication, &result)
                    .and(Err(report))
            }
        }
    }

    fn canonical_query_store(&self) -> Self {
        let root = Arc::new(ScopeNode {
            parent: None,
            tag: ScopeTag::Root,
        });
        Self {
            backend: Arc::clone(&self.backend),
            scope: Arc::new(ScopeNode {
                parent: Some(root),
                tag: ScopeTag::named("query-store"),
            }),
        }
    }

    /// Reserve a backend-owned staging file for bounded streaming capture.
    pub(crate) fn begin_staged_payload(
        &self,
    ) -> Result<(StagedArtifact, BudgetedArtifactWriter), FailureReport> {
        StagedArtifact::begin(Arc::clone(&self.backend), self.scope.path())
    }

    pub(crate) fn resource_failure(&self) -> Option<FailureReport> {
        self.backend.resource_failure()
    }

    /// Resolve a typed reference at the filesystem presentation boundary.
    /// Whether this reference's payload is still on disk.
    pub fn is_retained(&self, reference: ArtifactRef) -> bool {
        self.backend
            .records
            .lock()
            .ok()
            .and_then(|records| records.get(&reference.artifact).map(|r| r.retained))
            .unwrap_or(false)
    }

    /// Which payloads this run keeps.
    pub fn retention(&self) -> Retention {
        self.backend.retention
    }

    /// The run root this store writes under.
    pub fn run_root(&self) -> &Path {
        &self.backend.run_root
    }

    /// Bind one run policy record to this run's identity.
    ///
    /// The first declaration persists the record — atomically, into the run
    /// root, so a later reopen can read it back without waiting for
    /// settlement — and every later declaration is compared with it. A
    /// disagreement is configuration drift and fails the run closed rather
    /// than letting later work proceed under a policy the earlier work was
    /// not done under. The record is opaque here: this store persists and
    /// compares it and never interprets it.
    pub fn bind_run_configuration(
        &self,
        record: serde_json::Value,
    ) -> Result<RunConfigurationBinding, FailureReport> {
        if self.backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "cannot bind a run configuration after artifact settlement begins",
            ));
        }
        let mut bound = self.backend.run_configuration.lock().map_err(|_| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "run-configuration lock was poisoned",
            )
        })?;
        if let Some(existing) = bound.as_ref() {
            if existing == &record {
                return Ok(RunConfigurationBinding::Unchanged);
            }
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "the run configuration bound to this artifact store disagrees with the one \
                 declared now",
            ));
        }
        let bytes = serde_json::to_vec_pretty(&record).map_err(|error| {
            FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("serialize the run configuration: {error}"),
            )
        })?;
        let staging = self
            .backend
            .run_root
            .join(format!("{RUN_CONFIGURATION_FILE}.part"));
        let destination = self.backend.run_root.join(RUN_CONFIGURATION_FILE);
        fs::write(&staging, bytes).map_err(|error| {
            let _ = fs::remove_file(&staging);
            FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("write the run configuration: {error}"),
            )
        })?;
        fs::rename(&staging, &destination).map_err(|error| {
            let _ = fs::remove_file(&staging);
            FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("freeze the run configuration: {error}"),
            )
        })?;
        *bound = Some(record);
        Ok(RunConfigurationBinding::Bound)
    }

    /// The run policy bound to this run's identity, if one has been.
    pub fn run_configuration(&self) -> Option<serde_json::Value> {
        self.backend
            .run_configuration
            .lock()
            .ok()
            .and_then(|bound| bound.clone())
    }

    /// Drop a payload whose only consumer has finished with it.
    ///
    /// A no-op under `Retention::All`. Otherwise the file is removed while
    /// its index record survives with `retained = false`, so reports can
    /// still say what existed rather than naming a path that is gone.
    /// Discarding as each job completes is what bounds peak disk use.
    pub fn discard(&self, reference: ArtifactRef) -> Result<(), FailureReport> {
        if self.backend.retention == Retention::All {
            return Ok(());
        }
        let mut records = self.backend.records.lock().map_err(|_| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact index lock was poisoned",
            )
        })?;
        let Some(record) = records.get_mut(&reference.artifact) else {
            return Ok(());
        };
        if !record.retained {
            return Ok(());
        }
        let path = self.backend.run_root.join(&record.relative_path);
        match fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(FailureReport::artifact(
                    FailureKind::PublicationFailure,
                    FailureScope::LaneLocal,
                    format!("discard required artifact: {error}"),
                ));
            }
        }
        record.retained = false;
        Ok(())
    }

    pub fn resolve(&self, reference: ArtifactRef) -> Result<ResolvedArtifact, FailureReport> {
        self.backend.resolve(reference)
    }

    pub fn diagnostics(&self) -> ArtifactBackendDiagnostics {
        self.backend.diagnostics()
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.backend.task
    }

    /// Append one already-serialized optional maintenance-history event.
    ///
    /// This compatibility path decodes on the caller. New maintenance code
    /// should use `append_maintenance_history_value`, which moves a structured
    /// value directly to the writer. Strict compatibility calls also wait for
    /// a boundary acknowledgement so their historical failure timing remains
    /// unchanged.
    pub(crate) fn append_maintenance_history(&self, record: &[u8]) -> Result<(), FailureReport> {
        if self.backend.history.is_none() {
            return Ok(());
        }
        let record = serde_json::from_slice(record).map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("decode maintenance-history compatibility record: {error}"),
            )
        })?;
        self.append_maintenance_history_value(record, &[])?;
        if self.backend.history_mode() == HistoryMode::Strict {
            self.backend.settle_history_boundary()?;
        }
        Ok(())
    }

    /// Nonblocking optional-history submission for maintenance hot paths.
    ///
    /// Serialization and filesystem work occur on the one backend writer.
    /// `clause_ids` selects persistent per-clause index entries and is
    /// deduplicated by that writer.
    pub fn append_maintenance_history_value(
        &self,
        record: serde_json::Value,
        clause_ids: &[u64],
    ) -> Result<(), FailureReport> {
        if self.backend.history.is_none() {
            return Ok(());
        }
        self.backend.append_history(
            self.scope.path(),
            HistoryRecordPayload::Value {
                record,
                clause_ids: clause_ids.to_vec(),
            },
        )
    }

    /// Defer construction of an optional-history record and its clause index.
    ///
    /// The bounded writer invokes `build`. Callers can therefore move sorting,
    /// snapshot flattening, and JSON construction entirely off async lanes.
    /// Submit a deferred history record without blocking an async lane.
    ///
    /// Backend-owned work retains strict backpressure even if the initiating
    /// future is dropped. Best-effort mode retains its nonblocking policy.
    pub(crate) async fn append_maintenance_history_deferred_async<F>(
        &self,
        build: F,
    ) -> Result<(), FailureReport>
    where
        F: FnOnce() -> Result<(serde_json::Value, Vec<u64>), FailureReport> + Send + 'static,
    {
        if self.backend.history.is_none() {
            return Ok(());
        }
        let store = self.clone();
        let scope = self.scope.path();
        let registration = self.register_owned_work()?;
        tokio::task::spawn_blocking(move || {
            let guard = OwnedWorkCompletion::new(registration);
            let result = store
                .backend
                .append_history(scope, HistoryRecordPayload::Deferred(Box::new(build)));
            drop(guard);
            result
        })
        .await
        .map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::RunGlobal,
                format!("maintenance-history submission worker failed: {error}"),
            )
        })?
    }

    /// Flush the optional maintenance-history stream at a semantic boundary.
    pub(crate) fn settle_maintenance_history(&self) -> Result<(), FailureReport> {
        self.backend.settle_history_boundary()
    }

    /// Flush history without blocking an async runtime worker on queue I/O.
    pub(crate) async fn settle_maintenance_history_async(&self) -> Result<(), FailureReport> {
        let store = self.clone();
        let registration = self.register_owned_work()?;
        tokio::task::spawn_blocking(move || {
            let guard = OwnedWorkCompletion::new(registration);
            let result = store.backend.settle_history_boundary();
            drop(guard);
            result
        })
        .await
        .map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::RunGlobal,
                format!("maintenance-history settlement worker failed: {error}"),
            )
        })?
    }

    /// Read one bounded page of optional maintenance history for a clause.
    ///
    /// The cursor is a persistent sidecar byte offset, so each page avoids a
    /// scan of unrelated artifacts and earlier pages.
    pub fn query_maintenance_history(
        &self,
        clause_id: u64,
        cursor: MaintenanceHistoryCursor,
        limit: usize,
    ) -> Result<MaintenanceHistoryPage, FailureReport> {
        self.backend
            .query_history(clause_id, cursor, limit.min(MAX_HISTORY_PAGE_SIZE))
    }

    /// Return the immutable structured provenance of this scoped view.
    pub fn scope_tags(&self) -> Vec<ScopeTag> {
        self.scope.tags()
    }

    /// Register runtime work that must be explicitly joined before settlement.
    pub(crate) fn register_owned_work(&self) -> Result<OwnedWorkRegistration, FailureReport> {
        Backend::register_owned_work(Arc::clone(&self.backend), true)
    }

    /// Register a component-lifetime sentinel.
    ///
    /// A failed component cleanup deliberately leaves this registration
    /// active so final settlement fails closed. It is not a detached worker
    /// which the run owner can wait to finish.
    pub(crate) fn register_lifetime_owned_work(
        &self,
    ) -> Result<OwnedWorkRegistration, FailureReport> {
        Backend::register_owned_work(Arc::clone(&self.backend), false)
    }

    /// Wait for detached backend-owned blocking work to discharge.
    ///
    /// This is an observation boundary, not settlement authority. A scoped
    /// store can therefore join work owned by its operation while the unique
    /// backend owner remains outside that operation.
    pub(crate) async fn wait_for_background_work(&self) {
        self.backend.wait_for_background_work().await;
    }
}

// ------------------------------------------------------------
// Exclusive Backend Owner
// ------------------------------------------------------------

/// Unique run authority. It is intentionally neither `Clone` nor `Send`.
///
/// ```compile_fail
/// # fn duplicate(owner: whiel_runner::ArtifactBackendOwner) {
/// let _copy = owner.clone();
/// # }
/// ```
pub struct ArtifactBackendOwner {
    backend: Arc<Backend>,
    _not_send_or_sync: PhantomData<Rc<()>>,
}

impl fmt::Debug for ArtifactBackendOwner {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ArtifactBackendOwner")
            .field("backend_id", &self.backend.id)
            .finish_non_exhaustive()
    }
}

impl ArtifactBackendOwner {
    pub(crate) fn root_store(&self) -> ArtifactStore {
        ArtifactStore {
            backend: Arc::clone(&self.backend),
            scope: Arc::new(ScopeNode {
                parent: None,
                tag: ScopeTag::Root,
            }),
        }
    }

    /// Finalize this backend exactly once after all owned work has joined.
    pub fn settle(self) -> Result<(), FailureReport> {
        self.backend.settle(&[])
    }

    /// Finalize while naming the artifact references the terminal result
    /// carries.
    ///
    /// Under `Retention::All` the names are recorded intent only. Under
    /// `Retention::CertificateOnly` settlement removes every retained
    /// payload that is neither named here nor durable by kind, so a
    /// non-detailed run ends holding only what backs its result. References
    /// from another backend are ignored rather than rejected.
    pub fn settle_retaining(self, keep: &[ArtifactRef]) -> Result<(), FailureReport> {
        self.backend.settle(keep)
    }
}

/// Create one run backend, its exclusive owner, and its root handle.
pub fn new_artifact_store(
    task: &SynthesisTask,
    config: ArtifactStoreConfig,
) -> Result<(ArtifactBackendOwner, ArtifactStore), FailureReport> {
    let backend = Arc::new(Backend::new(task.identity().clone(), config)?);
    let owner = ArtifactBackendOwner {
        backend,
        _not_send_or_sync: PhantomData,
    };
    let store = owner.root_store();
    Ok((owner, store))
}

// ------------------------------------------------------------
// Backend State And Settlement
// ------------------------------------------------------------

#[derive(Clone, Debug, Serialize)]
struct ArtifactRecord {
    id: u64,
    kind: ArtifactKind,
    relative_path: String,
    byte_len: u64,
    scope: Vec<String>,
    /// False once the payload has been discarded under
    /// `Retention::CertificateOnly`. The record survives so run reports can
    /// still name what existed instead of citing a path that is now absent.
    retained: bool,
}

#[derive(Debug)]
struct HistoryPolicy {
    mode: HistoryMode,
    queue_capacity: usize,
    sink: Mutex<HistorySink>,
    shared: Arc<HistoryShared>,
    records_constructed: AtomicU64,
}

#[derive(Debug)]
struct HistorySink {
    runtime: Option<HistoryRuntime>,
    disabled: bool,
}

#[derive(Debug)]
struct HistoryRuntime {
    sender: SyncSender<HistoryCommand>,
    join: Option<JoinHandle<()>>,
}

#[derive(Debug)]
struct HistoryShared {
    worker_state: AtomicU8,
    queue_state: Mutex<HistoryQueueState>,
    queue_high_water: AtomicUsize,
    queue_available: Condvar,
    records_written: AtomicU64,
    failure: Mutex<Option<FailureReport>>,
    #[cfg(test)]
    fault_injection: Mutex<HistoryFaultInjection>,
    #[cfg(test)]
    barrier_commands_sent: AtomicUsize,
}

#[derive(Debug, Default)]
struct HistoryQueueState {
    depth: usize,
    failed: bool,
}

#[cfg(test)]
#[derive(Debug, Default)]
struct HistoryFaultInjection {
    fail_main_after_prefix: bool,
    fail_index_after: Option<usize>,
    barrier_pause: Option<HistoryBarrierPause>,
}

#[cfg(test)]
#[derive(Debug)]
struct HistoryBarrierPause {
    entered: mpsc::Sender<()>,
    release: mpsc::Receiver<()>,
}

#[derive(Debug)]
enum HistoryCommand {
    Event(HistoryEvent),
    Barrier(mpsc::Sender<Result<(), FailureReport>>),
    Shutdown(mpsc::Sender<Result<(), FailureReport>>),
}

#[derive(Debug)]
struct HistoryEvent {
    scope: Vec<String>,
    record: HistoryRecordPayload,
}

type DeferredHistoryBuilder =
    Box<dyn FnOnce() -> Result<(serde_json::Value, Vec<u64>), FailureReport> + Send>;

enum HistoryRecordPayload {
    Value {
        record: serde_json::Value,
        clause_ids: Vec<u64>,
    },
    Deferred(DeferredHistoryBuilder),
}

impl fmt::Debug for HistoryRecordPayload {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value { .. } => formatter.write_str("Value(..)"),
            Self::Deferred(_) => formatter.write_str("Deferred(..)"),
        }
    }
}

impl HistoryRecordPayload {
    fn materialize(self) -> Result<(serde_json::Value, Vec<u64>), FailureReport> {
        match self {
            Self::Value { record, clause_ids } => Ok((record, clause_ids)),
            Self::Deferred(build) => build(),
        }
    }
}

#[derive(Clone, Debug)]
enum QueryPublicationState {
    Publishing,
    Ready(ArtifactRef),
    Failed(FailureReport),
}

#[derive(Debug)]
struct QueryPublication {
    fingerprint: QueryFingerprint,
    payload: Arc<[u8]>,
    state: watch::Sender<QueryPublicationState>,
}

impl QueryPublication {
    fn new(fingerprint: QueryFingerprint, payload: Arc<[u8]>) -> Self {
        let (state, _) = watch::channel(QueryPublicationState::Publishing);
        Self {
            fingerprint,
            payload,
            state,
        }
    }

    fn finish(&self, state: QueryPublicationState) {
        self.state.send_replace(state);
    }

    async fn wait(&self) -> Result<ArtifactRef, FailureReport> {
        let mut state = self.state.subscribe();
        loop {
            let observed = state.borrow_and_update().clone();
            match observed {
                QueryPublicationState::Publishing => {}
                QueryPublicationState::Ready(reference) => return Ok(reference),
                QueryPublicationState::Failed(report) => return Err(report),
            }
            state.changed().await.map_err(|_| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "query publisher ended without a result",
                )
            })?;
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct QueryFingerprint {
    digest: Arc<str>,
    byte_len: u64,
}

#[derive(Debug)]
enum QueryIndexEntry {
    Publishing(Arc<QueryPublication>),
    Ready(ArtifactRef),
}

enum QuerySelection {
    Reuse(ArtifactRef),
    Wait(Arc<QueryPublication>),
    Publish(Arc<QueryPublication>),
}

#[derive(Debug)]
struct Backend {
    id: BackendId,
    task: TaskIdentity,
    run_root: PathBuf,
    required_root: PathBuf,
    staging_root: PathBuf,
    state: AtomicU8,
    active_publications: AtomicUsize,
    active_owned_work: AtomicUsize,
    active_background_work: AtomicUsize,
    owned_work_changed: Notify,
    next_artifact_id: IdAllocator,
    next_attempt_id: IdAllocator,
    records: Mutex<BTreeMap<ArtifactId, ArtifactRecord>>,
    query_publications: Mutex<HashMap<QueryFingerprint, QueryIndexEntry>>,
    history: Option<HistoryPolicy>,
    required_payloads_published: AtomicU64,
    required_bytes_published: AtomicU64,
    payload_files_created: AtomicU64,
    payload_budget_bytes: Option<u64>,
    payload_file_budget: Option<u64>,
    budget_failure: Mutex<Option<FailureReport>>,
    retention: Retention,
    /// The run policy this run identity is bound to, once it has been
    /// declared. Opaque here: the artifact store persists and compares it
    /// and never interprets it.
    run_configuration: Mutex<Option<serde_json::Value>>,
}

impl Backend {
    fn new(task: TaskIdentity, config: ArtifactStoreConfig) -> Result<Self, FailureReport> {
        if config.history_mode() != HistoryMode::Disabled && config.history_queue_capacity == 0 {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "maintenance-history queue capacity must be positive",
            ));
        }
        let (id, run_root) = reserve_run_root(&config.root)?;
        let required_root = run_root.join("required");
        let staging_root = run_root.join("staging");
        if let Err(error) = fs::create_dir(&required_root) {
            let _ = fs::remove_dir(&run_root);
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                format!("create required artifact directory: {error}"),
            ));
        }
        if let Err(error) = fs::create_dir(&staging_root) {
            let _ = fs::remove_dir_all(&run_root);
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                format!("create artifact staging directory: {error}"),
            ));
        }
        let history = match config.history_mode() {
            HistoryMode::Disabled => None,
            mode => Some(HistoryPolicy {
                mode,
                queue_capacity: config.history_queue_capacity,
                sink: Mutex::new(HistorySink {
                    runtime: None,
                    disabled: false,
                }),
                shared: Arc::new(HistoryShared {
                    worker_state: AtomicU8::new(HISTORY_DORMANT),
                    queue_state: Mutex::new(HistoryQueueState::default()),
                    queue_high_water: AtomicUsize::new(0),
                    queue_available: Condvar::new(),
                    records_written: AtomicU64::new(0),
                    failure: Mutex::new(None),
                    #[cfg(test)]
                    fault_injection: Mutex::new(HistoryFaultInjection::default()),
                    #[cfg(test)]
                    barrier_commands_sent: AtomicUsize::new(0),
                }),
                records_constructed: AtomicU64::new(0),
            }),
        };
        Ok(Self {
            id,
            task,
            run_root,
            required_root,
            staging_root,
            state: AtomicU8::new(OPEN),
            active_publications: AtomicUsize::new(0),
            active_owned_work: AtomicUsize::new(0),
            active_background_work: AtomicUsize::new(0),
            owned_work_changed: Notify::new(),
            next_artifact_id: IdAllocator::new(0),
            next_attempt_id: IdAllocator::new(0),
            records: Mutex::new(BTreeMap::new()),
            query_publications: Mutex::new(HashMap::new()),
            history,
            required_payloads_published: AtomicU64::new(0),
            required_bytes_published: AtomicU64::new(0),
            payload_files_created: AtomicU64::new(0),
            payload_budget_bytes: config.payload_budget_bytes,
            payload_file_budget: config.payload_file_budget,
            budget_failure: Mutex::new(None),
            retention: config.retention,
            run_configuration: Mutex::new(None),
        })
    }

    // One lock linearizes both allowances and their terminal failure. Charges
    // precede writes/creates and are never refunded, including failed I/O.
    fn charge_budget(
        &self,
        counter: &AtomicU64,
        amount: u64,
        maximum: Option<u64>,
        unit: &str,
    ) -> Result<(), FailureReport> {
        let mut failure = self
            .budget_failure
            .lock()
            .unwrap_or_else(|p| p.into_inner());
        if let Some(report) = &*failure {
            return Err(report.clone());
        }
        let next = counter.load(Ordering::Relaxed).checked_add(amount);
        if next.is_none_or(|n| maximum.is_some_and(|maximum| n > maximum)) {
            let report = FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                format!(
                    "resource_exhausted: artifact {unit} allowance {:?}; input stopped before the next write or create",
                    maximum
                ),
            );
            *failure = Some(report.clone());
            return Err(report);
        }
        counter.store(next.unwrap(), Ordering::Relaxed);
        Ok(())
    }
    fn charge_payload_budget(&self, bytes: u64) -> Result<(), FailureReport> {
        self.charge_budget(
            &self.required_bytes_published,
            bytes,
            self.payload_budget_bytes,
            "bytes",
        )
    }
    fn charge_payload_file_budget(&self) -> Result<(), FailureReport> {
        self.charge_budget(
            &self.payload_files_created,
            1,
            self.payload_file_budget,
            "file creations",
        )
    }
    fn resource_failure(&self) -> Option<FailureReport> {
        self.budget_failure
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .clone()
    }

    fn resolve(&self, reference: ArtifactRef) -> Result<ResolvedArtifact, FailureReport> {
        if reference.backend != self.id {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact reference belongs to a different run backend",
            ));
        }
        let record = self
            .records
            .lock()
            .map_err(|_| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "artifact index lock was poisoned",
                )
            })?
            .get(&reference.artifact)
            .cloned()
            .ok_or_else(|| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "artifact reference is not published",
                )
            })?;
        if record.kind != reference.kind {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact reference kind does not match its record",
            ));
        }
        Ok(ResolvedArtifact {
            path: self.run_root.join(record.relative_path),
            kind: record.kind,
            byte_len: record.byte_len,
            scope: record.scope,
        })
    }

    fn select_query(
        &self,
        fingerprint: QueryFingerprint,
        payload: Arc<[u8]>,
    ) -> Result<QuerySelection, FailureReport> {
        if self.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "cannot publish a query after artifact settlement begins",
            ));
        }
        let mut publications = self.query_publications.lock().map_err(|_| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "query-publication index lock was poisoned",
            )
        })?;
        if let Some(entry) = publications.get(&fingerprint) {
            return Ok(match entry {
                QueryIndexEntry::Publishing(publication) => {
                    QuerySelection::Wait(Arc::clone(publication))
                }
                QueryIndexEntry::Ready(reference) => QuerySelection::Reuse(*reference),
            });
        }
        let publication = Arc::new(QueryPublication::new(fingerprint.clone(), payload));
        publications.insert(
            fingerprint,
            QueryIndexEntry::Publishing(Arc::clone(&publication)),
        );
        Ok(QuerySelection::Publish(publication))
    }

    fn finish_query_publication(
        &self,
        publication: &Arc<QueryPublication>,
        result: &Result<ArtifactRef, FailureReport>,
    ) -> Result<(), FailureReport> {
        let cleanup = self.query_publications.lock().map_err(|_| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "query-publication index lock was poisoned after publication finished",
            )
        });
        let mut publications = match cleanup {
            Ok(publications) => publications,
            Err(cleanup_report) => {
                publication.finish(QueryPublicationState::Failed(cleanup_report.clone()));
                return Err(cleanup_report);
            }
        };
        let Some(entry) = publications.get_mut(&publication.fingerprint) else {
            let report = FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "completed query publication has no cache bucket",
            );
            publication.finish(QueryPublicationState::Failed(report.clone()));
            return Err(report);
        };
        if !matches!(entry, QueryIndexEntry::Publishing(current) if Arc::ptr_eq(current, publication))
        {
            let report = FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "completed query publication has no in-flight cache entry",
            );
            publication.finish(QueryPublicationState::Failed(report.clone()));
            return Err(report);
        }
        let terminal = match result {
            Ok(reference) => {
                *entry = QueryIndexEntry::Ready(*reference);
                QueryPublicationState::Ready(*reference)
            }
            Err(report) => {
                publications.remove(&publication.fingerprint);
                QueryPublicationState::Failed(report.clone())
            }
        };
        drop(publications);
        publication.finish(terminal);
        Ok(())
    }

    fn settle(&self, keep: &[ArtifactRef]) -> Result<(), FailureReport> {
        self.state
            .compare_exchange(OPEN, SETTLING, Ordering::AcqRel, Ordering::Acquire)
            .map_err(|_| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "artifact backend settlement was attempted more than once",
                )
            })?;
        let result = self.finish_settlement(keep);
        self.state.store(
            if result.is_ok() {
                SETTLED
            } else {
                SETTLEMENT_FAILED
            },
            Ordering::Release,
        );
        result
    }

    fn finish_settlement(&self, keep: &[ArtifactRef]) -> Result<(), FailureReport> {
        if self.active_owned_work.load(Ordering::Acquire) != 0 {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact settlement began before backend-owned work was explicitly joined",
            ));
        }
        if self.active_publications.load(Ordering::Acquire) != 0 {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact settlement began before publishers stopped",
            ));
        }
        // Optional history cannot suppress required artifact preservation.
        // Retain a strict failure, finish the required manifest, then report it
        // only if required settlement itself succeeded.
        let history_result = self.finalize_history();
        if self.staging_root.exists() {
            fs::remove_dir_all(&self.staging_root).map_err(|error| {
                FailureReport::artifact(
                    FailureKind::ManifestFailure,
                    FailureScope::RunGlobal,
                    format!("discard incomplete artifact staging: {error}"),
                )
            })?;
        }
        self.sweep_unreferenced_payloads(keep)?;
        let records: Vec<ArtifactRecord> = self
            .records
            .lock()
            .map_err(|_| {
                FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "artifact index lock was poisoned",
                )
            })?
            .values()
            .cloned()
            .collect();
        let manifest = Manifest {
            format_version: MANIFEST_FORMAT_VERSION,
            backend_id: self.id.to_string(),
            task: ManifestTask {
                canonical_id: self.task.canonical_id(),
                module: self.task.module(),
                namespace: self.task.namespace(),
                source_sha256: self.task.source_digest().as_str(),
                semantic_version: self.task.semantic_version(),
                encoding_version: self.task.encoding_version(),
            },
            run_configuration: self
                .run_configuration
                .lock()
                .map_err(|_| {
                    FailureReport::artifact(
                        FailureKind::InfrastructureFailure,
                        FailureScope::RunGlobal,
                        "run-configuration lock was poisoned",
                    )
                })?
                .clone(),
            artifacts: records,
        };
        let bytes = serde_json::to_vec_pretty(&manifest).map_err(|error| {
            FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("serialize artifact manifest: {error}"),
            )
        })?;
        let staging = self.run_root.join("manifest.json.part");
        let destination = self.run_root.join("manifest.json");
        if let Err(error) = fs::write(&staging, bytes) {
            let _ = fs::remove_file(&staging);
            return Err(FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("write artifact manifest: {error}"),
            ));
        }
        fs::rename(&staging, &destination).map_err(|error| {
            let _ = fs::remove_file(&staging);
            FailureReport::artifact(
                FailureKind::ManifestFailure,
                FailureScope::RunGlobal,
                format!("freeze artifact manifest: {error}"),
            )
        })?;
        history_result
    }

    /// Remove settled payloads the terminal result does not justify.
    ///
    /// Runs only under `Retention::CertificateOnly`, inside settlement,
    /// after publishers have provably stopped — nothing resolves a payload
    /// after this point, so removing files here is safe where removing them
    /// mid-run would not be. Records survive with `retained: false`, and
    /// the manifest is written after this sweep so it reports the truth.
    fn sweep_unreferenced_payloads(&self, keep: &[ArtifactRef]) -> Result<(), FailureReport> {
        if self.retention != Retention::CertificateOnly {
            return Ok(());
        }
        let keep: HashSet<ArtifactId> = keep
            .iter()
            .filter(|reference| reference.backend == self.id)
            .map(|reference| reference.artifact)
            .collect();
        let mut records = self.records.lock().map_err(|_| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact index lock was poisoned",
            )
        })?;
        for (id, record) in records.iter_mut() {
            if !record.retained || record.kind.certificate_only_durable() || keep.contains(id) {
                continue;
            }
            let path = self.run_root.join(&record.relative_path);
            match fs::remove_file(&path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(FailureReport::artifact(
                        FailureKind::ManifestFailure,
                        FailureScope::RunGlobal,
                        format!("sweep unreferenced required artifact: {error}"),
                    ));
                }
            }
            record.retained = false;
        }
        Ok(())
    }

    fn register_owned_work(
        backend: Arc<Self>,
        joinable_background: bool,
    ) -> Result<OwnedWorkRegistration, FailureReport> {
        if backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "cannot register backend-owned work after settlement begins",
            ));
        }
        backend.active_owned_work.fetch_add(1, Ordering::AcqRel);
        if joinable_background {
            backend
                .active_background_work
                .fetch_add(1, Ordering::AcqRel);
        }
        if backend.state.load(Ordering::Acquire) != OPEN {
            backend.active_owned_work.fetch_sub(1, Ordering::AcqRel);
            if joinable_background {
                backend
                    .active_background_work
                    .fetch_sub(1, Ordering::AcqRel);
            }
            backend.owned_work_changed.notify_waiters();
            return Err(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact backend began settlement during owned-work registration",
            ));
        }
        Ok(OwnedWorkRegistration {
            backend,
            discharged: AtomicBool::new(false),
            joinable_background,
        })
    }

    async fn wait_for_background_work(&self) {
        loop {
            let changed = self.owned_work_changed.notified();
            tokio::pin!(changed);
            changed.as_mut().enable();
            if self.active_background_work.load(Ordering::Acquire) == 0 {
                return;
            }
            changed.await;
        }
    }

    fn diagnostics(&self) -> ArtifactBackendDiagnostics {
        let (
            history_mode,
            sink_initialized,
            records_constructed,
            queue_capacity,
            queue_depth,
            queue_high_water,
            records_written,
            worker_state,
        ) = match &self.history {
            Some(history) => {
                let sink_initialized = history
                    .sink
                    .lock()
                    .map(|sink| sink.runtime.is_some())
                    .unwrap_or(false);
                (
                    history.mode,
                    sink_initialized,
                    history.records_constructed.load(Ordering::Relaxed),
                    history.queue_capacity,
                    history
                        .shared
                        .queue_state
                        .lock()
                        .map(|state| state.depth)
                        .unwrap_or(0),
                    history.shared.queue_high_water.load(Ordering::Relaxed),
                    history.shared.records_written.load(Ordering::Relaxed),
                    decode_history_worker_state(
                        history.shared.worker_state.load(Ordering::Acquire),
                    ),
                )
            }
            None => (
                HistoryMode::Disabled,
                false,
                0,
                0,
                0,
                0,
                0,
                HistoryWorkerState::Disabled,
            ),
        };
        let (ready_query_artifacts, in_flight_query_payload_bytes) =
            self.query_publications
                .lock()
                .map(|publications| {
                    publications
                        .values()
                        .fold((0_usize, 0_usize), |(ready, bytes), entry| match entry {
                            QueryIndexEntry::Publishing(publication) => {
                                (ready, bytes.saturating_add(publication.payload.len()))
                            }
                            QueryIndexEntry::Ready(_) => (ready + 1, bytes),
                        })
                })
                .unwrap_or((0_usize, 0_usize));
        ArtifactBackendDiagnostics {
            backend_id: self.id,
            history_mode,
            history_sink_initialized: sink_initialized,
            history_records_constructed: records_constructed,
            history_path_exists: self.run_root.join("history").exists(),
            history_queue_capacity: queue_capacity,
            history_queue_depth: queue_depth,
            history_queue_high_water: queue_high_water,
            history_records_written: records_written,
            history_worker_state: worker_state,
            required_payloads_published: self.required_payloads_published.load(Ordering::Relaxed),
            required_payload_files_created: self.payload_files_created.load(Ordering::Relaxed),
            ready_query_artifacts,
            in_flight_query_payload_bytes,
            active_publications: self.active_publications.load(Ordering::Relaxed),
            settled: self.state.load(Ordering::Acquire) == SETTLED,
            settlement_failed: self.state.load(Ordering::Acquire) == SETTLEMENT_FAILED,
        }
    }

    fn history_mode(&self) -> HistoryMode {
        self.history
            .as_ref()
            .map_or(HistoryMode::Disabled, |history| history.mode)
    }

    fn append_history(
        &self,
        scope: Vec<String>,
        record: HistoryRecordPayload,
    ) -> Result<(), FailureReport> {
        let Some(history) = &self.history else {
            return Ok(());
        };
        // This lock is also the command-enqueue gate. Holding it through queue
        // admission and send prevents a barrier or final shutdown from
        // overtaking an append that already passed the OPEN-state check.
        let mut sink = match history.sink.lock() {
            Ok(sink) => sink,
            Err(poisoned) if history.mode == HistoryMode::BestEffort => {
                let mut sink = poisoned.into_inner();
                sink.disabled = true;
                return Ok(());
            }
            Err(_) => {
                return Err(FailureReport::maintenance_history(
                    FailureScope::RunGlobal,
                    "maintenance-history sink lock was poisoned",
                ));
            }
        };
        if self.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::maintenance_history(
                FailureScope::RunGlobal,
                "cannot append maintenance history after artifact settlement begins",
            ));
        }
        if sink.disabled {
            return Ok(());
        }
        if let Some(report) = retained_history_failure(&history.shared) {
            return handle_known_history_failure(history.mode, &mut sink, report);
        }
        if sink.runtime.is_none() {
            let runtime = match start_history_writer(
                &self.run_root,
                history.queue_capacity,
                Arc::clone(&history.shared),
            ) {
                Ok(runtime) => runtime,
                Err(report) => {
                    retain_history_failure(&history.shared, report.clone());
                    return handle_known_history_failure(history.mode, &mut sink, report);
                }
            };
            sink.runtime = Some(runtime);
        }
        let command = HistoryCommand::Event(HistoryEvent { scope, record });
        let queue_depth = match history.mode {
            HistoryMode::Strict => {
                reserve_history_queue_slot_blocking(&history.shared, history.queue_capacity)?
            }
            HistoryMode::BestEffort => {
                let Some(depth) =
                    reserve_history_queue_slot(&history.shared, history.queue_capacity)
                else {
                    let report = FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        format!(
                            "maintenance-history queue capacity {} was exhausted",
                            history.queue_capacity
                        ),
                    );
                    retain_history_failure(&history.shared, report);
                    sink.disabled = true;
                    return Ok(());
                };
                depth
            }
            HistoryMode::Disabled => return Ok(()),
        };
        history
            .shared
            .queue_high_water
            .fetch_max(queue_depth, Ordering::Relaxed);
        let sender = &sink
            .runtime
            .as_ref()
            .expect("history runtime was initialized")
            .sender;
        let send_result = match history.mode {
            HistoryMode::Strict => sender.send(command).map_err(|error| error.0),
            HistoryMode::BestEffort => sender.try_send(command).map_err(|error| match error {
                TrySendError::Full(command) | TrySendError::Disconnected(command) => command,
            }),
            HistoryMode::Disabled => unreachable!("disabled history has no policy"),
        };
        match send_result {
            Ok(()) => {
                history.records_constructed.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            Err(_) => {
                release_history_queue_slot(&history.shared);
                let report = retained_history_failure(&history.shared).unwrap_or_else(|| {
                    FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        "maintenance-history writer stopped before accepting an event",
                    )
                });
                retain_history_failure(&history.shared, report.clone());
                if history.mode == HistoryMode::Strict {
                    Err(report)
                } else {
                    sink.disabled = true;
                    Ok(())
                }
            }
        }
    }

    fn settle_history_boundary(&self) -> Result<(), FailureReport> {
        let Some(history) = &self.history else {
            return Ok(());
        };
        let sender = {
            let mut sink = history.sink.lock().map_err(|_| {
                FailureReport::maintenance_history(
                    FailureScope::RunGlobal,
                    "maintenance-history sink lock was poisoned",
                )
            })?;
            if let Some(report) = retained_history_failure(&history.shared) {
                return handle_known_history_failure(history.mode, &mut sink, report);
            }
            if history.mode == HistoryMode::BestEffort {
                return Ok(());
            }
            sink.runtime.as_ref().map(|runtime| runtime.sender.clone())
        };
        if let Some(sender) = sender {
            send_history_barrier(&sender, &history.shared)?;
        }
        Ok(())
    }

    fn finalize_history(&self) -> Result<(), FailureReport> {
        let Some(history) = &self.history else {
            return Ok(());
        };
        let mut sink = match history.sink.lock() {
            Ok(sink) => sink,
            Err(poisoned) if history.mode == HistoryMode::BestEffort => {
                let mut sink = poisoned.into_inner();
                sink.disabled = true;
                sink
            }
            Err(_) => {
                return Err(FailureReport::maintenance_history(
                    FailureScope::RunGlobal,
                    "maintenance-history sink lock was poisoned",
                ));
            }
        };
        let runtime = sink.runtime.take();
        drop(sink);
        if let Some(mut runtime) = runtime {
            let (ack_sender, ack_receiver) = mpsc::channel();
            let send_result = runtime.sender.send(HistoryCommand::Shutdown(ack_sender));
            let acknowledged = if send_result.is_ok() {
                ack_receiver.recv().ok()
            } else {
                None
            };
            let joined = runtime
                .join
                .take()
                .expect("history writer has one owner")
                .join();
            if joined.is_err() {
                retain_history_failure(
                    &history.shared,
                    FailureReport::maintenance_history(
                        FailureScope::RunGlobal,
                        "maintenance-history writer thread panicked",
                    ),
                );
            }
            if let Some(Err(report)) = acknowledged {
                retain_history_failure(&history.shared, report);
            }
        }
        match retained_history_failure(&history.shared) {
            Some(report) if history.mode == HistoryMode::Strict => Err(report),
            _ => Ok(()),
        }
    }

    fn query_history(
        &self,
        clause_id: u64,
        cursor: MaintenanceHistoryCursor,
        limit: usize,
    ) -> Result<MaintenanceHistoryPage, FailureReport> {
        if self.history.is_none() || limit == 0 {
            return Ok(MaintenanceHistoryPage {
                records: Vec::new(),
                next_cursor: None,
            });
        }
        self.flush_history_for_query()?;
        if self.history.as_ref().is_some_and(|history| {
            history.mode == HistoryMode::BestEffort
                && retained_history_failure(&history.shared).is_some()
                && history.shared.records_written.load(Ordering::Acquire) == 0
        }) {
            return Ok(MaintenanceHistoryPage {
                records: Vec::new(),
                next_cursor: None,
            });
        }
        read_history_page(&self.run_root, clause_id, cursor, limit)
    }

    fn flush_history_for_query(&self) -> Result<(), FailureReport> {
        let Some(history) = &self.history else {
            return Ok(());
        };
        let sender = {
            let mut sink = history.sink.lock().map_err(|_| {
                FailureReport::maintenance_history(
                    FailureScope::RunGlobal,
                    "maintenance-history sink lock was poisoned",
                )
            })?;
            if let Some(report) = retained_history_failure(&history.shared) {
                return if history.mode == HistoryMode::Strict {
                    Err(report)
                } else {
                    sink.disabled = true;
                    Ok(())
                };
            }
            if sink.runtime.is_none() {
                return Ok(());
            }
            sink.runtime.as_ref().map(|runtime| runtime.sender.clone())
        };
        if let Some(sender) = sender
            && let Err(report) = send_history_barrier(&sender, &history.shared)
        {
            retain_history_failure(&history.shared, report.clone());
            if history.mode == HistoryMode::Strict {
                return Err(report);
            }
            let mut sink = history.sink.lock().map_err(|_| {
                FailureReport::maintenance_history(
                    FailureScope::RunGlobal,
                    "maintenance-history sink lock was poisoned",
                )
            })?;
            sink.disabled = true;
        }
        Ok(())
    }
}

#[derive(Serialize)]
struct HistoryEnvelope<'a> {
    scope: &'a [String],
    #[serde(flatten)]
    record: &'a serde_json::Value,
}

fn start_history_writer(
    run_root: &Path,
    capacity: usize,
    shared: Arc<HistoryShared>,
) -> Result<HistoryRuntime, FailureReport> {
    let (sender, receiver) = mpsc::sync_channel(capacity);
    let worker_root = run_root.to_path_buf();
    shared
        .worker_state
        .store(HISTORY_RUNNING, Ordering::Release);
    let worker_shared = Arc::clone(&shared);
    let join = thread::Builder::new()
        .name("whiel-history-writer".to_string())
        .spawn(move || run_history_writer(&worker_root, receiver, &worker_shared))
        .map_err(|error| {
            shared.worker_state.store(HISTORY_FAILED, Ordering::Release);
            FailureReport::maintenance_history(
                FailureScope::RunGlobal,
                format!("start maintenance-history writer: {error}"),
            )
        })?;
    Ok(HistoryRuntime {
        sender,
        join: Some(join),
    })
}

fn run_history_writer(run_root: &Path, receiver: Receiver<HistoryCommand>, shared: &HistoryShared) {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_history_writer_inner(run_root, receiver, shared)
    }))
    .unwrap_or_else(|_| {
        Err(FailureReport::maintenance_history(
            FailureScope::RunGlobal,
            "maintenance-history writer thread panicked",
        ))
    });
    match result {
        Ok(()) if retained_history_failure(shared).is_none() => shared
            .worker_state
            .store(HISTORY_STOPPED, Ordering::Release),
        Ok(()) => shared.worker_state.store(HISTORY_FAILED, Ordering::Release),
        Err(report) => {
            publish_history_queue_failure(shared, report);
        }
    }
}

fn run_history_writer_inner(
    run_root: &Path,
    receiver: Receiver<HistoryCommand>,
    shared: &HistoryShared,
) -> Result<(), FailureReport> {
    let directory = run_root.join("history");
    fs::create_dir_all(&directory).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("create maintenance-history directory: {error}"),
        )
    })?;
    fs::create_dir_all(directory.join("by-clause")).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("create maintenance-history clause index: {error}"),
        )
    })?;
    let file = File::options()
        .create(true)
        .append(true)
        .open(directory.join("maintenance.jsonl"))
        .map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("open maintenance-history stream: {error}"),
            )
        })?;
    let mut offset = file
        .metadata()
        .map(|metadata| metadata.len())
        .map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("inspect maintenance-history stream: {error}"),
            )
        })?;
    let mut writer = file;
    while let Ok(command) = receiver.recv() {
        match command {
            HistoryCommand::Event(event) => {
                let queue_slot = HistoryQueueSlot(shared);
                if let Err(report) =
                    write_history_event(&directory, &mut writer, &mut offset, event, shared)
                {
                    publish_history_queue_failure(shared, report.clone());
                    drop(queue_slot);
                    return Err(report);
                }
            }
            HistoryCommand::Barrier(acknowledgement) => {
                #[cfg(test)]
                pause_history_barrier(shared);
                let result = writer.flush().map_err(|error| {
                    FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        format!("flush maintenance history: {error}"),
                    )
                });
                let _ = acknowledgement.send(result.clone());
                result?;
            }
            HistoryCommand::Shutdown(acknowledgement) => {
                let result = writer.flush().map_err(|error| {
                    FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        format!("finalize maintenance history: {error}"),
                    )
                });
                let _ = acknowledgement.send(result.clone());
                return result;
            }
        }
    }
    writer.flush().map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("flush disconnected maintenance history: {error}"),
        )
    })
}

fn write_history_event(
    directory: &Path,
    writer: &mut File,
    offset: &mut u64,
    event: HistoryEvent,
    shared: &HistoryShared,
) -> Result<(), FailureReport> {
    let (record, mut clause_ids) = event.record.materialize()?;
    if record
        .as_object()
        .is_some_and(|object| object.contains_key("scope"))
    {
        return Err(FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            "maintenance-history record uses reserved key `scope`",
        ));
    }
    clause_ids.sort_unstable();
    clause_ids.dedup();
    let envelope = HistoryEnvelope {
        scope: &event.scope,
        record: &record,
    };
    let mut encoded = serde_json::to_vec(&envelope).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("serialize scoped maintenance history: {error}"),
        )
    })?;
    encoded.push(b'\n');
    let encoded_len = u64::try_from(encoded.len()).map_err(|_| {
        FailureReport::maintenance_history(
            FailureScope::RunGlobal,
            "maintenance-history record length exceeded u64",
        )
    })?;
    let next_offset = offset.checked_add(encoded_len).ok_or_else(|| {
        FailureReport::maintenance_history(
            FailureScope::RunGlobal,
            "maintenance-history byte offset overflowed",
        )
    })?;
    let mut indexes = open_clause_indexes(directory, &clause_ids)?;
    let original_offset = *offset;
    let append_result = (|| {
        // Sidecars are tentative until the main stream reaches record_end.
        // The main-file length is therefore the lock-free commit marker used
        // by concurrent readers.
        for index in &mut indexes {
            append_clause_index(index, original_offset, encoded.len(), shared)?;
        }
        append_history_body(writer, &encoded, shared)?;
        Ok(())
    })();
    if let Err(report) = append_result {
        return Err(rollback_history_event(
            writer,
            original_offset,
            &mut indexes,
            report,
        ));
    }
    *offset = next_offset;
    shared.records_written.fetch_add(1, Ordering::Relaxed);
    Ok(())
}

struct ClauseIndexAppend {
    clause_id: u64,
    path: PathBuf,
    original_len: u64,
}

fn open_clause_indexes(
    history_directory: &Path,
    clause_ids: &[u64],
) -> Result<Vec<ClauseIndexAppend>, FailureReport> {
    clause_ids
        .iter()
        .map(|&clause_id| {
            let path = history_directory
                .join("by-clause")
                .join(format!("clause-{clause_id:020}.idx"));
            let file = File::options()
                .create(true)
                .append(true)
                .open(&path)
                .map_err(|error| {
                    FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        format!("open maintenance-history clause index: {error}"),
                    )
                })?;
            let original_len = file
                .metadata()
                .map(|metadata| metadata.len())
                .map_err(|error| {
                    FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        format!("inspect maintenance-history clause index: {error}"),
                    )
                })?;
            Ok(ClauseIndexAppend {
                clause_id,
                path,
                original_len,
            })
        })
        .collect()
}

fn append_history_body(
    writer: &mut File,
    encoded: &[u8],
    _shared: &HistoryShared,
) -> Result<(), FailureReport> {
    #[cfg(test)]
    if take_main_write_fault(_shared) {
        let prefix_len = (encoded.len() / 2).clamp(1, encoded.len() - 1);
        writer.write_all(&encoded[..prefix_len]).map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("append injected maintenance-history prefix: {error}"),
            )
        })?;
        return Err(FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            "injected short maintenance-history body write",
        ));
    }
    writer.write_all(encoded).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("append maintenance history: {error}"),
        )
    })
}

fn append_clause_index(
    index: &mut ClauseIndexAppend,
    offset: u64,
    encoded_len: usize,
    _shared: &HistoryShared,
) -> Result<(), FailureReport> {
    let encoded = format!("{offset} {encoded_len}\n");
    let mut file = File::options()
        .append(true)
        .open(&index.path)
        .map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!(
                    "reopen maintenance-history clause {} index: {error}",
                    index.clause_id
                ),
            )
        })?;
    #[cfg(test)]
    if take_index_write_fault(_shared) {
        let prefix_len = (encoded.len() / 2).clamp(1, encoded.len() - 1);
        file.write_all(&encoded.as_bytes()[..prefix_len])
            .map_err(|error| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    format!(
                        "append injected maintenance-history clause {} index prefix: {error}",
                        index.clause_id
                    ),
                )
            })?;
        return Err(FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!(
                "injected short maintenance-history clause {} index write",
                index.clause_id
            ),
        ));
    }
    file.write_all(encoded.as_bytes()).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!(
                "append maintenance-history clause {} index: {error}",
                index.clause_id
            ),
        )
    })
}

fn rollback_history_event(
    writer: &mut File,
    original_offset: u64,
    indexes: &mut [ClauseIndexAppend],
    primary: FailureReport,
) -> FailureReport {
    let mut rollback_failures = Vec::new();
    if let Err(error) = writer.set_len(original_offset) {
        rollback_failures.push(format!("restore maintenance-history body: {error}"));
    }
    for index in indexes {
        match File::options().write(true).open(&index.path) {
            Ok(file) => {
                if let Err(error) = file.set_len(index.original_len) {
                    rollback_failures.push(format!(
                        "restore maintenance-history clause {} index: {error}",
                        index.clause_id
                    ));
                }
            }
            Err(error) => {
                rollback_failures.push(format!(
                    "reopen maintenance-history clause {} index for rollback: {error}",
                    index.clause_id
                ));
            }
        }
    }
    if rollback_failures.is_empty() {
        primary
    } else {
        let primary_detail = primary
            .detail()
            .unwrap_or("maintenance-history append failed");
        FailureReport::maintenance_history(
            FailureScope::RunGlobal,
            format!(
                "{primary_detail}; transactional rollback also failed: {}",
                rollback_failures.join("; ")
            ),
        )
    }
}

#[cfg(test)]
fn take_main_write_fault(shared: &HistoryShared) -> bool {
    let mut fault = shared
        .fault_injection
        .lock()
        .expect("history fault-injection lock was poisoned");
    std::mem::take(&mut fault.fail_main_after_prefix)
}

#[cfg(test)]
fn take_index_write_fault(shared: &HistoryShared) -> bool {
    let mut fault = shared
        .fault_injection
        .lock()
        .expect("history fault-injection lock was poisoned");
    match fault.fail_index_after.as_mut() {
        Some(remaining) if *remaining == 0 => {
            fault.fail_index_after = None;
            true
        }
        Some(remaining) => {
            *remaining -= 1;
            false
        }
        None => false,
    }
}

#[cfg(test)]
fn pause_history_barrier(shared: &HistoryShared) {
    let pause = shared
        .fault_injection
        .lock()
        .expect("history fault-injection lock was poisoned")
        .barrier_pause
        .take();
    if let Some(pause) = pause {
        pause.entered.send(()).unwrap();
        pause.release.recv().unwrap();
    }
}

fn send_history_barrier(
    sender: &SyncSender<HistoryCommand>,
    shared: &HistoryShared,
) -> Result<(), FailureReport> {
    let (ack_sender, ack_receiver) = mpsc::channel();
    sender
        .send(HistoryCommand::Barrier(ack_sender))
        .map_err(|_| {
            retained_history_failure(shared).unwrap_or_else(|| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    "maintenance-history writer stopped before a barrier",
                )
            })
        })?;
    #[cfg(test)]
    shared.barrier_commands_sent.fetch_add(1, Ordering::Release);
    ack_receiver.recv().map_err(|_| {
        retained_history_failure(shared).unwrap_or_else(|| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                "maintenance-history writer did not acknowledge a barrier",
            )
        })
    })?
}

fn handle_known_history_failure(
    mode: HistoryMode,
    sink: &mut HistorySink,
    report: FailureReport,
) -> Result<(), FailureReport> {
    if mode == HistoryMode::Strict {
        Err(report)
    } else {
        sink.disabled = true;
        Ok(())
    }
}

fn retain_history_failure(shared: &HistoryShared, report: FailureReport) {
    let mut failure = shared
        .failure
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    failure.get_or_insert(report);
}

fn retained_history_failure(shared: &HistoryShared) -> Option<FailureReport> {
    shared
        .failure
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone()
}

fn reserve_history_queue_slot(shared: &HistoryShared, capacity: usize) -> Option<usize> {
    let mut state = shared
        .queue_state
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if state.failed || state.depth >= capacity {
        return None;
    }
    state.depth += 1;
    Some(state.depth)
}

fn reserve_history_queue_slot_blocking(
    shared: &HistoryShared,
    capacity: usize,
) -> Result<usize, FailureReport> {
    let mut state = shared.queue_state.lock().map_err(|_| {
        FailureReport::maintenance_history(
            FailureScope::RunGlobal,
            "maintenance-history queue wait lock was poisoned",
        )
    })?;
    loop {
        if state.failed {
            drop(state);
            return Err(retained_history_failure(shared).unwrap_or_else(|| {
                FailureReport::maintenance_history(
                    FailureScope::RunGlobal,
                    "maintenance-history queue failed without a retained reason",
                )
            }));
        }
        if state.depth < capacity {
            state.depth += 1;
            return Ok(state.depth);
        }
        state = shared.queue_available.wait(state).map_err(|_| {
            FailureReport::maintenance_history(
                FailureScope::RunGlobal,
                "maintenance-history queue wait lock was poisoned",
            )
        })?;
    }
}

fn release_history_queue_slot(shared: &HistoryShared) {
    let mut state = shared
        .queue_state
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if !state.failed && state.depth > 0 {
        state.depth -= 1;
    }
    drop(state);
    shared.queue_available.notify_one();
}

fn fail_history_queue(shared: &HistoryShared) {
    let mut state = shared
        .queue_state
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    state.failed = true;
    state.depth = 0;
    drop(state);
    shared.queue_available.notify_all();
}

fn publish_history_queue_failure(shared: &HistoryShared, report: FailureReport) {
    retain_history_failure(shared, report);
    shared.worker_state.store(HISTORY_FAILED, Ordering::Release);
    fail_history_queue(shared);
}

struct HistoryQueueSlot<'a>(&'a HistoryShared);

impl Drop for HistoryQueueSlot<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            publish_history_queue_failure(
                self.0,
                FailureReport::maintenance_history(
                    FailureScope::RunGlobal,
                    "maintenance-history writer thread panicked",
                ),
            );
        } else {
            release_history_queue_slot(self.0);
        }
    }
}

fn decode_history_worker_state(state: u8) -> HistoryWorkerState {
    match state {
        HISTORY_DORMANT => HistoryWorkerState::Dormant,
        HISTORY_RUNNING => HistoryWorkerState::Running,
        HISTORY_FAILED => HistoryWorkerState::Failed,
        HISTORY_STOPPED => HistoryWorkerState::Stopped,
        _ => HistoryWorkerState::Failed,
    }
}

fn read_history_page(
    run_root: &Path,
    clause_id: u64,
    cursor: MaintenanceHistoryCursor,
    limit: usize,
) -> Result<MaintenanceHistoryPage, FailureReport> {
    let index_path = run_root
        .join("history/by-clause")
        .join(format!("clause-{clause_id:020}.idx"));
    let index_file = match File::open(&index_path) {
        Ok(file) => file,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(MaintenanceHistoryPage {
                records: Vec::new(),
                next_cursor: None,
            });
        }
        Err(error) => {
            return Err(FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("open maintenance-history clause index: {error}"),
            ));
        }
    };
    let mut index = BufReader::new(index_file);
    index.seek(SeekFrom::Start(cursor.0)).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("seek maintenance-history clause index: {error}"),
        )
    })?;
    let mut main = File::open(run_root.join("history/maintenance.jsonl")).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("open maintenance-history stream for query: {error}"),
        )
    })?;
    // The preceding writer barrier made this prefix visible. A later event can
    // publish its tentative sidecar before its main-body commit, so the query
    // must not advance its persistent cursor beyond this stable main-file end.
    let stable_main_len = main
        .metadata()
        .map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("inspect maintenance-history query prefix: {error}"),
            )
        })?
        .len();
    let mut records = Vec::with_capacity(limit);
    let mut line = String::new();
    while records.len() < limit {
        let line_start = index.stream_position().map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("inspect maintenance-history index cursor: {error}"),
            )
        })?;
        line.clear();
        if index.read_line(&mut line).map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("read maintenance-history clause index: {error}"),
            )
        })? == 0
        {
            break;
        }
        // A concurrent writer publishes sidecars before the main-body commit
        // marker. Treat its unterminated tail as tentative, not malformed.
        if !line.ends_with('\n') {
            index.seek(SeekFrom::Start(line_start)).map_err(|error| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    format!("restore tentative maintenance-history index cursor: {error}"),
                )
            })?;
            break;
        }
        let (offset, length) = line.trim_end().split_once(' ').ok_or_else(|| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                "malformed maintenance-history clause index entry",
            )
        })?;
        let offset = offset.parse::<u64>().map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("decode maintenance-history offset: {error}"),
            )
        })?;
        let length = length.parse::<usize>().map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("decode maintenance-history length: {error}"),
            )
        })?;
        let record_end = offset
            .checked_add(u64::try_from(length).map_err(|_| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    "maintenance-history indexed record length exceeds UInt64",
                )
            })?)
            .ok_or_else(|| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    "maintenance-history indexed record range overflowed",
                )
            })?;
        if record_end > stable_main_len {
            index.seek(SeekFrom::Start(line_start)).map_err(|error| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    format!("restore maintenance-history index cursor: {error}"),
                )
            })?;
            break;
        }
        let mut encoded = vec![0_u8; length];
        main.seek(SeekFrom::Start(offset))
            .and_then(|_| main.read_exact(&mut encoded))
            .map_err(|error| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    format!("read indexed maintenance-history record: {error}"),
                )
            })?;
        records.push(
            serde_json::from_slice(encoded.strip_suffix(b"\n").unwrap_or(&encoded)).map_err(
                |error| {
                    FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        format!("decode indexed maintenance-history record: {error}"),
                    )
                },
            )?,
        );
    }
    let next_offset = index.stream_position().map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("inspect maintenance-history cursor: {error}"),
        )
    })?;
    let has_more = !index
        .fill_buf()
        .map_err(|error| {
            FailureReport::maintenance_history(
                FailureScope::LaneLocal,
                format!("inspect maintenance-history next page: {error}"),
            )
        })?
        .is_empty();
    Ok(MaintenanceHistoryPage {
        records,
        next_cursor: has_more.then_some(MaintenanceHistoryCursor(next_offset)),
    })
}

// ------------------------------------------------------------
// Backend-Owned Work
// ------------------------------------------------------------

/// A runtime component's obligation to join its work before backend settlement.
///
/// Drop deliberately does not discharge this obligation. The component must
/// call `discharge` only after its owned work has stopped.
pub(crate) struct OwnedWorkRegistration {
    backend: Arc<Backend>,
    discharged: AtomicBool,
    joinable_background: bool,
}

struct OwnedWorkCompletion(Option<OwnedWorkRegistration>);

impl OwnedWorkCompletion {
    fn new(registration: OwnedWorkRegistration) -> Self {
        Self(Some(registration))
    }
}

impl Drop for OwnedWorkCompletion {
    fn drop(&mut self) {
        if let Some(registration) = self.0.take() {
            registration.discharge();
        }
    }
}

struct QueryPublicationWorkGuard {
    backend: Arc<Backend>,
    publication: Arc<QueryPublication>,
    registration: Option<OwnedWorkRegistration>,
    finished: bool,
}

impl QueryPublicationWorkGuard {
    fn finish(mut self, result: &Result<ArtifactRef, FailureReport>) -> Result<(), FailureReport> {
        // Discharge before publishing the terminal state. A waiter that
        // observes Ready may immediately drop its store and settle the
        // backend; the reverse order let settlement race this discharge and
        // fail with "backend-owned work was not explicitly joined".
        self.finished = true;
        if let Some(registration) = self.registration.take() {
            registration.discharge();
        }
        self.backend
            .finish_query_publication(&self.publication, result)
    }
}

impl Drop for QueryPublicationWorkGuard {
    fn drop(&mut self) {
        if let Some(registration) = self.registration.take() {
            registration.discharge();
        }
        if !self.finished {
            let report = FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "query publication worker stopped before publishing a terminal state",
            );
            let result = Err(report);
            let _ = self
                .backend
                .finish_query_publication(&self.publication, &result);
        }
    }
}

fn run_query_publication_worker(
    query_store: ArtifactStore,
    publication: Arc<QueryPublication>,
    guard: QueryPublicationWorkGuard,
) -> Result<ArtifactRef, FailureReport> {
    let result = query_store.publish_bytes(ArtifactKind::Query, &publication.payload);
    guard.finish(&result).and(result)
}

impl OwnedWorkRegistration {
    pub(crate) fn discharge(&self) {
        if self
            .discharged
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            self.backend
                .active_owned_work
                .fetch_sub(1, Ordering::AcqRel);
            if self.joinable_background {
                self.backend
                    .active_background_work
                    .fetch_sub(1, Ordering::AcqRel);
            }
            self.backend.owned_work_changed.notify_waiters();
        }
    }
}

// ------------------------------------------------------------
// Streaming Artifact Publication
// ------------------------------------------------------------

/*
  A stage reserves publication for its full lifetime. Its artifact
  kind is assigned only after capture is complete. Commit atomically
  moves the payload into required storage; Drop removes an unfinished
  staging file.
*/

pub(crate) struct BudgetedArtifactWriter {
    backend: Arc<Backend>,
    writer: File,
}
impl Write for BudgetedArtifactWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.backend
            .charge_payload_budget(bytes.len() as u64)
            .map_err(|report| std::io::Error::other(format!("{report:?}")))?;
        self.writer.write(bytes)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.writer.flush()
    }
}

pub(crate) struct StagedArtifact {
    backend: Arc<Backend>,
    artifact_id: ArtifactId,
    scope: Vec<String>,
    staging: PathBuf,
    final_name: String,
    committed: bool,
}

impl StagedArtifact {
    fn begin(
        backend: Arc<Backend>,
        scope: Vec<String>,
    ) -> Result<(Self, BudgetedArtifactWriter), FailureReport> {
        if backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "artifact backend is not open",
            ));
        }
        // Recheck after joining the active set. This closes the race
        // with settlement changing OPEN immediately after the first check.
        backend.active_publications.fetch_add(1, Ordering::AcqRel);
        if backend.state.load(Ordering::Acquire) != OPEN {
            backend.active_publications.fetch_sub(1, Ordering::AcqRel);
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "artifact backend is settling",
            ));
        }
        let id = match backend.next_artifact_id.allocate() {
            Some(id) => id,
            None => {
                backend.active_publications.fetch_sub(1, Ordering::AcqRel);
                return Err(FailureReport::artifact(
                    FailureKind::InfrastructureFailure,
                    FailureScope::RunGlobal,
                    "artifact identity space exhausted",
                ));
            }
        };
        // Every payload file this backend ever creates passes through here,
        // so this is the one chokepoint where the file budget can be exact.
        // Charging before File::create means a run over its allowance stops
        // producing filesystem records entirely.
        if let Err(report) = backend.charge_payload_file_budget() {
            backend.active_publications.fetch_sub(1, Ordering::AcqRel);
            return Err(report);
        }
        let staging = backend.staging_root.join(format!("artifact-{id:020}.part"));
        let writer = match File::create(&staging) {
            Ok(writer) => writer,
            Err(error) => {
                backend.active_publications.fetch_sub(1, Ordering::AcqRel);
                return Err(FailureReport::artifact(
                    FailureKind::PublicationFailure,
                    FailureScope::LaneLocal,
                    format!("create staged required artifact {id}: {error}"),
                ));
            }
        };
        Ok((
            Self {
                backend: Arc::clone(&backend),
                artifact_id: ArtifactId(id),
                scope,
                staging,
                final_name: format!("artifact-{id:020}.bin"),
                committed: false,
            },
            BudgetedArtifactWriter { backend, writer },
        ))
    }

    pub(crate) fn commit(mut self, kind: ArtifactKind) -> Result<ArtifactRef, FailureReport> {
        if self.backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "artifact backend began settlement during publication",
            ));
        }
        let byte_len = fs::metadata(&self.staging)
            .map_err(|error| {
                FailureReport::artifact(
                    FailureKind::PublicationFailure,
                    FailureScope::LaneLocal,
                    format!("inspect staged required artifact: {error}"),
                )
            })?
            .len();
        if let Some(report) = self.backend.resource_failure() {
            return Err(report);
        }
        if self.backend.state.load(Ordering::Acquire) != OPEN {
            return Err(FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::RunGlobal,
                "artifact backend began settlement during publication",
            ));
        }
        let destination = self.backend.required_root.join(&self.final_name);
        fs::rename(&self.staging, &destination).map_err(|error| {
            FailureReport::artifact(
                FailureKind::PublicationFailure,
                FailureScope::LaneLocal,
                format!("publish staged required artifact: {error}"),
            )
        })?;
        let mut records = self.backend.records.lock().map_err(|_| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "artifact index lock was poisoned",
            )
        })?;
        records.insert(
            self.artifact_id,
            ArtifactRecord {
                id: self.artifact_id.0,
                kind,
                relative_path: format!("required/{}", self.final_name),
                byte_len,
                scope: std::mem::take(&mut self.scope),
                retained: true,
            },
        );
        self.backend
            .required_payloads_published
            .fetch_add(1, Ordering::Relaxed);
        self.committed = true;
        Ok(ArtifactRef {
            backend: self.backend.id,
            artifact: self.artifact_id,
            kind,
        })
    }
}

impl Drop for StagedArtifact {
    fn drop(&mut self) {
        if !self.committed {
            let _ = fs::remove_file(&self.staging);
        }
        self.backend
            .active_publications
            .fetch_sub(1, Ordering::AcqRel);
    }
}

// ------------------------------------------------------------
// Frozen Manifest Types
// ------------------------------------------------------------

#[derive(Serialize)]
struct Manifest<'a> {
    format_version: u64,
    backend_id: String,
    task: ManifestTask<'a>,
    /// The run policy this run was bound to, or `null` for a run that
    /// declared none. Written verbatim, so a manifest-driven reopen reads
    /// back exactly what was bound.
    run_configuration: Option<serde_json::Value>,
    artifacts: Vec<ArtifactRecord>,
}

#[derive(Serialize)]
struct ManifestTask<'a> {
    canonical_id: &'a str,
    module: &'a str,
    namespace: &'a str,
    source_sha256: &'a str,
    semantic_version: u64,
    encoding_version: u64,
}

// ------------------------------------------------------------
// Identity Allocation And Run Roots
// ------------------------------------------------------------

#[derive(Debug)]
struct IdAllocator {
    next: AtomicU64,
    max_claimed: AtomicBool,
}

impl IdAllocator {
    const fn new(first: u64) -> Self {
        Self {
            next: AtomicU64::new(first),
            max_claimed: AtomicBool::new(false),
        }
    }

    fn allocate(&self) -> Option<u64> {
        let mut current = self.next.load(Ordering::Relaxed);
        loop {
            if current == u64::MAX {
                return self
                    .max_claimed
                    .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                    .ok()
                    .map(|_| u64::MAX);
            }
            match self.next.compare_exchange_weak(
                current,
                current + 1,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Some(current),
                Err(observed) => current = observed,
            }
        }
    }
}

fn reserve_run_root(root: &Path) -> Result<(BackendId, PathBuf), FailureReport> {
    fs::create_dir_all(root).map_err(|error| {
        FailureReport::artifact(
            FailureKind::PublicationFailure,
            FailureScope::RunGlobal,
            format!("create artifact root: {error}"),
        )
    })?;
    loop {
        let id = fresh_backend_id().ok_or_else(|| {
            FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "backend identity space exhausted",
            )
        })?;
        let run_root = root.join(format!("run-{id}"));
        match fs::create_dir(&run_root) {
            Ok(()) => return Ok((id, run_root)),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => {
                return Err(FailureReport::artifact(
                    FailureKind::PublicationFailure,
                    FailureScope::RunGlobal,
                    format!("reserve run artifact directory: {error}"),
                ));
            }
        }
    }
}

fn fresh_backend_id() -> Option<BackendId> {
    let prefix = *BACKEND_PREFIX.get_or_init(|| {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|duration| duration.as_nanos())
            .unwrap_or(0);
        let folded_time = (nanos as u64) ^ ((nanos >> 64) as u64);
        folded_time ^ ((std::process::id() as u64) << 32)
    });
    NEXT_BACKEND_SEQUENCE
        .allocate()
        .map(|sequence| BackendId(((prefix as u128) << 64) | sequence as u128))
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_path_is_determined_by_backend_and_local_identity() {
        let reference = ArtifactRef {
            backend: BackendId(0x12),
            artifact: ArtifactId(34),
            kind: ArtifactKind::Certificate,
        };
        assert_eq!(
            reference.retained_path(Path::new("artifacts/task/solver-artifacts")),
            PathBuf::from(
                "artifacts/task/solver-artifacts/run-00000000000000000000000000000012/required/artifact-00000000000000000034.bin"
            )
        );
    }

    #[test]
    fn allocator_uses_max_once_then_fails_closed() {
        let allocator = IdAllocator::new(u64::MAX - 1);
        assert_eq!(allocator.allocate(), Some(u64::MAX - 1));
        assert_eq!(allocator.allocate(), Some(u64::MAX));
        assert_eq!(allocator.allocate(), None);
        assert_eq!(allocator.next.load(Ordering::Relaxed), u64::MAX);
        assert!(allocator.max_claimed.load(Ordering::Relaxed));
    }

    #[test]
    fn query_fingerprint_is_bounded_metadata() {
        let first = QueryFingerprint {
            digest: Arc::from("forced-collision"),
            byte_len: 5,
        };
        let second = QueryFingerprint {
            digest: Arc::clone(&first.digest),
            byte_len: 6,
        };
        assert_ne!(first, second);
    }

    #[tokio::test]
    async fn query_cache_uses_compact_identity_and_backend_neutral_scope() {
        let task = SynthesisTask::from_json(
            r#"{
              "format_version":3,"semantic_version":1,"encoding_version":1,
              "identity":{"canonical_id":"ArtifactQueryCache","module":"Whiel.Test.ArtifactQueryCache","namespace":"Whiel.Test.ArtifactQueryCache","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"},
              "schema":{"expression":"Whiel.Test.ArtifactQueryCache.programSchema","display":"schema"},
              "original":{"pre":{"expression":"Whiel.Test.ArtifactQueryCache.inputPre","display":"true"},"command":{"expression":"Whiel.Test.ArtifactQueryCache.inputCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ArtifactQueryCache.inputPost","display":"true"}},
              "preprocessed":{"pre":{"expression":"Whiel.Test.ArtifactQueryCache.inputPreproc.loopPre","display":"true"},"command":{"expression":"Whiel.Test.ArtifactQueryCache.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ArtifactQueryCache.inputPreproc.loopPost","display":"true"}},
              "preprocessing_evidence":{"expression":"Whiel.Test.ArtifactQueryCache.inputPreproc"},
              "solver":{"schema_relations":[{"key":"rel:R:0","arity":1}],"task_constants":[],
                "preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.ArtifactQueryCache.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.ArtifactQueryCache.inputPreproc.loopPre_noBound","constants":[],"relations":["rel:R:0"]},
                "preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.ArtifactQueryCache.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.ArtifactQueryCache.inputPreproc.loopPost_noBound","constants":[],"relations":["rel:R:0"]},
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":["rel:R:0"]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":["rel:R:0"]}}
            }"#,
        )
        .unwrap();
        let root = std::env::temp_dir().join(format!(
            "whiel_artifact_query_cache_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let digest: Arc<str> = Arc::from("forced-collision");
        let first = store
            .scoped(ScopeTag::Inv)
            .publish_query(Arc::clone(&digest), Arc::from(&b"first"[..]))
            .await
            .unwrap();
        let first_again = store
            .publish_query(digest, Arc::from(&b"first"[..]))
            .await
            .unwrap();

        assert_eq!(first, first_again);
        assert_eq!(
            store.resolve(first).unwrap().scope(),
            ["root", "query-store"]
        );
        let diagnostics = store.diagnostics();
        assert_eq!(diagnostics.ready_query_artifacts, 1);
        assert_eq!(diagnostics.in_flight_query_payload_bytes, 0);

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn dropped_query_publisher_cannot_strand_a_coalesced_cache_entry() {
        let task = SynthesisTask::from_json(
            r#"{
              "format_version":3,"semantic_version":1,"encoding_version":1,
              "identity":{"canonical_id":"ArtifactDroppedQuery","module":"Whiel.Test.ArtifactDroppedQuery","namespace":"Whiel.Test.ArtifactDroppedQuery","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"},
              "schema":{"expression":"Whiel.Test.ArtifactDroppedQuery.programSchema","display":"schema"},
              "original":{"pre":{"expression":"Whiel.Test.ArtifactDroppedQuery.inputPre","display":"true"},"command":{"expression":"Whiel.Test.ArtifactDroppedQuery.inputCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ArtifactDroppedQuery.inputPost","display":"true"}},
              "preprocessed":{"pre":{"expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc.loopPre","display":"true"},"command":{"expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc.loopPost","display":"true"}},
              "preprocessing_evidence":{"expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc"},
              "solver":{"schema_relations":[{"key":"rel:R:0","arity":1}],"task_constants":[],
                "preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc.loopPre_noBound","constants":[],"relations":["rel:R:0"]},
                "preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.ArtifactDroppedQuery.inputPreproc.loopPost_noBound","constants":[],"relations":["rel:R:0"]},
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":["rel:R:0"]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":["rel:R:0"]}}
            }"#,
        )
        .unwrap();
        let root = std::env::temp_dir().join(format!(
            "whiel_artifact_dropped_query_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let publisher_store = store.clone();
        let payload: Arc<[u8]> = Arc::from(vec![0x71_u8; 8 * 1024 * 1024]);
        let publisher_payload = Arc::clone(&payload);
        let publisher = tokio::spawn(async move {
            publisher_store
                .publish_query(Arc::from("dropped-query"), publisher_payload)
                .await
        });

        tokio::time::timeout(std::time::Duration::from_secs(2), async {
            while store.diagnostics().active_publications == 0 {
                tokio::task::yield_now().await;
            }
        })
        .await
        .expect("query publication did not begin");
        publisher.abort();
        let _ = publisher.await;

        let reference = tokio::time::timeout(
            std::time::Duration::from_secs(5),
            store.publish_query(Arc::from("dropped-query"), payload),
        )
        .await
        .expect("coalesced query cache entry remained Publishing")
        .unwrap();
        assert_eq!(
            store.resolve(reference).unwrap().byte_len(),
            8 * 1024 * 1024
        );
        assert_eq!(store.diagnostics().ready_query_artifacts, 1);

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn rejected_query_work_registration_publishes_failure_to_waiters() {
        let task = artifact_test_task("ArtifactRejectedQueryWork");
        let root = artifact_test_root("rejected_query_work");
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let fingerprint = QueryFingerprint {
            digest: Arc::from("registration-race"),
            byte_len: 5,
        };
        let publication = match store
            .backend
            .select_query(fingerprint, Arc::from(&b"query"[..]))
            .unwrap()
        {
            QuerySelection::Publish(publication) => publication,
            _ => panic!("fresh query must select publication"),
        };
        let waiter = Arc::clone(&publication);
        store.backend.state.store(SETTLING, Ordering::Release);

        assert!(store.begin_query_publication_work(publication).is_err());
        let error = tokio::time::timeout(std::time::Duration::from_secs(1), waiter.wait())
            .await
            .expect("registration failure stranded query waiter")
            .unwrap_err();
        assert_eq!(error.scope(), FailureScope::RunGlobal);
        assert!(store.backend.query_publications.lock().unwrap().is_empty());

        store.backend.state.store(OPEN, Ordering::Release);
        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn certificate_only_retention_discards_a_consumed_payload() {
        // Runtime proofs are never read back and certification re-runs
        // Vampire, so outside detailed diagnostics they are provenance no
        // one consults. Discarding as each job ends is what bounds peak
        // disk use, which pruning at settlement cannot.
        let task = artifact_test_task("ArtifactRetention");
        let root = artifact_test_root("retention");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).retention(Retention::CertificateOnly),
        )
        .unwrap();

        let reference = store
            .publish(ArtifactKind::Proof, vec![b'p'; 32].into_boxed_slice())
            .expect("publish proof");
        let path = store
            .resolve(reference)
            .expect("resolve")
            .path()
            .to_path_buf();
        assert!(path.exists(), "payload should exist before discard");
        assert!(store.is_retained(reference));

        store.discard(reference).expect("discard");
        assert!(!path.exists(), "discard must remove the payload");
        assert!(
            !store.is_retained(reference),
            "the index record must survive so reports can say what existed"
        );
        store.discard(reference).expect("discard is idempotent");

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retain_all_keeps_payloads_that_certificate_only_would_discard() {
        let task = artifact_test_task("ArtifactRetentionAll");
        let root = artifact_test_root("retention_all");
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();

        let reference = store
            .publish(ArtifactKind::Proof, vec![b'p'; 32].into_boxed_slice())
            .expect("publish proof");
        let path = store
            .resolve(reference)
            .expect("resolve")
            .path()
            .to_path_buf();
        store.discard(reference).expect("discard is a no-op here");
        assert!(
            path.exists(),
            "detailed runs must keep every artifact for debugging"
        );
        assert!(store.is_retained(reference));

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn payload_budget_stops_a_run_before_it_exhausts_its_volume() {
        // An unbounded run can write artifacts until its volume fills,
        // taking the filesystem's shared metadata down with it. A
        // budgeted run must fail cleanly instead.
        let task = artifact_test_task("ArtifactPayloadBudget");
        let root = artifact_test_root("payload_budget");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).payload_budget(Some(64)),
        )
        .unwrap();

        store
            .publish(
                ArtifactKind::RuntimeTrace,
                vec![b'x'; 40].into_boxed_slice(),
            )
            .expect("first payload fits the budget");
        let overflow = store
            .publish(
                ArtifactKind::RuntimeTrace,
                vec![b'x'; 40].into_boxed_slice(),
            )
            .expect_err("second payload must exceed the 64-byte budget");
        assert_eq!(overflow.kind(), FailureKind::PublicationFailure);
        assert_eq!(overflow.scope(), FailureScope::RunGlobal);

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn certificate_only_publishes_provenance_without_files() {
        // Pure-provenance kinds must never touch the filesystem on a
        // certificate-only run — a manifest record is the whole
        // publication. A created-then-deleted file would still cost
        // filesystem watchers two bookkeeping records per payload.
        let task = artifact_test_task("ArtifactRecordOnly");
        let root = artifact_test_root("record_only");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).retention(Retention::CertificateOnly),
        )
        .unwrap();

        let reference = store
            .publish(
                ArtifactKind::RuntimeTrace,
                vec![b't'; 24].into_boxed_slice(),
            )
            .expect("publish runtime trace");
        let resolved = store.resolve(reference).expect("record must resolve");
        assert_eq!(resolved.byte_len(), 24);
        assert!(
            !resolved.path().exists(),
            "a record-only publication must create no payload file"
        );
        assert!(!store.is_retained(reference));
        assert_eq!(store.diagnostics().required_payloads_published, 1);
        assert_eq!(
            store.diagnostics().required_payload_files_created,
            0,
            "no staged file may back a record-only publication"
        );

        drop(store);
        owner.settle().unwrap();
        let manifest: serde_json::Value = serde_json::from_slice(
            &fs::read(
                root.join(format!("run-{}", reference.backend_id()))
                    .join("manifest.json"),
            )
            .expect("read manifest"),
        )
        .expect("decode manifest");
        let records = manifest["artifacts"].as_array().expect("artifact records");
        assert_eq!(records.len(), 1);
        assert_eq!(records[0]["kind"], "runtime_trace");
        assert_eq!(records[0]["retained"], false);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn settlement_sweeps_payloads_the_terminal_result_does_not_reference() {
        // Only jobs backing a certificate need to survive. A
        // certificate-only run ends holding its certificate,
        // acceptance record, and whatever the terminal result references —
        // nothing else.
        let task = artifact_test_task("ArtifactSweep");
        let root = artifact_test_root("sweep");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).retention(Retention::CertificateOnly),
        )
        .unwrap();

        let query = store
            .publish(ArtifactKind::Query, b"tptp".as_slice().into())
            .expect("publish query");
        let certificate = store
            .publish(ArtifactKind::Certificate, b"lean".as_slice().into())
            .expect("publish certificate");
        let terminal_witness = store
            .publish(ArtifactKind::Witness, b"kept".as_slice().into())
            .expect("publish terminal witness");
        let interim_witness = store
            .publish(ArtifactKind::Witness, b"swept".as_slice().into())
            .expect("publish interim witness");
        let paths: Vec<PathBuf> = [query, certificate, terminal_witness, interim_witness]
            .iter()
            .map(|reference| store.resolve(*reference).unwrap().path().to_path_buf())
            .collect();
        assert!(paths.iter().all(|path| path.exists()));

        drop(store);
        owner.settle_retaining(&[terminal_witness]).unwrap();
        assert!(!paths[0].exists(), "unreferenced query must be swept");
        assert!(paths[1].exists(), "certificates are durable by kind");
        assert!(
            paths[2].exists(),
            "terminal-referenced witness must survive"
        );
        assert!(!paths[3].exists(), "unreferenced witness must be swept");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn payload_file_budget_stops_a_run_before_it_floods_the_filesystem() {
        // Companion to the byte budget: file count is the number bytes
        // cannot stand in for.
        let task = artifact_test_task("ArtifactFileBudget");
        let root = artifact_test_root("file_budget");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).payload_file_budget(Some(1)),
        )
        .unwrap();

        store
            .publish(ArtifactKind::RuntimeTrace, vec![b'x'; 8].into_boxed_slice())
            .expect("first payload file fits the allowance");
        let overflow = store
            .publish(ArtifactKind::RuntimeTrace, vec![b'x'; 8].into_boxed_slice())
            .expect_err("second payload file must exceed the 1-file allowance");
        assert_eq!(overflow.kind(), FailureKind::PublicationFailure);
        assert_eq!(overflow.scope(), FailureScope::RunGlobal);

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn streamed_payloads_charge_before_write_and_latch_across_scopes() {
        let task = artifact_test_task("ArtifactStreamBudget");
        let root = artifact_test_root("stream_budget");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).payload_budget(Some(64)),
        )
        .unwrap();
        let (stage, mut writer) = store.begin_staged_payload().unwrap();
        writer.write_all(&[b's'; 32]).unwrap();
        assert_eq!(fs::metadata(&stage.staging).unwrap().len(), 32);
        let other = store.scoped(ScopeTag::named("stderr"));
        let (other_stage, mut other_writer) = other.begin_staged_payload().unwrap();
        other_writer.write_all(&[b'x'; 32]).unwrap();
        assert!(writer.write_all(b"x").is_err());
        assert_eq!(fs::metadata(&stage.staging).unwrap().len(), 32);
        assert!(other_writer.write_all(b"x").is_err());
        drop(writer);
        drop(other_writer);
        assert_eq!(
            stage.commit(ArtifactKind::Proof).unwrap_err().scope(),
            FailureScope::RunGlobal
        );
        drop(other_stage);
        assert!(store.begin_staged_payload().is_err());
        drop(other);
        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn concurrent_scoped_writers_reserve_one_shared_boundary() {
        let task = artifact_test_task("ConcurrentArtifactBudget");
        let root = artifact_test_root("concurrent_budget");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).payload_budget(Some(4)),
        )
        .unwrap();
        let barrier = Arc::new(std::sync::Barrier::new(2));
        let mut threads = Vec::new();
        for name in ["stdout", "stderr"] {
            let (stage, mut writer) = store
                .scoped(ScopeTag::named(name))
                .begin_staged_payload()
                .unwrap();
            let barrier = Arc::clone(&barrier);
            threads.push(std::thread::spawn(move || {
                barrier.wait();
                let written = writer.write_all(b"1234").is_ok();
                drop(writer);
                let length = fs::metadata(&stage.staging).unwrap().len();
                (stage, written, length)
            }));
        }
        let results = threads
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(results.iter().filter(|(_, success, _)| *success).count(), 1);
        assert_eq!(results.iter().map(|(_, _, length)| length).sum::<u64>(), 4);
        assert_eq!(
            store
                .backend
                .required_bytes_published
                .load(Ordering::Relaxed),
            4
        );
        assert_eq!(
            store.resource_failure().unwrap().scope(),
            FailureScope::RunGlobal
        );
        drop(results);
        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn payload_counter_overflow_latches_before_a_write() {
        let task = artifact_test_task("ArtifactOverflow");
        let root = artifact_test_root("budget_overflow");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).payload_budget(Some(u64::MAX)),
        )
        .unwrap();
        let (stage, mut writer) = store.begin_staged_payload().unwrap();
        store
            .backend
            .required_bytes_published
            .store(u64::MAX, Ordering::Relaxed);
        assert!(writer.write_all(b"x").is_err());
        assert_eq!(fs::metadata(&stage.staging).unwrap().len(), 0);
        assert_eq!(
            store
                .backend
                .required_bytes_published
                .load(Ordering::Relaxed),
            u64::MAX
        );
        drop(writer);
        drop(stage);
        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn streamed_commit_does_not_double_charge_and_dropped_stage_is_not_refunded() {
        let task = artifact_test_task("ArtifactStreamExact");
        let root = artifact_test_root("stream_exact");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).payload_budget(Some(8)),
        )
        .unwrap();
        let (stage, mut writer) = store.begin_staged_payload().unwrap();
        writer.write_all(b"1234").unwrap();
        drop(writer);
        stage.commit(ArtifactKind::Proof).unwrap();
        let (stage, mut writer) = store.begin_staged_payload().unwrap();
        writer.write_all(b"5678").unwrap();
        drop(writer);
        drop(stage);
        let (stage, mut writer) = store.begin_staged_payload().unwrap();
        assert!(writer.write_all(b"x").is_err());
        drop(writer);
        drop(stage);
        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn scoped_store_joins_registered_work_before_owner_settlement() {
        let task = artifact_test_task("ArtifactOwnerJoin");
        let root = artifact_test_root("owner_join");
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let registration = store.register_owned_work().unwrap();

        {
            let waiting = store.wait_for_background_work();
            tokio::pin!(waiting);
            assert!(
                tokio::time::timeout(std::time::Duration::from_millis(10), &mut waiting)
                    .await
                    .is_err()
            );
            registration.discharge();
            tokio::time::timeout(std::time::Duration::from_secs(1), waiting)
                .await
                .expect("scoped store did not observe discharged work");
        }

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn failed_lifetime_sentinel_does_not_deadlock_background_join() {
        let task = artifact_test_task("ArtifactLifetimeSentinel");
        let root = artifact_test_root("lifetime_sentinel");
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let lifetime = store.register_lifetime_owned_work().unwrap();

        tokio::time::timeout(
            std::time::Duration::from_secs(1),
            store.wait_for_background_work(),
        )
        .await
        .expect("a lifetime failure sentinel is not joinable background work");
        drop(store);
        let failure = owner
            .settle()
            .expect_err("an undisclosed lifetime cleanup failure must fail settlement");
        assert!(
            failure
                .detail()
                .is_some_and(|detail| detail.contains("explicitly joined"))
        );
        lifetime.discharge();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn unwinding_query_worker_guard_publishes_failure_to_waiters() {
        let task = artifact_test_task("ArtifactPanickedQueryWork");
        let root = artifact_test_root("panicked_query_work");
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let fingerprint = QueryFingerprint {
            digest: Arc::from("worker-panic"),
            byte_len: 5,
        };
        let publication = match store
            .backend
            .select_query(fingerprint, Arc::from(&b"query"[..]))
            .unwrap()
        {
            QuerySelection::Publish(publication) => publication,
            _ => panic!("fresh query must select publication"),
        };
        let waiter = Arc::clone(&publication);
        let guard = store.begin_query_publication_work(publication).unwrap();
        let worker = std::thread::spawn(move || {
            let _guard = guard;
            panic!("adversarial query worker panic");
        });
        assert!(worker.join().is_err());

        let error = tokio::time::timeout(std::time::Duration::from_secs(1), waiter.wait())
            .await
            .expect("panicked worker stranded query waiter")
            .unwrap_err();
        assert_eq!(error.scope(), FailureScope::RunGlobal);
        assert!(store.backend.query_publications.lock().unwrap().is_empty());
        assert_eq!(store.backend.active_owned_work.load(Ordering::Acquire), 0);

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn deferred_required_builder_and_publication_share_one_blocking_worker() {
        let task = artifact_test_task("ArtifactDeferredRequired");
        let root = artifact_test_root("deferred_required");
        let (owner, store) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let caller_thread = std::thread::current().id();
        let builder_thread = Arc::new(Mutex::new(None));
        let observed = Arc::clone(&builder_thread);

        let reference = store
            .publish_required_deferred_async(ArtifactKind::RuntimeTrace, move || {
                *observed.lock().unwrap() = Some(std::thread::current().id());
                Ok(Arc::from(&b"deferred-required"[..]))
            })
            .await
            .unwrap();

        assert_ne!(*builder_thread.lock().unwrap(), Some(caller_thread));
        assert_eq!(
            fs::read(store.resolve(reference).unwrap().path()).unwrap(),
            b"deferred-required"
        );
        assert_eq!(store.diagnostics().required_payloads_published, 1);

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn deferred_history_builder_runs_on_history_writer() {
        let task = artifact_test_task("ArtifactDeferredHistory");
        let root = artifact_test_root("deferred_history");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).maintenance_history(true, true),
        )
        .unwrap();
        let builder_thread = Arc::new(Mutex::new(None));
        let observed = Arc::clone(&builder_thread);

        store
            .append_maintenance_history_deferred_async(move || {
                *observed.lock().unwrap() = std::thread::current().name().map(str::to_owned);
                Ok((serde_json::json!({"event":"deferred"}), vec![17]))
            })
            .await
            .unwrap();
        store.settle_maintenance_history_async().await.unwrap();
        assert_eq!(
            builder_thread.lock().unwrap().as_deref(),
            Some("whiel-history-writer")
        );

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn concurrent_history_boundaries_each_wait_for_writer_acknowledgement() {
        let task = artifact_test_task("ArtifactConcurrentHistoryBoundaries");
        let root = artifact_test_root("concurrent_history_boundaries");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root)
                .maintenance_history(true, true)
                .maintenance_history_queue_capacity(2),
        )
        .unwrap();
        store
            .append_maintenance_history_value(serde_json::json!({"event":"baseline"}), &[31])
            .unwrap();
        let shared = Arc::clone(&store.backend.history.as_ref().unwrap().shared);
        let (entered_sender, entered_receiver) = mpsc::channel();
        let (release_sender, release_receiver) = mpsc::channel();
        shared.fault_injection.lock().unwrap().barrier_pause = Some(HistoryBarrierPause {
            entered: entered_sender,
            release: release_receiver,
        });

        let first_store = store.clone();
        let first = std::thread::spawn(move || first_store.settle_maintenance_history());
        entered_receiver
            .recv_timeout(std::time::Duration::from_secs(2))
            .expect("first boundary did not reach the paused writer");

        let second_store = store.clone();
        let second = std::thread::spawn(move || {
            second_store.query_maintenance_history(31, MaintenanceHistoryCursor::start(), 1)
        });
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while shared.barrier_commands_sent.load(Ordering::Acquire) < 2
            && std::time::Instant::now() < deadline
        {
            std::thread::yield_now();
        }
        assert_eq!(
            shared.barrier_commands_sent.load(Ordering::Acquire),
            2,
            "the second boundary incorrectly reused an unacknowledged barrier"
        );
        assert!(
            !second.is_finished(),
            "the second boundary returned before writer acknowledgement"
        );

        release_sender.send(()).unwrap();
        first.join().unwrap().unwrap();
        let page = second.join().unwrap().unwrap();
        assert_eq!(page.records.len(), 1);

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn history_writer_panic_fails_and_wakes_strict_producers() {
        let task = artifact_test_task("ArtifactHistoryPanic");
        let root = artifact_test_root("history_panic");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root)
                .maintenance_history(true, true)
                .maintenance_history_queue_capacity(1),
        )
        .unwrap();
        let (entered_sender, entered_receiver) = mpsc::channel();
        let (release_sender, release_receiver) = mpsc::channel();
        let first_store = store.clone();
        let first = tokio::spawn(async move {
            first_store
                .append_maintenance_history_deferred_async(move || {
                    entered_sender.send(()).unwrap();
                    release_receiver.recv().unwrap();
                    panic!("adversarial deferred-history builder panic");
                })
                .await
        });
        assert!(first.await.unwrap().is_ok());
        tokio::task::spawn_blocking(move || entered_receiver.recv())
            .await
            .unwrap()
            .unwrap();

        let second_store = store.clone();
        let second = tokio::spawn(async move {
            second_store
                .append_maintenance_history_deferred_async(|| {
                    Ok((serde_json::json!({"event":"blocked"}), vec![2]))
                })
                .await
        });
        tokio::time::timeout(std::time::Duration::from_secs(2), async {
            while store.backend.active_owned_work.load(Ordering::Acquire) == 0 {
                tokio::task::yield_now().await;
            }
        })
        .await
        .expect("strict producer did not register its blocked submission");
        assert!(!second.is_finished());
        release_sender.send(()).unwrap();
        let second_result = tokio::time::timeout(std::time::Duration::from_secs(2), second)
            .await
            .expect("panicked history writer stranded a strict producer")
            .unwrap();
        assert!(second_result.is_err());
        assert_eq!(
            store.diagnostics().history_worker_state,
            HistoryWorkerState::Failed
        );
        assert_eq!(store.diagnostics().history_queue_depth, 0);

        drop(store);
        assert!(owner.settle().is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn failed_index_append_rolls_back_body_and_every_clause_index() {
        let task = artifact_test_task("ArtifactTransactionalIndex");
        let root = artifact_test_root("transactional_index");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).maintenance_history(true, true),
        )
        .unwrap();
        store
            .append_maintenance_history_value(serde_json::json!({"event":"baseline"}), &[17, 19])
            .unwrap();
        store.settle_maintenance_history_async().await.unwrap();

        let history_root = store.backend.run_root.join("history");
        let body = history_root.join("maintenance.jsonl");
        let first_index = history_root.join("by-clause/clause-00000000000000000017.idx");
        let second_index = history_root.join("by-clause/clause-00000000000000000019.idx");
        let original_lengths = [
            fs::metadata(&body).unwrap().len(),
            fs::metadata(&first_index).unwrap().len(),
            fs::metadata(&second_index).unwrap().len(),
        ];
        store
            .backend
            .history
            .as_ref()
            .unwrap()
            .shared
            .fault_injection
            .lock()
            .unwrap()
            .fail_index_after = Some(1);

        store
            .append_maintenance_history_value(
                serde_json::json!({"event":"must-rollback"}),
                &[17, 19],
            )
            .unwrap();
        let error = store.settle_maintenance_history_async().await.unwrap_err();
        assert!(
            error
                .detail()
                .is_some_and(|detail| detail.contains("injected short"))
        );
        assert_eq!(
            [
                fs::metadata(&body).unwrap().len(),
                fs::metadata(&first_index).unwrap().len(),
                fs::metadata(&second_index).unwrap().len(),
            ],
            original_lengths
        );
        assert_eq!(store.diagnostics().history_records_written, 1);

        drop(store);
        assert!(owner.settle().is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn short_body_append_rolls_back_tentative_clause_indexes() {
        let task = artifact_test_task("ArtifactTransactionalBody");
        let root = artifact_test_root("transactional_body");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).maintenance_history(true, true),
        )
        .unwrap();
        store
            .append_maintenance_history_value(serde_json::json!({"event":"baseline"}), &[23])
            .unwrap();
        store.settle_maintenance_history_async().await.unwrap();

        let history_root = store.backend.run_root.join("history");
        let body = history_root.join("maintenance.jsonl");
        let index = history_root.join("by-clause/clause-00000000000000000023.idx");
        let original_lengths = [
            fs::metadata(&body).unwrap().len(),
            fs::metadata(&index).unwrap().len(),
        ];
        store
            .backend
            .history
            .as_ref()
            .unwrap()
            .shared
            .fault_injection
            .lock()
            .unwrap()
            .fail_main_after_prefix = true;

        store
            .append_maintenance_history_value(serde_json::json!({"event":"must-rollback"}), &[23])
            .unwrap();
        let error = store.settle_maintenance_history_async().await.unwrap_err();
        assert!(
            error
                .detail()
                .is_some_and(|detail| detail.contains("injected short"))
        );
        assert_eq!(
            [
                fs::metadata(&body).unwrap().len(),
                fs::metadata(&index).unwrap().len(),
            ],
            original_lengths
        );
        assert_eq!(store.diagnostics().history_records_written, 1);

        drop(store);
        assert!(owner.settle().is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn best_effort_failure_preserves_its_committed_queryable_prefix() {
        let task = artifact_test_task("ArtifactBestEffortPrefix");
        let root = artifact_test_root("best_effort_prefix");
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&root).maintenance_history(true, false),
        )
        .unwrap();
        store
            .append_maintenance_history_value(serde_json::json!({"event":"baseline"}), &[31])
            .unwrap();
        store.backend.flush_history_for_query().unwrap();
        let before = store
            .query_maintenance_history(31, MaintenanceHistoryCursor::start(), 8)
            .unwrap();
        assert_eq!(before.records.len(), 1);

        store
            .backend
            .history
            .as_ref()
            .unwrap()
            .shared
            .fault_injection
            .lock()
            .unwrap()
            .fail_main_after_prefix = true;
        store
            .append_maintenance_history_value(serde_json::json!({"event":"must-rollback"}), &[37])
            .unwrap();
        // Best-effort queries observe the writer failure, disable future
        // writes, and retain the already committed prefix.
        let after = store
            .query_maintenance_history(31, MaintenanceHistoryCursor::start(), 8)
            .unwrap();
        assert_eq!(after.records, before.records);
        assert_eq!(store.diagnostics().history_records_written, 1);
        assert_eq!(
            store.diagnostics().history_worker_state,
            HistoryWorkerState::Failed
        );
        assert!(
            store
                .query_maintenance_history(37, MaintenanceHistoryCursor::start(), 8)
                .unwrap()
                .records
                .is_empty()
        );

        drop(store);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn history_query_treats_an_unterminated_sidecar_tail_as_tentative() {
        let root = artifact_test_root("tentative_sidecar_tail");
        let history = root.join("history");
        fs::create_dir_all(history.join("by-clause")).unwrap();
        fs::write(history.join("maintenance.jsonl"), b"").unwrap();
        fs::write(
            history.join("by-clause/clause-00000000000000000029.idx"),
            b"0 37",
        )
        .unwrap();

        let page = read_history_page(&root, 29, MaintenanceHistoryCursor::start(), 1).unwrap();
        assert!(page.records.is_empty());
        assert_eq!(page.next_cursor, Some(MaintenanceHistoryCursor::start()));

        fs::remove_dir_all(root).unwrap();
    }

    /// Pass 7.5g review, finding 6: a manifest whose `format_version` this
    /// host does not understand fails closed rather than answering "this
    /// run declared no policy".
    ///
    /// The lower version is the case that matters. A v1 manifest carries no
    /// `run_configuration` member at all, so reading it leniently would
    /// report a run bound to no policy — which is exactly the answer a
    /// caller uses to decide that any policy is compatible with it.
    #[test]
    fn a_manifest_of_another_format_version_is_refused_rather_than_read() {
        let root = artifact_test_root("manifest_version");
        fs::create_dir_all(&root).unwrap();
        let manifest = root.join("manifest.json");
        let policy = serde_json::json!({"kind": "whiel_framework_ii_run_configuration"});

        let write = |value: serde_json::Value| {
            fs::write(&manifest, serde_json::to_vec(&value).unwrap()).unwrap();
        };

        // The current version reads back exactly what was bound, and the
        // absence of a policy is `None` rather than an error.
        write(serde_json::json!({
            "format_version": MANIFEST_FORMAT_VERSION,
            "run_configuration": policy,
        }));
        assert_eq!(read_run_configuration(&root).unwrap(), Some(policy.clone()));
        write(serde_json::json!({
            "format_version": MANIFEST_FORMAT_VERSION,
            "run_configuration": serde_json::Value::Null,
        }));
        assert_eq!(read_run_configuration(&root).unwrap(), None);

        for stale in [
            serde_json::json!({"format_version": MANIFEST_FORMAT_VERSION - 1}),
            serde_json::json!({
                "format_version": MANIFEST_FORMAT_VERSION + 1,
                "run_configuration": policy,
            }),
            serde_json::json!({"format_version": "two", "run_configuration": policy}),
            serde_json::json!({"run_configuration": policy}),
        ] {
            write(stale.clone());
            let report = read_run_configuration(&root)
                .expect_err("a manifest of another format version is refused");
            assert_eq!(report.kind(), FailureKind::ManifestFailure);
            assert!(
                report
                    .detail()
                    .is_some_and(|detail| detail.contains("format_version")),
                "{report:?} for {stale}"
            );
        }

        fs::remove_dir_all(&root).unwrap();
    }

    fn artifact_test_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "whiel_artifact_{name}_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    fn artifact_test_task(name: &str) -> SynthesisTask {
        SynthesisTask::from_json(
            &format!(
                r#"{{
                  "format_version":3,"semantic_version":1,"encoding_version":1,
                  "identity":{{"canonical_id":"{name}","module":"Whiel.Test.{name}","namespace":"Whiel.Test.{name}","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"}},
                  "schema":{{"expression":"Whiel.Test.{name}.programSchema","display":"schema"}},
                  "original":{{"pre":{{"expression":"Whiel.Test.{name}.inputPre","display":"true"}},"command":{{"expression":"Whiel.Test.{name}.inputCmd","display":"SKIP"}},"post":{{"expression":"Whiel.Test.{name}.inputPost","display":"true"}}}},
                  "preprocessed":{{"pre":{{"expression":"Whiel.Test.{name}.inputPreproc.loopPre","display":"true"}},"command":{{"expression":"Whiel.Test.{name}.inputPreproc.loopCmd","display":"SKIP"}},"post":{{"expression":"Whiel.Test.{name}.inputPreproc.loopPost","display":"true"}}}},
                  "preprocessing_evidence":{{"expression":"Whiel.Test.{name}.inputPreproc"}},
                  "solver":{{"schema_relations":[{{"key":"rel:R:0","arity":1}}],"task_constants":[],
                    "preprocessed_pre":{{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.{name}.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.{name}.inputPreproc.loopPre_noBound","constants":[],"relations":["rel:R:0"]}},
                    "preprocessed_post":{{"source_id":"task.preprocessed_post","expression":"Whiel.Test.{name}.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.{name}.inputPreproc.loopPost_noBound","constants":[],"relations":["rel:R:0"]}},
                    "loop_guard":{{"source_id":"task.loop_guard","constants":[],"relations":["rel:R:0"]}},
                    "negated_loop_guard":{{"source_id":"task.negated_loop_guard","constants":[],"relations":["rel:R:0"]}}}}
                }}"#
            ),
        )
        .unwrap()
    }
}

//! Lossless proved-W handoff from the CEX lane to the INV lane.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

use crate::artifact::{ArtifactKind, ArtifactRef, BackendId};
use crate::encoding::PreparedWLayerBundle;
use crate::houdini::{ClauseFormula, ClauseId};
use crate::task::TaskIdentity;

static NEXT_W_CHANNEL_ID: AtomicU64 = AtomicU64::new(0);

// ------------------------------------------------------------
// Published And Admitted Entries
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct ProvedWEntry {
    index: u64,
    formula: ClauseFormula,
    /// Every production entry carries its complete CEX-owned bundle. Unit
    /// tests may use the formula-only constructor below to isolate channel
    /// behavior from the Lean worker.
    bundle: Option<Arc<PreparedWLayerBundle>>,
    initialization_evidence: ArtifactRef,
}

impl ProvedWEntry {
    /// Construct one production publication from the complete validated W
    /// bundle. No caller can publish a reconstructed formula by index alone.
    #[allow(dead_code)] // Phase 4C connects the production CEX-to-INV publisher.
    pub(crate) fn from_bundle(
        bundle: Arc<PreparedWLayerBundle>,
        initialization_evidence: ArtifactRef,
    ) -> Result<Self, &'static str> {
        if initialization_evidence.kind() != ArtifactKind::InitializationCheck {
            return Err("a proved W entry requires initialization evidence");
        }
        let index = bundle.index();
        let formula = ClauseFormula::from_validated_w_bundle(&bundle);
        Ok(Self {
            index,
            formula,
            bundle: Some(bundle),
            initialization_evidence,
        })
    }

    /// Construct a formula-only publication for isolated channel tests.
    #[cfg(test)]
    pub(crate) fn new(
        index: u64,
        formula: ClauseFormula,
        initialization_evidence: ArtifactRef,
    ) -> Result<Self, &'static str> {
        if initialization_evidence.kind() != ArtifactKind::InitializationCheck {
            return Err("a proved W entry requires initialization evidence");
        }
        Ok(Self {
            index,
            formula,
            bundle: None,
            initialization_evidence,
        })
    }

    pub fn index(&self) -> u64 {
        self.index
    }

    pub fn formula(&self) -> &ClauseFormula {
        &self.formula
    }

    pub(crate) fn bundle(&self) -> Option<&PreparedWLayerBundle> {
        self.bundle.as_deref()
    }

    pub fn initialization_evidence(&self) -> ArtifactRef {
        self.initialization_evidence
    }
}

#[derive(Clone, Debug)]
pub struct AdmittedWEntry {
    clause_id: ClauseId,
    initialization_evidence: ArtifactRef,
}

impl AdmittedWEntry {
    pub fn clause_id(&self) -> ClauseId {
        self.clause_id
    }

    pub fn initialization_evidence(&self) -> ArtifactRef {
        self.initialization_evidence
    }
}

#[derive(Debug, Default)]
pub struct WAdmissionIndex {
    by_index: HashMap<u64, AdmittedWEntry>,
    by_clause: HashMap<ClauseId, HashSet<u64>>,
    support_provenance: HashMap<(u64, u64), ArtifactRef>,
}

impl WAdmissionIndex {
    pub fn get(&self, index: u64) -> Option<&AdmittedWEntry> {
        self.by_index.get(&index)
    }

    pub fn indices_for_clause(&self, clause: ClauseId) -> Option<&HashSet<u64>> {
        self.by_clause.get(&clause)
    }

    pub fn len(&self) -> usize {
        self.by_index.len()
    }

    pub fn is_empty(&self) -> bool {
        self.by_index.is_empty()
    }

    pub(crate) fn insert(
        &mut self,
        index: u64,
        clause_id: ClauseId,
        initialization_evidence: ArtifactRef,
    ) -> Result<bool, &'static str> {
        if let Some(existing) = self.by_index.get(&index) {
            return if existing.clause_id == clause_id
                && existing.initialization_evidence == initialization_evidence
            {
                Ok(false)
            } else {
                Err("one W index was admitted with conflicting provenance")
            };
        }
        self.by_index.insert(
            index,
            AdmittedWEntry {
                clause_id,
                initialization_evidence,
            },
        );
        self.by_clause.entry(clause_id).or_default().insert(index);
        Ok(true)
    }

    pub(crate) fn admitted_clauses(&self) -> HashSet<ClauseId> {
        self.by_clause.keys().copied().collect()
    }

    pub(crate) fn support_provenance(
        &self,
        source_index: u64,
        target_index: u64,
    ) -> Option<ArtifactRef> {
        self.support_provenance
            .get(&(source_index, target_index))
            .copied()
    }

    pub(crate) fn reserve_support_provenance(&mut self) -> Result<(), &'static str> {
        self.support_provenance
            .try_reserve(1)
            .map_err(|_| "W support-provenance index capacity is exhausted")
    }

    pub(crate) fn record_support_provenance(
        &mut self,
        source_index: u64,
        target_index: u64,
        provenance: ArtifactRef,
    ) -> Result<(), &'static str> {
        match self
            .support_provenance
            .insert((source_index, target_index), provenance)
        {
            None => Ok(()),
            Some(existing) if existing == provenance => Ok(()),
            Some(existing) => {
                self.support_provenance
                    .insert((source_index, target_index), existing);
                Err("one W support edge has conflicting theorem provenance")
            }
        }
    }
}

// ------------------------------------------------------------
// Linearizable Peek-And-Acknowledge Channel
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct ProvedWBatch {
    channel_id: u64,
    task: TaskIdentity,
    backend: BackendId,
    entries: Arc<[ProvedWEntry]>,
}

impl ProvedWBatch {
    pub fn entries(&self) -> &[ProvedWEntry] {
        &self.entries
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Result of one atomic sparse proved-W publication.
///
/// `NoChange` means that the batch was empty or every exact entry was already
/// pending or acknowledged. `ReceiverClosed` is a benign delivery outcome:
/// the CEX lane retains the durable proof independently and must keep running.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WPublicationOutcome {
    Published { new_entries: usize },
    NoChange,
    ReceiverClosed,
}

#[derive(Debug)]
struct ChannelState {
    pending: BTreeMap<u64, ProvedWEntry>,
    acknowledged: BTreeMap<u64, PublicationFingerprint>,
    sender_count: usize,
    sender_open: bool,
    receiver_open: bool,
}

#[derive(Debug)]
struct ChannelInner {
    id: u64,
    task: TaskIdentity,
    backend: BackendId,
    state: Mutex<ChannelState>,
}

#[derive(Debug)]
pub struct WProofSender {
    inner: Arc<ChannelInner>,
}

#[derive(Debug)]
pub struct WProofReceiver {
    inner: Arc<ChannelInner>,
}

#[derive(Clone, Debug)]
struct PublicationFingerprint {
    formula_identity: Arc<str>,
    bundle_identity: Option<Arc<str>>,
    initialization_evidence: ArtifactRef,
}

pub fn create_w_proof_channel(
    task: &TaskIdentity,
    backend: BackendId,
) -> (WProofSender, WProofReceiver) {
    let id = NEXT_W_CHANNEL_ID.fetch_add(1, Ordering::Relaxed);
    let inner = Arc::new(ChannelInner {
        id,
        task: task.clone(),
        backend,
        state: Mutex::new(ChannelState {
            pending: BTreeMap::new(),
            acknowledged: BTreeMap::new(),
            sender_count: 1,
            sender_open: true,
            receiver_open: true,
        }),
    });
    (
        WProofSender {
            inner: Arc::clone(&inner),
        },
        WProofReceiver { inner },
    )
}

impl Clone for WProofSender {
    fn clone(&self) -> Self {
        let mut state = lock(&self.inner.state);
        state.sender_count = state
            .sender_count
            .checked_add(1)
            .expect("proved W sender clone count is exhausted");
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl WProofSender {
    pub(crate) fn matches_authority(&self, task: &TaskIdentity, backend: BackendId) -> bool {
        &self.inner.task == task && self.inner.backend == backend
    }

    /// Publish one entry through the compatibility API.
    ///
    /// A closed receiver is a benign no-change result. New code that needs to
    /// distinguish that case should use [`Self::publish_batch`].
    pub fn publish(&self, entry: ProvedWEntry) -> Result<bool, &'static str> {
        match self.publish_batch(std::iter::once(entry))? {
            WPublicationOutcome::Published { .. } => Ok(true),
            WPublicationOutcome::NoChange | WPublicationOutcome::ReceiverClosed => Ok(false),
        }
    }

    /// Atomically publish one possibly sparse batch under one channel lock.
    ///
    /// The method validates the complete batch before inserting any entry.
    /// Exact retries are idempotent even after acknowledgement. A conflicting
    /// entry for one index rejects the whole batch.
    pub fn publish_batch(
        &self,
        entries: impl IntoIterator<Item = ProvedWEntry>,
    ) -> Result<WPublicationOutcome, &'static str> {
        let entries = entries.into_iter().collect::<Vec<_>>();
        let mut state = lock(&self.inner.state);
        if !state.sender_open {
            return Err("the proved W sender is closed");
        }
        if !state.receiver_open {
            return Ok(WPublicationOutcome::ReceiverClosed);
        }

        let mut batch = BTreeMap::new();
        for entry in entries {
            if entry.formula.task_identity() != &self.inner.task
                || entry.initialization_evidence.backend_id() != self.inner.backend
            {
                return Err("proved W publication belongs to another task or artifact backend");
            }
            match batch.get(&entry.index) {
                Some(existing) if !same_entry(existing, &entry) => {
                    return Err("one W batch contains conflicting proof data for an index");
                }
                Some(_) => {}
                None => {
                    batch.insert(entry.index, entry);
                }
            }
        }

        let mut fresh = Vec::new();
        for (index, entry) in &batch {
            if let Some(existing) = state.pending.get(index) {
                if !same_entry(existing, entry) {
                    return Err("one pending W index has conflicting proof data");
                }
                continue;
            }
            if let Some(existing) = state.acknowledged.get(index) {
                if !same_fingerprint(existing, entry) {
                    return Err("one acknowledged W index has conflicting proof data");
                }
                continue;
            }
            fresh.push(*index);
        }

        if fresh.is_empty() {
            return Ok(WPublicationOutcome::NoChange);
        }
        for index in &fresh {
            let entry = batch
                .remove(index)
                .expect("fresh W publication was prevalidated in this batch");
            state.pending.insert(*index, entry);
        }
        Ok(WPublicationOutcome::Published {
            new_entries: fresh.len(),
        })
    }

    pub fn close(&self) {
        lock(&self.inner.state).sender_open = false;
    }
}

impl WProofReceiver {
    pub(crate) fn matches_authority(&self, task: &TaskIdentity, backend: BackendId) -> bool {
        &self.inner.task == task && self.inner.backend == backend
    }

    pub fn peek_proved_batch(&self) -> Option<ProvedWBatch> {
        let state = lock(&self.inner.state);
        if state.pending.is_empty() {
            return None;
        }
        Some(ProvedWBatch {
            channel_id: self.inner.id,
            task: self.inner.task.clone(),
            backend: self.inner.backend,
            entries: state.pending.values().cloned().collect::<Vec<_>>().into(),
        })
    }

    pub(crate) fn validate_batch(&self, batch: &ProvedWBatch) -> bool {
        batch.channel_id == self.inner.id
            && batch.task == self.inner.task
            && batch.backend == self.inner.backend
    }

    pub fn acknowledge_proved_batch(&self, batch: &ProvedWBatch) -> Result<(), &'static str> {
        if !self.validate_batch(batch) {
            return Err("proved W acknowledgement belongs to another channel");
        }
        let mut state = lock(&self.inner.state);

        // Validate the full acknowledgement before removing any pending
        // entry. This keeps a conflicting acknowledgement atomic.
        for entry in batch.entries.iter() {
            match state.pending.get(&entry.index) {
                Some(current) if same_entry(current, entry) => {}
                Some(_) => return Err("pending W entry changed before acknowledgement"),
                None => match state.acknowledged.get(&entry.index) {
                    Some(current) if same_fingerprint(current, entry) => {}
                    Some(_) => {
                        return Err("acknowledged W entry changed before acknowledgement");
                    }
                    None => return Err("acknowledged W entry is not owned by this channel"),
                },
            }
        }
        for entry in batch.entries.iter() {
            if let Some(pending) = state.pending.remove(&entry.index) {
                state
                    .acknowledged
                    .insert(entry.index, PublicationFingerprint::from_entry(&pending));
            }
        }
        Ok(())
    }

    pub fn is_closed_and_empty(&self) -> bool {
        let state = lock(&self.inner.state);
        !state.sender_open && state.pending.is_empty()
    }
}

impl Drop for WProofSender {
    fn drop(&mut self) {
        let mut state = lock(&self.inner.state);
        debug_assert!(state.sender_count > 0);
        state.sender_count -= 1;
        if state.sender_count == 0 {
            state.sender_open = false;
        }
    }
}

impl Drop for WProofReceiver {
    fn drop(&mut self) {
        // Leave prior pending publications intact. They remain durable until
        // the final sender is dropped, while every later publication observes
        // a benign closed-receiver outcome.
        lock(&self.inner.state).receiver_open = false;
    }
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn same_bundle(
    left: Option<&Arc<PreparedWLayerBundle>>,
    right: Option<&Arc<PreparedWLayerBundle>>,
) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => Arc::ptr_eq(left, right),
        (None, None) => true,
        _ => false,
    }
}

fn same_entry(left: &ProvedWEntry, right: &ProvedWEntry) -> bool {
    left.index == right.index
        && left.formula == right.formula
        && same_bundle(left.bundle.as_ref(), right.bundle.as_ref())
        && left.initialization_evidence == right.initialization_evidence
}

impl PublicationFingerprint {
    fn from_entry(entry: &ProvedWEntry) -> Self {
        Self {
            formula_identity: entry.formula.identity_arc(),
            bundle_identity: entry.bundle.as_ref().map(|bundle| bundle.identity_arc()),
            initialization_evidence: entry.initialization_evidence,
        }
    }
}

fn same_fingerprint(fingerprint: &PublicationFingerprint, entry: &ProvedWEntry) -> bool {
    fingerprint.formula_identity.as_ref() == entry.formula.identity()
        && fingerprint.bundle_identity.as_deref()
            == entry.bundle.as_ref().map(|bundle| bundle.identity())
        && fingerprint.initialization_evidence == entry.initialization_evidence
}

#[cfg(test)]
mod tests {
    use crate::artifact::{ArtifactKind, ArtifactStoreConfig, new_artifact_store};
    use crate::encoding::QfSolverSource;
    use crate::houdini::ClauseFormula;
    use crate::task::SynthesisTask;

    use super::*;

    fn task() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version": 3,
              "semantic_version": 1,
              "encoding_version": 1,
              "identity": {
                "canonical_id": "WChannel",
                "module": "Benchmark.WChannel.Input",
                "namespace": "Whiel.Benchmark.WChannel",
                "source_sha256": "6fe56e9493eefa68d69085d1602adda3a0d522d964f1a8bf6ef3996f08cd3195"
              },
              "schema": {"expression":"Whiel.Benchmark.WChannel.programSchema","display":"{}"},
              "original": {
                "pre":{"expression":"Whiel.Benchmark.WChannel.inputPre","display":"true"},
                "command":{"expression":"Whiel.Benchmark.WChannel.inputCmd","display":"SKIP"},
                "post":{"expression":"Whiel.Benchmark.WChannel.inputPost","display":"true"}
              },
              "preprocessed": {
                "pre":{"expression":"Whiel.Benchmark.WChannel.inputPreproc.loopPre","display":"true"},
                "command":{"expression":"Whiel.Benchmark.WChannel.inputPreproc.loopCmd","display":"WHILE true DO SKIP END"},
                "post":{"expression":"Whiel.Benchmark.WChannel.inputPreproc.loopPost","display":"true"}
              },
              "preprocessing_evidence":{"expression":"Whiel.Benchmark.WChannel.inputPreproc"},
              "solver": {
                "schema_relations": [], "task_constants": [],
                "preprocessed_pre": {"source_id":"task.preprocessed_pre","expression":"Whiel.Benchmark.WChannel.inputPreproc.loopPre","no_bound_expression":"Whiel.Benchmark.WChannel.inputPreproc.loopPre_noBound","constants":[],"relations":[]},
                "preprocessed_post": {"source_id":"task.preprocessed_post","expression":"Whiel.Benchmark.WChannel.inputPreproc.loopPost","no_bound_expression":"Whiel.Benchmark.WChannel.inputPreproc.loopPost_noBound","constants":[],"relations":[]},
                "loop_guard": {"source_id":"task.loop_guard","constants":[],"relations":[]},
                "negated_loop_guard": {"source_id":"task.negated_loop_guard","constants":[],"relations":[]}
              }
            }"#,
        )
        .expect("channel fixture task")
    }

    fn entry(
        task: &SynthesisTask,
        artifacts: &crate::artifact::ArtifactStore,
        index: u64,
    ) -> ProvedWEntry {
        let source =
            QfSolverSource::new(task, format!("test.w.{index}"), Vec::new(), Vec::new()).unwrap();
        let formula = ClauseFormula::from_trusted_lean_source(
            format!("W({index})"),
            crate::encoding::SolverBodySource::QuantifierFree(source),
        )
        .unwrap();
        let evidence = artifacts
            .publish(
                ArtifactKind::InitializationCheck,
                format!("proof-{index}").into_bytes().into_boxed_slice(),
            )
            .unwrap();
        ProvedWEntry::new(index, formula, evidence).unwrap()
    }

    #[test]
    fn sparse_batch_publication_is_atomic_and_idempotent_after_acknowledgement() {
        let task = task();
        let directory =
            std::env::temp_dir().join(format!("whiel-phase4c-channel-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(directory.join("artifacts")))
                .unwrap();
        let (sender, receiver) = create_w_proof_channel(task.identity(), artifacts.backend_id());
        let entries = [entry(&task, &artifacts, 7), entry(&task, &artifacts, 2)];
        assert_eq!(
            sender.publish_batch(entries.clone()).unwrap(),
            WPublicationOutcome::Published { new_entries: 2 }
        );
        let batch = receiver.peek_proved_batch().unwrap();
        assert_eq!(
            batch
                .entries()
                .iter()
                .map(ProvedWEntry::index)
                .collect::<Vec<_>>(),
            vec![2, 7]
        );
        receiver.acknowledge_proved_batch(&batch).unwrap();
        assert_eq!(
            sender.publish_batch(entries).unwrap(),
            WPublicationOutcome::NoChange
        );

        drop(receiver);
        assert_eq!(
            sender
                .publish_batch(std::iter::once(entry(&task, &artifacts, 11)))
                .unwrap(),
            WPublicationOutcome::ReceiverClosed
        );
        sender.close();
        drop(sender);
        drop(artifacts);
        owner.settle().unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn conflicting_sparse_batch_publishes_nothing() {
        let task = task();
        let directory = std::env::temp_dir().join(format!(
            "whiel-phase4c-channel-conflict-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&directory);
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(directory.join("artifacts")))
                .unwrap();
        let (sender, receiver) = create_w_proof_channel(task.identity(), artifacts.backend_id());
        let first = entry(&task, &artifacts, 4);
        let mut conflicting = entry(&task, &artifacts, 4);
        conflicting.formula = ClauseFormula::from_trusted_lean_source(
            "different W(4)",
            first.formula.source().clone(),
        )
        .unwrap();
        assert!(
            sender
                .publish_batch([first, conflicting])
                .unwrap_err()
                .contains("conflicting")
        );
        assert!(receiver.peek_proved_batch().is_none());

        sender.close();
        drop(sender);
        drop(receiver);
        drop(artifacts);
        owner.settle().unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }
}

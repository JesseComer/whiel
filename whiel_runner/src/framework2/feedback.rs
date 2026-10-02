//! Bounded, immutable feedback for pre-certificate AgentHoudini search.
//!
//! This module is a presentation boundary, never a logical authority. Exact
//! Lean-owned values remain in the fixed-ambient state and in a private
//! validation manifest. The agent sees bounded typed summaries, opaque
//! consultation-bound references, and no raw artifact handle or payload.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;
use std::time::Duration;

use serde_json::{Value, json};

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore, BackendId};
use crate::encoding::canonical_value_sha256;
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::ClauseId;
use crate::task::{SynthesisTask, TaskIdentity};

use super::catalog::{
    ExtendedClauseOrigin, FrameworkIIStateError, LeveledClauseCatalog, LeveledClauseRecord,
    task_identity_fields,
};
use super::host_limits::{
    HOST_LIMIT_NAMES, HostLimitDisagreement, HostLimitTruncation, HostLimits,
};
use super::ledger::{
    FrameworkIICheckEvidence, FrameworkIICheckOutcome, FrameworkIICheckRole, FrameworkIIDeadReason,
    FrameworkIIInconclusiveReason, FrameworkIIInvalidationReason, LevelLedgerRow,
};
use super::production::{
    FrameworkIIEntailmentProgress, ProofSearchProfile, ProtectedTheoremSelectionReceipt,
    RuntimeProofReceipt, ValidatedFiniteRefutation,
};
use super::proposal::{FrameworkIIProposalContext, FrameworkIIProposalDrop};
use super::snapshot::LeveledCandidateSnapshot;
use super::stabilization::{CurrentFrameworkIIRoot, FrameworkIIDeadCause, LeveledHoudiniState};
use super::types::FrameworkIILevel;

// Pass 7.5c-2: the push replaced its `retry` list with `pending` (identity,
// source, minimum level, current level), `last_round` lost the exhausted and
// inconclusive outcomes, and the `latest` event kinds became `initial`,
// `postcondition_open`, `failure`, and `counterexample_rejected`, so the
// feedback pin moves 6 -> 7. The standing presentation dropped exhaustion and
// the reconsideration policies, made the level bound conditional, and gained
// the halting rule, the per-round retry rule, and the two death rules, so the
// presentation pin moves 7 -> 8. The agent protocol (4) and the worker
// protocol (6) are unchanged. `AgentFeedback::push_value` reuses the feedback
// pin for its own `schema_version` field. The standing presentation then
// spelled out the counterexample instance shape in `proposal_kinds` (8 -> 9)
// and named the relation table's `key` column as the one accepted spelling
// of a relation in it (9 -> 10). The Milestone 7.5 review then added two
// sentences: `checks` says what a proof root's `profile` field means and
// that a run may disable the `casc_2025` portfolio entirely (finding 5), and
// `proposal_kinds` says that an instance proposal needs a quantifier-free
// input pre- and postcondition, so a proposer does not spend rounds on a
// task where every instance is refused `not_quantifier_free` (finding 9).
// Both are presentation text inside the digested schema, so the pin moves
// 11 -> 12. Pass 7.5h then changed what the task view's seven text fields
// mean: a relation in the schema, the original triple and the preprocessed
// triple is spelled the way the input notation spells it (`T_aux`, `R\u{221e}`)
// rather than as the structural `Repr` of its name. The fields and their
// shape are unchanged, but their content is a different convention and a
// reader that learned the old spelling would misread the new one, so the
// pin moves 12 -> 13. The same pass carries that one convention through
// the rest of what the agent reads: a clause's `display` and the relation
// table's `display` column now spell a relation the same way, so a name
// reads identically wherever the agent meets it. Solver keys, the relation
// table's `key` column and the clause surface syntax are untouched, and a
// display sits in no identity or digest, so nothing else moves. A flag has
// no notation spelling and renders as the display-only marker
// `\u{27e8}flag id index\u{27e9}`, which no notation reads back; Pass 7.8e
// owns choosing a parsable one.
//
// API 3.1.0 then made two changes in one revision. Every clause identity the
// push and the read surface expose carries the record's own admitted text —
// `canonical_source` and `display` — so a proposer can read every clause it is
// shown; the feedback pin moves 9 -> 10. The standing presentation dropped its
// ten tutorial strings (`clause_grammar`, `system_clauses`,
// `prophecy_semantics`, `checks`, `core`, `pending_retry`, `host_limits_note`,
// `death_rules`, `proposal_kinds` and the `note` inside `resource_limits`),
// keeping every structured field, so the presentation pin moves 15 -> 16. The
// rules those sentences worded are stated in `agent_houdini.tex` and enforced
// here; the proposer words them for its own agent. Wire 3, the agent protocol
// (4) and the worker protocol are unchanged.
pub(crate) use crate::proposer_api::version::{
    AGENT_FEEDBACK_SCHEMA_VERSION, AGENT_PRESENTATION_SCHEMA_VERSION,
};
const MINIMUM_PAGE_BYTES: usize = 4 * 1024;
const MAXIMUM_POLICY_BYTES: usize = 64 * 1024 * 1024;
const MAXIMUM_POLICY_ITEMS: usize = 1_000_000;

// ------------------------------------------------------------
// Validated Feedback Policy
// ------------------------------------------------------------

/// Finite limits for one feedback session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentFeedbackLimits {
    pub max_shared_presentation_bytes: usize,
    pub max_private_manifest_bytes: usize,
    pub max_feedback_bytes: usize,
    pub max_page_bytes: usize,
    pub clause_page_items: usize,
    pub ledger_page_items: usize,
    pub max_artifact_references: usize,
    /// The run's optional host limits: absent by default, so nothing is
    /// truncated and nothing is refused. This is the one surface for every
    /// optional limit of the fixed-ambient path — the catalog size, the
    /// proposal size and clause-text size, the drop count, the countermodel
    /// retention bound, the `strongest_refutations` count, the evaluation
    /// cost, the pushed-Core size, the reply size, and the level bound. The
    /// presentation lists whichever are in force, and a refusal caused by
    /// one carries the single `host_limit` code.
    pub host_limits: HostLimits,
    pub resource_limits: Option<super::resource_limits::CampaignResourceLimits>,
}

impl Default for AgentFeedbackLimits {
    fn default() -> Self {
        Self {
            max_shared_presentation_bytes: 4 * 1024 * 1024,
            max_private_manifest_bytes: 2 * 1024 * 1024,
            max_feedback_bytes: 8 * 1024 * 1024,
            max_page_bytes: 256 * 1024,
            clause_page_items: 64,
            ledger_page_items: 64,
            max_artifact_references: 8,
            host_limits: HostLimits::UNBOUNDED,
            resource_limits: None,
        }
    }
}

/// A checked feedback policy with a stable nonsemantic digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentFeedbackPolicy {
    limits: AgentFeedbackLimits,
    digest: Arc<str>,
}

impl AgentFeedbackPolicy {
    pub fn new(limits: AgentFeedbackLimits) -> Result<Self, AgentFeedbackError> {
        let item_limits = [
            limits.clause_page_items,
            limits.ledger_page_items,
            limits.max_artifact_references,
        ];
        if item_limits.contains(&0)
            || item_limits
                .iter()
                .any(|limit| *limit > MAXIMUM_POLICY_ITEMS)
        {
            return Err(AgentFeedbackError::InvalidPolicy(
                "feedback item limits must be positive and bounded",
            ));
        }
        let byte_limits = [
            limits.max_shared_presentation_bytes,
            limits.max_private_manifest_bytes,
            limits.max_feedback_bytes,
            limits.max_page_bytes,
        ];
        if byte_limits.contains(&0)
            || byte_limits
                .iter()
                .any(|limit| *limit > MAXIMUM_POLICY_BYTES)
            || limits.max_page_bytes < MINIMUM_PAGE_BYTES
            || limits.max_shared_presentation_bytes > limits.max_feedback_bytes
        {
            return Err(AgentFeedbackError::InvalidPolicy(
                "feedback byte limits are inconsistent or out of range",
            ));
        }
        // A host limit is optional, but a limit of zero is a typo, never a
        // policy: it would refuse everything, including the empty
        // submission the contract requires to be admissible.
        if HOST_LIMIT_NAMES
            .into_iter()
            .any(|name| limits.host_limits.get(name) == Some(0))
        {
            return Err(AgentFeedbackError::InvalidPolicy(
                "a host limit that is set must be positive",
            ));
        }
        let fields = policy_fields(&limits);
        Ok(Self {
            limits,
            digest: Arc::from(canonical_value_sha256(&fields)),
        })
    }

    pub fn limits(&self) -> &AgentFeedbackLimits {
        &self.limits
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    /// The run's optional host limits (absent by default).
    pub fn host_limits(&self) -> &HostLimits {
        &self.limits.host_limits
    }
}

impl Default for AgentFeedbackPolicy {
    fn default() -> Self {
        Self::new(AgentFeedbackLimits::default())
            .expect("the built-in AgentFeedback limits are valid")
    }
}

fn policy_fields(limits: &AgentFeedbackLimits) -> Value {
    json!({
        "domain": "whiel-proposer-feedback-policy-v1",
        "max_shared_presentation_bytes": limits.max_shared_presentation_bytes,
        "max_private_manifest_bytes": limits.max_private_manifest_bytes,
        "max_feedback_bytes": limits.max_feedback_bytes,
        "max_page_bytes": limits.max_page_bytes,
        "clause_page_items": limits.clause_page_items,
        "ledger_page_items": limits.ledger_page_items,
        "max_artifact_references": limits.max_artifact_references,
        "host_limits": limits.host_limits.digest_value(),
        "resource_limits": limits.resource_limits,
    })
}

// ------------------------------------------------------------
// Immutable Shared Presentation
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentTaskTriple {
    precondition: Arc<str>,
    command: Arc<str>,
    postcondition: Arc<str>,
}

impl AgentTaskTriple {
    pub fn precondition(&self) -> &str {
        &self.precondition
    }

    pub fn command(&self) -> &str {
        &self.command
    }

    pub fn postcondition(&self) -> &str {
        &self.postcondition
    }

    fn wire_value(&self) -> Value {
        json!({
            "precondition": self.precondition.as_ref(),
            "command": self.command.as_ref(),
            "postcondition": self.postcondition.as_ref(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentTaskPresentation {
    canonical_id: Arc<str>,
    task_digest: Arc<str>,
    semantic_version: u64,
    encoding_version: u64,
    schema: Arc<str>,
    original: AgentTaskTriple,
    preprocessed: AgentTaskTriple,
}

impl AgentTaskPresentation {
    pub fn canonical_id(&self) -> &str {
        &self.canonical_id
    }

    pub fn task_digest(&self) -> &str {
        &self.task_digest
    }

    pub fn original(&self) -> &AgentTaskTriple {
        &self.original
    }

    pub fn preprocessed(&self) -> &AgentTaskTriple {
        &self.preprocessed
    }

    fn wire_value(&self) -> Value {
        json!({
            "canonical_id": self.canonical_id.as_ref(),
            "task_digest": self.task_digest.as_ref(),
            "semantic_version": self.semantic_version,
            "encoding_version": self.encoding_version,
            "schema": self.schema.as_ref(),
            "original": self.original.wire_value(),
            "preprocessed": self.preprocessed.wire_value(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentProphecyBinding {
    program_relation: Arc<str>,
    prophecy_relation: Arc<str>,
    arity: u64,
}

impl AgentProphecyBinding {
    fn wire_value(&self) -> Value {
        json!({
            "program_relation": self.program_relation.as_ref(),
            "prophecy_relation": self.prophecy_relation.as_ref(),
            "arity": self.arity,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentFeedbackPresentation {
    task: AgentTaskPresentation,
    scope_digest: Arc<str>,
    ambient_relations: Arc<[(Arc<str>, u64)]>,
    prophecy_map: Arc<[AgentProphecyBinding]>,
    /// Every host limit in force for this run, each named with its value.
    /// An empty list — the default — is the run's honest statement that it
    /// sets none.
    host_limits: Arc<Value>,
    resource_limits: Arc<Value>,
    presentation_digest: Arc<str>,
}

impl AgentFeedbackPresentation {
    pub fn task(&self) -> &AgentTaskPresentation {
        &self.task
    }

    pub fn scope_digest(&self) -> &str {
        &self.scope_digest
    }

    pub fn prophecy_map(&self) -> &[AgentProphecyBinding] {
        &self.prophecy_map
    }

    pub fn presentation_digest(&self) -> &str {
        &self.presentation_digest
    }

    fn wire_without_digest(&self) -> Value {
        json!({
            "schema_version": AGENT_PRESENTATION_SCHEMA_VERSION,
            "task": self.task.wire_value(),
            "ambient_schema": {
                "scope_digest": self.scope_digest.as_ref(),
                "relations": relation_rows(&self.ambient_relations),
                "prophecy_map": self.prophecy_map.iter().map(AgentProphecyBinding::wire_value).collect::<Vec<_>>(),
            },
            "host_limits": self.host_limits.as_ref(),
            "resource_limits": self.resource_limits.as_ref(),
        })
    }

    fn wire_value(&self) -> Value {
        let mut value = self.wire_without_digest();
        value
            .as_object_mut()
            .expect("presentation is an object")
            .insert(
                "presentation_digest".to_string(),
                Value::String(self.presentation_digest.to_string()),
            );
        value
    }
}

fn relation_rows(relations: &[(Arc<str>, u64)]) -> Vec<Value> {
    relations
        .iter()
        .map(|(key, arity)| json!({"key": key.as_ref(), "arity": arity}))
        .collect()
}

fn build_shared_presentation(
    task: &SynthesisTask,
    state: &LeveledHoudiniState,
    policy: &AgentFeedbackPolicy,
) -> Result<Arc<AgentFeedbackPresentation>, AgentFeedbackError> {
    let scope = state.catalog().scope();
    if task.identity() != scope.task_identity() {
        return Err(AgentFeedbackError::WrongTask);
    }
    let limits = policy.limits();
    // The policy is the single source of the run's host limits; the
    // controller state's bound fills in only where the policy names none,
    // and a state that contradicts a declared bound fails closed. What is
    // reconciled here is what the presentation lists and what a refusal
    // cites.
    let host_limits = limits
        .host_limits
        .with_level_bound(state.max_level().map(|bound| bound.get()))
        .map_err(AgentFeedbackError::HostLimits)?;
    for text in [
        task.schema().display(),
        task.original_pre().display(),
        task.original_command().display(),
        task.original_post().display(),
        task.preprocessed_pre().display(),
        task.preprocessed_command().display(),
        task.preprocessed_post().display(),
    ] {
        validate_presentation_text(text)?;
    }
    let task_digest = canonical_value_sha256(&task_identity_fields(scope));
    let task_view = AgentTaskPresentation {
        canonical_id: Arc::from(task.identity().canonical_id()),
        task_digest: Arc::from(task_digest),
        semantic_version: task.identity().semantic_version(),
        encoding_version: task.identity().encoding_version(),
        schema: Arc::from(task.schema().display()),
        original: AgentTaskTriple {
            precondition: Arc::from(task.original_pre().display()),
            command: Arc::from(task.original_command().display()),
            postcondition: Arc::from(task.original_post().display()),
        },
        preprocessed: AgentTaskTriple {
            precondition: Arc::from(task.preprocessed_pre().display()),
            command: Arc::from(task.preprocessed_command().display()),
            postcondition: Arc::from(task.preprocessed_post().display()),
        },
    };
    let ambient_relations = scope
        .relations()
        .iter()
        .map(|relation| (Arc::from(relation.key().as_str()), relation.arity()))
        .collect::<Vec<_>>();
    let prophecy_map = scope
        .prophecy_bindings()
        .iter()
        .map(|binding| AgentProphecyBinding {
            program_relation: Arc::from(binding.program().as_str()),
            prophecy_relation: Arc::from(binding.prophecy().as_str()),
            arity: binding.arity(),
        })
        .collect::<Vec<_>>();
    // The presentation publishes data, not prose. What a clause may say, how
    // the checks work, what a host limit means and which proposals exist are
    // the contract's rules (`agent_houdini.tex`, `houdini.tex`); the verifier
    // states them once there and enforces them, and the proposer's own layer
    // explains them to whoever it is asking. A sentence shipped from here
    // could only be a second, drifting copy — the one drafted for API 3.0
    // disagreed with the report in six places — so none is shipped.
    let mut presentation = AgentFeedbackPresentation {
        task: task_view,
        scope_digest: Arc::from(scope.identity_sha256()),
        ambient_relations: ambient_relations.into(),
        prophecy_map: prophecy_map.into(),
        host_limits: Arc::new(host_limits.wire_value()),
        resource_limits: Arc::new(
            json!({"api_packet_bytes": 67108864, "configured": limits.resource_limits}),
        ),
        presentation_digest: Arc::from(""),
    };
    presentation.presentation_digest =
        Arc::from(canonical_value_sha256(&presentation.wire_without_digest()));
    let encoded = json_bytes(&presentation.wire_value())?;
    if encoded > limits.max_shared_presentation_bytes {
        return Err(AgentFeedbackError::MandatoryPresentationTooLarge {
            found: encoded,
            limit: limits.max_shared_presentation_bytes,
        });
    }
    Ok(Arc::new(presentation))
}

/// A presentation string is checked for *safety*, never for size.
///
/// Milestone 7.5 review, finding 8: this used to refuse a run whose task
/// text display exceeded a hard-coded 16 KiB, which is a functional bound on
/// what may be verified, not a guard on a resource. Display text is never
/// truncated and never silently dropped for its length; the memory the
/// pushed document may occupy is bounded by the push-size guard
/// (`agent.rs`'s `max_request_bytes`), whose own failure is the run-global
/// resource fault of finding 7, and a run may declare the optional
/// `clause_text_bytes` host limit if it wants a stated bound on submitted
/// clause text. What is refused here is text that is empty or carries a
/// control character other than a newline or a tab.
pub(super) fn validate_presentation_text(text: &str) -> Result<(), AgentFeedbackError> {
    if text.is_empty()
        || text
            .chars()
            .any(|character| character.is_control() && !matches!(character, '\n' | '\t'))
    {
        return Err(AgentFeedbackError::UnsafePresentationText);
    }
    Ok(())
}

// ------------------------------------------------------------
// Exact Clause Identities
// ------------------------------------------------------------

/// One clause's exact identity, together with the text the verifier admitted
/// for it.
///
/// The three digest fields are the identity. `canonical_source` and `display`
/// are the admitted record's own text, carried so that every clause the API
/// shows can be read as well as named; they are a rendering of the record the
/// `record_digest` already fixes, never an independent fact, so they take no
/// part in identity equality and a reference that omits them names the same
/// clause. Either is absent only when the text itself is unsafe to present
/// (see [`optional_presentation_text`]).
#[derive(Clone, Debug, Eq)]
pub struct AgentClauseIdentity {
    clause_id: ClauseId,
    record_digest: Arc<str>,
    formula_digest: Arc<str>,
    canonical_source: Option<Arc<str>>,
    display: Option<Arc<str>>,
}

/// Identity equality is the three pinned identity fields and nothing else: a
/// clause reference reconstructed from the wire carries no text, and must
/// still compare equal to the same clause read out of the frozen catalog.
impl PartialEq for AgentClauseIdentity {
    fn eq(&self, other: &Self) -> bool {
        self.clause_id == other.clause_id
            && self.record_digest == other.record_digest
            && self.formula_digest == other.formula_digest
    }
}

impl AgentClauseIdentity {
    /// Reconstruct a clause reference from its own wire fields (Pass 7.5c:
    /// a tool call names a clause "as in the push" the exact same way a
    /// drop reference does). Never itself an authority: the caller must
    /// still resolve it through
    /// [`AgentFeedbackValidationManifest::resolve_shown_clause`] before
    /// trusting it names a clause actually shown this consultation.
    ///
    /// Not yet called: its only intended caller is the Pass 7.5c
    /// AgentHoudini tool surface's clause-reference resolver, which is out
    /// of scope for this pass and tracked separately, so `dead_code` is
    /// silenced here rather than papered over by wiring a caller that
    /// belongs to that other work.
    #[allow(dead_code)]
    pub(crate) fn from_wire_fields(
        clause_id: ClauseId,
        record_digest: impl Into<Arc<str>>,
        formula_digest: impl Into<Arc<str>>,
    ) -> Self {
        Self {
            clause_id,
            record_digest: record_digest.into(),
            formula_digest: formula_digest.into(),
            canonical_source: None,
            display: None,
        }
    }

    pub fn clause_id(&self) -> ClauseId {
        self.clause_id
    }

    pub fn record_digest(&self) -> &str {
        &self.record_digest
    }

    pub fn formula_digest(&self) -> &str {
        &self.formula_digest
    }

    /// The exact parseable clause source the verifier admitted, in the clause
    /// grammar a submission is written in.
    pub fn canonical_source(&self) -> Option<&str> {
        self.canonical_source.as_deref()
    }

    /// The record's separate display spelling of the same clause.
    pub fn display(&self) -> Option<&str> {
        self.display.as_deref()
    }

    /// Whether a clause reference carries text that contradicts this identity.
    /// Omitted text asserts nothing and never contradicts anything.
    pub(crate) fn contradicted_by(
        &self,
        canonical_source: Option<&str>,
        display: Option<&str>,
    ) -> bool {
        let disagrees = |claimed: Option<&str>, held: Option<&str>| {
            claimed.is_some_and(|claimed| held != Some(claimed))
        };
        disagrees(canonical_source, self.canonical_source()) || disagrees(display, self.display())
    }

    pub(crate) fn wire_value(&self) -> Value {
        json!({
            "clause_id": self.clause_id.get(),
            "record_digest": self.record_digest.as_ref(),
            "formula_digest": self.formula_digest.as_ref(),
            "canonical_source": self.canonical_source.as_deref(),
            "display": self.display.as_deref(),
        })
    }

    /// The identity as a bare reference: the three identity fields, without
    /// the record's text.
    ///
    /// Used where a clause is *named* rather than shown — inside a drop
    /// authorization, which sits in the same push entry as the clause it
    /// authorizes and would otherwise repeat that clause's whole source a
    /// second time. The proposer echoes this token back exactly as it
    /// arrives, and the read surface accepts either form.
    fn reference_wire_value(&self) -> Value {
        json!({
            "clause_id": self.clause_id.get(),
            "record_digest": self.record_digest.as_ref(),
            "formula_digest": self.formula_digest.as_ref(),
        })
    }
}

pub(crate) fn record_clause_identity(record: &LeveledClauseRecord) -> AgentClauseIdentity {
    AgentClauseIdentity {
        clause_id: record.id(),
        record_digest: Arc::from(record.record_digest()),
        formula_digest: Arc::from(record.formula().identity_sha256()),
        canonical_source: optional_presentation_text(record.formula().canonical_source()),
        display: optional_presentation_text(record.formula().display()),
    }
}

fn referenceable_clause_identities(
    page: &AgentClausePage,
) -> Result<BTreeMap<ClauseId, AgentClauseIdentity>, AgentFeedbackError> {
    let mut referenceable = BTreeMap::new();
    for identity in page.items().iter().map(AgentClauseFeedback::clause) {
        match referenceable.get(&identity.clause_id) {
            Some(existing) if existing != identity => {
                return Err(AgentFeedbackError::ConflictingExposedClauseIdentity {
                    clause: identity.clause_id.get(),
                });
            }
            Some(_) => {}
            None => {
                referenceable.insert(identity.clause_id, identity.clone());
            }
        }
    }
    Ok(referenceable)
}

// ------------------------------------------------------------
// Sanitized Stable Artifact References
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AgentArtifactRole {
    Proof,
    Model,
    EmptyCheck,
    RouteReceipt,
    ValidationReceipt,
    ProgressReceipt,
    FailureDiagnostic,
}

impl AgentArtifactRole {
    fn identity_name(self) -> &'static str {
        match self {
            Self::Proof => "proof",
            Self::Model => "model",
            Self::EmptyCheck => "empty_check",
            Self::RouteReceipt => "route_receipt",
            Self::ValidationReceipt => "validation_receipt",
            Self::ProgressReceipt => "progress_receipt",
            Self::FailureDiagnostic => "failure_diagnostic",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentArtifactReference {
    stable_id: Arc<str>,
    role: AgentArtifactRole,
    kind: ArtifactKind,
}

impl AgentArtifactReference {
    pub fn stable_id(&self) -> &str {
        &self.stable_id
    }

    pub fn role(&self) -> AgentArtifactRole {
        self.role
    }

    pub fn kind(&self) -> ArtifactKind {
        self.kind
    }

    fn wire_value(&self) -> Value {
        json!({
            "stable_id": self.stable_id.as_ref(),
            "role": self.role.identity_name(),
            "kind": artifact_kind_name(self.kind),
        })
    }
}

struct AgentArtifactSanitizer {
    replay_references: BTreeMap<Arc<str>, (ArtifactRef, AgentArtifactRole)>,
    backend: BackendId,
    run_digest: Arc<str>,
    session_digest: Arc<str>,
    references: BTreeMap<Arc<str>, ArtifactRef>,
}

impl AgentArtifactSanitizer {
    fn new(backend: BackendId, run_digest: Arc<str>, session_digest: Arc<str>) -> Self {
        Self {
            backend,
            run_digest,
            session_digest,
            references: BTreeMap::new(),
            replay_references: BTreeMap::new(),
        }
    }

    fn sanitize(
        &mut self,
        reference: ArtifactRef,
        role: AgentArtifactRole,
        expected: &[ArtifactKind],
    ) -> Result<AgentArtifactReference, AgentFeedbackError> {
        if reference.backend_id() != self.backend {
            return Err(AgentFeedbackError::ForeignArtifactReference);
        }
        if !expected.contains(&reference.kind()) {
            return Err(AgentFeedbackError::UnexpectedArtifactKind {
                role,
                found: reference.kind(),
            });
        }
        let stable_id: Arc<str> = Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-agent-artifact-reference-v1",
            "run_digest": self.run_digest.as_ref(),
            "session_digest": self.session_digest.as_ref(),
            "local_id": reference.local_id(),
            "artifact_kind": artifact_kind_name(reference.kind()),
            "role": role.identity_name(),
        })));
        self.references.insert(Arc::clone(&stable_id), reference);
        self.replay_references
            .insert(Arc::clone(&stable_id), (reference, role));
        Ok(AgentArtifactReference {
            stable_id,
            role,
            kind: reference.kind(),
        })
    }

    fn validate_hidden(
        &self,
        reference: ArtifactRef,
        expected: ArtifactKind,
    ) -> Result<(), AgentFeedbackError> {
        if reference.backend_id() != self.backend {
            return Err(AgentFeedbackError::ForeignArtifactReference);
        }
        if reference.kind() != expected {
            return Err(AgentFeedbackError::UnexpectedArtifactKind {
                role: AgentArtifactRole::ProgressReceipt,
                found: reference.kind(),
            });
        }
        Ok(())
    }

    fn sanitize_failure(
        &mut self,
        report: &FailureReport,
        maximum: usize,
    ) -> Result<(Arc<[AgentArtifactReference]>, usize), AgentFeedbackError> {
        let mut exposed = Vec::new();
        let mut withheld = 0_usize;
        for reference in report.artifact_references() {
            if reference.backend_id() != self.backend {
                return Err(AgentFeedbackError::ForeignArtifactReference);
            }
            if reference.kind() == ArtifactKind::FailureDiagnostic && exposed.len() < maximum {
                exposed.push(self.sanitize(
                    *reference,
                    AgentArtifactRole::FailureDiagnostic,
                    &[ArtifactKind::FailureDiagnostic],
                )?);
            } else {
                withheld = withheld
                    .checked_add(1)
                    .ok_or(AgentFeedbackError::ArithmeticOverflow)?;
            }
        }
        Ok((exposed.into(), withheld))
    }
}

fn artifact_kind_name(kind: ArtifactKind) -> &'static str {
    match kind {
        ArtifactKind::Query => "query",
        ArtifactKind::Proof => "proof",
        ArtifactKind::Model => "model",
        ArtifactKind::EmptyInstanceCheck => "empty_instance_check",
        ArtifactKind::InitializationCheck => "initialization_check",
        ArtifactKind::Certificate => "certificate",
        ArtifactKind::AcceptanceRecord => "acceptance_record",
        ArtifactKind::Witness => "witness",
        ArtifactKind::FailureDiagnostic => "failure_diagnostic",
        ArtifactKind::RuntimeTrace => "runtime_trace",
    }
}

// ------------------------------------------------------------
// Latest Nonledger Feedback
// ------------------------------------------------------------

/// The four contract event kinds (agent report, Section "Transitions and
/// feedback"): `initial`, `postcondition_open`, `failure`, and
/// `counterexample_rejected`.
#[derive(Clone, Debug)]
enum AgentSearchFeedbackKind {
    Initial,
    PostconditionOpen(AgentPostconditionOpenSource),
    Failure(FailureReport),
    CounterexampleRejected { code: Arc<str>, reason: Arc<str> },
}

/// Why the postcondition is still open after an epoch: the epoch's
/// termination check on its Core was refuted — naming the checker attempt
/// whose Lean-validated countermodel the `countermodel` tool returns — or was
/// inconclusive with its reason.
#[derive(Clone, Debug)]
enum AgentPostconditionOpenSource {
    Refuted {
        attempt: Option<u64>,
    },
    Inconclusive {
        reason: FrameworkIIInconclusiveReason,
    },
}

#[derive(Clone, Debug)]
struct AgentSearchFeedbackBinding {
    catalog: LeveledClauseCatalog,
    context: FrameworkIIProposalContext,
}

/// One latest event bound to the exact post-epoch fixed-ambient state.
#[derive(Clone)]
pub struct AgentSearchFeedback {
    binding: Option<AgentSearchFeedbackBinding>,
    kind: AgentSearchFeedbackKind,
}

impl fmt::Debug for AgentSearchFeedback {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match &self.kind {
            AgentSearchFeedbackKind::Initial => "initial",
            AgentSearchFeedbackKind::PostconditionOpen(_) => "postcondition_open",
            AgentSearchFeedbackKind::Failure(_) => "failure",
            AgentSearchFeedbackKind::CounterexampleRejected { .. } => {
                AGENT_COUNTEREXAMPLE_REJECTED_KIND
            }
        };
        formatter
            .debug_struct("AgentSearchFeedback")
            .field("kind", &kind)
            .field("is_bound", &self.binding.is_some())
            .finish_non_exhaustive()
    }
}

impl AgentSearchFeedback {
    fn initial() -> Self {
        Self {
            binding: None,
            kind: AgentSearchFeedbackKind::Initial,
        }
    }

    /// The epoch's termination check was refuted. `attempt` is the checker's
    /// own attempt identifier — the id its retained countermodel is keyed
    /// under, which the `countermodel` tool serves — or `None` when the
    /// checker published no validated refutation receipt.
    pub fn postcondition_open_refuted(
        state: &LeveledHoudiniState,
        attempt: Option<u64>,
    ) -> Result<Self, AgentFeedbackError> {
        Self::bound(
            state,
            AgentSearchFeedbackKind::PostconditionOpen(AgentPostconditionOpenSource::Refuted {
                attempt,
            }),
        )
    }

    /// The epoch's termination check was inconclusive; the same key is
    /// relaunched on a later epoch under the retry policy.
    pub fn postcondition_open_inconclusive(
        state: &LeveledHoudiniState,
        reason: FrameworkIIInconclusiveReason,
    ) -> Result<Self, AgentFeedbackError> {
        Self::bound(
            state,
            AgentSearchFeedbackKind::PostconditionOpen(
                AgentPostconditionOpenSource::Inconclusive { reason },
            ),
        )
    }

    pub fn failure(
        state: &LeveledHoudiniState,
        report: FailureReport,
    ) -> Result<Self, AgentFeedbackError> {
        Self::bound(state, AgentSearchFeedbackKind::Failure(report))
    }

    /// Lean rejected a submitted counterexample instance (agent report,
    /// Section "Counterexample proposals"): the next consultation starts and
    /// the state is unchanged, so `last_round` and `pending` are exactly what
    /// the previous epoch left.
    pub fn counterexample_rejected(
        state: &LeveledHoudiniState,
        code: impl Into<Arc<str>>,
        reason: impl Into<Arc<str>>,
    ) -> Result<Self, AgentFeedbackError> {
        Self::bound(
            state,
            AgentSearchFeedbackKind::CounterexampleRejected {
                code: code.into(),
                reason: reason.into(),
            },
        )
    }

    fn bound(
        state: &LeveledHoudiniState,
        kind: AgentSearchFeedbackKind,
    ) -> Result<Self, AgentFeedbackError> {
        Ok(Self {
            binding: Some(AgentSearchFeedbackBinding {
                catalog: state.catalog().clone(),
                context: state.proposal_context()?,
            }),
            kind,
        })
    }

    fn matches(&self, eligibility: &AgentEligibilitySnapshot, initial_allowed: bool) -> bool {
        match (&self.binding, &self.kind) {
            (None, AgentSearchFeedbackKind::Initial) => initial_allowed,
            (Some(binding), _) => {
                binding.catalog == eligibility.catalog
                    && binding.context.proposal_revision() == eligibility.proposal_revision
                    && binding.context.expected_registration_ordinal()
                        == eligibility.registration_ordinal
                    && binding
                        .context
                        .core_snapshot()
                        .same_partition(&eligibility.core_snapshot)
                    && binding.context.drop_eligible_records()
                        == eligibility.proposal_context.drop_eligible_records()
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentFailureFeedback {
    origin: FailureOrigin,
    kind: FailureKind,
    retryable: bool,
    scope: FailureScope,
    has_detail: bool,
    artifacts: Arc<[AgentArtifactReference]>,
    withheld_artifacts: usize,
}

impl AgentFailureFeedback {
    fn wire_value(&self) -> Value {
        json!({
            "origin": failure_origin_name(self.origin),
            "kind": failure_kind_name(self.kind),
            "retryable": self.retryable,
            "scope": failure_scope_name(self.scope),
            "has_withheld_detail": self.has_detail,
            "artifacts": self.artifacts.iter().map(AgentArtifactReference::wire_value).collect::<Vec<_>>(),
            "withheld_artifacts": self.withheld_artifacts,
        })
    }
}

/// Why the postcondition is still open after an epoch, as the agent sees it.
///
/// `Refuted` names the checker attempt whose Lean-validated countermodel the
/// `countermodel` tool returns; `Inconclusive` carries the reason the epoch's
/// termination check did not decide.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentPostconditionOpenFeedback {
    Refuted {
        attempt: Option<u64>,
    },
    Inconclusive {
        reason: FrameworkIIInconclusiveReason,
    },
}

impl AgentPostconditionOpenFeedback {
    /// The checker attempt the `countermodel` tool serves for this
    /// refutation, when one is addressable.
    pub fn attempt(&self) -> Option<u64> {
        match self {
            Self::Refuted { attempt } => *attempt,
            Self::Inconclusive { .. } => None,
        }
    }

    fn wire_value(&self) -> Value {
        match self {
            Self::Refuted { attempt } => json!({"outcome": "refuted", "attempt": attempt}),
            Self::Inconclusive { reason } => json!({
                "outcome": "inconclusive",
                "reason": inconclusive_name(*reason),
            }),
        }
    }
}

/// The wire `kind` of the counterexample-rejection event.
pub(crate) const AGENT_COUNTEREXAMPLE_REJECTED_KIND: &str = "counterexample_rejected";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentLatestFeedback {
    Initial,
    PostconditionOpen(AgentPostconditionOpenFeedback),
    Failure(AgentFailureFeedback),
    /// A submitted counterexample instance Lean rejected, carrying Lean's
    /// own rejection code and reason (the host's call-local timeout uses the
    /// `timeout` code). See [`AGENT_COUNTEREXAMPLE_REJECTED_KIND`].
    CounterexampleRejected {
        code: Arc<str>,
        reason: Arc<str>,
    },
}

impl AgentLatestFeedback {
    fn wire_value(&self) -> Value {
        match self {
            Self::Initial => json!({"kind": "initial"}),
            Self::PostconditionOpen(open) => json!({
                "kind": "postcondition_open",
                "postcondition_open": open.wire_value(),
            }),
            Self::Failure(failure) => json!({
                "kind": "failure",
                "failure": failure.wire_value(),
            }),
            Self::CounterexampleRejected { code, reason } => json!({
                "kind": AGENT_COUNTEREXAMPLE_REJECTED_KIND,
                "counterexample_rejected": {
                    "code": code.as_ref(),
                    "reason": reason.as_ref(),
                },
            }),
        }
    }
}

fn project_latest_feedback(
    latest: &AgentSearchFeedback,
    sanitizer: &mut AgentArtifactSanitizer,
    policy: &AgentFeedbackPolicy,
) -> Result<AgentLatestFeedback, AgentFeedbackError> {
    match &latest.kind {
        AgentSearchFeedbackKind::Initial => Ok(AgentLatestFeedback::Initial),
        AgentSearchFeedbackKind::PostconditionOpen(source) => {
            Ok(AgentLatestFeedback::PostconditionOpen(match source {
                AgentPostconditionOpenSource::Refuted { attempt } => {
                    AgentPostconditionOpenFeedback::Refuted { attempt: *attempt }
                }
                AgentPostconditionOpenSource::Inconclusive { reason } => {
                    AgentPostconditionOpenFeedback::Inconclusive { reason: *reason }
                }
            }))
        }
        AgentSearchFeedbackKind::Failure(report) => {
            let (artifacts, withheld_artifacts) =
                sanitizer.sanitize_failure(report, policy.limits().max_artifact_references)?;
            Ok(AgentLatestFeedback::Failure(AgentFailureFeedback {
                origin: report.origin(),
                kind: report.kind(),
                retryable: report.retryable(),
                scope: report.scope(),
                has_detail: report.detail().is_some(),
                artifacts,
                withheld_artifacts,
            }))
        }
        AgentSearchFeedbackKind::CounterexampleRejected { code, reason } => {
            Ok(AgentLatestFeedback::CounterexampleRejected {
                code: Arc::clone(code),
                reason: Arc::clone(reason),
            })
        }
    }
}

// ------------------------------------------------------------
// Compact Attempt Routes
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentEvidenceRoute {
    RuntimeProof {
        profile: ProofSearchProfile,
        receipt_digest: Arc<str>,
        semantic_vc_digest: Arc<str>,
        artifacts: Arc<[AgentArtifactReference]>,
    },
    ProtectedTheorem {
        target_vc_digest: Arc<str>,
        theorem_name: Arc<str>,
        artifact: AgentArtifactReference,
    },
    ValidatedRefutation {
        refutation_digest: Arc<str>,
        semantic_vc_digest: Arc<str>,
        artifacts: Arc<[AgentArtifactReference]>,
    },
    RetryProgress {
        progress_digest: Arc<str>,
        semantic_vc_digest: Arc<str>,
        next_fmb_start_size: Option<u64>,
        previous_proof_allowance_ns: Arc<str>,
        current_proof_allowance_ns: Arc<str>,
        peer_failure: Option<AgentFailureFeedback>,
        artifacts: Arc<[AgentArtifactReference]>,
    },
    /// A check the controller had already suspended for its epoch: served
    /// from the semantic dictionary alone, and inconclusive without a
    /// launch because the dictionary had no answer. It carries no receipt
    /// and no artifact because no solver ran.
    Suspended,
    #[cfg(test)]
    TestScaffold,
}

impl AgentEvidenceRoute {
    fn identity_name(&self) -> &'static str {
        match self {
            Self::RuntimeProof { .. } => "runtime_proof",
            Self::ProtectedTheorem { .. } => "protected_theorem",
            Self::ValidatedRefutation { .. } => "validated_refutation",
            Self::RetryProgress { .. } => "retry_progress",
            Self::Suspended => "suspended",
            #[cfg(test)]
            Self::TestScaffold => "test_scaffold",
        }
    }

    fn wire_value(&self) -> Value {
        match self {
            Self::RuntimeProof {
                profile,
                receipt_digest,
                semantic_vc_digest,
                artifacts,
            } => json!({
                "kind": "runtime_proof",
                "profile": proof_profile_name(*profile),
                "receipt_digest": receipt_digest.as_ref(),
                "semantic_vc_digest": semantic_vc_digest.as_ref(),
                "artifacts": artifacts.iter().map(AgentArtifactReference::wire_value).collect::<Vec<_>>(),
            }),
            Self::ProtectedTheorem {
                target_vc_digest,
                theorem_name,
                artifact,
            } => json!({
                "kind": "protected_theorem",
                "target_vc_digest": target_vc_digest.as_ref(),
                "theorem_name": theorem_name.as_ref(),
                "artifact": artifact.wire_value(),
            }),
            Self::ValidatedRefutation {
                refutation_digest,
                semantic_vc_digest,
                artifacts,
            } => json!({
                "kind": "validated_refutation",
                "refutation_digest": refutation_digest.as_ref(),
                "semantic_vc_digest": semantic_vc_digest.as_ref(),
                "artifacts": artifacts.iter().map(AgentArtifactReference::wire_value).collect::<Vec<_>>(),
            }),
            Self::RetryProgress {
                progress_digest,
                semantic_vc_digest,
                next_fmb_start_size,
                previous_proof_allowance_ns,
                current_proof_allowance_ns,
                peer_failure,
                artifacts,
            } => json!({
                "kind": "retry_progress",
                "progress_digest": progress_digest.as_ref(),
                "semantic_vc_digest": semantic_vc_digest.as_ref(),
                "next_fmb_start_size": next_fmb_start_size,
                "previous_proof_allowance_ns": previous_proof_allowance_ns.as_ref(),
                "current_proof_allowance_ns": current_proof_allowance_ns.as_ref(),
                "peer_failure": peer_failure.as_ref().map(AgentFailureFeedback::wire_value),
                "artifacts": artifacts.iter().map(AgentArtifactReference::wire_value).collect::<Vec<_>>(),
            }),
            Self::Suspended => json!({"kind": "suspended"}),
            #[cfg(test)]
            Self::TestScaffold => json!({"kind": "test_scaffold"}),
        }
    }
}

fn project_evidence_route(
    evidence: &FrameworkIICheckEvidence,
    sanitizer: &mut AgentArtifactSanitizer,
    policy: &AgentFeedbackPolicy,
) -> Result<AgentEvidenceRoute, AgentFeedbackError> {
    if let Some(receipt) = evidence.runtime_proof() {
        return project_runtime_proof(receipt, sanitizer);
    }
    if let Some(selection) = evidence.protected_theorem_selection() {
        return project_protected_theorem(selection, sanitizer);
    }
    if let Some(refutation) = evidence.validated_refutation() {
        return project_validated_refutation(refutation, sanitizer);
    }
    if let Some(progress) = evidence.progress() {
        return project_retry_progress(progress, sanitizer, policy);
    }
    if evidence.is_launch_suppressed() {
        return Ok(AgentEvidenceRoute::Suspended);
    }
    #[cfg(test)]
    {
        Ok(AgentEvidenceRoute::TestScaffold)
    }
    #[cfg(not(test))]
    {
        Err(AgentFeedbackError::UnvalidatedEvidence)
    }
}

fn project_runtime_proof(
    receipt: &RuntimeProofReceipt,
    sanitizer: &mut AgentArtifactSanitizer,
) -> Result<AgentEvidenceRoute, AgentFeedbackError> {
    sanitizer.validate_hidden(receipt.terminal_artifact(), ArtifactKind::RuntimeTrace)?;
    let artifacts = vec![
        sanitizer.sanitize(
            receipt.proof_artifact(),
            AgentArtifactRole::Proof,
            &[ArtifactKind::Proof],
        )?,
        sanitizer.sanitize(
            receipt.empty_check_artifact(),
            AgentArtifactRole::EmptyCheck,
            &[ArtifactKind::EmptyInstanceCheck],
        )?,
        sanitizer.sanitize(
            receipt.receipt_artifact(),
            AgentArtifactRole::RouteReceipt,
            &[ArtifactKind::Witness],
        )?,
    ];
    Ok(AgentEvidenceRoute::RuntimeProof {
        profile: receipt.winner(),
        receipt_digest: Arc::from(receipt.receipt_digest()),
        semantic_vc_digest: Arc::from(receipt.semantic_vc_digest()),
        artifacts: artifacts.into(),
    })
}

fn project_protected_theorem(
    receipt: &ProtectedTheoremSelectionReceipt,
    sanitizer: &mut AgentArtifactSanitizer,
) -> Result<AgentEvidenceRoute, AgentFeedbackError> {
    Ok(AgentEvidenceRoute::ProtectedTheorem {
        target_vc_digest: Arc::from(receipt.target_vc_digest()),
        theorem_name: Arc::from(receipt.theorem_name()),
        artifact: sanitizer.sanitize(
            receipt.receipt_artifact(),
            AgentArtifactRole::RouteReceipt,
            &[ArtifactKind::Witness],
        )?,
    })
}

fn project_validated_refutation(
    refutation: &ValidatedFiniteRefutation,
    sanitizer: &mut AgentArtifactSanitizer,
) -> Result<AgentEvidenceRoute, AgentFeedbackError> {
    sanitizer.validate_hidden(refutation.terminal_artifact(), ArtifactKind::RuntimeTrace)?;
    let source_role = match refutation.source_artifact().kind() {
        ArtifactKind::Model => AgentArtifactRole::Model,
        ArtifactKind::EmptyInstanceCheck => AgentArtifactRole::EmptyCheck,
        found => {
            return Err(AgentFeedbackError::UnexpectedArtifactKind {
                role: AgentArtifactRole::Model,
                found,
            });
        }
    };
    let artifacts = vec![
        sanitizer.sanitize(
            refutation.source_artifact(),
            source_role,
            &[ArtifactKind::Model, ArtifactKind::EmptyInstanceCheck],
        )?,
        sanitizer.sanitize(
            refutation.validation_artifact(),
            AgentArtifactRole::ValidationReceipt,
            &[ArtifactKind::Witness],
        )?,
        sanitizer.sanitize(
            refutation.receipt_artifact(),
            AgentArtifactRole::RouteReceipt,
            &[ArtifactKind::Witness],
        )?,
    ];
    Ok(AgentEvidenceRoute::ValidatedRefutation {
        refutation_digest: Arc::from(refutation.refutation_digest()),
        semantic_vc_digest: Arc::from(refutation.semantic_vc_digest()),
        artifacts: artifacts.into(),
    })
}

fn project_retry_progress(
    progress: &FrameworkIIEntailmentProgress,
    sanitizer: &mut AgentArtifactSanitizer,
    policy: &AgentFeedbackPolicy,
) -> Result<AgentEvidenceRoute, AgentFeedbackError> {
    sanitizer.validate_hidden(progress.terminal_artifact(), ArtifactKind::RuntimeTrace)?;
    let artifacts = vec![sanitizer.sanitize(
        progress.progress_artifact(),
        AgentArtifactRole::ProgressReceipt,
        &[ArtifactKind::Witness],
    )?];
    let peer_failure = if let Some(report) = progress.peer_failure() {
        let (references, withheld_artifacts) =
            sanitizer.sanitize_failure(report, policy.limits().max_artifact_references)?;
        Some(AgentFailureFeedback {
            origin: report.origin(),
            kind: report.kind(),
            retryable: report.retryable(),
            scope: report.scope(),
            has_detail: report.detail().is_some(),
            artifacts: references,
            withheld_artifacts,
        })
    } else {
        None
    };
    Ok(AgentEvidenceRoute::RetryProgress {
        progress_digest: Arc::from(progress.progress_digest()),
        semantic_vc_digest: Arc::from(progress.semantic_vc_digest()),
        next_fmb_start_size: progress.next_fmb_start_size().map(|size| size.get()),
        previous_proof_allowance_ns: Arc::from(
            progress.previous_proof_allowance().as_nanos().to_string(),
        ),
        current_proof_allowance_ns: Arc::from(
            progress.current_proof_allowance().as_nanos().to_string(),
        ),
        peer_failure,
        artifacts: artifacts.into(),
    })
}

// ------------------------------------------------------------
// Paged Clause And Ledger Detail
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AgentFeedbackPageCategory {
    Clauses,
    Ledger,
}

impl AgentFeedbackPageCategory {
    fn identity_name(self) -> &'static str {
        match self {
            Self::Clauses => "clauses",
            Self::Ledger => "ledger",
        }
    }
}

#[derive(Clone)]
pub struct AgentFeedbackCursor {
    category: AgentFeedbackPageCategory,
    offset: usize,
    token_digest: Arc<str>,
    source_consultation_digest: Arc<str>,
    state_snapshot_digest: Arc<str>,
    authority: Arc<AgentEligibilitySnapshot>,
}

impl AgentFeedbackCursor {
    pub fn category(&self) -> AgentFeedbackPageCategory {
        self.category
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn token_digest(&self) -> &str {
        &self.token_digest
    }

    fn wire_value(&self) -> Value {
        json!({
            "category": self.category.identity_name(),
            "offset": self.offset,
            "token_digest": self.token_digest.as_ref(),
        })
    }
}

impl fmt::Debug for AgentFeedbackCursor {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentFeedbackCursor")
            .field("category", &self.category)
            .field("offset", &self.offset)
            .field("token_digest", &self.token_digest)
            .finish_non_exhaustive()
    }
}

#[derive(Clone, Debug)]
pub struct AgentPageMetadata {
    total_items: usize,
    first_index: usize,
    returned_items: usize,
    omitted_before: usize,
    omitted_after: usize,
    encoded_item_bytes: usize,
    continuation: Option<AgentFeedbackCursor>,
}

impl AgentPageMetadata {
    pub fn total_items(&self) -> usize {
        self.total_items
    }

    pub fn first_index(&self) -> usize {
        self.first_index
    }

    pub fn returned_items(&self) -> usize {
        self.returned_items
    }

    pub fn continuation(&self) -> Option<&AgentFeedbackCursor> {
        self.continuation.as_ref()
    }

    fn wire_value(&self) -> Value {
        json!({
            "total_items": self.total_items,
            "first_index": self.first_index,
            "returned_items": self.returned_items,
            "omitted_before": self.omitted_before,
            "omitted_after": self.omitted_after,
            "encoded_item_bytes": self.encoded_item_bytes,
            "continuation": self.continuation.as_ref().map(AgentFeedbackCursor::wire_value),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentClauseDropReference {
    clause: AgentClauseIdentity,
    consultation_digest: Arc<str>,
    authorization_digest: Arc<str>,
}

impl AgentClauseDropReference {
    pub fn clause(&self) -> &AgentClauseIdentity {
        &self.clause
    }

    pub fn consultation_digest(&self) -> &str {
        &self.consultation_digest
    }

    pub fn authorization_digest(&self) -> &str {
        &self.authorization_digest
    }

    fn wire_value(&self) -> Value {
        json!({
            "clause": self.clause.reference_wire_value(),
            "consultation_digest": self.consultation_digest.as_ref(),
            "authorization_digest": self.authorization_digest.as_ref(),
        })
    }
}

/// The contract's three partitions, and only those: `agent_houdini.tex`
/// gives a clause exactly these statuses, so a catalog record no partition
/// holds — what a rolled-back epoch leaves behind as provenance — has none
/// and is not shown at all (`AgentEligibilitySnapshot::visible_records`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentClauseStatus {
    Committed(FrameworkIILevel),
    Pending(FrameworkIILevel),
    /// Dead by refutation: a never-committed prophecy-free clause whose
    /// initialization was refuted at some level. Never revived.
    DeadRefuted(FrameworkIIDeadReason),
    /// Dead by drop: only an exact resubmission revives it, pending at its
    /// minimum level.
    DeadDropped,
}

impl AgentClauseStatus {
    fn wire_value(&self) -> Value {
        match self {
            Self::Committed(level) => {
                json!({"kind": "committed", "level": level.get()})
            }
            Self::Pending(level) => json!({"kind": "pending", "level": level.get()}),
            Self::DeadRefuted(reason) => json!({
                "kind": "dead",
                "cause": "refuted",
                "reason": reason.identity_fields(),
            }),
            Self::DeadDropped => json!({"kind": "dead", "cause": "dropped"}),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentCurrentRoot {
    role: FrameworkIICheckRole,
    attempt_row: u64,
    request_digest: Arc<str>,
    partition_digest: Arc<str>,
}

impl AgentCurrentRoot {
    fn wire_value(&self) -> Value {
        json!({
            "role": check_role_name(self.role),
            "attempt_row": self.attempt_row,
            "request_digest": self.request_digest.as_ref(),
            "partition_digest": self.partition_digest.as_ref(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentClauseFeedback {
    clause: AgentClauseIdentity,
    display: Option<Arc<str>>,
    origin: Arc<str>,
    protected: bool,
    minimum_level: FrameworkIILevel,
    status: AgentClauseStatus,
    current_roots: Arc<[AgentCurrentRoot]>,
    drop_reference: Option<AgentClauseDropReference>,
    summarized: bool,
}

impl AgentClauseFeedback {
    pub fn clause(&self) -> &AgentClauseIdentity {
        &self.clause
    }

    pub fn display(&self) -> Option<&str> {
        self.display.as_deref()
    }

    pub fn status(&self) -> &AgentClauseStatus {
        &self.status
    }

    pub fn drop_reference(&self) -> Option<&AgentClauseDropReference> {
        self.drop_reference.as_ref()
    }

    fn summarized(&self) -> Self {
        let mut summary = self.clone();
        summary.display = None;
        summary.current_roots = Arc::from([]);
        summary.summarized = true;
        summary
    }

    fn wire_value(&self) -> Value {
        json!({
            "clause": self.clause.wire_value(),
            "display": self.display.as_deref(),
            "origin": self.origin.as_ref(),
            "protected": self.protected,
            "minimum_level": self.minimum_level.get(),
            "status": self.status.wire_value(),
            "current_roots": self.current_roots.iter().map(AgentCurrentRoot::wire_value).collect::<Vec<_>>(),
            "drop_reference": self.drop_reference.as_ref().map(AgentClauseDropReference::wire_value),
            "summarized": self.summarized,
        })
    }
}

#[derive(Clone, Debug)]
pub struct AgentClausePage {
    metadata: AgentPageMetadata,
    items: Arc<[AgentClauseFeedback]>,
}

impl AgentClausePage {
    pub fn metadata(&self) -> &AgentPageMetadata {
        &self.metadata
    }

    pub fn items(&self) -> &[AgentClauseFeedback] {
        &self.items
    }

    fn wire_value(&self) -> Value {
        json!({
            "metadata": self.metadata.wire_value(),
            "items": self.items.iter().map(AgentClauseFeedback::wire_value).collect::<Vec<_>>(),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AgentAttemptOutcomeKind {
    Proved,
    Refuted,
    Inconclusive(FrameworkIIInconclusiveReason),
}

impl AgentAttemptOutcomeKind {
    fn wire_value(self) -> Value {
        match self {
            Self::Proved => json!({"kind": "proved"}),
            Self::Refuted => json!({"kind": "refuted"}),
            Self::Inconclusive(reason) => json!({
                "kind": "inconclusive",
                "reason": inconclusive_name(reason),
            }),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentAttemptOutcome {
    kind: AgentAttemptOutcomeKind,
    route_kind: Arc<str>,
    route_digest: Arc<str>,
    route: Option<AgentEvidenceRoute>,
    /// The numeric `AttemptId` a `Refuted` outcome's countermodel is keyed
    /// under (Pass 7.5c), so the `countermodel` tool can be pointed at this
    /// exact row's attempt. `None` for every non-refuting outcome, which
    /// keys no countermodel.
    attempt_id: Option<u64>,
}

impl AgentAttemptOutcome {
    pub fn kind(&self) -> AgentAttemptOutcomeKind {
        self.kind
    }

    pub fn route_kind(&self) -> &str {
        &self.route_kind
    }

    pub fn route(&self) -> Option<&AgentEvidenceRoute> {
        self.route.as_ref()
    }

    pub fn attempt_id(&self) -> Option<u64> {
        self.attempt_id
    }

    fn summarized(&self) -> Self {
        Self {
            kind: self.kind,
            route_kind: Arc::clone(&self.route_kind),
            route_digest: Arc::clone(&self.route_digest),
            route: None,
            attempt_id: self.attempt_id,
        }
    }

    fn wire_value(&self) -> Value {
        json!({
            "outcome": self.kind.wire_value(),
            "route_kind": self.route_kind.as_ref(),
            "route_digest": self.route_digest.as_ref(),
            "route": self.route.as_ref().map(AgentEvidenceRoute::wire_value),
            "route_summarized": self.route.is_none(),
            "attempt_id": self.attempt_id,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentLedgerFeedback {
    Attempt {
        row_ordinal: u64,
        clause: AgentClauseIdentity,
        level: FrameworkIILevel,
        role: FrameworkIICheckRole,
        request_digest: Arc<str>,
        partition_digest: Arc<str>,
        invalidated: bool,
        outcome: Box<AgentAttemptOutcome>,
        /// Measured Vampire wall time for this attempt, in nanoseconds.
        /// Absent for a theorem-closed or dictionary/semantic-key-reused row.
        solver_time_nanos: Option<u64>,
        /// Measured obligation-preparation time for this attempt, in
        /// nanoseconds. Absent for the same rows that leave
        /// `solver_time_nanos` absent. The wire name is on the pinned
        /// feedback-push schema and stays as it is; what it measures is the
        /// adapter's whole `prepare` call — piece-cache splicing plus any
        /// worker round trips that cache missed on — not one worker round
        /// trip.
        preparation_time_nanos: Option<u64>,
        previous_row_digest: Option<Arc<str>>,
        row_digest: Arc<str>,
    },
    Invalidation {
        row_ordinal: u64,
        invalidated_attempt: u64,
        target: AgentClauseIdentity,
        cause: Option<AgentClauseIdentity>,
        reason: FrameworkIIInvalidationReason,
        previous_row_digest: Option<Arc<str>>,
        row_digest: Arc<str>,
    },
}

impl AgentLedgerFeedback {
    fn summarized(&self) -> Self {
        match self {
            Self::Attempt {
                row_ordinal,
                clause,
                level,
                role,
                request_digest,
                partition_digest,
                invalidated,
                outcome,
                solver_time_nanos,
                preparation_time_nanos,
                previous_row_digest,
                row_digest,
                ..
            } => Self::Attempt {
                row_ordinal: *row_ordinal,
                clause: clause.clone(),
                level: *level,
                role: *role,
                request_digest: Arc::clone(request_digest),
                partition_digest: Arc::clone(partition_digest),
                invalidated: *invalidated,
                outcome: Box::new(outcome.summarized()),
                solver_time_nanos: *solver_time_nanos,
                preparation_time_nanos: *preparation_time_nanos,
                previous_row_digest: previous_row_digest.clone(),
                row_digest: Arc::clone(row_digest),
            },
            Self::Invalidation { .. } => self.clone(),
        }
    }

    /// Pass 7.5c: `pub(crate)` (not private) so the `history` tool surface
    /// in `search.rs` can render rows it fetched via
    /// [`PreCertificateAgentHoudiniState::clause_history_tool`] without
    /// duplicating this wire shape.
    pub(crate) fn wire_value(&self) -> Value {
        match self {
            Self::Attempt {
                row_ordinal,
                clause,
                level,
                role,
                request_digest,
                partition_digest,
                invalidated,
                outcome,
                solver_time_nanos,
                preparation_time_nanos,
                previous_row_digest,
                row_digest,
            } => json!({
                "kind": "attempt",
                "row_ordinal": row_ordinal,
                "clause": clause.wire_value(),
                "level": level.get(),
                "role": check_role_name(*role),
                "request_digest": request_digest.as_ref(),
                "partition_digest": partition_digest.as_ref(),
                "invalidated": invalidated,
                "result": outcome.wire_value(),
                "solver_time_nanos": solver_time_nanos,
                "preparation_time_nanos": preparation_time_nanos,
                "previous_row_digest": previous_row_digest.as_deref(),
                "row_digest": row_digest.as_ref(),
            }),
            Self::Invalidation {
                row_ordinal,
                invalidated_attempt,
                target,
                cause,
                reason,
                previous_row_digest,
                row_digest,
            } => json!({
                "kind": "invalidation",
                "row_ordinal": row_ordinal,
                "invalidated_attempt": invalidated_attempt,
                "target": target.wire_value(),
                "cause": cause.as_ref().map(AgentClauseIdentity::wire_value),
                "reason": invalidation_name(*reason),
                "previous_row_digest": previous_row_digest.as_deref(),
                "row_digest": row_digest.as_ref(),
            }),
        }
    }
}

#[derive(Clone, Debug)]
pub struct AgentLedgerPage {
    metadata: AgentPageMetadata,
    items: Arc<[AgentLedgerFeedback]>,
}

impl AgentLedgerPage {
    pub fn metadata(&self) -> &AgentPageMetadata {
        &self.metadata
    }

    pub fn items(&self) -> &[AgentLedgerFeedback] {
        &self.items
    }

    /// Pass 7.5c: `pub(crate)` (not private) so the `ledger` tool surface in
    /// `search.rs` can render a page it built via
    /// [`PreCertificateAgentHoudiniState::ledger_tool_page`] without
    /// duplicating this wire shape.
    pub(crate) fn wire_value(&self) -> Value {
        json!({
            "metadata": self.metadata.wire_value(),
            "items": self.items.iter().map(AgentLedgerFeedback::wire_value).collect::<Vec<_>>(),
        })
    }
}

// ------------------------------------------------------------
// Complete Private Validation Snapshot
// ------------------------------------------------------------

/// One pending clause of this consultation, with whether the controller
/// still authorizes a drop of it.
#[derive(Clone, Debug)]
struct AgentPendingEligibility {
    record: LeveledClauseRecord,
    level: FrameworkIILevel,
    drop_eligible: bool,
}

#[derive(Clone, Debug)]
struct AgentEligibilitySnapshot {
    catalog: LeveledClauseCatalog,
    proposal_revision: u64,
    registration_ordinal: u64,
    core_snapshot: Arc<LeveledCandidateSnapshot>,
    records: Arc<[LeveledClauseRecord]>,
    /// The catalog records some partition currently holds, in catalog
    /// order: the agent-visible clause state, and the exact window the
    /// clause page and its cursors range over.
    ///
    /// A rolled-back epoch leaves its interned records in the catalog as
    /// provenance while the partition goes back to the epoch's start
    /// (`houdini.tex` Algorithm 1), so `records` can hold a record no
    /// partition names. `agent_houdini.tex` gives a clause exactly three
    /// statuses — committed at a level, dead with its cause, pending at a
    /// level — so such a record has no status to show and is not part of
    /// what the agent is shown; an exact resubmission re-admits it and it
    /// is fresh again.
    visible_records: Arc<[LeveledClauseRecord]>,
    proposal_context: FrameworkIIProposalContext,
    pending: Arc<[AgentPendingEligibility]>,
    state_snapshot_digest: Arc<str>,
}

#[derive(Clone)]
pub(crate) struct AgentFeedbackValidationManifest {
    eligibility: Arc<AgentEligibilitySnapshot>,
    task_identity: TaskIdentity,
    run_digest: Arc<str>,
    consultation_digest: Arc<str>,
    shown_clauses: BTreeMap<ClauseId, AgentClauseIdentity>,
    shown_drops: BTreeMap<Arc<str>, ClauseId>,
    /// Clause identities shown as this push's Core (Pass 7.5c): tracked
    /// separately so a rejected drop attempt against one of them can name
    /// the specific reason ("Core clauses cannot be dropped") instead of
    /// the generic unauthorized-drop diagnostic.
    core_clause_ids: BTreeSet<ClauseId>,
    artifacts: BTreeMap<Arc<str>, ArtifactRef>,
    manifest_digest: Arc<str>,
}

struct AgentManifestVisibleAuthority {
    shown_clauses: BTreeMap<ClauseId, AgentClauseIdentity>,
    shown_drops: BTreeMap<Arc<str>, ClauseId>,
    core_clause_ids: BTreeSet<ClauseId>,
    artifacts: BTreeMap<Arc<str>, ArtifactRef>,
}

impl AgentFeedbackValidationManifest {
    #[allow(dead_code)] // Consumed by Pass 6d response admission.
    pub(crate) fn proposal_context(&self) -> &FrameworkIIProposalContext {
        &self.eligibility.proposal_context
    }

    pub(crate) fn pending_clauses(&self) -> impl ExactSizeIterator<Item = (ClauseId, bool)> + '_ {
        self.eligibility
            .pending
            .iter()
            .map(|entry| (entry.record.id(), entry.drop_eligible))
    }

    #[allow(dead_code)] // Consumed by Pass 6d response admission.
    pub(crate) fn pending_records(
        &self,
    ) -> impl ExactSizeIterator<Item = (&LeveledClauseRecord, bool)> + '_ {
        self.eligibility
            .pending
            .iter()
            .map(|entry| (&entry.record, entry.drop_eligible))
    }

    /// Resolve a read against the frozen catalog, independently of display/drop eligibility.
    pub(crate) fn resolve_read_clause(
        &self,
        identity: &AgentClauseIdentity,
    ) -> Option<&LeveledClauseRecord> {
        let index = usize::try_from(identity.clause_id.get()).ok()?;
        let record = self.eligibility.records.get(index)?;
        (record.id() == identity.clause_id && record_clause_identity(record) == *identity)
            .then_some(record)
    }

    pub(crate) fn read_clause_identity(&self, clause: ClauseId) -> Option<AgentClauseIdentity> {
        let record = self
            .eligibility
            .records
            .get(usize::try_from(clause.get()).ok()?)?;
        (record.id() == clause).then(|| record_clause_identity(record))
    }

    /// Resolve only an exact clause identity shown on this consultation's
    /// current clause page.
    #[allow(dead_code)] // Consumed by Pass 6d response admission.
    pub(crate) fn resolve_shown_clause(
        &self,
        identity: &AgentClauseIdentity,
    ) -> Option<&LeveledClauseRecord> {
        if self.shown_clauses.get(&identity.clause_id) != Some(identity) {
            return None;
        }
        let index = usize::try_from(identity.clause_id.get()).ok()?;
        let record = self.eligibility.records.get(index)?;
        (record.id() == identity.clause_id && record_clause_identity(record) == *identity)
            .then_some(record)
    }

    /// Resolve one shown drop reference against the exact drop eligibility
    /// of this consultation: a drop targets a pending clause, never a
    /// committed (Core) or dead one — see
    /// [`LeveledHoudiniState::drop_eligible_records`].
    pub(crate) fn resolve_shown_drop(
        &self,
        reference: &AgentClauseDropReference,
    ) -> Option<FrameworkIIProposalDrop> {
        if reference.consultation_digest.as_ref() != self.consultation_digest.as_ref()
            || self
                .shown_drops
                .get(&reference.authorization_digest)
                .copied()
                != Some(reference.clause.clause_id)
        {
            return None;
        }
        let shown_record = self.resolve_shown_clause(&reference.clause)?;
        let eligible_record = self
            .eligibility
            .proposal_context
            .drop_eligible_records()
            .iter()
            .find(|record| record.id() == reference.clause.clause_id)?;
        if eligible_record != shown_record {
            return None;
        }
        self.eligibility
            .proposal_context
            .drop_token(reference.clause.clause_id)
    }

    /// Whether `clause` is shown as part of this push's Core (Pass 7.5c),
    /// used to give a dropped Core clause the specific
    /// `core_clause_not_droppable` correction instead of the generic
    /// unauthorized-drop one (see `resolve_drops` in `agent.rs`).
    pub(crate) fn is_core_clause(&self, clause: ClauseId) -> bool {
        self.core_clause_ids.contains(&clause)
    }

    pub(crate) fn contains_artifact_reference(&self, reference: &AgentArtifactReference) -> bool {
        self.artifacts.contains_key(&reference.stable_id)
    }
}

impl fmt::Debug for AgentFeedbackValidationManifest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentFeedbackValidationManifest")
            .field("task", &self.task_identity.canonical_id())
            .field("run_digest", &self.run_digest)
            .field("consultation_digest", &self.consultation_digest)
            .field("pending_count", &self.eligibility.pending.len())
            .field("shown_clause_count", &self.shown_clauses.len())
            .field("shown_drop_count", &self.shown_drops.len())
            .field("artifact_reference_count", &self.artifacts.len())
            .field("manifest_digest", &self.manifest_digest)
            .finish_non_exhaustive()
    }
}

// ------------------------------------------------------------
// Complete Bounded Summary And Feedback Envelope
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentFeedbackSummary {
    tracked_clauses: usize,
    committed_clauses: usize,
    pending_clauses: usize,
    dead_clauses: usize,
    dead_refuted_clauses: usize,
    dead_dropped_clauses: usize,
    current_roots: usize,
    ledger_rows: usize,
    proved_attempts: usize,
    refuted_attempts: usize,
    inconclusive_attempts: usize,
    invalidations: usize,
    missing_current_roots: usize,
}

// ------------------------------------------------------------
// Pass 7.5c Push: Core, Last-Round Outcomes, And Retry
// ------------------------------------------------------------

/// A committed Core clause, as pushed every round: its identity, the
/// audited origin that placed it, and the level it was committed at.
#[derive(Clone, Debug, PartialEq, Eq)]
struct AgentPushCoreEntry {
    clause: AgentClauseIdentity,
    source: Arc<str>,
    level: FrameworkIILevel,
}

impl AgentPushCoreEntry {
    fn wire_value(&self) -> Value {
        json!({
            "clause": self.clause.wire_value(),
            "source": self.source.as_ref(),
            "level": self.level.get(),
        })
    }
}

/// One pending clause, as pushed every round: its identity, the audited
/// origin that placed it, its Lean-owned minimum level, and its current
/// level — the level it failed through in the last scan. Every pending
/// clause is checked at least once per epoch, so the current level is
/// always defined. Pending clauses are exactly the droppable ones, so
/// `drop_reference` is present whenever the push shows the drop authority.
#[derive(Clone, Debug, PartialEq, Eq)]
struct AgentPushPendingEntry {
    clause: AgentClauseIdentity,
    source: Arc<str>,
    minimum_level: FrameworkIILevel,
    current_level: FrameworkIILevel,
    drop_reference: Option<AgentClauseDropReference>,
}

impl AgentPushPendingEntry {
    fn wire_value(&self) -> Value {
        json!({
            "clause": self.clause.wire_value(),
            "source": self.source.as_ref(),
            "minimum_level": self.minimum_level.get(),
            "current_level": self.current_level.get(),
            "drop_reference": self.drop_reference.as_ref().map(AgentClauseDropReference::wire_value),
        })
    }
}

/// The outcome of one clause the agent proposed in the immediately
/// preceding consultation round, as reported by the following round's push.
/// The three contract outcomes: committed at a level, dead with a reason
/// (refuted or dropped), or pending having failed through a level.
#[derive(Clone, Debug, PartialEq, Eq)]
enum AgentLastRoundOutcome {
    Committed(FrameworkIILevel),
    DeadRefuted(FrameworkIIDeadReason),
    DeadDropped,
    Pending(FrameworkIILevel),
}

impl AgentLastRoundOutcome {
    fn wire_value(&self) -> Value {
        match self {
            Self::Committed(level) => json!({"kind": "committed", "level": level.get()}),
            Self::DeadRefuted(reason) => json!({
                "kind": "dead",
                "cause": "refuted",
                "reason": reason.identity_fields(),
            }),
            Self::DeadDropped => json!({"kind": "dead", "cause": "dropped"}),
            Self::Pending(level) => json!({"kind": "pending", "level": level.get()}),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AgentLastRoundEntry {
    clause: AgentClauseIdentity,
    source: Arc<str>,
    outcome: AgentLastRoundOutcome,
}

impl AgentLastRoundEntry {
    fn wire_value(&self) -> Value {
        json!({
            "clause": self.clause.wire_value(),
            "source": self.source.as_ref(),
            "outcome": self.outcome.wire_value(),
        })
    }
}

/// Whether some partition currently holds `clause`.
///
/// The catalog outlives the partitions: a rolled-back epoch's interned
/// records survive as provenance while the partition returns to the epoch's
/// start, so a catalog record is not by itself agent-visible clause state.
fn clause_partition_held(state: &LeveledHoudiniState, clause: ClauseId) -> bool {
    state.committed_levels().contains_key(&clause)
        || state.is_dead(clause)
        || state.pending_levels().contains_key(&clause)
}

/// Classify one previously proposed clause's current outcome for the push's
/// `last_round` field, over the contract's three partitions and no fourth.
///
/// A clause no partition holds has no outcome to report, and no round that
/// reaches this reports one: a rolled-back epoch records nothing at all as
/// its round's outcomes ([`FrameworkIIEpochResult::round_outcomes`]), and
/// an applied epoch leaves every identity it registered committed, dead, or
/// pending. The error is that invariant's check, never a reachable state.
fn last_round_outcome(
    state: &LeveledHoudiniState,
    clause: ClauseId,
) -> Result<AgentLastRoundOutcome, AgentFeedbackError> {
    Ok(
        if let Some(level) = state.committed_levels().get(&clause).copied() {
            AgentLastRoundOutcome::Committed(level)
        } else if let Some(cause) = state.dead_cause(clause) {
            match cause {
                FrameworkIIDeadCause::Refuted(reason) => AgentLastRoundOutcome::DeadRefuted(reason),
                FrameworkIIDeadCause::Dropped => AgentLastRoundOutcome::DeadDropped,
            }
        } else if let Some(level) = state.pending_levels().get(&clause).copied() {
            AgentLastRoundOutcome::Pending(level)
        } else {
            return Err(AgentFeedbackError::UnpartitionedClause(clause.get()));
        },
    )
}

fn build_core_entries(
    eligibility: &AgentEligibilitySnapshot,
    host_limits: &HostLimits,
) -> (Arc<[AgentPushCoreEntry]>, Option<HostLimitTruncation>) {
    let snapshot = &eligibility.core_snapshot;
    let order = snapshot.canonical_order();
    let total = order.len();
    let take = host_limits.shown_of("pushed_core", total);
    let entries = order[..take]
        .iter()
        .map(|clause| {
            let record = &snapshot.records()[clause];
            let level = snapshot
                .level_of(*clause)
                .expect("every canonical-order member has a level in its own snapshot");
            AgentPushCoreEntry {
                clause: record_clause_identity(record),
                source: Arc::from(origin_name(record.origin())),
                level,
            }
        })
        .collect::<Vec<_>>();
    let truncated = HostLimitTruncation::of(host_limits, "core", "pushed_core", total);
    (entries.into(), truncated)
}

/// Every pending clause, with its minimum and current levels and, when the
/// controller still authorizes it, the drop reference that removes it.
fn build_pending_entries(
    state: &LeveledHoudiniState,
    eligibility: &AgentEligibilitySnapshot,
    consultation_digest: &Arc<str>,
) -> Result<Arc<[AgentPushPendingEntry]>, AgentFeedbackError> {
    let drop_eligible = eligibility
        .proposal_context
        .drop_eligible_records()
        .iter()
        .map(LeveledClauseRecord::id)
        .collect::<BTreeSet<_>>();
    let mut entries = Vec::new();
    for (clause, current_level) in state.pending_levels() {
        let record = snapshot_record(eligibility.records.as_ref(), *clause)?;
        let identity = record_clause_identity(record);
        let drop_reference = drop_eligible.contains(clause).then(|| {
            let authorization_digest: Arc<str> = Arc::from(canonical_value_sha256(&json!({
                "domain": "whiel-agent-shown-drop-v1",
                "consultation_digest": consultation_digest.as_ref(),
                "proposal_revision": eligibility.proposal_revision,
                "registration_ordinal": eligibility.registration_ordinal,
                "record_digest": identity.record_digest(),
                "clause_id": identity.clause_id().get(),
            })));
            AgentClauseDropReference {
                clause: identity.clone(),
                consultation_digest: Arc::clone(consultation_digest),
                authorization_digest,
            }
        });
        entries.push(AgentPushPendingEntry {
            clause: identity,
            source: Arc::from(origin_name(record.origin())),
            minimum_level: record.minimum_level(),
            current_level: *current_level,
            drop_reference,
        });
    }
    Ok(entries.into())
}

fn build_last_round_entries(
    state: &LeveledHoudiniState,
    eligibility: &AgentEligibilitySnapshot,
    proposed: &[ClauseId],
) -> Result<Arc<[AgentLastRoundEntry]>, AgentFeedbackError> {
    let mut entries = Vec::with_capacity(proposed.len());
    for clause in proposed {
        let record = snapshot_record(eligibility.records.as_ref(), *clause)?;
        entries.push(AgentLastRoundEntry {
            clause: record_clause_identity(record),
            source: Arc::from(origin_name(record.origin())),
            outcome: last_round_outcome(state, *clause)?,
        });
    }
    Ok(entries.into())
}

impl AgentFeedbackSummary {
    fn wire_value(&self) -> Value {
        json!({
            "tracked_clauses": self.tracked_clauses,
            "committed_clauses": self.committed_clauses,
            "pending_clauses": self.pending_clauses,
            "dead_clauses": self.dead_clauses,
            "dead_refuted_clauses": self.dead_refuted_clauses,
            "dead_dropped_clauses": self.dead_dropped_clauses,
            "current_roots": self.current_roots,
            "ledger_rows": self.ledger_rows,
            "proved_attempts": self.proved_attempts,
            "refuted_attempts": self.refuted_attempts,
            "inconclusive_attempts": self.inconclusive_attempts,
            "invalidations": self.invalidations,
            "missing_current_roots": self.missing_current_roots,
        })
    }
}

#[derive(Clone)]
pub struct AgentFeedback {
    replay_owner: Result<
        Arc<super::replay_correspondence::ReplayFeedbackOwner>,
        super::replay_correspondence::ReplayCaptureError,
    >,
    task_digest: Arc<str>,
    scope_digest: Arc<str>,
    run_digest: Arc<str>,
    consultation_digest: Arc<str>,
    state_snapshot_digest: Arc<str>,
    validation_manifest_digest: Arc<str>,
    iteration: u64,
    remaining_search_budget: Duration,
    presentation: Arc<AgentFeedbackPresentation>,
    latest: AgentLatestFeedback,
    summary: AgentFeedbackSummary,
    clauses: AgentClausePage,
    ledger: AgentLedgerPage,
    manifest: Arc<AgentFeedbackValidationManifest>,
    encoded_bytes: usize,
    /// Pass 7.5c push data: precomputed at construction so `push_value`
    /// stays infallible and never repeats the truncation or classification
    /// work per call.
    core_entries: Arc<[AgentPushCoreEntry]>,
    /// The list this push truncated under a host limit, if any: the
    /// contract's `truncated` object, which generalises the old Core-only
    /// `core_truncated` marker by naming which list was cut and by which
    /// limit. `None` — the default — when no limit is set or none bit. Only
    /// the Core is truncatable today; a second truncatable pushed list
    /// would be a schema change, not a silent shape change here.
    truncated: Option<HostLimitTruncation>,
    /// The host limits in force for this push, reconciled with the
    /// controller state's own level bound. The response validator and the
    /// tool surface read them from here, so the limits enforced are exactly
    /// the limits the presentation stated.
    host_limits: HostLimits,
    last_round: Arc<[AgentLastRoundEntry]>,
    pending_entries: Arc<[AgentPushPendingEntry]>,
}

impl AgentFeedback {
    pub(super) fn replay_owner(
        &self,
    ) -> Result<
        &super::replay_correspondence::ReplayFeedbackOwner,
        super::replay_correspondence::ReplayCaptureError,
    > {
        self.replay_owner.as_deref().map_err(|error| *error)
    }
    pub fn task_digest(&self) -> &str {
        &self.task_digest
    }

    pub fn scope_digest(&self) -> &str {
        &self.scope_digest
    }

    pub fn run_digest(&self) -> &str {
        &self.run_digest
    }

    pub fn consultation_digest(&self) -> &str {
        &self.consultation_digest
    }

    pub fn state_snapshot_digest(&self) -> &str {
        &self.state_snapshot_digest
    }

    pub fn validation_manifest_digest(&self) -> &str {
        &self.validation_manifest_digest
    }

    pub fn iteration(&self) -> u64 {
        self.iteration
    }

    pub fn remaining_search_budget(&self) -> Duration {
        self.remaining_search_budget
    }

    /// The host limits in force for the push this feedback is, exactly as
    /// the presentation stated them.
    pub fn host_limits(&self) -> &HostLimits {
        &self.host_limits
    }

    pub fn presentation(&self) -> &Arc<AgentFeedbackPresentation> {
        &self.presentation
    }

    pub fn latest(&self) -> &AgentLatestFeedback {
        &self.latest
    }

    pub fn summary(&self) -> &AgentFeedbackSummary {
        &self.summary
    }

    pub fn clauses(&self) -> &AgentClausePage {
        &self.clauses
    }

    pub fn ledger(&self) -> &AgentLedgerPage {
        &self.ledger
    }

    /// Every drop reference shown anywhere in this push: the deprecated
    /// page's per-clause references plus each `pending` entry's reference.
    /// Response admission (`resolve_drops` in `agent.rs`) resolves a
    /// submitted drop against this set (via
    /// [`AgentFeedbackValidationManifest::resolve_shown_drop`]), never
    /// against either source alone.
    pub(crate) fn drop_references(&self) -> impl Iterator<Item = &AgentClauseDropReference> {
        self.clauses
            .items()
            .iter()
            .filter_map(AgentClauseFeedback::drop_reference)
            .chain(
                self.pending_entries
                    .iter()
                    .filter_map(|entry| entry.drop_reference.as_ref()),
            )
    }

    pub fn encoded_bytes(&self) -> usize {
        self.encoded_bytes
    }

    /// The number of pending clauses this push's private manifest records.
    pub fn private_pending_clause_count(&self) -> usize {
        self.manifest.pending_clauses().len()
    }

    pub fn authorizes_shown_drop(&self, reference: &AgentClauseDropReference) -> bool {
        self.manifest.resolve_shown_drop(reference).is_some()
    }

    pub fn issued_artifact_reference(&self, reference: &AgentArtifactReference) -> bool {
        self.manifest.contains_artifact_reference(reference)
    }

    /// Deprecated (Pass 7.5c): the single-request-response wire, carrying
    /// `summary`, the paged `clauses` list, and the paged `ledger` rows.
    /// Kept for one release for the pre-session request path in `agent.rs`;
    /// new callers use [`Self::push_value`], which never carries those
    /// three keys. Remove once the session/tool protocol switches callers.
    pub fn to_json_value(&self) -> Value {
        self.wire_value()
    }

    pub fn to_json_string(&self) -> Result<String, AgentFeedbackError> {
        serde_json::to_string(&self.wire_value())
            .map_err(|error| AgentFeedbackError::Serialization(error.to_string()))
    }

    /// The consultation-session push: schema version, the six binding
    /// digests, iteration and remaining budget, the standing presentation,
    /// the full (optionally capped) Core, the previous round's clause
    /// outcomes, every pending clause, the latest event, the enabled tool
    /// names, and the state revision this push carries.
    ///
    /// Never carries `summary`, the paged `clauses` list, or the paged
    /// `ledger` rows (see [`Self::to_json_value`] for those, until the
    /// session/tool protocol switches callers). Never carries `correction`:
    /// that belongs to the session/tool layer built on top of this method,
    /// which merges it in from its own correction state.
    pub fn push_value(&self, enabled_tools: &[&str], state_revision: u64) -> Value {
        let mut value = json!({
            "schema_version": AGENT_FEEDBACK_SCHEMA_VERSION,
            "binding": {
                "task_digest": self.task_digest.as_ref(),
                "scope_digest": self.scope_digest.as_ref(),
                "run_digest": self.run_digest.as_ref(),
                "consultation_digest": self.consultation_digest.as_ref(),
                "state_snapshot_digest": self.state_snapshot_digest.as_ref(),
                "validation_manifest_digest": self.validation_manifest_digest.as_ref(),
            },
            "iteration": self.iteration,
            "remaining_search_budget_ns": self.remaining_search_budget.as_nanos().to_string(),
            "presentation": self.presentation.wire_value(),
            "core": self.core_entries.iter().map(AgentPushCoreEntry::wire_value).collect::<Vec<_>>(),
            "last_round": self.last_round.iter().map(AgentLastRoundEntry::wire_value).collect::<Vec<_>>(),
            "pending": self.pending_entries.iter().map(AgentPushPendingEntry::wire_value).collect::<Vec<_>>(),
            "latest": self.latest.wire_value(),
            "tools": enabled_tools,
            "state_revision": state_revision,
        });
        if let Some(truncation) = &self.truncated {
            value
                .as_object_mut()
                .expect("push is an object")
                .insert("truncated".to_string(), truncation.wire_value());
        }
        value
    }

    #[allow(dead_code)] // Consumed by Pass 6d response admission.
    pub(crate) fn validation_manifest(&self) -> &AgentFeedbackValidationManifest {
        &self.manifest
    }

    fn wire_value(&self) -> Value {
        json!({
            "schema_version": AGENT_FEEDBACK_SCHEMA_VERSION,
            "binding": {
                "task_digest": self.task_digest.as_ref(),
                "scope_digest": self.scope_digest.as_ref(),
                "run_digest": self.run_digest.as_ref(),
                "consultation_digest": self.consultation_digest.as_ref(),
                "state_snapshot_digest": self.state_snapshot_digest.as_ref(),
                "validation_manifest_digest": self.validation_manifest_digest.as_ref(),
            },
            "iteration": self.iteration,
            "remaining_search_budget_ns": self.remaining_search_budget.as_nanos().to_string(),
            "presentation": self.presentation.wire_value(),
            "latest": self.latest.wire_value(),
            "summary": self.summary.wire_value(),
            "clauses": self.clauses.wire_value(),
            "ledger": self.ledger.wire_value(),
        })
    }
}

impl fmt::Debug for AgentFeedback {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentFeedback")
            .field("task_digest", &self.task_digest)
            .field("scope_digest", &self.scope_digest)
            .field("run_digest", &self.run_digest)
            .field("consultation_digest", &self.consultation_digest)
            .field("iteration", &self.iteration)
            .field("encoded_bytes", &self.encoded_bytes)
            .finish_non_exhaustive()
    }
}

// ------------------------------------------------------------
// Pre-Certificate Feedback Session
// ------------------------------------------------------------

#[derive(Clone, Copy)]
enum AgentFeedbackPageRequest<'a> {
    Advance(Option<&'a AgentFeedbackCursor>),
    PreserveCurrent,
}

/// Search-facing state for Pass 6 before termination or evidence freezing.
///
/// The caller-neutral [`LeveledHoudiniState`] remains the verification-state
/// owner. This wrapper owns only immutable presentation data, paging state,
/// and the current private validation manifest.
#[derive(Clone)]
pub struct PreCertificateAgentHoudiniState {
    replay_run_configuration: Result<
        Option<super::replay_correspondence::ReplayRunConfiguration>,
        super::replay_correspondence::ReplayCaptureError,
    >,
    task: Arc<SynthesisTask>,
    artifact_backend: BackendId,
    session_digest: Arc<str>,
    catalog: LeveledClauseCatalog,
    policy: AgentFeedbackPolicy,
    presentation: Arc<AgentFeedbackPresentation>,
    consultation_ordinal: u64,
    current_latest: AgentSearchFeedback,
    current_feedback: Option<AgentFeedback>,
    eligibility_cache: Option<Arc<AgentEligibilitySnapshot>>,
    /// Clause identities the agent proposed in the round that most recently
    /// concluded (Pass 7.5c), set by [`Self::record_round_proposals`]. The
    /// next built push reports each one's current outcome as `last_round`.
    /// Empty before any round has been recorded, including at session
    /// start.
    previous_round_proposed: Arc<[ClauseId]>,
    /// The run's host limits, reconciled once with the controller state's
    /// own level bound. Every push carries this value, so what the
    /// presentation states, what the push truncates, what the tools
    /// truncate, and what a submission is refused by are all one thing.
    host_limits: HostLimits,
}

impl PreCertificateAgentHoudiniState {
    pub fn new(
        task: Arc<SynthesisTask>,
        artifacts: &ArtifactStore,
        houdini: &LeveledHoudiniState,
        remaining_search_budget: Duration,
        policy: AgentFeedbackPolicy,
    ) -> Result<Self, AgentFeedbackError> {
        if artifacts.task_identity() != task.identity() {
            return Err(AgentFeedbackError::WrongArtifactBackend);
        }
        let host_limits = policy
            .limits()
            .host_limits
            .with_level_bound(houdini.max_level().map(|bound| bound.get()))
            .map_err(AgentFeedbackError::HostLimits)?;
        let presentation = build_shared_presentation(&task, houdini, &policy)?;
        let artifact_backend = artifacts.backend_id();
        let session_digest: Arc<str> = Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-agent-feedback-session-v2",
            "artifact_backend": artifact_backend.to_string(),
        })));
        let initial = AgentSearchFeedback::initial();
        let mut state = Self {
            replay_run_configuration: artifacts
                .run_configuration()
                .map(super::replay_correspondence::ReplayRunConfiguration::capture)
                .transpose(),
            task,
            artifact_backend,
            session_digest,
            catalog: houdini.catalog().clone(),
            policy,
            presentation,
            consultation_ordinal: 0,
            current_latest: initial.clone(),
            current_feedback: None,
            eligibility_cache: None,
            previous_round_proposed: Arc::from([]),
            host_limits,
        };
        let feedback = state.build_feedback_candidate(
            houdini,
            &initial,
            remaining_search_budget,
            1,
            AgentFeedbackPageRequest::Advance(None),
        )?;
        state
            .catalog
            .install_record_limit(state.host_limits.get_usize("catalog_size"))?;
        let (_, records) = state.catalog.record_snapshot()?;
        if records.as_ref() != feedback.manifest.eligibility.records.as_ref() {
            return Err(AgentFeedbackError::ConcurrentCatalogChange);
        }
        state.consultation_ordinal = 1;
        state.current_feedback = Some(feedback);
        Ok(state)
    }

    pub fn feedback(&self) -> &AgentFeedback {
        self.current_feedback
            .as_ref()
            .expect("a feedback session always has its initial view")
    }

    pub fn policy(&self) -> &AgentFeedbackPolicy {
        &self.policy
    }

    /// The run's host limits, with the controller state's level bound
    /// folded in. Absent limits are the default.
    pub fn host_limits(&self) -> &HostLimits {
        &self.host_limits
    }

    /// Record the clause identities the agent proposed in the round that
    /// just concluded (Pass 7.5c), deduplicated and sorted. The next push
    /// built by [`Self::build_next_feedback`] (or
    /// [`Self::build_next_feedback_from_cursor`]) reports each one's
    /// current outcome as its `last_round`. The session/tool layer calls
    /// this once per round, after applying a submission to `houdini` and
    /// before requesting the next push.
    pub fn record_round_proposals<I>(&mut self, clauses: I)
    where
        I: IntoIterator<Item = ClauseId>,
    {
        let mut proposed = clauses.into_iter().collect::<Vec<_>>();
        proposed.sort_unstable();
        proposed.dedup();
        self.previous_round_proposed = proposed.into();
    }

    /// The clause identities most recently recorded by
    /// [`Self::record_round_proposals`], in ascending order.
    pub fn previous_round_proposals(&self) -> &[ClauseId] {
        &self.previous_round_proposed
    }

    /// Pass 7.5c `ledger` tool: one page of ledger rows ending at `end` (or
    /// the full ledger when `end` is `None`), reusing `build_ledger_page`
    /// directly against the exact eligibility snapshot and ledger this
    /// session's current push was built from. Unlike the deprecated paged
    /// `ledger` key the pre-7.5c wire carried, the tool's cursor is a plain
    /// row-index local to this session's current push: it needs none of the
    /// cross-consultation staleness machinery `AgentFeedbackCursor` carries
    /// for [`Self::build_next_feedback_from_cursor`], because the tool
    /// answers only inside the single push it is bound to.
    pub fn ledger_tool_page(
        &self,
        houdini: &LeveledHoudiniState,
        end: Option<usize>,
    ) -> Result<AgentLedgerPage, AgentFeedbackError> {
        self.validate_run_state(houdini)?;
        let feedback = self.feedback();
        let eligibility = &feedback.manifest.eligibility;
        let total_ledger = houdini.attempts().rows().len();
        let end = end.unwrap_or(total_ledger).min(total_ledger);
        let consultation_digest: Arc<str> = Arc::from(feedback.consultation_digest());
        let mut sanitizer = AgentArtifactSanitizer::new(
            self.artifact_backend,
            Arc::from(self.catalog.instance_digest()),
            Arc::clone(&self.session_digest),
        );
        build_ledger_page(
            houdini,
            eligibility,
            end,
            &consultation_digest,
            &mut sanitizer,
            &self.policy,
        )
    }

    /// The `history` tool: `clause`'s own attempt rows (never invalidation
    /// rows), oldest first and complete. Per-clause history carries no
    /// page and no cap (`agent_houdini.tex`: `history(clause)` is the
    /// per-clause history, `ledger(cursor)` the paged rows), so nothing a
    /// clause has been through is hidden from the proposer; the attempt
    /// history's own memory guard is the only bound on its length. Reuses
    /// the same sanitized per-row projection as the ledger page — never
    /// proof text, only level, role, outcome kind, profile, and
    /// solver/preparation time (`AgentEvidenceRoute` never carries proof
    /// text).
    pub fn clause_history_tool(
        &self,
        houdini: &LeveledHoudiniState,
        clause: ClauseId,
    ) -> Result<Vec<AgentLedgerFeedback>, AgentFeedbackError> {
        self.validate_run_state(houdini)?;
        let feedback = self.feedback();
        let eligibility = &feedback.manifest.eligibility;
        let mut sanitizer = AgentArtifactSanitizer::new(
            self.artifact_backend,
            Arc::from(self.catalog.instance_digest()),
            Arc::clone(&self.session_digest),
        );
        let rows = houdini.attempts().rows();
        let mut matches = Vec::new();
        for row in rows.iter() {
            let LevelLedgerRow::Attempt(attempt) = row else {
                continue;
            };
            if attempt.request().clause() != clause {
                continue;
            }
            matches.push(project_ledger_feedback(
                houdini,
                eligibility.records.as_ref(),
                row,
                &mut sanitizer,
                &self.policy,
            )?);
        }
        Ok(matches)
    }

    /// Refresh only the authoritative time shown by the current consultation.
    ///
    /// This must run before the current consultation has been submitted. The
    /// consultation ordinal and exact clause and ledger positions remain
    /// unchanged. Because time is part of consultation authority, refreshed
    /// feedback receives new consultation and private-manifest digests.
    pub fn refresh_current_feedback(
        &mut self,
        houdini: &LeveledHoudiniState,
        remaining_search_budget: Duration,
    ) -> Result<&AgentFeedback, AgentFeedbackError> {
        let latest = self.current_latest.clone();
        let feedback = self.build_feedback_candidate(
            houdini,
            &latest,
            remaining_search_budget,
            self.consultation_ordinal,
            AgentFeedbackPageRequest::PreserveCurrent,
        )?;
        self.current_feedback = Some(feedback);
        Ok(self.feedback())
    }

    pub fn build_next_feedback(
        &mut self,
        houdini: &LeveledHoudiniState,
        latest: &AgentSearchFeedback,
        remaining_search_budget: Duration,
    ) -> Result<&AgentFeedback, AgentFeedbackError> {
        self.publish_next_feedback(houdini, latest, remaining_search_budget, None)
    }

    pub fn build_next_feedback_from_cursor(
        &mut self,
        houdini: &LeveledHoudiniState,
        latest: &AgentSearchFeedback,
        remaining_search_budget: Duration,
        cursor: &AgentFeedbackCursor,
    ) -> Result<&AgentFeedback, AgentFeedbackError> {
        self.publish_next_feedback(houdini, latest, remaining_search_budget, Some(cursor))
    }

    fn publish_next_feedback(
        &mut self,
        houdini: &LeveledHoudiniState,
        latest: &AgentSearchFeedback,
        remaining_search_budget: Duration,
        cursor: Option<&AgentFeedbackCursor>,
    ) -> Result<&AgentFeedback, AgentFeedbackError> {
        let next = self
            .consultation_ordinal
            .checked_add(1)
            .ok_or(AgentFeedbackError::ArithmeticOverflow)?;
        let feedback = self.build_feedback_candidate(
            houdini,
            latest,
            remaining_search_budget,
            next,
            AgentFeedbackPageRequest::Advance(cursor),
        )?;
        self.consultation_ordinal = next;
        self.current_latest = latest.clone();
        self.current_feedback = Some(feedback);
        Ok(self.feedback())
    }

    fn build_feedback_candidate(
        &mut self,
        houdini: &LeveledHoudiniState,
        latest: &AgentSearchFeedback,
        remaining_search_budget: Duration,
        iteration: u64,
        page_request: AgentFeedbackPageRequest<'_>,
    ) -> Result<AgentFeedback, AgentFeedbackError> {
        self.validate_run_state(houdini)?;
        let eligibility = self.eligibility(houdini)?;
        let initial_allowed =
            iteration == 1 && matches!(&latest.kind, AgentSearchFeedbackKind::Initial);
        if !latest.matches(&eligibility, initial_allowed) {
            return Err(AgentFeedbackError::StaleLatestFeedback);
        }
        let total_clauses = eligibility.visible_records.len();
        let total_ledger = houdini.attempts().rows().len();
        let (clause_start, ledger_end) =
            self.page_positions(page_request, &eligibility, total_clauses, total_ledger)?;
        let replay_latest = latest.clone();
        let latest_digest = latest_binding_digest(latest)?;
        let consultation_digest: Arc<str> = Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-agent-consultation-v2",
            "task_digest": self.presentation.task.task_digest(),
            "scope_digest": self.presentation.scope_digest(),
            "run_digest": self.catalog.instance_digest(),
            "iteration": iteration,
            "state_snapshot_digest": eligibility.state_snapshot_digest.as_ref(),
            "latest_digest": latest_digest,
            "session_digest": self.session_digest.as_ref(),
            "remaining_search_budget_ns": remaining_search_budget.as_nanos().to_string(),
            "clause_page_start": clause_start,
            "ledger_page_end": ledger_end,
            "policy_digest": self.policy.digest(),
        })));
        let mut sanitizer = AgentArtifactSanitizer::new(
            self.artifact_backend,
            Arc::from(self.catalog.instance_digest()),
            Arc::clone(&self.session_digest),
        );
        let latest = project_latest_feedback(latest, &mut sanitizer, &self.policy)?;
        let clauses = build_clause_page(
            houdini,
            &eligibility,
            clause_start,
            &consultation_digest,
            &self.policy,
        )?;
        let ledger = build_ledger_page(
            houdini,
            &eligibility,
            ledger_end,
            &consultation_digest,
            &mut sanitizer,
            &self.policy,
        )?;
        let summary = build_feedback_summary(houdini, eligibility.records.as_ref())?;
        let host_limits = self.host_limits;
        let (core_entries, core_truncation) = build_core_entries(&eligibility, &host_limits);
        let pending_entries = build_pending_entries(houdini, &eligibility, &consultation_digest)?;
        let last_round =
            build_last_round_entries(houdini, &eligibility, &self.previous_round_proposed)?;

        // A tool's clause reference must resolve against every clause the
        // push actually shows (Core, pending, last-round),
        // not only the deprecated page window `clauses` still computes
        // internally (see `to_json_value`). Fold every push clause identity
        // and drop reference into the manifest's visible authority so
        // `resolve_shown_clause`/`resolve_shown_drop` cover both.
        let mut shown_clauses = referenceable_clause_identities(&clauses)?;
        let mut shown_drops = clauses
            .items()
            .iter()
            .filter_map(AgentClauseFeedback::drop_reference)
            .map(|reference| {
                (
                    Arc::clone(&reference.authorization_digest),
                    reference.clause.clause_id,
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut core_clause_ids = BTreeSet::new();
        for entry in core_entries.iter() {
            core_clause_ids.insert(entry.clause.clause_id);
            shown_clauses
                .entry(entry.clause.clause_id)
                .or_insert_with(|| entry.clause.clone());
        }
        for entry in last_round.iter() {
            shown_clauses
                .entry(entry.clause.clause_id)
                .or_insert_with(|| entry.clause.clone());
        }
        for entry in pending_entries.iter() {
            shown_clauses
                .entry(entry.clause.clause_id)
                .or_insert_with(|| entry.clause.clone());
            if let Some(drop_reference) = &entry.drop_reference {
                shown_drops.insert(
                    Arc::clone(&drop_reference.authorization_digest),
                    drop_reference.clause.clause_id,
                );
            }
        }
        let shown_artifacts = shown_artifact_ids(&latest, &ledger);
        sanitizer
            .references
            .retain(|stable_id, _| shown_artifacts.contains(stable_id));
        let manifest = build_validation_manifest(
            &self.task,
            Arc::clone(&eligibility),
            Arc::clone(&self.session_digest),
            Arc::clone(&consultation_digest),
            AgentManifestVisibleAuthority {
                shown_clauses,
                shown_drops,
                core_clause_ids,
                artifacts: sanitizer.references,
            },
            &self.policy,
        )?;
        let replay_owner = capture_replay_feedback_owner(
            self,
            houdini,
            &replay_latest,
            &eligibility,
            &manifest,
            iteration,
            remaining_search_budget,
            clause_start,
            ledger_end,
            &clauses,
            &ledger,
        )
        .map(Arc::new);
        let mut feedback = AgentFeedback {
            replay_owner,
            task_digest: Arc::from(self.presentation.task.task_digest()),
            scope_digest: Arc::from(self.presentation.scope_digest()),
            run_digest: Arc::from(self.catalog.instance_digest()),
            consultation_digest,
            state_snapshot_digest: Arc::clone(&eligibility.state_snapshot_digest),
            validation_manifest_digest: Arc::clone(&manifest.manifest_digest),
            iteration,
            remaining_search_budget,
            presentation: Arc::clone(&self.presentation),
            latest,
            summary,
            clauses,
            ledger,
            manifest: Arc::new(manifest),
            encoded_bytes: 0,
            core_entries,
            truncated: core_truncation,
            host_limits,
            last_round,
            pending_entries,
        };
        let encoded_bytes = json_bytes(&feedback.wire_value())?;
        if encoded_bytes > self.policy.limits().max_feedback_bytes {
            return Err(AgentFeedbackError::FeedbackTooLarge {
                found: encoded_bytes,
                limit: self.policy.limits().max_feedback_bytes,
            });
        }
        feedback.encoded_bytes = encoded_bytes;
        let (final_ordinal, final_records) = self.catalog.record_snapshot()?;
        if final_ordinal != eligibility.registration_ordinal
            || final_records.as_ref() != eligibility.records.as_ref()
        {
            return Err(AgentFeedbackError::ConcurrentCatalogChange);
        }
        Ok(feedback)
    }

    fn validate_run_state(&self, houdini: &LeveledHoudiniState) -> Result<(), AgentFeedbackError> {
        if houdini.catalog() != &self.catalog {
            return Err(AgentFeedbackError::WrongRun);
        }
        if houdini.catalog().scope().task_identity() != self.task.identity() {
            return Err(AgentFeedbackError::WrongTask);
        }
        // The retained attempt history has one documented memory guard,
        // the agent policy's `max_attempt_history_records`; the feedback
        // side keeps no second bound on the run's length.
        Ok(())
    }

    fn eligibility(
        &mut self,
        houdini: &LeveledHoudiniState,
    ) -> Result<Arc<AgentEligibilitySnapshot>, AgentFeedbackError> {
        let context = houdini.proposal_context()?;
        let (registration_ordinal, records) = self.catalog.record_snapshot()?;
        if context.expected_registration_ordinal() != registration_ordinal {
            return Err(AgentFeedbackError::ConcurrentCatalogChange);
        }
        if let Some(limit) = self.host_limits.get_usize("catalog_size")
            && records.len() > limit
        {
            return Err(AgentFeedbackError::TrackedClauseLimit {
                found: records.len(),
                limit,
            });
        }
        let drop_eligible = context
            .drop_eligible_records()
            .iter()
            .map(LeveledClauseRecord::id)
            .collect::<BTreeSet<_>>();
        let mut pending = Vec::new();
        for (clause, level) in houdini.pending_levels() {
            if houdini.committed_levels().contains_key(clause) || houdini.is_dead(*clause) {
                return Err(AgentFeedbackError::InconsistentPendingPartition);
            }
            pending.push(AgentPendingEligibility {
                record: snapshot_record(&records, *clause)?.clone(),
                level: *level,
                drop_eligible: drop_eligible.contains(clause),
            });
        }
        // The agent-visible window: the records some partition holds. A
        // rolled-back epoch's interned records stay in the catalog as
        // provenance but leave every partition, and the contract gives a
        // clause no status outside the three partitions.
        let visible_records: Arc<[LeveledClauseRecord]> = records
            .iter()
            .filter(|record| clause_partition_held(houdini, record.id()))
            .cloned()
            .collect();
        let state_snapshot_digest: Arc<str> = Arc::from(state_snapshot_digest(
            houdini,
            registration_ordinal,
            &records,
        )?);
        if let Some(cached) = &self.eligibility_cache
            && cached.catalog == self.catalog
            && cached.proposal_revision == houdini.proposal_revision()
            && cached.registration_ordinal == registration_ordinal
            && cached.records.as_ref() == records.as_ref()
            && cached
                .core_snapshot
                .same_partition(houdini.core().snapshot())
            && cached.pending.len() == pending.len()
            && cached.pending.iter().zip(&pending).all(|(left, right)| {
                left.record == right.record
                    && left.level == right.level
                    && left.drop_eligible == right.drop_eligible
            })
            && cached.state_snapshot_digest == state_snapshot_digest
            && cached.visible_records.as_ref() == visible_records.as_ref()
        {
            return Ok(Arc::clone(cached));
        }
        let snapshot = Arc::new(AgentEligibilitySnapshot {
            catalog: self.catalog.clone(),
            proposal_revision: houdini.proposal_revision(),
            registration_ordinal,
            core_snapshot: Arc::clone(houdini.core().snapshot()),
            records,
            visible_records,
            proposal_context: context,
            pending: pending.into(),
            state_snapshot_digest,
        });
        self.eligibility_cache = Some(Arc::clone(&snapshot));
        Ok(snapshot)
    }

    fn page_positions(
        &self,
        request: AgentFeedbackPageRequest<'_>,
        eligibility: &Arc<AgentEligibilitySnapshot>,
        total_clauses: usize,
        total_ledger: usize,
    ) -> Result<(usize, usize), AgentFeedbackError> {
        if matches!(request, AgentFeedbackPageRequest::PreserveCurrent) {
            let current = self
                .current_feedback
                .as_ref()
                .ok_or(AgentFeedbackError::StaleLatestFeedback)?;
            if !Arc::ptr_eq(&current.manifest.eligibility, eligibility)
                || current.state_snapshot_digest != eligibility.state_snapshot_digest
            {
                return Err(AgentFeedbackError::StaleLatestFeedback);
            }
            let ledger_end = current
                .ledger
                .metadata
                .first_index
                .checked_add(current.ledger.metadata.returned_items)
                .ok_or(AgentFeedbackError::ArithmeticOverflow)?;
            if current.clauses.metadata.first_index > total_clauses || ledger_end > total_ledger {
                return Err(AgentFeedbackError::StaleLatestFeedback);
            }
            return Ok((current.clauses.metadata.first_index, ledger_end));
        }

        let mut clause_start = 0;
        let mut ledger_end = total_ledger;
        if let Some(current) = &self.current_feedback {
            clause_start = current
                .clauses
                .metadata
                .continuation
                .as_ref()
                .map_or(0, AgentFeedbackCursor::offset)
                .min(total_clauses);
            ledger_end = current
                .ledger
                .metadata
                .continuation
                .as_ref()
                .map_or(total_ledger, AgentFeedbackCursor::offset)
                .min(total_ledger);
        }
        let AgentFeedbackPageRequest::Advance(Some(cursor)) = request else {
            return Ok((clause_start, ledger_end));
        };
        let current = self
            .current_feedback
            .as_ref()
            .ok_or(AgentFeedbackError::StaleCursor)?;
        let issued = match cursor.category {
            AgentFeedbackPageCategory::Clauses => current.clauses.metadata.continuation.as_ref(),
            AgentFeedbackPageCategory::Ledger => current.ledger.metadata.continuation.as_ref(),
        }
        .ok_or(AgentFeedbackError::StaleCursor)?;
        if cursor.token_digest != issued.token_digest
            || cursor.offset != issued.offset
            || cursor.source_consultation_digest != current.consultation_digest
            || cursor.state_snapshot_digest != eligibility.state_snapshot_digest
            || !Arc::ptr_eq(&cursor.authority, eligibility)
            || !Arc::ptr_eq(&issued.authority, eligibility)
        {
            return Err(AgentFeedbackError::StaleCursor);
        }
        match cursor.category {
            AgentFeedbackPageCategory::Clauses => {
                if cursor.offset > total_clauses {
                    return Err(AgentFeedbackError::StaleCursor);
                }
                clause_start = cursor.offset;
            }
            AgentFeedbackPageCategory::Ledger => {
                if cursor.offset > total_ledger {
                    return Err(AgentFeedbackError::StaleCursor);
                }
                ledger_end = cursor.offset;
            }
        }
        Ok((clause_start, ledger_end))
    }
}

fn shown_artifact_ids(
    latest: &AgentLatestFeedback,
    ledger: &AgentLedgerPage,
) -> BTreeSet<Arc<str>> {
    let mut shown = BTreeSet::new();
    match latest {
        AgentLatestFeedback::Failure(failure) => {
            collect_failure_artifacts(failure, &mut shown);
        }
        AgentLatestFeedback::Initial
        | AgentLatestFeedback::PostconditionOpen(_)
        | AgentLatestFeedback::CounterexampleRejected { .. } => {}
    }
    for row in ledger.items() {
        if let AgentLedgerFeedback::Attempt { outcome, .. } = row
            && let Some(route) = &outcome.route
        {
            collect_route_artifacts(route, &mut shown);
        }
    }
    shown
}

fn collect_failure_artifacts(failure: &AgentFailureFeedback, shown: &mut BTreeSet<Arc<str>>) {
    shown.extend(
        failure
            .artifacts
            .iter()
            .map(|reference| Arc::clone(&reference.stable_id)),
    );
}

fn collect_route_artifacts(route: &AgentEvidenceRoute, shown: &mut BTreeSet<Arc<str>>) {
    match route {
        AgentEvidenceRoute::RuntimeProof { artifacts, .. }
        | AgentEvidenceRoute::ValidatedRefutation { artifacts, .. } => {
            shown.extend(
                artifacts
                    .iter()
                    .map(|reference| Arc::clone(&reference.stable_id)),
            );
        }
        AgentEvidenceRoute::ProtectedTheorem { artifact, .. } => {
            shown.insert(Arc::clone(&artifact.stable_id));
        }
        AgentEvidenceRoute::RetryProgress {
            peer_failure,
            artifacts,
            ..
        } => {
            shown.extend(
                artifacts
                    .iter()
                    .map(|reference| Arc::clone(&reference.stable_id)),
            );
            if let Some(failure) = peer_failure {
                collect_failure_artifacts(failure, shown);
            }
        }
        // A suspended check ran no solver and published no artifact.
        AgentEvidenceRoute::Suspended => {}
        #[cfg(test)]
        AgentEvidenceRoute::TestScaffold => {}
    }
}

impl fmt::Debug for PreCertificateAgentHoudiniState {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("PreCertificateAgentHoudiniState")
            .field("task", &self.task.identity().canonical_id())
            .field("run_digest", &self.catalog.instance_digest())
            .field("consultation_ordinal", &self.consultation_ordinal)
            .field("policy_digest", &self.policy.digest())
            .finish_non_exhaustive()
    }
}

fn snapshot_record(
    records: &[LeveledClauseRecord],
    clause: ClauseId,
) -> Result<&LeveledClauseRecord, AgentFeedbackError> {
    usize::try_from(clause.get())
        .ok()
        .and_then(|index| records.get(index))
        .filter(|record| record.id() == clause)
        .ok_or(AgentFeedbackError::UnknownClause(clause.get()))
}

fn state_snapshot_digest(
    state: &LeveledHoudiniState,
    registration_ordinal: u64,
    records: &[LeveledClauseRecord],
) -> Result<String, AgentFeedbackError> {
    state_snapshot_digest_in_domain(
        "whiel-agent-feedback-state-snapshot-v3",
        state,
        registration_ordinal,
        records,
    )
}

fn state_snapshot_digest_in_domain(
    domain: &str,
    state: &LeveledHoudiniState,
    registration_ordinal: u64,
    records: &[LeveledClauseRecord],
) -> Result<String, AgentFeedbackError> {
    let committed = state
        .committed_levels()
        .iter()
        .map(|(clause, level)| json!([clause.get(), level.get()]))
        .collect::<Vec<_>>();
    let pending = state
        .pending_levels()
        .iter()
        .map(|(clause, level)| json!([clause.get(), level.get()]))
        .collect::<Vec<_>>();
    let dead = state
        .dead()
        .iter()
        .map(|(clause, cause)| match cause {
            FrameworkIIDeadCause::Refuted(reason) => {
                json!([clause.get(), "refuted", reason.identity_fields()])
            }
            FrameworkIIDeadCause::Dropped => json!([clause.get(), "dropped"]),
        })
        .collect::<Vec<_>>();
    let mut roots = Vec::new();
    for record in records {
        for role in [
            FrameworkIICheckRole::Initialization,
            FrameworkIICheckRole::Maintenance,
        ] {
            if let Some(root) = state.current_root(record.id(), role) {
                roots.push(json!({
                    "clause": record.id().get(),
                    "role": check_role_name(role),
                    "attempt_row": root.attempt_row(),
                    "request_digest": root.request_digest(),
                    "partition_digest": root.partition_digest(),
                }));
            }
        }
    }
    let ledger_head = state
        .attempts()
        .rows()
        .last()
        .map(LevelLedgerRow::row_digest);
    Ok(canonical_value_sha256(&json!({
        "domain": domain,
        "task": task_identity_fields(state.catalog().scope()),
        "scope_digest": state.catalog().scope().identity_sha256(),
        "run_digest": state.catalog().instance_digest(),
        "proposal_revision": state.proposal_revision(),
        "registration_ordinal": registration_ordinal,
        "record_digests": records.iter().map(LeveledClauseRecord::record_digest).collect::<Vec<_>>(),
        "core_partition_digest": state.core().snapshot().partition_digest(),
        "committed": committed,
        "pending": pending,
        "dead": dead,
        "current_roots": roots,
        "ledger_rows": state.attempts().rows().len(),
        "ledger_head": ledger_head,
    })))
}

#[cfg(test)]
pub(super) fn legacy_v2_state_snapshot_digest_for_test(
    state: &LeveledHoudiniState,
    registration_ordinal: u64,
    records: &[LeveledClauseRecord],
) -> Result<String, AgentFeedbackError> {
    state_snapshot_digest_in_domain(
        "whiel-agent-feedback-state-snapshot-v2",
        state,
        registration_ordinal,
        records,
    )
}

fn latest_binding_fields(latest: &AgentSearchFeedback) -> Value {
    match &latest.kind {
        AgentSearchFeedbackKind::Initial => json!({"kind": "initial"}),
        AgentSearchFeedbackKind::PostconditionOpen(AgentPostconditionOpenSource::Refuted {
            attempt,
        }) => json!({"kind": "postcondition_open", "outcome": "refuted", "attempt": attempt}),
        AgentSearchFeedbackKind::PostconditionOpen(
            AgentPostconditionOpenSource::Inconclusive { reason },
        ) => json!({
            "kind": "postcondition_open",
            "outcome": "inconclusive",
            "reason": inconclusive_name(*reason),
        }),
        AgentSearchFeedbackKind::Failure(report) => json!({
            "kind": "failure",
            "origin": failure_origin_name(report.origin()),
            "failure_kind": failure_kind_name(report.kind()),
            "retryable": report.retryable(),
            "scope": failure_scope_name(report.scope()),
            "detail_digest": report.detail().map(|detail| canonical_value_sha256(&json!(detail))),
            "artifacts": report.artifact_references().iter().map(|reference| json!({
                "backend_matches_only": true,
                "local_id": reference.local_id(),
                "kind": artifact_kind_name(reference.kind()),
            })).collect::<Vec<_>>(),
        }),
        AgentSearchFeedbackKind::CounterexampleRejected { code, reason } => json!({
            "kind": AGENT_COUNTEREXAMPLE_REJECTED_KIND,
            "code": code.as_ref(),
            "reason": reason.as_ref(),
        }),
    }
}

fn latest_binding_digest(latest: &AgentSearchFeedback) -> Result<String, AgentFeedbackError> {
    Ok(canonical_value_sha256(&latest_binding_fields(latest)))
}

fn build_clause_page(
    state: &LeveledHoudiniState,
    eligibility: &Arc<AgentEligibilitySnapshot>,
    start: usize,
    consultation_digest: &Arc<str>,
    policy: &AgentFeedbackPolicy,
) -> Result<AgentClausePage, AgentFeedbackError> {
    // The agent-visible window, not the whole catalog: a record no
    // partition holds has no status the contract defines.
    let records = eligibility.visible_records.as_ref();
    if start > records.len() {
        return Err(AgentFeedbackError::StaleCursor);
    }
    let mut index = start;
    let mut encoded_item_bytes = 0_usize;
    let mut items = Vec::new();
    while index < records.len() && items.len() < policy.limits().clause_page_items {
        let item =
            project_clause_feedback(state, eligibility, &records[index], consultation_digest)?;
        let next_index = index
            .checked_add(1)
            .ok_or(AgentFeedbackError::ArithmeticOverflow)?;
        let (item, next_bytes) = fit_clause_page_item(
            item,
            records.len(),
            start,
            next_index,
            items.len(),
            encoded_item_bytes,
            consultation_digest,
            eligibility,
            policy,
        )?;
        let Some(item) = item else {
            break;
        };
        encoded_item_bytes = next_bytes;
        items.push(item);
        index += 1;
    }
    let continuation = (index < records.len()).then(|| {
        make_cursor(
            AgentFeedbackPageCategory::Clauses,
            index,
            consultation_digest,
            eligibility,
            policy,
        )
    });
    let page = AgentClausePage {
        metadata: AgentPageMetadata {
            total_items: records.len(),
            first_index: start,
            returned_items: items.len(),
            omitted_before: start,
            omitted_after: records.len().saturating_sub(index),
            encoded_item_bytes,
            continuation,
        },
        items: items.into(),
    };
    ensure_page_bound(
        &page.metadata,
        page.items.len(),
        policy.limits().max_page_bytes,
    )?;
    Ok(page)
}

#[allow(clippy::too_many_arguments)]
fn fit_clause_page_item(
    item: AgentClauseFeedback,
    total_items: usize,
    first_index: usize,
    next_index: usize,
    current_items: usize,
    current_item_bytes: usize,
    consultation_digest: &Arc<str>,
    eligibility: &Arc<AgentEligibilitySnapshot>,
    policy: &AgentFeedbackPolicy,
) -> Result<(Option<AgentClauseFeedback>, usize), AgentFeedbackError> {
    for candidate in [item.clone(), item.summarized()] {
        let item_bytes = json_bytes(&candidate.wire_value())?;
        let encoded_item_bytes = current_item_bytes
            .checked_add(item_bytes)
            .ok_or(AgentFeedbackError::ArithmeticOverflow)?;
        let continuation = (next_index < total_items).then(|| {
            make_cursor(
                AgentFeedbackPageCategory::Clauses,
                next_index,
                consultation_digest,
                eligibility,
                policy,
            )
        });
        let metadata = AgentPageMetadata {
            total_items,
            first_index,
            returned_items: current_items + 1,
            omitted_before: first_index,
            omitted_after: total_items.saturating_sub(next_index),
            encoded_item_bytes,
            continuation,
        };
        if page_wire_bytes(&metadata, current_items + 1)? <= policy.limits().max_page_bytes {
            return Ok((Some(candidate), encoded_item_bytes));
        }
    }
    if current_items == 0 {
        Err(AgentFeedbackError::PageItemTooLarge)
    } else {
        Ok((None, current_item_bytes))
    }
}

fn project_clause_feedback(
    state: &LeveledHoudiniState,
    eligibility: &AgentEligibilitySnapshot,
    record: &LeveledClauseRecord,
    consultation_digest: &Arc<str>,
) -> Result<AgentClauseFeedback, AgentFeedbackError> {
    let clause = record.id();
    let status = if let Some(level) = state.committed_levels().get(&clause).copied() {
        AgentClauseStatus::Committed(level)
    } else if let Some(cause) = state.dead_cause(clause) {
        match cause {
            FrameworkIIDeadCause::Refuted(reason) => AgentClauseStatus::DeadRefuted(reason),
            FrameworkIIDeadCause::Dropped => AgentClauseStatus::DeadDropped,
        }
    } else if let Some(level) = state.pending_levels().get(&clause).copied() {
        AgentClauseStatus::Pending(level)
    } else {
        // The page ranges over `visible_records`, which is exactly the
        // records some partition holds, so this is that filter's check.
        return Err(AgentFeedbackError::UnpartitionedClause(clause.get()));
    };
    let mut current_roots = Vec::new();
    for role in [
        FrameworkIICheckRole::Initialization,
        FrameworkIICheckRole::Maintenance,
    ] {
        if let Some(root) = state.current_root(clause, role) {
            current_roots.push(project_current_root(role, root));
        }
    }
    let pending = eligibility
        .pending
        .iter()
        .find(|entry| entry.record.id() == clause);
    let drop_reference = pending.filter(|entry| entry.drop_eligible).map(|_| {
        let clause = record_clause_identity(record);
        let authorization_digest = Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-agent-shown-drop-v1",
            "consultation_digest": consultation_digest.as_ref(),
            "proposal_revision": eligibility.proposal_revision,
            "registration_ordinal": eligibility.registration_ordinal,
            "record_digest": clause.record_digest(),
            "clause_id": clause.clause_id().get(),
        })));
        AgentClauseDropReference {
            clause,
            consultation_digest: Arc::clone(consultation_digest),
            authorization_digest,
        }
    });
    Ok(AgentClauseFeedback {
        clause: record_clause_identity(record),
        display: optional_presentation_text(record.formula().display()),
        origin: Arc::from(origin_name(record.origin())),
        protected: record.is_protected(),
        minimum_level: record.minimum_level(),
        status,
        current_roots: current_roots.into(),
        drop_reference,
        summarized: false,
    })
}

/// One clause display, present unless the text itself is unsafe.
///
/// Size is not a reason to omit it: a clause whose display would not fit its
/// page is carried as the page fitter's `summarized` form instead, which is
/// a paging decision the push states, not a silent truncation.
fn optional_presentation_text(text: &str) -> Option<Arc<str>> {
    validate_presentation_text(text)
        .is_ok()
        .then(|| Arc::from(text))
}

fn project_current_root(
    role: FrameworkIICheckRole,
    root: &CurrentFrameworkIIRoot,
) -> AgentCurrentRoot {
    AgentCurrentRoot {
        role,
        attempt_row: root.attempt_row(),
        request_digest: Arc::from(root.request_digest()),
        partition_digest: Arc::from(root.partition_digest()),
    }
}

fn build_ledger_page(
    state: &LeveledHoudiniState,
    eligibility: &Arc<AgentEligibilitySnapshot>,
    end: usize,
    consultation_digest: &Arc<str>,
    sanitizer: &mut AgentArtifactSanitizer,
    policy: &AgentFeedbackPolicy,
) -> Result<AgentLedgerPage, AgentFeedbackError> {
    let rows = state.attempts().rows();
    if end > rows.len() {
        return Err(AgentFeedbackError::StaleCursor);
    }
    let mut index = end;
    let mut encoded_item_bytes = 0_usize;
    let mut reversed = Vec::new();
    while index > 0 && reversed.len() < policy.limits().ledger_page_items {
        let row_index = index - 1;
        let item = project_ledger_feedback(
            state,
            eligibility.records.as_ref(),
            &rows[row_index],
            sanitizer,
            policy,
        )?;
        let (item, next_bytes) = fit_ledger_page_item(
            item,
            rows.len(),
            end,
            row_index,
            reversed.len(),
            encoded_item_bytes,
            consultation_digest,
            eligibility,
            policy,
        )?;
        let Some(item) = item else {
            break;
        };
        encoded_item_bytes = next_bytes;
        reversed.push(item);
        index = row_index;
    }
    reversed.reverse();
    let continuation = (index > 0).then(|| {
        make_cursor(
            AgentFeedbackPageCategory::Ledger,
            index,
            consultation_digest,
            eligibility,
            policy,
        )
    });
    let page = AgentLedgerPage {
        metadata: AgentPageMetadata {
            total_items: rows.len(),
            first_index: index,
            returned_items: reversed.len(),
            omitted_before: index,
            omitted_after: rows.len().saturating_sub(end),
            encoded_item_bytes,
            continuation,
        },
        items: reversed.into(),
    };
    ensure_page_bound(
        &page.metadata,
        page.items.len(),
        policy.limits().max_page_bytes,
    )?;
    Ok(page)
}

#[allow(clippy::too_many_arguments)]
fn fit_ledger_page_item(
    item: AgentLedgerFeedback,
    total_items: usize,
    original_end: usize,
    next_index: usize,
    current_items: usize,
    current_item_bytes: usize,
    consultation_digest: &Arc<str>,
    eligibility: &Arc<AgentEligibilitySnapshot>,
    policy: &AgentFeedbackPolicy,
) -> Result<(Option<AgentLedgerFeedback>, usize), AgentFeedbackError> {
    for candidate in [item.clone(), item.summarized()] {
        let item_bytes = json_bytes(&candidate.wire_value())?;
        let encoded_item_bytes = current_item_bytes
            .checked_add(item_bytes)
            .ok_or(AgentFeedbackError::ArithmeticOverflow)?;
        let continuation = (next_index > 0).then(|| {
            make_cursor(
                AgentFeedbackPageCategory::Ledger,
                next_index,
                consultation_digest,
                eligibility,
                policy,
            )
        });
        let metadata = AgentPageMetadata {
            total_items,
            first_index: next_index,
            returned_items: current_items + 1,
            omitted_before: next_index,
            omitted_after: total_items.saturating_sub(original_end),
            encoded_item_bytes,
            continuation,
        };
        if page_wire_bytes(&metadata, current_items + 1)? <= policy.limits().max_page_bytes {
            return Ok((Some(candidate), encoded_item_bytes));
        }
    }
    if current_items == 0 {
        Err(AgentFeedbackError::PageItemTooLarge)
    } else {
        Ok((None, current_item_bytes))
    }
}

fn page_wire_bytes(
    metadata: &AgentPageMetadata,
    item_count: usize,
) -> Result<usize, AgentFeedbackError> {
    let empty_envelope = json_bytes(&json!({
        "metadata": metadata.wire_value(),
        "items": [],
    }))?;
    let separators = item_count.saturating_sub(1);
    empty_envelope
        .checked_add(metadata.encoded_item_bytes)
        .and_then(|bytes| bytes.checked_add(separators))
        .ok_or(AgentFeedbackError::ArithmeticOverflow)
}

fn ensure_page_bound(
    metadata: &AgentPageMetadata,
    item_count: usize,
    maximum: usize,
) -> Result<(), AgentFeedbackError> {
    if page_wire_bytes(metadata, item_count)? > maximum {
        Err(AgentFeedbackError::PageItemTooLarge)
    } else {
        Ok(())
    }
}

fn project_ledger_feedback(
    state: &LeveledHoudiniState,
    records: &[LeveledClauseRecord],
    row: &LevelLedgerRow,
    sanitizer: &mut AgentArtifactSanitizer,
    policy: &AgentFeedbackPolicy,
) -> Result<AgentLedgerFeedback, AgentFeedbackError> {
    match row {
        LevelLedgerRow::Attempt(attempt) => {
            let request = attempt.request();
            let route = match attempt.outcome() {
                FrameworkIICheckOutcome::Proved(evidence)
                | FrameworkIICheckOutcome::Refuted(evidence) => {
                    project_evidence_route(evidence, sanitizer, policy)?
                }
                FrameworkIICheckOutcome::Inconclusive { progress, .. } => {
                    project_evidence_route(progress, sanitizer, policy)?
                }
            };
            let kind = match attempt.outcome() {
                FrameworkIICheckOutcome::Proved(_) => AgentAttemptOutcomeKind::Proved,
                FrameworkIICheckOutcome::Refuted(_) => AgentAttemptOutcomeKind::Refuted,
                FrameworkIICheckOutcome::Inconclusive { reason, .. } => {
                    AgentAttemptOutcomeKind::Inconclusive(*reason)
                }
            };
            let route_digest = Arc::from(canonical_value_sha256(&route.wire_value()));
            let route_kind = Arc::from(route.identity_name());
            let solver_time_nanos = match attempt.outcome() {
                FrameworkIICheckOutcome::Proved(evidence)
                | FrameworkIICheckOutcome::Refuted(evidence) => evidence.solver_time(),
                FrameworkIICheckOutcome::Inconclusive { progress, .. } => progress.solver_time(),
            }
            .map(|duration| u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX));
            let preparation_time_nanos = match attempt.outcome() {
                FrameworkIICheckOutcome::Proved(evidence)
                | FrameworkIICheckOutcome::Refuted(evidence) => evidence.preparation_time(),
                FrameworkIICheckOutcome::Inconclusive { progress, .. } => {
                    progress.preparation_time()
                }
            }
            .map(|duration| u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX));
            // Pass 7.5c: only a Refuted outcome keys a countermodel, and
            // only when it closed by a fresh worker validation (never a
            // dictionary/semantic-key reuse, whose `validated_refutation`
            // is the same shared evidence but whose countermodel was
            // already retained under the *original* attempt).
            let attempt_id = match attempt.outcome() {
                FrameworkIICheckOutcome::Refuted(evidence) => evidence
                    .validated_refutation()
                    .map(|refutation| refutation.attempt().get()),
                FrameworkIICheckOutcome::Proved(_)
                | FrameworkIICheckOutcome::Inconclusive { .. } => None,
            };
            Ok(AgentLedgerFeedback::Attempt {
                row_ordinal: attempt.row_ordinal(),
                clause: record_clause_identity(snapshot_record(records, request.clause())?),
                level: request.level(),
                role: request.role(),
                request_digest: Arc::from(request.request_digest()),
                partition_digest: Arc::from(request.snapshot().partition_digest()),
                invalidated: state.attempts().is_invalidated(attempt.row_ordinal()),
                outcome: Box::new(AgentAttemptOutcome {
                    kind,
                    route_kind,
                    route_digest,
                    route: Some(route),
                    attempt_id,
                }),
                solver_time_nanos,
                preparation_time_nanos,
                previous_row_digest: attempt.previous_digest().map(Arc::from),
                row_digest: Arc::from(attempt.row_digest()),
            })
        }
        LevelLedgerRow::Invalidation(invalidation) => Ok(AgentLedgerFeedback::Invalidation {
            row_ordinal: row.row_ordinal(),
            invalidated_attempt: invalidation.invalidated_attempt(),
            target: record_clause_identity(snapshot_record(records, invalidation.target())?),
            cause: invalidation
                .cause()
                .map(|clause| snapshot_record(records, clause).map(record_clause_identity))
                .transpose()?,
            reason: invalidation.reason(),
            previous_row_digest: invalidation.previous_digest().map(Arc::from),
            row_digest: Arc::from(invalidation.row_digest()),
        }),
    }
}

fn make_cursor(
    category: AgentFeedbackPageCategory,
    offset: usize,
    consultation_digest: &Arc<str>,
    eligibility: &Arc<AgentEligibilitySnapshot>,
    policy: &AgentFeedbackPolicy,
) -> AgentFeedbackCursor {
    let token_digest = Arc::from(canonical_value_sha256(&json!({
        "domain": "whiel-agent-feedback-cursor-v2",
        "category": category.identity_name(),
        "offset": offset,
        "source_consultation_digest": consultation_digest.as_ref(),
        "state_snapshot_digest": eligibility.state_snapshot_digest.as_ref(),
        "policy_digest": policy.digest(),
    })));
    AgentFeedbackCursor {
        category,
        offset,
        token_digest,
        source_consultation_digest: Arc::clone(consultation_digest),
        state_snapshot_digest: Arc::clone(&eligibility.state_snapshot_digest),
        authority: Arc::clone(eligibility),
    }
}

fn build_feedback_summary(
    state: &LeveledHoudiniState,
    records: &[LeveledClauseRecord],
) -> Result<AgentFeedbackSummary, AgentFeedbackError> {
    let mut proved_attempts = 0_usize;
    let mut refuted_attempts = 0_usize;
    let mut inconclusive_attempts = 0_usize;
    let mut invalidations = 0_usize;
    for row in state.attempts().rows() {
        match row {
            LevelLedgerRow::Attempt(attempt) => match attempt.outcome() {
                FrameworkIICheckOutcome::Proved(_) => {
                    proved_attempts = checked_increment(proved_attempts)?;
                }
                FrameworkIICheckOutcome::Refuted(_) => {
                    refuted_attempts = checked_increment(refuted_attempts)?;
                }
                FrameworkIICheckOutcome::Inconclusive { .. } => {
                    inconclusive_attempts = checked_increment(inconclusive_attempts)?;
                }
            },
            LevelLedgerRow::Invalidation(_) => {
                invalidations = checked_increment(invalidations)?;
            }
        }
    }
    let mut current_roots = 0_usize;
    for clause in records.iter().map(LeveledClauseRecord::id) {
        for role in [
            FrameworkIICheckRole::Initialization,
            FrameworkIICheckRole::Maintenance,
        ] {
            if state.current_root(clause, role).is_some() {
                current_roots = checked_increment(current_roots)?;
            }
        }
    }
    let missing_current_roots = state.root_coverage()?.missing().len();
    Ok(AgentFeedbackSummary {
        tracked_clauses: records.len(),
        committed_clauses: state.committed_levels().len(),
        pending_clauses: state.pending_levels().len(),
        dead_clauses: state.dead().len(),
        dead_refuted_clauses: state
            .dead()
            .values()
            .filter(|cause| cause.refutation().is_some())
            .count(),
        dead_dropped_clauses: state.dropped_clauses().count(),
        current_roots,
        ledger_rows: state.attempts().rows().len(),
        proved_attempts,
        refuted_attempts,
        inconclusive_attempts,
        invalidations,
        missing_current_roots,
    })
}

fn checked_increment(value: usize) -> Result<usize, AgentFeedbackError> {
    value
        .checked_add(1)
        .ok_or(AgentFeedbackError::ArithmeticOverflow)
}

fn validation_manifest_fields(
    eligibility: &AgentEligibilitySnapshot,
    session_digest: &str,
    consultation_digest: &str,
    visible: &AgentManifestVisibleAuthority,
    policy: &AgentFeedbackPolicy,
) -> Value {
    let run_digest = eligibility.catalog.instance_digest();
    json!({
        "domain": "whiel-agent-feedback-private-validation-manifest-v2",
        "task": task_identity_fields(eligibility.catalog.scope()),
        "scope_digest": eligibility.catalog.scope().identity_sha256(),
        "run_digest": run_digest,
        "session_digest": session_digest,
        "consultation_digest": consultation_digest,
        "policy_digest": policy.digest(),
        "proposal_revision": eligibility.proposal_revision,
        "registration_ordinal": eligibility.registration_ordinal,
        "state_snapshot_digest": eligibility.state_snapshot_digest.as_ref(),
        "core_partition_digest": eligibility.core_snapshot.partition_digest(),
        "pending": eligibility.pending.iter().map(|entry| json!({
            "clause_id": entry.record.id().get(),
            "record_digest": entry.record.record_digest(),
            "level": entry.level.get(),
            "drop_eligible": entry.drop_eligible,
        })).collect::<Vec<_>>(),
        "shown_clauses": visible.shown_clauses.values()
            .map(AgentClauseIdentity::wire_value)
            .collect::<Vec<_>>(),
        "shown_drops": visible.shown_drops.iter().map(|(authorization, clause)| json!({
            "authorization_digest": authorization.as_ref(),
            "clause_id": clause.get(),
        })).collect::<Vec<_>>(),
        "artifact_references": visible.artifacts.iter().map(|(stable_id, reference)| json!({
            "stable_id": stable_id.as_ref(),
            "local_id": reference.local_id(),
            "kind": artifact_kind_name(reference.kind()),
        })).collect::<Vec<_>>(),
        "core_clause_ids": visible.core_clause_ids.iter().map(|clause| clause.get()).collect::<Vec<_>>(),
    })
}

fn build_validation_manifest(
    task: &SynthesisTask,
    eligibility: Arc<AgentEligibilitySnapshot>,
    session_digest: Arc<str>,
    consultation_digest: Arc<str>,
    visible: AgentManifestVisibleAuthority,
    policy: &AgentFeedbackPolicy,
) -> Result<AgentFeedbackValidationManifest, AgentFeedbackError> {
    let run_digest: Arc<str> = Arc::from(eligibility.catalog.instance_digest());
    let fields = validation_manifest_fields(
        &eligibility,
        &session_digest,
        &consultation_digest,
        &visible,
        policy,
    );
    let encoded_bytes = json_bytes(&fields)?;
    if encoded_bytes > policy.limits().max_private_manifest_bytes {
        return Err(AgentFeedbackError::PrivateManifestTooLarge {
            found: encoded_bytes,
            limit: policy.limits().max_private_manifest_bytes,
        });
    }
    Ok(AgentFeedbackValidationManifest {
        eligibility,
        task_identity: task.identity().clone(),
        run_digest,
        consultation_digest,
        shown_clauses: visible.shown_clauses,
        shown_drops: visible.shown_drops,
        core_clause_ids: visible.core_clause_ids,
        artifacts: visible.artifacts,
        manifest_digest: Arc::from(canonical_value_sha256(&fields)),
    })
}

// ------------------------------------------------------------
// Closed Names, Encoding, And Errors
// ------------------------------------------------------------

pub(crate) fn origin_name(origin: &ExtendedClauseOrigin) -> &'static str {
    match origin {
        ExtendedClauseOrigin::Submitted => "submitted",
        ExtendedClauseOrigin::Symbolic => "symbolic",
        ExtendedClauseOrigin::EdbPreconditionSystem { .. } => "edb_precondition_system",
    }
}

fn check_role_name(role: FrameworkIICheckRole) -> &'static str {
    match role {
        FrameworkIICheckRole::Initialization => "initialization",
        FrameworkIICheckRole::Maintenance => "maintenance",
    }
}

fn inconclusive_name(reason: FrameworkIIInconclusiveReason) -> &'static str {
    match reason {
        FrameworkIIInconclusiveReason::TimedOut => "timed_out",
        FrameworkIIInconclusiveReason::SolverUnknown => "solver_unknown",
        FrameworkIIInconclusiveReason::PeerFailed => "peer_failed",
        FrameworkIIInconclusiveReason::UnvalidatedRefutation => "unvalidated_refutation",
        FrameworkIIInconclusiveReason::Cancelled => "cancelled",
        FrameworkIIInconclusiveReason::Suspended => "suspended",
    }
}

fn invalidation_name(reason: FrameworkIIInvalidationReason) -> &'static str {
    match reason {
        FrameworkIIInvalidationReason::AntecedentClauseDeleted => "antecedent_clause_deleted",
        FrameworkIIInvalidationReason::AntecedentClausePromoted => "antecedent_clause_promoted",
        FrameworkIIInvalidationReason::AntecedentClauseExcluded => "antecedent_clause_excluded",
        FrameworkIIInvalidationReason::SnapshotChanged => "snapshot_changed",
        FrameworkIIInvalidationReason::SystemClausesInstalled => "system_clauses_installed",
    }
}

fn proof_profile_name(profile: ProofSearchProfile) -> &'static str {
    match profile {
        ProofSearchProfile::Direct => "direct",
        ProofSearchProfile::Casc2025 => "casc_2025",
    }
}

fn failure_scope_name(scope: FailureScope) -> &'static str {
    match scope {
        FailureScope::LaneLocal => "lane_local",
        FailureScope::RunGlobal => "run_global",
    }
}

fn failure_origin_name(origin: FailureOrigin) -> &'static str {
    match origin {
        FailureOrigin::RunControl => "run_control",
        FailureOrigin::ArtifactSettlement => "artifact_settlement",
        FailureOrigin::AgentConsultation => "agent_consultation",
        FailureOrigin::ResponseValidation => "response_validation",
        FailureOrigin::EncodingPreparation => "encoding_preparation",
        FailureOrigin::InitializationExecution => "initialization_execution",
        FailureOrigin::VampireProofSearch => "vampire_proof_search",
        FailureOrigin::VampireFiniteModelBuilding => "vampire_finite_model_building",
        FailureOrigin::VampireRace => "vampire_race",
        FailureOrigin::SymbolicRace => "symbolic_race",
        FailureOrigin::ModelDecoding => "model_decoding",
        FailureOrigin::TerminationCheck => "termination_check",
        FailureOrigin::MaintenanceExecution => "maintenance_execution",
        FailureOrigin::MaintenanceHistory => "maintenance_history",
        FailureOrigin::ValidityCertification => "validity_certification",
        FailureOrigin::InvalidityCertification => "invalidity_certification",
    }
}

fn failure_kind_name(kind: FailureKind) -> &'static str {
    match kind {
        FailureKind::OverallTimeout => "overall_timeout",
        FailureKind::Interrupted => "interrupted",
        FailureKind::ConsultationTimeout => "consultation_timeout",
        FailureKind::IterationLimitExhausted => "iteration_limit_exhausted",
        FailureKind::SourceExhausted => "source_exhausted",
        FailureKind::CorrectionExhausted => "correction_exhausted",
        FailureKind::NoResponse => "no_response",
        FailureKind::TransportFailure => "transport_failure",
        FailureKind::ValidationInfrastructureFailure => "validation_infrastructure_failure",
        FailureKind::UnsupportedCheck => "unsupported_check",
        FailureKind::FuelExhausted => "fuel_exhausted",
        FailureKind::CheckTimeout => "check_timeout",
        FailureKind::SolverUnknown => "solver_unknown",
        FailureKind::MalformedResult => "malformed_result",
        FailureKind::ProcessFailure => "process_failure",
        FailureKind::InfrastructureFailure => "infrastructure_failure",
        FailureKind::ConcurrentWorkerFailures => "concurrent_worker_failures",
        FailureKind::CertificateConstructionFailure => "certificate_construction_failure",
        FailureKind::CertificateRejected => "certificate_rejected",
        FailureKind::CertificateTypecheckFailure => "certificate_typecheck_failure",
        FailureKind::ManifestFailure => "manifest_failure",
        FailureKind::PublicationFailure => "publication_failure",
        FailureKind::HistoryLogFailure => "history_log_failure",
        FailureKind::StateInvariantViolation => "state_invariant_violation",
    }
}

fn json_bytes(value: &Value) -> Result<usize, AgentFeedbackError> {
    serde_json::to_vec(value)
        .map(|encoded| encoded.len())
        .map_err(|error| AgentFeedbackError::Serialization(error.to_string()))
}

#[derive(Debug)]
pub enum AgentFeedbackError {
    InvalidPolicy(&'static str),
    WrongTask,
    WrongRun,
    WrongArtifactBackend,
    TrackedClauseLimit {
        found: usize,
        limit: usize,
    },
    /// Two authorities of one run name different values for one host limit.
    HostLimits(HostLimitDisagreement),
    MandatoryPresentationTooLarge {
        found: usize,
        limit: usize,
    },
    PrivateManifestTooLarge {
        found: usize,
        limit: usize,
    },
    FeedbackTooLarge {
        found: usize,
        limit: usize,
    },
    UnsafePresentationText,
    ConflictingExposedClauseIdentity {
        clause: u64,
    },
    UnknownClause(u64),
    /// A clause the agent-visible projections were asked to describe that
    /// no partition holds. Unreachable by construction — the clause page
    /// ranges over the held records and a rolled-back round reports no
    /// outcomes — so this is that invariant's check.
    UnpartitionedClause(u64),
    InconsistentPendingPartition,
    ForeignArtifactReference,
    UnexpectedArtifactKind {
        role: AgentArtifactRole,
        found: ArtifactKind,
    },
    UnvalidatedEvidence,
    PageItemTooLarge,
    StaleLatestFeedback,
    StaleCursor,
    ConcurrentCatalogChange,
    ArithmeticOverflow,
    Serialization(String),
    FrameworkII(FrameworkIIStateError),
}

impl fmt::Display for AgentFeedbackError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPolicy(detail) => write!(formatter, "invalid feedback policy: {detail}"),
            Self::WrongTask => formatter.write_str("feedback belongs to another task or scope"),
            Self::WrongRun => formatter.write_str("feedback belongs to another fixed-ambient run"),
            Self::WrongArtifactBackend => {
                formatter.write_str("feedback artifacts belong to another task backend")
            }
            Self::TrackedClauseLimit { found, limit } => {
                write!(formatter, "run tracks {found} clauses; limit is {limit}")
            }
            Self::HostLimits(disagreement) => disagreement.fmt(formatter),
            Self::MandatoryPresentationTooLarge { found, limit } => write!(
                formatter,
                "mandatory presentation is {found} bytes; limit is {limit}",
            ),
            Self::PrivateManifestTooLarge { found, limit } => write!(
                formatter,
                "private validation manifest is {found} bytes; limit is {limit}",
            ),
            Self::FeedbackTooLarge { found, limit } => {
                write!(formatter, "feedback is {found} bytes; limit is {limit}")
            }
            Self::UnsafePresentationText => {
                formatter.write_str("feedback presentation text is empty, unsafe, or oversized")
            }
            Self::ConflictingExposedClauseIdentity { clause } => write!(
                formatter,
                "agent-visible projections disagree on exact clause identity {clause}",
            ),
            Self::UnknownClause(clause) => {
                write!(formatter, "feedback references unknown clause {clause}")
            }
            Self::UnpartitionedClause(clause) => write!(
                formatter,
                "clause {clause} is in no fixed-ambient partition and has no status to show",
            ),
            Self::InconsistentPendingPartition => formatter
                .write_str("the pending partition overlaps the committed or dead partition"),
            Self::ForeignArtifactReference => {
                formatter.write_str("feedback contains a foreign artifact reference")
            }
            Self::UnexpectedArtifactKind { role, found } => write!(
                formatter,
                "artifact kind {found:?} is not eligible for agent role {role:?}",
            ),
            Self::UnvalidatedEvidence => {
                formatter.write_str("feedback contains evidence without typed authority")
            }
            Self::PageItemTooLarge => {
                formatter.write_str("one summarized feedback row exceeds the page byte limit")
            }
            Self::StaleLatestFeedback => formatter
                .write_str("latest feedback is initial-only, stale, or bound to another run state"),
            Self::StaleCursor => {
                formatter.write_str("feedback cursor is stale, foreign, or category-mismatched")
            }
            Self::ConcurrentCatalogChange => formatter
                .write_str("the fixed-ambient catalog changed while feedback was being built"),
            Self::ArithmeticOverflow => {
                formatter.write_str("feedback counter or ordinal overflowed")
            }
            Self::Serialization(detail) => {
                write!(formatter, "serialize bounded agent feedback: {detail}")
            }
            Self::FrameworkII(error) => write!(formatter, "build fixed-ambient feedback: {error}"),
        }
    }
}

impl std::error::Error for AgentFeedbackError {}

impl From<FrameworkIIStateError> for AgentFeedbackError {
    fn from(error: FrameworkIIStateError) -> Self {
        Self::FrameworkII(error)
    }
}

#[allow(clippy::too_many_arguments)]
fn capture_replay_feedback_owner(
    session: &PreCertificateAgentHoudiniState,
    state: &LeveledHoudiniState,
    latest: &AgentSearchFeedback,
    eligibility: &AgentEligibilitySnapshot,
    manifest: &AgentFeedbackValidationManifest,
    iteration: u64,
    remaining: Duration,
    clause_page_start: usize,
    ledger_page_end: usize,
    clauses: &AgentClausePage,
    ledger: &AgentLedgerPage,
) -> Result<
    super::replay_correspondence::ReplayFeedbackOwner,
    super::replay_correspondence::ReplayCaptureError,
> {
    use super::production::{ReplayArtifactIdentity, ReplayBackendIdentity, ReplayPrivateFailure};
    use super::replay_correspondence::*;
    // Scan private detail before constructing even its commitment. No raw
    // detail or commitment derived from a redacted detail enters the projection.
    let latest_artifacts = if let AgentSearchFeedbackKind::Failure(report) = &latest.kind {
        ReplayPrivateFailure::capture(report).map_err(|error| match error {
            super::production::ReplayPrivateFailureError::Redacted => {
                ReplayCaptureError::SemanticRedaction
            }
            _ => ReplayCaptureError::UnsupportedSchema,
        })?;
        report
            .artifact_references()
            .iter()
            .copied()
            .map(ReplayArtifactIdentity::capture)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| ReplayCaptureError::UnsupportedSchema)?
    } else {
        Vec::new()
    };
    let owner = ReplayStateOwner::capture(state, &eligibility.state_snapshot_digest)?;
    let mut sanitizer = AgentArtifactSanitizer::new(
        session.artifact_backend,
        Arc::from(session.catalog.instance_digest()),
        Arc::clone(&session.session_digest),
    );
    project_latest_feedback(latest, &mut sanitizer, &session.policy)
        .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
    let mut routes = Vec::new();
    for row in state.attempts().rows() {
        if let LevelLedgerRow::Attempt(row) = row {
            let route =
                project_evidence_route(row.outcome().evidence(), &mut sanitizer, &session.policy)
                    .map_err(|_| ReplayCaptureError::OwnerInvariant)?
                    .wire_value();
            routes.push(ReplayRouteProjection {
                row_ordinal: super::replay_identity::LedgerRowOrdinal(row.row_ordinal()),
                route_digest: decode_owner(&json!(canonical_value_sha256(&route)))?,
                route: decode_owner(&route)?,
            });
        }
    }
    let stable_artifacts = sanitizer
        .replay_references
        .iter()
        .map(|(stable_id, (artifact, role))| {
            Ok(ReplayStableArtifactProjection {
                stable_id: decode_owner(&json!(stable_id.as_ref()))?,
                role: decode_owner(&json!(role.identity_name()))?,
                artifact: ReplayArtifactIdentity::capture(*artifact)
                    .map_err(|_| ReplayCaptureError::UnsupportedSchema)?,
            })
        })
        .collect::<Result<Vec<_>, ReplayCaptureError>>()?;
    if owner.projection.catalog.registration_ordinal != eligibility.registration_ordinal
        || owner
            .projection
            .catalog
            .records
            .iter()
            .map(|r| r.record_digest.0.as_str())
            .ne(eligibility
                .records
                .iter()
                .map(LeveledClauseRecord::record_digest))
    {
        return Err(ReplayCaptureError::OwnerInvariant);
    }
    let visible = AgentManifestVisibleAuthority {
        shown_clauses: manifest.shown_clauses.clone(),
        shown_drops: manifest.shown_drops.clone(),
        core_clause_ids: manifest.core_clause_ids.clone(),
        artifacts: manifest.artifacts.clone(),
    };
    let cursors = [
        clauses.metadata.continuation.as_ref(),
        ledger.metadata.continuation.as_ref(),
    ]
    .into_iter()
    .flatten()
    .map(|cursor| {
        Ok(ReplayCursorProjection {
            category: decode_owner(&json!(cursor.category.identity_name()))?,
            offset: cursor.offset,
            token_digest: decode_owner(&json!(cursor.token_digest.as_ref()))?,
            source_consultation_digest: decode_owner(&json!(
                cursor.source_consultation_digest.as_ref()
            ))?,
            state_snapshot_digest: decode_owner(&json!(cursor.state_snapshot_digest.as_ref()))?,
        })
    })
    .collect::<Result<Vec<_>, ReplayCaptureError>>()?;
    ReplayFeedbackOwner::capture(
        owner,
        routes,
        stable_artifacts,
        cursors,
        ReplayBackendIdentity::parse(&session.artifact_backend.to_string())
            .map_err(|_| ReplayCaptureError::UnsupportedSchema)?,
        session.replay_run_configuration.clone()?,
        decode_owner(&policy_fields(session.policy.limits()))?,
        decode_owner(&json!(session.policy.digest()))?,
        decode_owner(&json!(session.session_digest.as_ref()))?,
        decode_owner(&latest_binding_fields(latest))?,
        latest_artifacts,
        decode_owner(&json!(
            latest_binding_digest(latest).map_err(|_| ReplayCaptureError::OwnerInvariant)?
        ))?,
        ReplayEligibilityProjection {
            visible_records: eligibility
                .visible_records
                .iter()
                .map(|r| r.id().get())
                .collect(),
            proposal_revision: eligibility.proposal_context.proposal_revision(),
            expected_registration_ordinal: eligibility
                .proposal_context
                .expected_registration_ordinal(),
            core: ReplayPartitionProjection::capture(eligibility.proposal_context.core_snapshot())?,
            drop_eligible_records: eligibility
                .proposal_context
                .drop_eligible_records()
                .iter()
                .map(|r| r.id().get())
                .collect(),
        },
        ReplayConsultationInputs {
            iteration,
            remaining_search_budget_ns: remaining.as_nanos().to_string(),
            clause_page_start,
            ledger_page_end,
            previous_round_proposed: session
                .previous_round_proposed
                .iter()
                .map(|id| id.get())
                .collect(),
            reconciled_host_limits: decode_owner(&session.host_limits.digest_value())?,
        },
        decode_owner(&validation_manifest_fields(
            eligibility,
            &session.session_digest,
            &manifest.consultation_digest,
            &visible,
            &session.policy,
        ))?,
        decode_owner(&json!(manifest.manifest_digest.as_ref()))?,
    )
}

impl PreCertificateAgentHoudiniState {
    pub(super) fn replay_final_state_owner(
        &self,
        state: &LeveledHoudiniState,
        policy: &super::AgentConsultationPolicy,
        outcome: super::replay_correspondence::ReplayFinalOutcome,
    ) -> Result<
        super::replay_correspondence::ReplayFinalStateOwner,
        super::replay_correspondence::ReplayCaptureError,
    > {
        use super::replay_correspondence::*;
        if self.catalog.instance_digest() != state.catalog().instance_digest()
            || self.catalog.scope().identity() != state.catalog().scope().identity()
        {
            return Err(ReplayCaptureError::OwnerInvariant);
        }
        let (ordinal, records) = state
            .catalog()
            .record_snapshot()
            .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        let digest = state_snapshot_digest(state, ordinal, &records)
            .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        ReplayFinalStateOwner::capture(
            ReplayStateOwner::capture(state, &digest)?,
            super::production::ReplayBackendIdentity::parse(&self.artifact_backend.to_string())
                .map_err(|_| ReplayCaptureError::UnsupportedSchema)?,
            self.replay_run_configuration.clone()?,
            decode_owner(&policy_fields(self.policy.limits()))?,
            decode_owner(&json!(self.policy.digest()))?,
            policy,
            outcome,
        )
    }
}

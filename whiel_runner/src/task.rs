//! Typed Rust view of one Lean-evaluated synthesis task.

use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;

use serde::Deserialize;

/// Version of the Lean-to-Rust task transport.
pub const TASK_MANIFEST_VERSION: u64 = 3;
/// Manifest format of fixed-ambient tasks, whose `schema`, `preprocessed`, and
/// `solver` sections describe the lifted loop over the computed prophecy schema.
pub const FIXED_AMBIENT_TASK_MANIFEST_VERSION: u64 = 4;

/// Resource bound for an opaque relation key admitted by the compiled Lean
/// fixed-ambient scope service.
pub(crate) const MAX_FRAMEWORK_II_RELATION_KEY_BYTES: usize = 4096;

/// The Lean-owned relation-name universe used by one task manifest.
///
/// This is a transport distinction, not a Rust interpretation of relation
/// constructors. Fixed-ambient keys remain opaque after bounded admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TaskSchemaKind {
    LegacyProgram,
    FixedAmbient,
}

// ------------------------------------------------------------
// Task Identity
// ------------------------------------------------------------

/// A normalized SHA-256 digest used as source identity metadata.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceDigest(Arc<str>);

impl SourceDigest {
    fn parse(value: String) -> Result<Self, TaskLoadError> {
        if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(TaskLoadError::InvalidField {
                field: "identity.source_sha256",
                detail: "expected exactly 64 hexadecimal digits".to_string(),
            });
        }
        Ok(Self(Arc::from(value.to_ascii_lowercase())))
    }

    /// Return the normalized lowercase hexadecimal digest.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Exact implementation-level identity of one exported Lean task.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TaskIdentity {
    canonical_id: Arc<str>,
    module: Arc<str>,
    namespace: Arc<str>,
    source_digest: SourceDigest,
    semantic_version: u64,
    encoding_version: u64,
}

impl TaskIdentity {
    /// Canonical benchmark or caller-supplied task identifier.
    pub fn canonical_id(&self) -> &str {
        &self.canonical_id
    }

    /// Lean module which owns the trusted task declarations.
    pub fn module(&self) -> &str {
        &self.module
    }

    /// Lean namespace which owns the trusted task declarations.
    pub fn namespace(&self) -> &str {
        &self.namespace
    }

    /// Digest of the trusted source module used for this export.
    pub fn source_digest(&self) -> &SourceDigest {
        &self.source_digest
    }

    /// Version of the task's Whiel semantic contract.
    pub fn semantic_version(&self) -> u64 {
        self.semantic_version
    }

    /// Version of the Lean-to-Rust task encoding.
    pub fn encoding_version(&self) -> u64 {
        self.encoding_version
    }
}

// ------------------------------------------------------------
// Lean-Owned Value References
// ------------------------------------------------------------

#[derive(Clone, Debug)]
struct LeanValueRef {
    expression: Arc<str>,
    display: Arc<str>,
}

macro_rules! lean_value_ref {
    ($name:ident) => {
        /// Opaque reference to a Lean-owned value with display-only text.
        #[derive(Clone, Debug)]
        pub struct $name(LeanValueRef);

        impl $name {
            /// Exact Lean expression used to recover the value.
            pub fn expression(&self) -> &str {
                &self.0.expression
            }

            /// Stable user-facing rendering; never semantic identity.
            pub fn display(&self) -> &str {
                &self.0.display
            }
        }
    };
}

lean_value_ref!(SchemaRef);
lean_value_ref!(AssertExprRef);
lean_value_ref!(WhielCommandRef);

/// Opaque reference to the trusted Lean preprocessing evidence.
#[derive(Clone, Debug)]
pub struct PreprocessingEvidenceRef {
    expression: Arc<str>,
}

// ------------------------------------------------------------
// Solver Metadata
// ------------------------------------------------------------

/// Exact Lean evidence that one task assertion has no bound symbols.
#[derive(Clone, Debug)]
pub struct NoBoundEvidenceRef {
    expression: Arc<str>,
}

impl NoBoundEvidenceRef {
    /// Exact Lean expression used to recover the proof.
    pub fn expression(&self) -> &str {
        &self.expression
    }
}

/// Injective task-scoped identity of one concrete domain constant.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstantKey(Arc<str>);

impl ConstantKey {
    /// Parse one canonical key for a concrete Whiel domain value.
    ///
    /// The Lean worker independently decodes and validates the key before it
    /// can affect a solver body or support block.
    pub fn from_canonical(value: impl Into<String>) -> Result<Self, TaskLoadError> {
        Ok(Self(parse_constant_key(value.into())?))
    }

    /// Return the exact injective key emitted by Lean.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Injective task-scoped identity of one schema relation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RelationKey(Arc<str>);

impl RelationKey {
    /// Decode one canonical key echoed by a trusted Lean schema service.
    /// Membership and arity are checked separately against that service's
    /// exact typed schema response.
    pub(crate) fn from_canonical(value: impl Into<String>) -> Result<Self, TaskLoadError> {
        Ok(Self(parse_relation_key(value.into())?))
    }

    /// Retain one exact relation key from the compiled Lean fixed-ambient
    /// scope service without interpreting its constructor tags.
    ///
    /// The ordinary task manifest continues to use `from_canonical` and its
    /// concrete `IndexAlphaName` grammar. The fixed-ambient framework admits keys only after
    /// checking the complete task-bound scope response, so this boundary owns
    /// only a resource bound and exact byte identity.
    pub(crate) fn from_lean_scope(value: impl Into<String>) -> Result<Self, TaskLoadError> {
        let value = value.into();
        if value.is_empty() || value.len() > MAX_FRAMEWORK_II_RELATION_KEY_BYTES {
            return Err(invalid(
                "solver.framework_ii_relation_key",
                "Lean-owned scope key must be nonempty and bounded",
            ));
        }
        Ok(Self(Arc::from(value)))
    }

    /// Return the exact injective key emitted by Lean.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Exact key and arity of one relation in the task schema.
#[derive(Clone, Debug)]
pub struct SchemaRelationRef {
    key: RelationKey,
    arity: u64,
}

impl SchemaRelationRef {
    /// Return the exact task-scoped relation key.
    pub fn key(&self) -> &RelationKey {
        &self.key
    }

    /// Return the relation arity evaluated by Lean.
    pub fn arity(&self) -> u64 {
        self.arity
    }
}

/// Exact solver-visible metadata for one Lean-owned assertion source.
#[derive(Clone, Debug)]
pub struct SolverAssertSourceRef {
    task: TaskIdentity,
    source_id: Arc<str>,
    expression: Arc<str>,
    no_bound: NoBoundEvidenceRef,
    constants: Arc<[ConstantKey]>,
    relations: Arc<[RelationKey]>,
}

/// Exact solver-visible metadata for one Lean-owned QF source.
#[derive(Clone, Debug)]
pub struct SolverQfSourceRef {
    task: TaskIdentity,
    source_id: Arc<str>,
    constants: Arc<[ConstantKey]>,
    relations: Arc<[RelationKey]>,
}

impl SolverAssertSourceRef {
    /// Return the exact task which owns this trusted source.
    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task
    }

    /// Return the stable role-neutral identity of this source.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return the exact Lean expression for the assertion.
    pub fn expression(&self) -> &str {
        &self.expression
    }

    /// Return the exact Lean evidence for QF conversion.
    pub fn no_bound(&self) -> &NoBoundEvidenceRef {
        &self.no_bound
    }

    /// Return the exact constants used by this assertion.
    pub fn constants(&self) -> &[ConstantKey] {
        &self.constants
    }

    /// Return the exact relations used by this assertion.
    pub fn relations(&self) -> &[RelationKey] {
        &self.relations
    }
}

impl SolverQfSourceRef {
    /// Return the exact task which owns this trusted source.
    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task
    }

    /// Return the stable role-neutral identity of this source.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return the exact constants used by this source.
    pub fn constants(&self) -> &[ConstantKey] {
        &self.constants
    }

    /// Return the exact relations used by this source.
    pub fn relations(&self) -> &[RelationKey] {
        &self.relations
    }
}

impl PreprocessingEvidenceRef {
    /// Exact Lean expression used to recover the evidence.
    pub fn expression(&self) -> &str {
        &self.expression
    }
}

// ------------------------------------------------------------
// Synthesis Task
// ------------------------------------------------------------

/// One sanitized original and preprocessed Hoare-triple task.
#[derive(Clone, Debug)]
pub struct SynthesisTask {
    identity: TaskIdentity,
    schema_kind: TaskSchemaKind,
    schema: SchemaRef,
    original_pre: AssertExprRef,
    original_command: WhielCommandRef,
    original_post: AssertExprRef,
    preprocessed_pre: AssertExprRef,
    preprocessed_command: WhielCommandRef,
    preprocessed_post: AssertExprRef,
    preprocessing_evidence: PreprocessingEvidenceRef,
    solver_relations: Arc<[SchemaRelationRef]>,
    solver_constants: Arc<[ConstantKey]>,
    preprocessed_pre_solver: SolverAssertSourceRef,
    preprocessed_post_solver: SolverAssertSourceRef,
    loop_guard_solver: SolverQfSourceRef,
    negated_loop_guard_solver: SolverQfSourceRef,
}

impl SynthesisTask {
    /// Decode and validate one task exported by Lean.
    pub fn from_json(text: &str) -> Result<Self, TaskLoadError> {
        let raw: RawTaskManifest =
            serde_json::from_str(text).map_err(|error| TaskLoadError::Json(error.to_string()))?;
        Self::from_raw(raw, TaskSchemaKind::LegacyProgram)
    }

    /// Decode an explicitly selected fixed-ambient task manifest.
    ///
    /// Keeping this entry point separate prevents a legacy benchmark from
    /// entering the V5 runtime merely by changing a relation-key spelling.
    pub fn from_fixed_ambient_json(text: &str) -> Result<Self, TaskLoadError> {
        let raw: RawTaskManifest =
            serde_json::from_str(text).map_err(|error| TaskLoadError::Json(error.to_string()))?;
        Self::from_raw(raw, TaskSchemaKind::FixedAmbient)
    }

    fn from_raw(raw: RawTaskManifest, schema_kind: TaskSchemaKind) -> Result<Self, TaskLoadError> {
        let expected_version = match schema_kind {
            TaskSchemaKind::LegacyProgram => TASK_MANIFEST_VERSION,
            TaskSchemaKind::FixedAmbient => FIXED_AMBIENT_TASK_MANIFEST_VERSION,
        };
        if raw.format_version != expected_version {
            return Err(TaskLoadError::UnsupportedVersion {
                found: raw.format_version,
                expected: expected_version,
            });
        }
        validate_identifier("identity.canonical_id", &raw.identity.canonical_id)?;
        validate_name("identity.module", &raw.identity.module)?;
        validate_name("identity.namespace", &raw.identity.namespace)?;
        if raw.semantic_version == 0 {
            return Err(invalid("semantic_version", "must be positive"));
        }
        if raw.encoding_version == 0 {
            return Err(invalid("encoding_version", "must be positive"));
        }

        let namespace: Arc<str> = Arc::from(raw.identity.namespace);
        let identity = TaskIdentity {
            canonical_id: Arc::from(raw.identity.canonical_id),
            module: Arc::from(raw.identity.module),
            namespace: Arc::clone(&namespace),
            source_digest: SourceDigest::parse(raw.identity.source_sha256)?,
            semantic_version: raw.semantic_version,
            encoding_version: raw.encoding_version,
        };

        let schema_suffix = match schema_kind {
            TaskSchemaKind::LegacyProgram => "programSchema",
            TaskSchemaKind::FixedAmbient => "inputPreproc.prophecySchema",
        };
        let schema = SchemaRef(value_ref(&namespace, "schema", schema_suffix, raw.schema)?);
        let original_pre = AssertExprRef(value_ref(
            &namespace,
            "original.pre",
            "inputPre",
            raw.original.pre,
        )?);
        let original_command = WhielCommandRef(value_ref(
            &namespace,
            "original.command",
            "inputCmd",
            raw.original.command,
        )?);
        let original_post = AssertExprRef(value_ref(
            &namespace,
            "original.post",
            "inputPost",
            raw.original.post,
        )?);
        let (pre_suffix, command_suffix, post_suffix) = match schema_kind {
            TaskSchemaKind::LegacyProgram => (
                "inputPreproc.loopPre",
                "inputPreproc.loopCmd",
                "inputPreproc.loopPost",
            ),
            TaskSchemaKind::FixedAmbient => (
                "inputPreproc.liftedLoop.preAssert",
                "inputPreproc.liftedLoop.cmd",
                "inputPreproc.liftedLoop.postAssert",
            ),
        };
        let preprocessed_pre = AssertExprRef(value_ref(
            &namespace,
            "preprocessed.pre",
            pre_suffix,
            raw.preprocessed.pre,
        )?);
        let preprocessed_command = WhielCommandRef(value_ref(
            &namespace,
            "preprocessed.command",
            command_suffix,
            raw.preprocessed.command,
        )?);
        let preprocessed_post = AssertExprRef(value_ref(
            &namespace,
            "preprocessed.post",
            post_suffix,
            raw.preprocessed.post,
        )?);
        let evidence_expression = exact_expression(
            &namespace,
            "preprocessing_evidence.expression",
            "inputPreproc",
            raw.preprocessing_evidence.expression,
        )?;
        let solver = solver_metadata(&identity, schema_kind, raw.solver)?;

        Ok(Self {
            identity,
            schema_kind,
            schema,
            original_pre,
            original_command,
            original_post,
            preprocessed_pre,
            preprocessed_command,
            preprocessed_post,
            preprocessing_evidence: PreprocessingEvidenceRef {
                expression: evidence_expression,
            },
            solver_relations: solver.relations,
            solver_constants: solver.constants,
            preprocessed_pre_solver: solver.preprocessed_pre,
            preprocessed_post_solver: solver.preprocessed_post,
            loop_guard_solver: solver.loop_guard,
            negated_loop_guard_solver: solver.negated_loop_guard,
        })
    }

    /// Exact task identity used by run-scoped runtime components.
    pub fn identity(&self) -> &TaskIdentity {
        &self.identity
    }

    /// Return whether this task uses the legacy or fixed ambient schema.
    pub fn schema_kind(&self) -> TaskSchemaKind {
        self.schema_kind
    }

    pub fn schema(&self) -> &SchemaRef {
        &self.schema
    }

    pub fn original_pre(&self) -> &AssertExprRef {
        &self.original_pre
    }

    pub fn original_command(&self) -> &WhielCommandRef {
        &self.original_command
    }

    pub fn original_post(&self) -> &AssertExprRef {
        &self.original_post
    }

    pub fn preprocessed_pre(&self) -> &AssertExprRef {
        &self.preprocessed_pre
    }

    pub fn preprocessed_command(&self) -> &WhielCommandRef {
        &self.preprocessed_command
    }

    pub fn preprocessed_post(&self) -> &AssertExprRef {
        &self.preprocessed_post
    }

    pub fn preprocessing_evidence(&self) -> &PreprocessingEvidenceRef {
        &self.preprocessing_evidence
    }

    /// Return the exact relation keys and arities of the schema.
    pub fn solver_relations(&self) -> &[SchemaRelationRef] {
        &self.solver_relations
    }

    /// Return every exact constant key used anywhere in the task.
    pub fn solver_constants(&self) -> &[ConstantKey] {
        &self.solver_constants
    }

    /// Return the trusted solver source for the preprocessed precondition.
    pub fn preprocessed_pre_solver(&self) -> &SolverAssertSourceRef {
        &self.preprocessed_pre_solver
    }

    /// Return the trusted solver source for the preprocessed postcondition.
    pub fn preprocessed_post_solver(&self) -> &SolverAssertSourceRef {
        &self.preprocessed_post_solver
    }

    /// Return the trusted QF source for the exact loop guard.
    pub fn loop_guard_solver(&self) -> &SolverQfSourceRef {
        &self.loop_guard_solver
    }

    /// Return the trusted QF source for the negated loop guard.
    pub fn negated_loop_guard_solver(&self) -> &SolverQfSourceRef {
        &self.negated_loop_guard_solver
    }

    /// Return the sanitized agent-facing projection.
    pub fn agent_view(&self) -> AgentTaskView<'_> {
        AgentTaskView {
            identity: &self.identity,
            schema: &self.schema,
            original_pre: &self.original_pre,
            original_command: &self.original_command,
            original_post: &self.original_post,
            preprocessed_pre: &self.preprocessed_pre,
            preprocessed_command: &self.preprocessed_command,
            preprocessed_post: &self.preprocessed_post,
        }
    }
}

/// Sanitized task projection. It intentionally has no preprocessing evidence.
#[derive(Clone, Copy, Debug)]
pub struct AgentTaskView<'a> {
    pub identity: &'a TaskIdentity,
    pub schema: &'a SchemaRef,
    pub original_pre: &'a AssertExprRef,
    pub original_command: &'a WhielCommandRef,
    pub original_post: &'a AssertExprRef,
    pub preprocessed_pre: &'a AssertExprRef,
    pub preprocessed_command: &'a WhielCommandRef,
    pub preprocessed_post: &'a AssertExprRef,
}

// ------------------------------------------------------------
// Transport Errors And Validation
// ------------------------------------------------------------

#[derive(Debug)]
pub enum TaskLoadError {
    Json(String),
    UnsupportedVersion { found: u64, expected: u64 },
    InvalidField { field: &'static str, detail: String },
}

impl fmt::Display for TaskLoadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Json(detail) => write!(formatter, "invalid task JSON: {detail}"),
            Self::UnsupportedVersion { found, expected } => write!(
                formatter,
                "unsupported task format version {found}; expected {expected}"
            ),
            Self::InvalidField { field, detail } => {
                write!(formatter, "invalid {field}: {detail}")
            }
        }
    }
}

impl std::error::Error for TaskLoadError {}

fn invalid(field: &'static str, detail: impl Into<String>) -> TaskLoadError {
    TaskLoadError::InvalidField {
        field,
        detail: detail.into(),
    }
}

fn validate_identifier(field: &'static str, value: &str) -> Result<(), TaskLoadError> {
    if value.is_empty()
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
    {
        return Err(invalid(
            field,
            "must be nonempty and contain only ASCII letters, digits, '_' or '-'",
        ));
    }
    Ok(())
}

fn validate_name(field: &'static str, value: &str) -> Result<(), TaskLoadError> {
    let valid = value.split('.').all(|segment| {
        let mut bytes = segment.bytes();
        matches!(bytes.next(), Some(first) if first.is_ascii_alphabetic() || first == b'_')
            && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\'')
    });
    if !valid {
        return Err(invalid(field, "must be a nonempty dotted Lean name"));
    }
    Ok(())
}

fn value_ref(
    namespace: &str,
    field: &'static str,
    suffix: &str,
    raw: RawLeanValue,
) -> Result<LeanValueRef, TaskLoadError> {
    if raw.display.is_empty() {
        return Err(invalid(field, "display text must be nonempty"));
    }
    Ok(LeanValueRef {
        expression: exact_expression(namespace, expression_field(field), suffix, raw.expression)?,
        display: Arc::from(raw.display),
    })
}

fn expression_field(field: &'static str) -> &'static str {
    match field {
        "schema" => "schema.expression",
        "original.pre" => "original.pre.expression",
        "original.command" => "original.command.expression",
        "original.post" => "original.post.expression",
        "preprocessed.pre" => "preprocessed.pre.expression",
        "preprocessed.command" => "preprocessed.command.expression",
        "preprocessed.post" => "preprocessed.post.expression",
        _ => "value.expression",
    }
}

fn exact_expression(
    namespace: &str,
    field: &'static str,
    suffix: &str,
    found: String,
) -> Result<Arc<str>, TaskLoadError> {
    let expected = format!("{namespace}.{suffix}");
    if found != expected {
        return Err(invalid(
            field,
            format!("expected {expected:?}, found {found:?}"),
        ));
    }
    Ok(Arc::from(found))
}

struct SolverMetadata {
    relations: Arc<[SchemaRelationRef]>,
    constants: Arc<[ConstantKey]>,
    preprocessed_pre: SolverAssertSourceRef,
    preprocessed_post: SolverAssertSourceRef,
    loop_guard: SolverQfSourceRef,
    negated_loop_guard: SolverQfSourceRef,
}

type SolverSourceKeys = (Arc<[ConstantKey]>, Arc<[RelationKey]>);

fn solver_metadata(
    task: &TaskIdentity,
    schema_kind: TaskSchemaKind,
    raw: RawSolverMetadata,
) -> Result<SolverMetadata, TaskLoadError> {
    let mut relation_keys = HashSet::new();
    let mut relations = Vec::with_capacity(raw.schema_relations.len());
    for relation in raw.schema_relations {
        let key = parse_task_relation_key(schema_kind, relation.key)?;
        if !relation_keys.insert(key.clone()) {
            return Err(invalid("solver.schema_relations", "duplicate relation key"));
        }
        relations.push(SchemaRelationRef {
            key,
            arity: relation.arity,
        });
    }
    let mut constant_keys = HashSet::new();
    let mut constants = Vec::with_capacity(raw.task_constants.len());
    for value in raw.task_constants {
        let key = ConstantKey(parse_constant_key(value)?);
        if !constant_keys.insert(key.clone()) {
            return Err(invalid("solver.task_constants", "duplicate constant key"));
        }
        constants.push(key);
    }
    let (pre_suffix, pre_no_bound, post_suffix, post_no_bound) = match schema_kind {
        TaskSchemaKind::LegacyProgram => (
            "inputPreproc.loopPre",
            "inputPreproc.loopPre_noBound",
            "inputPreproc.loopPost",
            "inputPreproc.loopPost_noBound",
        ),
        TaskSchemaKind::FixedAmbient => (
            "inputPreproc.liftedLoop.preAssert",
            "inputPreproc.liftedLoop.preAssert_noBound",
            "inputPreproc.liftedLoop.postAssert",
            "inputPreproc.liftedLoop.postAssert_noBound",
        ),
    };
    let preprocessed_pre = solver_source(
        task,
        "task.preprocessed_pre",
        pre_suffix,
        pre_no_bound,
        raw.preprocessed_pre,
        schema_kind,
        &relation_keys,
        &constant_keys,
    )?;
    let preprocessed_post = solver_source(
        task,
        "task.preprocessed_post",
        post_suffix,
        post_no_bound,
        raw.preprocessed_post,
        schema_kind,
        &relation_keys,
        &constant_keys,
    )?;
    let loop_guard = solver_qf_source(
        task,
        "task.loop_guard",
        raw.loop_guard,
        schema_kind,
        &relation_keys,
        &constant_keys,
    )?;
    let negated_loop_guard = solver_qf_source(
        task,
        "task.negated_loop_guard",
        raw.negated_loop_guard,
        schema_kind,
        &relation_keys,
        &constant_keys,
    )?;
    Ok(SolverMetadata {
        relations: Arc::from(relations),
        constants: Arc::from(constants),
        preprocessed_pre,
        preprocessed_post,
        loop_guard,
        negated_loop_guard,
    })
}

fn solver_qf_source(
    task: &TaskIdentity,
    expected_id: &'static str,
    raw: RawQfSolverSource,
    schema_kind: TaskSchemaKind,
    relations: &HashSet<RelationKey>,
    constants: &HashSet<ConstantKey>,
) -> Result<SolverQfSourceRef, TaskLoadError> {
    if raw.source_id != expected_id {
        return Err(invalid(
            "solver.source_id",
            format!("expected {expected_id:?}"),
        ));
    }
    let (source_constants, source_relations) = solver_source_keys(
        raw.constants,
        raw.relations,
        schema_kind,
        relations,
        constants,
    )?;
    Ok(SolverQfSourceRef {
        task: task.clone(),
        source_id: Arc::from(raw.source_id),
        constants: source_constants,
        relations: source_relations,
    })
}

#[allow(clippy::too_many_arguments)]
fn solver_source(
    task: &TaskIdentity,
    expected_id: &'static str,
    expression_suffix: &'static str,
    evidence_suffix: &'static str,
    raw: RawSolverSource,
    schema_kind: TaskSchemaKind,
    relations: &HashSet<RelationKey>,
    constants: &HashSet<ConstantKey>,
) -> Result<SolverAssertSourceRef, TaskLoadError> {
    if raw.source_id != expected_id {
        return Err(invalid(
            "solver.source_id",
            format!("expected {expected_id:?}"),
        ));
    }
    let expression = exact_expression(
        task.namespace(),
        "solver.source.expression",
        expression_suffix,
        raw.expression,
    )?;
    let no_bound = NoBoundEvidenceRef {
        expression: exact_expression(
            task.namespace(),
            "solver.source.no_bound_expression",
            evidence_suffix,
            raw.no_bound_expression,
        )?,
    };
    let (source_constants, source_relations) = solver_source_keys(
        raw.constants,
        raw.relations,
        schema_kind,
        relations,
        constants,
    )?;
    Ok(SolverAssertSourceRef {
        task: task.clone(),
        source_id: Arc::from(raw.source_id),
        expression,
        no_bound,
        constants: source_constants,
        relations: source_relations,
    })
}

fn solver_source_keys(
    raw_constants: Vec<String>,
    raw_relations: Vec<String>,
    schema_kind: TaskSchemaKind,
    relations: &HashSet<RelationKey>,
    constants: &HashSet<ConstantKey>,
) -> Result<SolverSourceKeys, TaskLoadError> {
    let mut source_constants = Vec::with_capacity(raw_constants.len());
    let mut seen_constants = HashSet::new();
    for value in raw_constants {
        let key = ConstantKey(parse_constant_key(value)?);
        if !constants.contains(&key) || !seen_constants.insert(key.clone()) {
            return Err(invalid(
                "solver.source.constants",
                "constant is absent from the task set or duplicated",
            ));
        }
        source_constants.push(key);
    }
    let mut source_relations = Vec::with_capacity(raw_relations.len());
    let mut seen_relations = HashSet::new();
    for value in raw_relations {
        let key = parse_task_relation_key(schema_kind, value)?;
        if !relations.contains(&key) || !seen_relations.insert(key.clone()) {
            return Err(invalid(
                "solver.source.relations",
                "relation is absent from the schema or duplicated",
            ));
        }
        source_relations.push(key);
    }
    Ok((Arc::from(source_constants), Arc::from(source_relations)))
}

fn parse_task_relation_key(
    schema_kind: TaskSchemaKind,
    value: String,
) -> Result<RelationKey, TaskLoadError> {
    match schema_kind {
        TaskSchemaKind::LegacyProgram => RelationKey::from_canonical(value),
        TaskSchemaKind::FixedAmbient => RelationKey::from_lean_scope(value),
    }
}

fn parse_relation_key(value: String) -> Result<Arc<str>, TaskLoadError> {
    let Some(rest) = value.strip_prefix("rel:") else {
        return Err(invalid("solver.relation_key", "missing rel: prefix"));
    };
    let Some((base, index)) = rest.rsplit_once(':') else {
        return Err(invalid("solver.relation_key", "missing relation index"));
    };
    if base.is_empty() || !base.chars().all(char::is_alphabetic) || !is_canonical_nat(index) {
        return Err(invalid(
            "solver.relation_key",
            "malformed concrete relation key",
        ));
    }
    Ok(Arc::from(value))
}

fn parse_constant_key(value: String) -> Result<Arc<str>, TaskLoadError> {
    let valid = if let Some(number) = value.strip_prefix("num:") {
        is_canonical_nat(number)
    } else {
        matches!(value.as_str(), "bool:0" | "bool:1") || value.starts_with("str:")
    };
    if !valid {
        return Err(invalid(
            "solver.constant_key",
            "malformed concrete constant key",
        ));
    }
    Ok(Arc::from(value))
}

fn is_canonical_nat(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| byte.is_ascii_digit())
        && (value == "0" || !value.starts_with('0'))
}

// ------------------------------------------------------------
// JSON Transport Records
// ------------------------------------------------------------

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTaskManifest {
    format_version: u64,
    semantic_version: u64,
    encoding_version: u64,
    identity: RawTaskIdentity,
    schema: RawLeanValue,
    original: RawTriple,
    preprocessed: RawTriple,
    preprocessing_evidence: RawEvidence,
    solver: RawSolverMetadata,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTaskIdentity {
    canonical_id: String,
    module: String,
    namespace: String,
    source_sha256: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTriple {
    pre: RawLeanValue,
    command: RawLeanValue,
    post: RawLeanValue,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLeanValue {
    expression: String,
    display: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawEvidence {
    expression: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSolverMetadata {
    schema_relations: Vec<RawSchemaRelation>,
    task_constants: Vec<String>,
    preprocessed_pre: RawSolverSource,
    preprocessed_post: RawSolverSource,
    loop_guard: RawQfSolverSource,
    negated_loop_guard: RawQfSolverSource,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSchemaRelation {
    key: String,
    arity: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSolverSource {
    source_id: String,
    expression: String,
    no_bound_expression: String,
    constants: Vec<String>,
    relations: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawQfSolverSource {
    source_id: String,
    constants: Vec<String>,
    relations: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid_json() -> String {
        r#"{
          "format_version": 3,
          "semantic_version": 1,
          "encoding_version": 1,
          "identity": {
            "canonical_id": "Example0012",
            "module": "Benchmark.Example0012.Input",
            "namespace": "Whiel.Benchmark.Example0012",
            "source_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
          },
          "schema": {"expression":"Whiel.Benchmark.Example0012.programSchema","display":"{R}"},
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
            "task_constants": ["num:0", "str:a:b", "bool:1"],
            "preprocessed_pre": {
              "source_id":"task.preprocessed_pre",
              "expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre",
              "no_bound_expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre_noBound",
              "constants":["num:0", "str:a:b"],
              "relations":["rel:E:0", "rel:T:1"]
            },
            "preprocessed_post": {
              "source_id":"task.preprocessed_post",
              "expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost",
              "no_bound_expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost_noBound",
              "constants":["bool:1"],
              "relations":["rel:T:0", "rel:TBound:0"]
            },
            "loop_guard": {
              "source_id":"task.loop_guard",
              "constants":["num:0"],
              "relations":["rel:T:1"]
            },
            "negated_loop_guard": {
              "source_id":"task.negated_loop_guard",
              "constants":["num:0"],
              "relations":["rel:T:1"]
            }
          }
        }"#.to_string()
    }

    fn fixed_ambient_json() -> String {
        valid_json()
            .replace("\"format_version\": 3", "\"format_version\": 4")
            .replace("programSchema", "inputPreproc.prophecySchema")
            .replace("inputPreproc.loopPre", "inputPreproc.liftedLoop.preAssert")
            .replace("inputPreproc.loopCmd", "inputPreproc.liftedLoop.cmd")
            .replace(
                "inputPreproc.loopPost",
                "inputPreproc.liftedLoop.postAssert",
            )
            .replace("rel:E:0", "o:p::E")
            .replace("rel:T:0", "o:p::T")
            .replace("rel:T:1", "o:p:s:T")
            .replace("rel:TBound:0", "y:p::T")
    }

    #[test]
    fn task_clone_shares_backing_strings() {
        let task = SynthesisTask::from_json(&valid_json()).unwrap();
        let clone = task.clone();
        assert!(Arc::ptr_eq(
            &task.original_command.0.display,
            &clone.original_command.0.display
        ));
        assert!(Arc::ptr_eq(
            &task.identity.canonical_id,
            &clone.identity.canonical_id
        ));
    }

    #[test]
    fn rejects_wrong_preprocessed_binding() {
        let text = valid_json().replace("inputPreproc.loopCmd", "inputPreproc.sourcePrefix");
        let error = SynthesisTask::from_json(&text).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("preprocessed.command.expression")
        );
    }

    #[test]
    fn rejects_unknown_fields() {
        let text = valid_json().replace(
            "\"format_version\": 3,",
            "\"format_version\": 3, \"surprise\": true,",
        );
        assert!(SynthesisTask::from_json(&text).is_err());
    }

    #[test]
    fn rejects_version_one_as_an_unsupported_transport() {
        let text = valid_json().replace("\"format_version\": 3", "\"format_version\": 1");
        assert!(matches!(
            SynthesisTask::from_json(&text),
            Err(TaskLoadError::UnsupportedVersion {
                found: 1,
                expected: 3
            })
        ));
    }

    #[test]
    fn rejects_malformed_dotted_names() {
        for invalid_name in ["Whiel..Task", "1Whiel.Task", ".Whiel", "Whiel."] {
            let text = valid_json().replace(
                "Whiel.Benchmark.Example0012\",",
                &format!("{invalid_name}\","),
            );
            assert!(SynthesisTask::from_json(&text).is_err(), "{invalid_name}");
        }
    }

    #[test]
    fn exposes_exact_solver_metadata() {
        let task = SynthesisTask::from_json(&valid_json()).unwrap();
        assert_eq!(
            task.solver_relations()
                .iter()
                .map(|relation| (relation.key().as_str(), relation.arity()))
                .collect::<Vec<_>>(),
            vec![
                ("rel:E:0", 2),
                ("rel:T:0", 2),
                ("rel:T:1", 2),
                ("rel:TBound:0", 2),
            ]
        );
        assert_eq!(
            task.solver_constants()
                .iter()
                .map(ConstantKey::as_str)
                .collect::<Vec<_>>(),
            vec!["num:0", "str:a:b", "bool:1"]
        );
        assert_eq!(
            task.preprocessed_pre_solver().no_bound().expression(),
            "Whiel.Benchmark.Example0012.inputPreproc.loopPre_noBound"
        );
        assert_eq!(
            task.preprocessed_pre_solver().task_identity(),
            task.identity()
        );
        assert_eq!(
            task.preprocessed_post_solver().source_id(),
            "task.preprocessed_post"
        );
        assert_eq!(task.loop_guard_solver().source_id(), "task.loop_guard");
        assert_eq!(
            task.negated_loop_guard_solver().source_id(),
            "task.negated_loop_guard"
        );
    }

    #[test]
    fn rejects_noncanonical_and_unknown_solver_keys() {
        for invalid_key in ["num:00", "string:a:b", "rel:E:00"] {
            let text = valid_json().replace(
                match invalid_key {
                    "num:00" => "num:0",
                    "string:a:b" => "str:a:b",
                    "rel:E:00" => "rel:E:0",
                    _ => unreachable!(),
                },
                invalid_key,
            );
            assert!(SynthesisTask::from_json(&text).is_err(), "{invalid_key}");
        }

        let text = valid_json().replace(
            "\"relations\":[\"rel:E:0\", \"rel:T:1\"]",
            "\"relations\":[\"rel:E:0\", \"rel:Missing:0\"]",
        );
        assert!(SynthesisTask::from_json(&text).is_err());
    }

    #[test]
    fn accepts_exact_unicode_relation_and_arbitrary_string_keys() {
        assert!(parse_relation_key("rel:É:0".to_string()).is_ok());
        assert_eq!(
            ConstantKey::from_canonical("str:").unwrap().as_str(),
            "str:"
        );
        assert_eq!(
            ConstantKey::from_canonical("str:a:b:λ").unwrap().as_str(),
            "str:a:b:λ"
        );
    }

    #[test]
    fn framework_ii_scope_keys_are_opaque_but_bounded() {
        assert!(RelationKey::from_canonical("prophecy:rel:T:0").is_err());
        assert_eq!(
            RelationKey::from_lean_scope("prophecy:rel:T:0")
                .unwrap()
                .as_str(),
            "prophecy:rel:T:0"
        );
        assert!(RelationKey::from_lean_scope("").is_err());
        assert!(
            RelationKey::from_lean_scope("x".repeat(MAX_FRAMEWORK_II_RELATION_KEY_BYTES + 1))
                .is_err()
        );
    }

    #[test]
    fn fixed_ambient_loading_is_explicit_and_keys_stay_opaque() {
        let fixed = fixed_ambient_json();
        assert!(SynthesisTask::from_json(&fixed).is_err());
        let task = SynthesisTask::from_fixed_ambient_json(&fixed).unwrap();
        assert_eq!(task.schema_kind(), TaskSchemaKind::FixedAmbient);
        assert_eq!(task.solver_relations()[0].key().as_str(), "o:p::E");
        assert_eq!(task.solver_relations()[3].key().as_str(), "y:p::T");
        assert!(SynthesisTask::from_fixed_ambient_json(&valid_json()).is_err());
    }

    #[test]
    fn rejects_solver_binding_and_evidence_drift() {
        let wrong_source = valid_json().replace("task.preprocessed_pre", "task.preprocessed_other");
        assert!(SynthesisTask::from_json(&wrong_source).is_err());

        let wrong_evidence = valid_json().replace(
            "inputPreproc.loopPost_noBound",
            "inputPreproc.loopPre_noBound",
        );
        assert!(SynthesisTask::from_json(&wrong_evidence).is_err());
    }
}

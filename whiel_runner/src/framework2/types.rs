//! Opaque Rust handles for Lean-owned fixed-ambient values.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use serde_json::Value;

use crate::encoding::canonical_value_sha256;
use crate::task::{RelationKey, TaskIdentity};

use super::components::{FrameworkIIClauseComponents, FrameworkIITaskComponents};

/// One Lean-issued lower-bound or Rust-owned fixed-ambient placement level.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FrameworkIILevel(u64);

impl FrameworkIILevel {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    /// Construct one nonnegative fixed-ambient level.
    ///
    /// Possessing a level value does not authorize a clause placement.  Only
    /// the leveled Houdini controller can publish a placement in a snapshot.
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn get(self) -> u64 {
        self.0
    }

    pub(super) const fn admitted(value: u64) -> Self {
        Self(value)
    }

    pub(super) fn checked_successor(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }
}

/// One exact relation in the Lean-owned ambient solver schema.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrameworkIIRelation {
    key: RelationKey,
    arity: u64,
}

impl FrameworkIIRelation {
    pub(super) fn new(key: RelationKey, arity: u64) -> Self {
        Self { key, arity }
    }

    pub fn key(&self) -> &RelationKey {
        &self.key
    }

    pub fn arity(&self) -> u64 {
        self.arity
    }
}

/// One opaque same-arity program-to-prophecy binding issued by Lean.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FrameworkIIProphecyBinding {
    program: RelationKey,
    prophecy: RelationKey,
    arity: u64,
}

impl FrameworkIIProphecyBinding {
    pub(super) fn new(program: RelationKey, prophecy: RelationKey, arity: u64) -> Self {
        Self {
            program,
            prophecy,
            arity,
        }
    }

    pub fn program(&self) -> &RelationKey {
        &self.program
    }

    pub fn prophecy(&self) -> &RelationKey {
        &self.prophecy
    }

    pub fn arity(&self) -> u64 {
        self.arity
    }
}

/// The exact Lean-owned fixed ambient scope for one synthesis task.
#[derive(Clone)]
pub struct FixedAmbientTaskScope {
    task: TaskIdentity,
    identity: Arc<Value>,
    identity_canonical: Arc<str>,
    identity_sha256: Arc<str>,
    relations: Arc<[FrameworkIIRelation]>,
    prophecy_bindings: Arc<[FrameworkIIProphecyBinding]>,
    components: Arc<FrameworkIITaskComponents>,
}

impl FixedAmbientTaskScope {
    pub(super) fn admitted(
        task: TaskIdentity,
        identity: Value,
        relations: Vec<FrameworkIIRelation>,
        prophecy_bindings: Vec<FrameworkIIProphecyBinding>,
        components: FrameworkIITaskComponents,
    ) -> Self {
        let identity_canonical = canonical_json(&identity);
        let identity_sha256 = Arc::from(canonical_value_sha256(&identity));
        Self {
            task,
            identity: Arc::new(identity),
            identity_canonical,
            identity_sha256,
            relations: relations.into(),
            prophecy_bindings: prophecy_bindings.into(),
            components: Arc::new(components),
        }
    }

    #[cfg(test)]
    pub(super) fn new(
        task: TaskIdentity,
        identity: Value,
        _presentation: Value,
        _program_relations: Vec<FrameworkIIRelation>,
        relations: Vec<FrameworkIIRelation>,
        prophecy_bindings: Vec<FrameworkIIProphecyBinding>,
    ) -> Self {
        let components = super::components::test_task_components(&identity);
        Self::admitted(task, identity, relations, prophecy_bindings, components)
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task
    }

    /// Return the complete unhashed Lean identity token.
    pub fn identity(&self) -> &Value {
        &self.identity
    }

    /// Return a non-authoritative lookup and logging aid.
    pub fn identity_sha256(&self) -> &str {
        &self.identity_sha256
    }

    /// Return the one ambient relation table in Lean's canonical order.
    pub fn relations(&self) -> &[FrameworkIIRelation] {
        &self.relations
    }

    /// Return every canonical source-IDB to prophecy binding.
    pub fn prophecy_bindings(&self) -> &[FrameworkIIProphecyBinding] {
        &self.prophecy_bindings
    }

    /// Return every task-scoped component admitted with this exact scope.
    pub fn components(&self) -> &FrameworkIITaskComponents {
        &self.components
    }
}

impl PartialEq for FixedAmbientTaskScope {
    fn eq(&self, other: &Self) -> bool {
        self.task == other.task
            && self.identity == other.identity
            && self.relations == other.relations
            && self.prophecy_bindings == other.prophecy_bindings
            && self.components == other.components
    }
}

impl Eq for FixedAmbientTaskScope {}

impl Hash for FixedAmbientTaskScope {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.task.hash(state);
        self.identity_canonical.hash(state);
        self.relations.hash(state);
        self.prophecy_bindings.hash(state);
        self.components.hash(state);
    }
}

impl fmt::Debug for FixedAmbientTaskScope {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FixedAmbientTaskScope")
            .field("task", &self.task.canonical_id())
            .field("identity_sha256", &self.identity_sha256)
            .finish_non_exhaustive()
    }
}

/// One exact Lean-admitted clause over the fixed ambient schema.
#[derive(Clone)]
pub struct ExtendedClause {
    scope: FixedAmbientTaskScope,
    identity: Arc<Value>,
    identity_canonical: Arc<str>,
    identity_sha256: Arc<str>,
    order_key: Arc<str>,
    canonical_source: Arc<str>,
    display: Arc<str>,
    relation_keys: Arc<[String]>,
    minimum_level: FrameworkIILevel,
    mentions_prophecy: bool,
    components: Arc<FrameworkIIClauseComponents>,
}

impl ExtendedClause {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn admitted(
        scope: FixedAmbientTaskScope,
        identity: Value,
        order_key: String,
        canonical_source: String,
        display: String,
        relation_keys: Vec<String>,
        minimum_level: FrameworkIILevel,
        mentions_prophecy: bool,
        components: FrameworkIIClauseComponents,
    ) -> Self {
        let identity_canonical = canonical_json(&identity);
        let identity_sha256 = Arc::from(canonical_value_sha256(&identity));
        Self {
            scope,
            identity: Arc::new(identity),
            identity_canonical,
            identity_sha256,
            order_key: Arc::from(order_key),
            canonical_source: Arc::from(canonical_source),
            display: Arc::from(display),
            relation_keys: relation_keys.into(),
            minimum_level,
            mentions_prophecy,
            components: Arc::new(components),
        }
    }

    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        scope: FixedAmbientTaskScope,
        identity: Value,
        order_key: String,
        display: String,
        relation_keys: Vec<String>,
        mentions_prophecy: bool,
        minimum_level: FrameworkIILevel,
    ) -> Self {
        let components =
            super::components::test_clause_components(scope.identity(), &identity, &relation_keys);
        Self::admitted(
            scope,
            identity,
            order_key,
            display.clone(),
            display,
            relation_keys,
            minimum_level,
            mentions_prophecy,
            components,
        )
    }

    pub fn scope(&self) -> &FixedAmbientTaskScope {
        &self.scope
    }

    /// Return the complete unhashed Lean formula identity token.
    pub fn identity(&self) -> &Value {
        &self.identity
    }

    pub fn identity_sha256(&self) -> &str {
        &self.identity_sha256
    }

    pub fn display(&self) -> &str {
        &self.display
    }

    /// Return the exact parseable source re-admitted by Lean.
    pub fn canonical_source(&self) -> &str {
        &self.canonical_source
    }

    pub fn relation_keys(&self) -> &[String] {
        &self.relation_keys
    }

    pub fn minimum_level(&self) -> FrameworkIILevel {
        self.minimum_level
    }

    /// Whether Lean's admitted formula mentions a prophecy relation.
    ///
    /// Drives the Pass 7.5b terminal `dead` rule: a clause for which this is
    /// `false` becomes permanently dead on a Lean-validated finite
    /// refutation of its level-zero initialization obligation, rather than
    /// promoting. A prophecy-bearing clause always keeps promoting.
    pub fn mentions_prophecy_relation(&self) -> bool {
        self.mentions_prophecy
    }

    /// Return every clause-scoped component admitted with this formula.
    pub fn components(&self) -> &FrameworkIIClauseComponents {
        &self.components
    }

    /// Exact structural transport key used for formula interning.
    ///
    /// Equality and interning use this complete identity rather than a digest
    /// or the separate Lean comparison key.
    pub(super) fn identity_intern_key(&self) -> &str {
        &self.identity_canonical
    }

    /// Lean-emitted deterministic comparison key for catalog registration.
    pub(super) fn registration_order_key(&self) -> &str {
        &self.order_key
    }

    pub(super) fn semantic_metadata_matches(&self, other: &Self) -> bool {
        self.scope == other.scope
            && self.identity == other.identity
            && self.order_key == other.order_key
            && self.canonical_source == other.canonical_source
            && self.relation_keys == other.relation_keys
            && self.minimum_level == other.minimum_level
            && self.mentions_prophecy == other.mentions_prophecy
            && self.components == other.components
    }
}

impl PartialEq for ExtendedClause {
    fn eq(&self, other: &Self) -> bool {
        self.scope == other.scope && self.identity == other.identity
    }
}

impl Eq for ExtendedClause {}

impl Hash for ExtendedClause {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.scope.hash(state);
        self.identity_canonical.hash(state);
    }
}

impl fmt::Debug for ExtendedClause {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ExtendedClause")
            .field("scope_sha256", &self.scope.identity_sha256())
            .field("identity_sha256", &self.identity_sha256)
            .field("canonical_source", &self.canonical_source)
            .field("display", &self.display)
            .field("minimum_level", &self.minimum_level)
            .finish_non_exhaustive()
    }
}

/// One bounded correction diagnostic produced by Lean admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmissionDiagnostic {
    code: Arc<str>,
    message: Arc<str>,
    item_index: Option<usize>,
    path: Option<Arc<str>>,
    offset: Option<usize>,
}

impl AdmissionDiagnostic {
    pub(super) fn new(
        code: String,
        message: String,
        item_index: Option<usize>,
        path: Option<String>,
        offset: Option<usize>,
    ) -> Self {
        Self {
            code: Arc::from(code),
            message: Arc::from(message),
            item_index,
            path: path.map(Arc::from),
            offset,
        }
    }

    pub fn code(&self) -> &str {
        &self.code
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn item_index(&self) -> Option<usize> {
        self.item_index
    }

    pub fn path(&self) -> Option<&str> {
        self.path.as_deref()
    }

    pub fn offset(&self) -> Option<usize> {
        self.offset
    }
}

/// A complete correctable admission result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmissionCorrection {
    diagnostics: Arc<[AdmissionDiagnostic]>,
}

impl AdmissionCorrection {
    pub(super) fn new(diagnostics: Vec<AdmissionDiagnostic>) -> Self {
        Self {
            diagnostics: diagnostics.into(),
        }
    }

    pub fn diagnostics(&self) -> &[AdmissionDiagnostic] {
        &self.diagnostics
    }
}

/// A semantic submission was accepted or can be corrected by its caller.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdmissionOutcome<T> {
    Accepted(T),
    Correctable(AdmissionCorrection),
}

impl<T> AdmissionOutcome<T> {
    pub fn accepted(&self) -> Option<&T> {
        match self {
            Self::Accepted(value) => Some(value),
            Self::Correctable(_) => None,
        }
    }

    pub fn correction(&self) -> Option<&AdmissionCorrection> {
        match self {
            Self::Accepted(_) => None,
            Self::Correctable(correction) => Some(correction),
        }
    }
}

fn canonical_json(value: &Value) -> Arc<str> {
    Arc::from(
        serde_json::to_string(value).expect("an in-memory JSON identity always serializes to JSON"),
    )
}

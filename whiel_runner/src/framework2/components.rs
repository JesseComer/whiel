//! Lean-owned fixed-ambient components.
//!
//! Rust retains complete identities and canonical sources, but never
//! interprets relation-name constructors or formula syntax.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use serde_json::{Value, json};

use crate::encoding::canonical_value_sha256;
use crate::task::{ConstantKey, RelationKey};

/// The Lean-issued role of one independently prepared formula.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FrameworkIIComponentRole {
    Precondition,
    Guard,
    NegatedThetaGuard,
    NegatedGuard,
    Postcondition,
    Clause,
    ThetaClause,
    MaintenanceWp,
    CollapsedClause,
}

impl FrameworkIIComponentRole {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Precondition => "precondition",
            Self::Guard => "guard",
            Self::NegatedThetaGuard => "negated_theta_guard",
            Self::NegatedGuard => "negated_guard",
            Self::Postcondition => "postcondition",
            Self::Clause => "clause",
            Self::ThetaClause => "theta_clause",
            Self::MaintenanceWp => "maintenance_wp",
            Self::CollapsedClause => "collapsed_clause",
        }
    }

    pub(super) fn is_task(self) -> bool {
        matches!(
            self,
            Self::Precondition
                | Self::Guard
                | Self::NegatedThetaGuard
                | Self::NegatedGuard
                | Self::Postcondition
        )
    }
}

/// Lean-owned metadata for one exact QF formula.
#[derive(Clone)]
pub struct FrameworkIIComponentFormula {
    source_id: Arc<str>,
    identity: Arc<Value>,
    identity_canonical: Arc<str>,
    identity_sha256: Arc<str>,
    canonical_source: Arc<str>,
    display: Arc<str>,
    relation_keys: Arc<[RelationKey]>,
    constant_keys: Arc<[ConstantKey]>,
    semantic_theorem: Arc<str>,
}

impl FrameworkIIComponentFormula {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        source_id: String,
        identity: Value,
        canonical_source: String,
        display: String,
        relation_keys: Vec<RelationKey>,
        constant_keys: Vec<ConstantKey>,
        semantic_theorem: String,
    ) -> Self {
        let identity_canonical = canonical_json(&identity);
        let identity_sha256 = Arc::from(canonical_value_sha256(&identity));
        Self {
            source_id: Arc::from(source_id),
            identity: Arc::new(identity),
            identity_canonical,
            identity_sha256,
            canonical_source: Arc::from(canonical_source),
            display: Arc::from(display),
            relation_keys: relation_keys.into(),
            constant_keys: constant_keys.into(),
            semantic_theorem: Arc::from(semantic_theorem),
        }
    }

    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    pub fn identity(&self) -> &Value {
        &self.identity
    }

    pub fn identity_sha256(&self) -> &str {
        &self.identity_sha256
    }

    pub fn canonical_source(&self) -> &str {
        &self.canonical_source
    }

    pub fn display(&self) -> &str {
        &self.display
    }

    pub fn relation_keys(&self) -> &[RelationKey] {
        &self.relation_keys
    }

    pub fn constant_keys(&self) -> &[ConstantKey] {
        &self.constant_keys
    }

    pub fn semantic_theorem(&self) -> &str {
        &self.semantic_theorem
    }
}

impl PartialEq for FrameworkIIComponentFormula {
    fn eq(&self, other: &Self) -> bool {
        self.source_id == other.source_id
            && self.identity == other.identity
            && self.canonical_source == other.canonical_source
            && self.display == other.display
            && self.relation_keys == other.relation_keys
            && self.constant_keys == other.constant_keys
            && self.semantic_theorem == other.semantic_theorem
    }
}

impl Eq for FrameworkIIComponentFormula {}

impl Hash for FrameworkIIComponentFormula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.source_id.hash(state);
        self.identity_canonical.hash(state);
        self.canonical_source.hash(state);
        self.display.hash(state);
        self.relation_keys.hash(state);
        self.constant_keys.hash(state);
        self.semantic_theorem.hash(state);
    }
}

impl fmt::Debug for FrameworkIIComponentFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FrameworkIIComponentFormula")
            .field("source_id", &self.source_id)
            .field("identity_sha256", &self.identity_sha256)
            .field("canonical_source", &self.canonical_source)
            .field("display", &self.display)
            .finish_non_exhaustive()
    }
}

/// Complete Lean authority for one fixed-ambient formula component.
#[derive(Clone)]
pub struct FrameworkIIComponentMetadata {
    role: FrameworkIIComponentRole,
    identity: Arc<Value>,
    identity_canonical: Arc<str>,
    digest: Arc<str>,
    formula: FrameworkIIComponentFormula,
}

impl FrameworkIIComponentMetadata {
    pub(super) fn new(
        role: FrameworkIIComponentRole,
        identity: Value,
        digest: String,
        formula: FrameworkIIComponentFormula,
    ) -> Self {
        Self {
            role,
            identity_canonical: canonical_json(&identity),
            identity: Arc::new(identity),
            digest: Arc::from(digest),
            formula,
        }
    }

    pub fn role(&self) -> FrameworkIIComponentRole {
        self.role
    }

    pub fn identity(&self) -> &Value {
        &self.identity
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    pub fn formula(&self) -> &FrameworkIIComponentFormula {
        &self.formula
    }
}

impl PartialEq for FrameworkIIComponentMetadata {
    fn eq(&self, other: &Self) -> bool {
        self.role == other.role
            && self.identity == other.identity
            && self.digest == other.digest
            && self.formula == other.formula
    }
}

impl Eq for FrameworkIIComponentMetadata {}

impl Hash for FrameworkIIComponentMetadata {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.role.hash(state);
        self.identity_canonical.hash(state);
        self.digest.hash(state);
        self.formula.hash(state);
    }
}

impl fmt::Debug for FrameworkIIComponentMetadata {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FrameworkIIComponentMetadata")
            .field("role", &self.role)
            .field("digest", &self.digest)
            .field("formula", &self.formula)
            .finish_non_exhaustive()
    }
}

/// The five immutable task components emitted by Lean.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FrameworkIITaskComponents {
    components: Arc<[FrameworkIIComponentMetadata]>,
    digest: Arc<str>,
}

impl FrameworkIITaskComponents {
    pub(super) fn new(components: Vec<FrameworkIIComponentMetadata>) -> Self {
        debug_assert_eq!(components.len(), 5);
        let digest = bundle_digest(
            "whiel-framework-ii-fixed-ambient-task-components-v1",
            &components,
        );
        Self {
            components: components.into(),
            digest,
        }
    }

    pub fn components(&self) -> &[FrameworkIIComponentMetadata] {
        &self.components
    }

    pub fn get(&self, role: FrameworkIIComponentRole) -> Option<&FrameworkIIComponentMetadata> {
        self.components
            .iter()
            .find(|component| component.role() == role)
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }
}

/// The four immutable components emitted with one admitted clause.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FrameworkIIClauseComponents {
    components: Arc<[FrameworkIIComponentMetadata]>,
    digest: Arc<str>,
}

impl FrameworkIIClauseComponents {
    pub(super) fn new(components: Vec<FrameworkIIComponentMetadata>) -> Self {
        debug_assert_eq!(components.len(), 4);
        let digest = bundle_digest(
            "whiel-framework-ii-fixed-ambient-clause-components-v1",
            &components,
        );
        Self {
            components: components.into(),
            digest,
        }
    }

    pub fn components(&self) -> &[FrameworkIIComponentMetadata] {
        &self.components
    }

    pub fn get(&self, role: FrameworkIIComponentRole) -> Option<&FrameworkIIComponentMetadata> {
        self.components
            .iter()
            .find(|component| component.role() == role)
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }
}

fn bundle_digest(domain: &str, components: &[FrameworkIIComponentMetadata]) -> Arc<str> {
    let rows = components
        .iter()
        .map(|component| {
            json!({
                "role": component.role().as_str(),
                "identity": component.identity(),
                "digest": component.digest(),
                "formula_identity": component.formula().identity(),
                "canonical_source": component.formula().canonical_source(),
                "source_id": component.formula().source_id(),
            })
        })
        .collect::<Vec<_>>();
    Arc::from(canonical_value_sha256(&json!({
        "domain": domain,
        "components": rows,
    })))
}

fn canonical_json(value: &Value) -> Arc<str> {
    Arc::from(serde_json::to_string(value).expect("an in-memory JSON identity always serializes"))
}

#[cfg(test)]
pub(super) fn test_task_components(scope_identity: &Value) -> FrameworkIITaskComponents {
    FrameworkIITaskComponents::new(
        [
            FrameworkIIComponentRole::Precondition,
            FrameworkIIComponentRole::Guard,
            FrameworkIIComponentRole::NegatedThetaGuard,
            FrameworkIIComponentRole::NegatedGuard,
            FrameworkIIComponentRole::Postcondition,
        ]
        .into_iter()
        .map(|role| test_component(role, scope_identity, None, Vec::new()))
        .collect(),
    )
}

#[cfg(test)]
pub(super) fn test_clause_components(
    scope_identity: &Value,
    clause_identity: &Value,
    relation_keys: &[String],
) -> FrameworkIIClauseComponents {
    let relations = relation_keys
        .iter()
        .map(|key| RelationKey::from_lean_scope(key.clone()).expect("bounded test relation key"))
        .collect::<Vec<_>>();
    FrameworkIIClauseComponents::new(
        [
            FrameworkIIComponentRole::Clause,
            FrameworkIIComponentRole::ThetaClause,
            FrameworkIIComponentRole::MaintenanceWp,
            FrameworkIIComponentRole::CollapsedClause,
        ]
        .into_iter()
        .map(|role| {
            test_component(
                role,
                scope_identity,
                Some(clause_identity),
                relations.clone(),
            )
        })
        .collect(),
    )
}

#[cfg(test)]
fn test_component(
    role: FrameworkIIComponentRole,
    scope_identity: &Value,
    clause_identity: Option<&Value>,
    relations: Vec<RelationKey>,
) -> FrameworkIIComponentMetadata {
    let result_identity = json!([
        "test-fixed-ambient-component-formula-v1",
        role.as_str(),
        clause_identity.unwrap_or(scope_identity),
    ]);
    let source_id = format!(
        "framework_ii.fixed_ambient.test.{}.{}",
        role.as_str(),
        canonical_value_sha256(&result_identity),
    );
    let mut identity = json!({
        "kind": "whiel_framework_ii_fixed_ambient_component",
        "version": 1,
        "scope_identity": scope_identity,
        "role": role.as_str(),
        "result_formula_identity": result_identity,
        "source_id": source_id,
    });
    if let Some(clause_identity) = clause_identity {
        identity["base_clause_identity"] = clause_identity.clone();
    }
    let digest = canonical_value_sha256(&identity);
    FrameworkIIComponentMetadata::new(
        role,
        identity,
        digest,
        FrameworkIIComponentFormula::new(
            source_id,
            result_identity,
            role.as_str().to_owned(),
            role.as_str().to_owned(),
            relations,
            Vec::new(),
            "Whiel.QFAssertExpr.toRelCalcSentence_correct".to_owned(),
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_ambient_bundles_are_role_ordered_and_source_bound() {
        let scope = json!(["scope"]);
        let task = test_task_components(&scope);
        assert_eq!(task.components().len(), 5);
        let clause = test_clause_components(&scope, &json!(["clause"]), &["o:p::R".to_owned()]);
        assert_eq!(clause.components().len(), 4);
        assert_ne!(task.digest(), clause.digest());
        assert!(
            clause
                .components()
                .iter()
                .all(|component| !component.formula().canonical_source().is_empty())
        );
    }
}

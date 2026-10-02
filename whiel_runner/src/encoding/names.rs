//! Stable append-only task-scoped solver names.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use super::solver_name::{SolverNameError, constant_solver_name, relation_solver_name};
use crate::task::{ConstantKey, RelationKey, SynthesisTask};

// ------------------------------------------------------------
// Wire Mappings
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NameMappingKind {
    Relation,
    Constant,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NameMapping {
    pub kind: NameMappingKind,
    pub key: String,
    pub tptp_name: String,
}

/// One contiguous append-only update replayed to each persistent worker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NameEnvDelta {
    pub(crate) base_revision: NameEnvRevision,
    pub(crate) revision: NameEnvRevision,
    pub(crate) relations: Arc<[NameMapping]>,
    pub(crate) constants: Arc<[NameMapping]>,
}

/// An immutable replay plan through one exact authoritative revision.
#[derive(Clone, Debug)]
pub(crate) struct NameEnvSync {
    pub(crate) target_revision: NameEnvRevision,
    pub(crate) deltas: Arc<Vec<Arc<NameEnvDelta>>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NameEnvRevision(u64);

impl NameEnvRevision {
    pub const INITIAL: Self = Self(0);

    pub fn get(self) -> u64 {
        self.0
    }

    #[cfg(test)]
    pub(crate) const fn from_raw(value: u64) -> Self {
        Self(value)
    }
}

// ------------------------------------------------------------
// Append-Only Environment
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct TaskNameEnv {
    relations: BTreeMap<RelationKey, Arc<str>>,
    constants: BTreeMap<ConstantKey, Arc<str>>,
    revision: NameEnvRevision,
    deltas: Arc<Vec<Arc<NameEnvDelta>>>,
}

impl TaskNameEnv {
    /// Build one append-only environment from Lean-issued opaque keys.
    pub(crate) fn from_keys(
        relations: impl IntoIterator<Item = RelationKey>,
        constants: impl IntoIterator<Item = ConstantKey>,
    ) -> Result<Self, SolverNameError> {
        let mut environment = Self {
            relations: BTreeMap::new(),
            constants: BTreeMap::new(),
            revision: NameEnvRevision::INITIAL,
            deltas: Arc::new(Vec::new()),
        };
        environment.extend(relations, constants)?;
        Ok(environment)
    }

    pub fn from_task(task: &SynthesisTask) -> Result<Self, SolverNameError> {
        Self::from_keys(
            task.solver_relations()
                .iter()
                .map(|relation| relation.key().clone()),
            task.solver_constants().iter().cloned(),
        )
    }

    pub fn revision(&self) -> NameEnvRevision {
        self.revision
    }

    /// Extend the environment once for a logical batch.
    ///
    /// Existing assignments are never changed.  The revision advances only
    /// when at least one new key is admitted.  Every name is computed before
    /// any is recorded, so a key whose solver name cannot be computed leaves
    /// the environment exactly as it was: no symbol ever receives a name of
    /// the environment's own invention.
    pub fn extend(
        &mut self,
        relations: impl IntoIterator<Item = RelationKey>,
        constants: impl IntoIterator<Item = ConstantKey>,
    ) -> Result<NameEnvRevision, SolverNameError> {
        let base_revision = self.revision;
        let mut admitted_relations = Vec::new();
        let mut admitted_constants = Vec::new();
        let mut pending_relations = BTreeSet::new();
        let mut pending_constants = BTreeSet::new();
        for relation in relations {
            if !self.relations.contains_key(&relation) && pending_relations.insert(relation.clone())
            {
                let name = relation_solver_name(relation.as_str())?;
                admitted_relations.push((relation, name));
            }
        }
        for constant in constants {
            if !self.constants.contains_key(&constant) && pending_constants.insert(constant.clone())
            {
                let name = constant_solver_name(constant.as_str())?;
                admitted_constants.push((constant, name));
            }
        }
        let mut new_relations = Vec::with_capacity(admitted_relations.len());
        let mut new_constants = Vec::with_capacity(admitted_constants.len());
        for (relation, name) in admitted_relations {
            self.relations.insert(relation.clone(), Arc::from(name));
            new_relations.push(self.relation_mapping(&relation));
        }
        for (constant, name) in admitted_constants {
            self.constants.insert(constant.clone(), Arc::from(name));
            new_constants.push(self.constant_mapping(&constant));
        }
        if !new_relations.is_empty() || !new_constants.is_empty() {
            self.revision = NameEnvRevision(
                self.revision
                    .0
                    .checked_add(1)
                    .expect("a task cannot exhaust the NameEnv revision space"),
            );
            Arc::make_mut(&mut self.deltas).push(Arc::new(NameEnvDelta {
                base_revision,
                revision: self.revision,
                relations: new_relations.into(),
                constants: new_constants.into(),
            }));
        }
        Ok(self.revision)
    }

    pub(crate) fn sync_through(&self, revision: NameEnvRevision) -> Option<NameEnvSync> {
        if revision > self.revision {
            return None;
        }
        // Every returned snapshot initially targets the current revision.
        // Retaining an older-prefix case keeps the API honest for tests and
        // future callers without copying the common current snapshot.
        let deltas = if revision == self.revision {
            Arc::clone(&self.deltas)
        } else {
            Arc::new(
                self.deltas
                    .iter()
                    .take_while(|delta| delta.revision <= revision)
                    .cloned()
                    .collect(),
            )
        };
        Some(NameEnvSync {
            target_revision: revision,
            deltas,
        })
    }

    pub fn mappings_for(
        &self,
        relations: impl IntoIterator<Item = RelationKey>,
        constants: impl IntoIterator<Item = ConstantKey>,
    ) -> Vec<NameMapping> {
        let mut mappings = Vec::new();
        for relation in relations {
            if let Some(name) = self.relations.get(&relation) {
                mappings.push(NameMapping {
                    kind: NameMappingKind::Relation,
                    key: relation.as_str().to_string(),
                    tptp_name: name.to_string(),
                });
            }
        }
        for constant in constants {
            if let Some(name) = self.constants.get(&constant) {
                mappings.push(NameMapping {
                    kind: NameMappingKind::Constant,
                    key: constant.as_str().to_string(),
                    tptp_name: name.to_string(),
                });
            }
        }
        mappings.sort_by(|left, right| {
            (left.kind as u8, &left.key).cmp(&(right.kind as u8, &right.key))
        });
        mappings.dedup();
        mappings
    }

    pub fn all_mappings(&self) -> Vec<NameMapping> {
        self.mappings_for(
            self.relations.keys().cloned(),
            self.constants.keys().cloned(),
        )
    }

    pub fn agrees_with(&self, mappings: &[NameMapping]) -> bool {
        mappings.iter().all(|mapping| match mapping.kind {
            NameMappingKind::Relation => self
                .relations
                .iter()
                .find(|(key, _)| key.as_str() == mapping.key)
                .is_some_and(|(_, name)| name.as_ref() == mapping.tptp_name),
            NameMappingKind::Constant => self
                .constants
                .iter()
                .find(|(key, _)| key.as_str() == mapping.key)
                .is_some_and(|(_, name)| name.as_ref() == mapping.tptp_name),
        })
    }

    fn relation_mapping(&self, key: &RelationKey) -> NameMapping {
        NameMapping {
            kind: NameMappingKind::Relation,
            key: key.as_str().to_string(),
            tptp_name: self
                .relations
                .get(key)
                .expect("a newly inserted relation has a name")
                .to_string(),
        }
    }

    fn constant_mapping(&self, key: &ConstantKey) -> NameMapping {
        NameMapping {
            kind: NameMappingKind::Constant,
            key: key.as_str().to_string(),
            tptp_name: self
                .constants
                .get(key)
                .expect("a newly inserted constant has a name")
                .to_string(),
        }
    }
}

impl fmt::Display for NameEnvRevision {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

#[cfg(test)]
pub(crate) fn sample_task_for_encoding_tests() -> SynthesisTask {
    SynthesisTask::from_json(
            r#"{
              "format_version":3,"semantic_version":1,"encoding_version":1,
              "identity":{"canonical_id":"EncodingNames","module":"Whiel.Test.EncodingNames","namespace":"Whiel.Test.EncodingNames","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"},
              "schema":{"expression":"Whiel.Test.EncodingNames.programSchema","display":"schema"},
              "original":{"pre":{"expression":"Whiel.Test.EncodingNames.inputPre","display":"true"},"command":{"expression":"Whiel.Test.EncodingNames.inputCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.EncodingNames.inputPost","display":"true"}},
              "preprocessed":{"pre":{"expression":"Whiel.Test.EncodingNames.inputPreproc.loopPre","display":"true"},"command":{"expression":"Whiel.Test.EncodingNames.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.EncodingNames.inputPreproc.loopPost","display":"true"}},
              "preprocessing_evidence":{"expression":"Whiel.Test.EncodingNames.inputPreproc"},
              "solver":{"schema_relations":[{"key":"rel:R:0","arity":1},{"key":"rel:S:0","arity":1}],"task_constants":[],
                "preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.EncodingNames.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.EncodingNames.inputPreproc.loopPre_noBound","constants":[],"relations":["rel:R:0"]},
                "preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.EncodingNames.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.EncodingNames.inputPreproc.loopPost_noBound","constants":[],"relations":["rel:S:0"]},
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":["rel:R:0"]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":["rel:R:0"]}}
            }"#,
        )
        .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extension_is_append_only_and_replayable_by_revision() {
        let task = super::sample_task_for_encoding_tests();
        let first = task.solver_relations()[0].key().clone();
        let second = task.solver_relations()[1].key().clone();
        let mut environment = TaskNameEnv {
            relations: BTreeMap::new(),
            constants: BTreeMap::new(),
            revision: NameEnvRevision::INITIAL,
            deltas: Arc::new(Vec::new()),
        };

        assert_eq!(
            environment.extend([first.clone()], []).unwrap(),
            NameEnvRevision::from_raw(1)
        );
        let first_name = environment.mappings_for([first.clone()], [])[0]
            .tptp_name
            .clone();
        assert_eq!(
            environment.extend([second], []).unwrap(),
            NameEnvRevision::from_raw(2)
        );
        assert_eq!(
            environment.mappings_for([first], [])[0].tptp_name,
            first_name
        );

        let sync = environment
            .sync_through(NameEnvRevision::from_raw(2))
            .unwrap();
        assert_eq!(sync.deltas.len(), 2);
        assert_eq!(sync.deltas[0].base_revision, NameEnvRevision::INITIAL);
        assert_eq!(sync.deltas[0].revision, NameEnvRevision::from_raw(1));
        assert_eq!(sync.deltas[1].base_revision, NameEnvRevision::from_raw(1));
        assert_eq!(sync.deltas[1].revision, NameEnvRevision::from_raw(2));
    }

    /// Two keys the old sanitizing pass folded together are now named apart
    /// by the escape itself, so nothing is suffixed to keep them distinct.
    #[test]
    fn keys_the_old_sanitizer_folded_are_named_apart_without_a_suffix() {
        let task = super::sample_task_for_encoding_tests();
        let mut environment = TaskNameEnv::from_task(&task).unwrap();
        let first = ConstantKey::from_canonical("str:a-b").unwrap();
        let second = ConstantKey::from_canonical("str:a_b").unwrap();

        environment.extend([], [first.clone()]).unwrap();
        let first_name = environment.mappings_for([], [first.clone()])[0]
            .tptp_name
            .clone();
        environment.extend([], [second.clone()]).unwrap();
        let mappings = environment.mappings_for([], [first, second]);

        assert_eq!(mappings[0].tptp_name, first_name);
        assert_eq!(mappings[0].tptp_name, "ksa_00002db");
        assert_eq!(mappings[1].tptp_name, "ksa_00005fb");
    }

    /// A fixed-ambient scope key Lean never emits is refused, not renamed.
    #[test]
    fn an_unnameable_relation_key_refuses_the_whole_extension() {
        let task = super::sample_task_for_encoding_tests();
        let mut environment = TaskNameEnv::from_task(&task).unwrap();
        let malformed = RelationKey::from_lean_scope("not a relation key").unwrap();

        let failure = environment
            .extend([malformed], [])
            .expect_err("an unnameable key is refused");
        assert_eq!(failure.key(), "not a relation key");
    }

    #[test]
    fn initial_task_mapping_is_revision_one_not_implicit_revision_zero() {
        let environment = TaskNameEnv::from_task(&super::sample_task_for_encoding_tests()).unwrap();
        assert_eq!(environment.revision(), NameEnvRevision::from_raw(1));
        let sync = environment.sync_through(environment.revision()).unwrap();
        assert_eq!(sync.deltas.len(), 1);
        assert_eq!(sync.deltas[0].relations.len(), 2);
    }
}

//! Canonical fixed-ambient finite interpretations decoded from Vampire.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde_json::{Value, json};

use crate::encoding::{NameMappingKind, TaskNameEnv};
use crate::entailment::{DecodedFiniteModel, ModelDecodeError, decode_vampire_model_for_relations};
use crate::task::{ConstantKey, RelationKey};

use super::FixedAmbientTaskScope;

/// One canonical complete Gamma-plus relation table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameworkIIRelationTable {
    name: RelationKey,
    arity: u64,
    rows: Arc<[Vec<String>]>,
}

impl FrameworkIIRelationTable {
    pub fn name(&self) -> &RelationKey {
        &self.name
    }

    pub fn arity(&self) -> u64 {
        self.arity
    }

    pub fn rows(&self) -> &[Vec<String>] {
        &self.rows
    }
}

/// One nonempty, canonical finite interpretation ready for Lean validation.
#[derive(Clone, Debug)]
pub struct FrameworkIIFiniteInterpretation {
    scope: FixedAmbientTaskScope,
    carrier_keys: Arc<[String]>,
    relations: Arc<[FrameworkIIRelationTable]>,
    constant_values: BTreeMap<ConstantKey, String>,
    value: Arc<Value>,
}

impl FrameworkIIFiniteInterpretation {
    pub fn scope(&self) -> &FixedAmbientTaskScope {
        &self.scope
    }

    pub fn carrier_keys(&self) -> &[String] {
        &self.carrier_keys
    }

    pub fn relations(&self) -> &[FrameworkIIRelationTable] {
        &self.relations
    }

    /// Return every constant interpretation carried by Vampire's model.
    pub fn constant_values(&self) -> &BTreeMap<ConstantKey, String> {
        &self.constant_values
    }

    /// Return the exact input shape accepted by Lean's refutation validator.
    pub fn as_json(&self) -> &Value {
        &self.value
    }
}

/// Decode and canonically relabel one complete Gamma-plus Vampire model.
///
/// `required_constants` must be the exact constants of the obligation being
/// refuted, rather than every constant ever appended to the task NameEnv.
/// `query` is the exact problem text the solver was handed, when the caller
/// still has it. It is what decides whether a relation the model omits was
/// unconstrained by the problem — and so may be interpreted by the empty
/// table — or was omitted despite occurring, which stays an error.
pub fn decode_framework_ii_vampire_model(
    scope: &FixedAmbientTaskScope,
    names: &TaskNameEnv,
    required_constants: &[ConstantKey],
    stdout: &str,
    query: Option<&str>,
) -> Result<FrameworkIIFiniteInterpretation, ModelDecodeError> {
    let relation_arities = scope
        .relations()
        .iter()
        .map(|relation| (relation.key().clone(), relation.arity()))
        .collect::<Vec<_>>();
    let decoded = decode_vampire_model_for_relations(
        names,
        &relation_arities,
        required_constants,
        stdout,
        query,
    )?;
    canonical_interpretation(scope, names, decoded)
}

fn canonical_interpretation(
    scope: &FixedAmbientTaskScope,
    names: &TaskNameEnv,
    decoded: DecodedFiniteModel,
) -> Result<FrameworkIIFiniteInterpretation, ModelDecodeError> {
    let mut occupied = names
        .all_mappings()
        .into_iter()
        .filter(|mapping| mapping.kind == NameMappingKind::Constant)
        .map(|mapping| mapping.key)
        .collect::<BTreeSet<_>>();
    let element_constants = decoded
        .constant_values
        .iter()
        .map(|(constant, element)| (element.clone(), constant.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut element_keys = BTreeMap::new();
    let mut fresh_index = 0_u64;
    for element in &decoded.carrier {
        let key = if let Some(constant) = element_constants.get(element) {
            constant.as_str().to_string()
        } else {
            let mut key = format!("str:__whiel_fmb_fresh_{fresh_index}");
            fresh_index = fresh_index.checked_add(1).ok_or_else(|| {
                ModelDecodeError::Domain("finite carrier index overflows u64".to_string())
            })?;
            while occupied.contains(&key) {
                key.push('_');
            }
            key
        };
        if !occupied.insert(key.clone()) && !element_constants.contains_key(element) {
            return Err(ModelDecodeError::Domain(format!(
                "canonical carrier key collision for {element:?}"
            )));
        }
        if element_keys.insert(element.clone(), key).is_some() {
            return Err(ModelDecodeError::Domain(format!(
                "duplicate finite carrier element {element:?}"
            )));
        }
    }

    let carrier_keys = element_keys
        .values()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if carrier_keys.len() != decoded.carrier.len() {
        return Err(ModelDecodeError::Domain(
            "finite carrier does not have an injective canonical relabeling".to_string(),
        ));
    }

    let mut relations = Vec::with_capacity(decoded.relations.len());
    for (name, relation) in decoded.relations {
        let rows = relation
            .true_tuples
            .into_iter()
            .map(|tuple| {
                tuple
                    .into_iter()
                    .map(|element| {
                        element_keys.get(&element).cloned().ok_or_else(|| {
                            ModelDecodeError::Relation {
                                relation: name.as_str().to_string(),
                                detail: format!(
                                    "tuple element {element:?} has no canonical carrier key"
                                ),
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<BTreeSet<_>, _>>()?
            .into_iter()
            .collect::<Vec<_>>();
        relations.push(FrameworkIIRelationTable {
            name,
            arity: relation.arity,
            rows: rows.into(),
        });
    }
    relations.sort_by(|left, right| left.name.cmp(&right.name));

    let constant_values = decoded
        .constant_values
        .into_iter()
        .map(|(constant, element)| {
            element_keys
                .get(&element)
                .cloned()
                .map(|value| (constant, value))
                .ok_or_else(|| {
                    ModelDecodeError::Constant(format!(
                        "constant denotation {element:?} has no canonical carrier key"
                    ))
                })
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let value = json!({
        "carrier_keys": carrier_keys,
        "relations": relations
            .iter()
            .map(|relation| json!({
                "name": relation.name.as_str(),
                "rows": relation.rows.as_ref(),
            }))
            .collect::<Vec<_>>(),
    });
    Ok(FrameworkIIFiniteInterpretation {
        scope: scope.clone(),
        carrier_keys: carrier_keys.into(),
        relations: relations.into(),
        constant_values,
        value: Arc::new(value),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoding::TaskNameEnv;
    use crate::entailment::{InstanceValue, decode_vampire_model};
    use crate::task::SynthesisTask;

    fn task() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version":3,
              "semantic_version":1,
              "encoding_version":1,
              "identity":{
                "canonical_id":"FrameworkIIModelTest",
                "module":"Whiel.Test.FrameworkIIModelTest",
                "namespace":"Whiel.Test.FrameworkIIModelTest",
                "source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
              },
              "schema":{"expression":"Whiel.Test.FrameworkIIModelTest.programSchema","display":"{R}"},
              "original":{
                "pre":{"expression":"Whiel.Test.FrameworkIIModelTest.inputPre","display":"true"},
                "command":{"expression":"Whiel.Test.FrameworkIIModelTest.inputCmd","display":"SKIP"},
                "post":{"expression":"Whiel.Test.FrameworkIIModelTest.inputPost","display":"true"}
              },
              "preprocessed":{
                "pre":{"expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc.loopPre","display":"true"},
                "command":{"expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc.loopCmd","display":"SKIP"},
                "post":{"expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc.loopPost","display":"true"}
              },
              "preprocessing_evidence":{"expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc"},
              "solver":{
                "schema_relations":[{"key":"rel:R:0","arity":1}],
                "task_constants":[],
                "preprocessed_pre":{
                  "source_id":"task.preprocessed_pre","expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc.loopPre",
                  "no_bound_expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc.loopPre_noBound",
                  "constants":[],"relations":[]
                },
                "preprocessed_post":{
                  "source_id":"task.preprocessed_post","expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc.loopPost",
                  "no_bound_expression":"Whiel.Test.FrameworkIIModelTest.inputPreproc.loopPost_noBound",
                  "constants":[],"relations":[]
                },
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}
              }
            }"#,
        )
        .unwrap()
    }

    fn setup() -> (
        SynthesisTask,
        FixedAmbientTaskScope,
        TaskNameEnv,
        RelationKey,
        ConstantKey,
    ) {
        let task = task();
        let source = task.solver_relations()[0].key().clone();
        let prophecy = RelationKey::from_canonical("rel:P:0").unwrap();
        let constant = ConstantKey::from_canonical("str:task").unwrap();
        let mut names = TaskNameEnv::from_task(&task).unwrap();
        names
            .extend([prophecy.clone()], [constant.clone()])
            .unwrap();
        let source_relation = super::super::types::FrameworkIIRelation::new(source.clone(), 1);
        let prophecy_relation = super::super::types::FrameworkIIRelation::new(prophecy.clone(), 1);
        let binding =
            super::super::types::FrameworkIIProphecyBinding::new(source.clone(), prophecy, 1);
        let scope = FixedAmbientTaskScope::new(
            task.identity().clone(),
            json!(["framework-ii-model-test"]),
            json!([]),
            vec![source_relation.clone()],
            vec![prophecy_relation, source_relation],
            vec![binding],
        );
        (task, scope, names, source, constant)
    }

    fn solver_name(names: &TaskNameEnv, kind: NameMappingKind, key: &str) -> String {
        names
            .all_mappings()
            .into_iter()
            .find(|mapping| mapping.kind == kind && mapping.key == key)
            .unwrap()
            .tptp_name
    }

    fn model(names: &TaskNameEnv) -> String {
        let source = solver_name(names, NameMappingKind::Relation, "rel:R:0");
        let prophecy = solver_name(names, NameMappingKind::Relation, "rel:P:0");
        let constant = solver_name(names, NameMappingKind::Constant, "str:task");
        format!(
            "% SZS status CounterSatisfiable for f2\n\
             % SZS output start FiniteModel for f2\n\
             tff(d1_type, type, fmb_$i_1: $i).\n\
             tff(d2_type, type, fmb_$i_2: $i).\n\
             tff(d3_type, type, fmb_$i_3: $i).\n\
             tff(source_type, type, {source}: $i > $o).\n\
             tff(prophecy_type, type, {prophecy}: $i > $o).\n\
             tff(constant_type, type, {constant}: $i).\n\
             tff(finite_domain_$i, axiom, ! [X:$i] : \
               (X = fmb_$i_1 | X = fmb_$i_2 | X = fmb_$i_3)).\n\
             tff(constant_value, axiom, {constant} = fmb_$i_2).\n\
             tff(source_value, axiom, \
               (~{source}(fmb_$i_1) & {source}(fmb_$i_2) & ~{source}(fmb_$i_3))).\n\
             tff(prophecy_value, axiom, \
               ({prophecy}(fmb_$i_1) & ~{prophecy}(fmb_$i_2) & {prophecy}(fmb_$i_3))).\n\
             % SZS output end FiniteModel for f2\n"
        )
    }

    #[test]
    fn decodes_prophecies_constants_and_the_complete_carrier_canonically() {
        let (_task, scope, names, _source, constant) = setup();
        let interpretation = decode_framework_ii_vampire_model(
            &scope,
            &names,
            std::slice::from_ref(&constant),
            &model(&names),
            None,
        )
        .unwrap();

        assert_eq!(
            interpretation.carrier_keys(),
            [
                "str:__whiel_fmb_fresh_0",
                "str:__whiel_fmb_fresh_1",
                "str:task"
            ]
        );
        assert_eq!(interpretation.constant_values()[&constant], "str:task");
        assert_eq!(
            interpretation.as_json(),
            &json!({
                "carrier_keys":[
                    "str:__whiel_fmb_fresh_0",
                    "str:__whiel_fmb_fresh_1",
                    "str:task"
                ],
                "relations":[
                    {"name":"rel:P:0","rows":[
                        ["str:__whiel_fmb_fresh_0"],
                        ["str:__whiel_fmb_fresh_1"]
                    ]},
                    {"name":"rel:R:0","rows":[["str:task"]]}
                ]
            })
        );
    }

    #[test]
    fn exact_schema_and_required_constant_checks_fail_closed() {
        let (task, scope, names, source, constant) = setup();
        let source_only = super::super::types::FrameworkIIRelation::new(source.clone(), 1);
        let incomplete_scope = FixedAmbientTaskScope::new(
            task.identity().clone(),
            json!(["source-only"]),
            json!([]),
            vec![source_only.clone()],
            vec![source_only],
            Vec::new(),
        );
        assert!(matches!(
            decode_framework_ii_vampire_model(
                &incomplete_scope,
                &names,
                std::slice::from_ref(&constant),
                &model(&names),
                None
            ),
            Err(ModelDecodeError::NameEnvironment(_))
        ));

        let duplicate = super::super::types::FrameworkIIRelation::new(source, 1);
        let duplicate_scope = FixedAmbientTaskScope::new(
            task.identity().clone(),
            json!(["duplicate"]),
            json!([]),
            vec![duplicate.clone()],
            vec![duplicate.clone(), duplicate],
            Vec::new(),
        );
        assert!(matches!(
            decode_framework_ii_vampire_model(
                &duplicate_scope,
                &names,
                std::slice::from_ref(&constant),
                &model(&names),
                None
            ),
            Err(ModelDecodeError::NameEnvironment(_))
        ));

        let without_prophecy = model(&names)
            .lines()
            .filter(|line| !line.contains("prophecy_value"))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(matches!(
            decode_framework_ii_vampire_model(
                &scope,
                &names,
                std::slice::from_ref(&constant),
                &without_prophecy,
                None
            ),
            Err(ModelDecodeError::Relation { .. })
        ));

        let without_constant = model(&names)
            .lines()
            .filter(|line| !line.contains("constant_type") && !line.contains("constant_value"))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(matches!(
            decode_framework_ii_vampire_model(
                &scope,
                &names,
                std::slice::from_ref(&constant),
                &without_constant,
                None
            ),
            Err(ModelDecodeError::Constant(_))
        ));
    }

    #[test]
    fn fresh_carrier_keys_avoid_every_append_only_name_env_constant() {
        let (_task, scope, mut names, _source, constant) = setup();
        let reserved = ConstantKey::from_canonical("str:__whiel_fmb_fresh_0").unwrap();
        names.extend([], [reserved]).unwrap();
        let interpretation = decode_framework_ii_vampire_model(
            &scope,
            &names,
            std::slice::from_ref(&constant),
            &model(&names),
            None,
        )
        .unwrap();
        assert_eq!(
            interpretation.carrier_keys(),
            [
                "str:__whiel_fmb_fresh_0_",
                "str:__whiel_fmb_fresh_1",
                "str:task"
            ]
        );
    }

    #[test]
    fn legacy_source_decoder_ignores_added_prophecy_symbols() {
        let (task, _scope, extended_names, source, _constant) = setup();
        let base_names = TaskNameEnv::from_task(&task).unwrap();
        let prophecy = RelationKey::from_canonical("rel:P:0").unwrap();
        let source_name = solver_name(&base_names, NameMappingKind::Relation, source.as_str());
        let prophecy_name = solver_name(
            &extended_names,
            NameMappingKind::Relation,
            prophecy.as_str(),
        );
        let stdout = format!(
            "% SZS status CounterSatisfiable for legacy\n\
             % SZS output start FiniteModel for legacy\n\
             tff(d1_type, type, fmb_$i_1: $i).\n\
             tff(source_type, type, {source_name}: $i > $o).\n\
             tff(prophecy_type, type, {prophecy_name}: $i > $o).\n\
             tff(finite_domain_$i, axiom, ! [X:$i] : (X = fmb_$i_1)).\n\
             tff(source_value, axiom, {source_name}(fmb_$i_1)).\n\
             tff(prophecy_value, axiom, {prophecy_name}(fmb_$i_1)).\n\
             % SZS output end FiniteModel for legacy\n"
        );
        let decoded = decode_vampire_model(&task, &extended_names, &stdout).unwrap();
        assert_eq!(
            decoded.relation(&source).unwrap().true_tuples(),
            &BTreeSet::from([vec![InstanceValue::Fresh(0)]])
        );
    }
}

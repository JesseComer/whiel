//! Pinned, strict wire inventory for replay comparison.
//!
//! These data types confer no controller or artifact authority. In particular,
//! physical attempt references and ledger row ordinals have distinct types.
//! A schema match alone is not checked old/live identity correspondence.
//! Tagged variants with no payload use empty struct variants: Serde ignores
//! unknown object fields on tagged unit variants even with deny_unknown_fields.

use super::strict_json::decode_strict_json;
use serde::{Deserialize, Serialize};
#[cfg(test)]
use serde_json::Value;

fn nullable<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplayDivergence {
    pub path: String,
    pub reason: String,
}

pub fn decode_wire<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, ReplayDivergence> {
    let value = decode_strict_json(bytes, None).map_err(|error| ReplayDivergence {
        path: "$".into(),
        reason: error.to_string(),
    })?;
    serde_json::from_value(value).map_err(|error| ReplayDivergence {
        path: "$".into(),
        reason: error.to_string(),
    })
}

pub use crate::proposer_api::observation::*;

pub use crate::proposer_api::proposals::*;

pub use crate::proposer_api::query_results::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecordedPresentationV1 {
    pub coordinates: super::transcript::TranscriptCoordinates,
    #[serde(deserialize_with = "decimal_nanos")]
    pub remaining_search_budget_ns: String,
    pub ledger_timings: Vec<RecordedRowTimingV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecordedRowTimingV1 {
    pub row_ordinal: LedgerRowOrdinal,
    #[serde(deserialize_with = "nullable")]
    pub solver_time_nanos: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub preparation_time_nanos: Option<u64>,
}

fn decimal_nanos<'de, D: serde::Deserializer<'de>>(deserializer: D) -> Result<String, D::Error> {
    let value = String::deserialize(deserializer)?;
    match value.parse::<u128>() {
        Ok(nanos) if nanos.to_string() == value => Ok(value),
        _ => Err(serde::de::Error::custom(
            "nanoseconds must be a canonical unsigned decimal string",
        )),
    }
}

pub fn decode_tool_arguments(
    tool: &str,
    bytes: &[u8],
) -> Result<ToolArgumentsV1, ReplayDivergence> {
    match tool {
        "countermodel" => decode_wire(bytes).map(ToolArgumentsV1::Countermodel),
        "strongest_refutations" => decode_wire(bytes).map(ToolArgumentsV1::StrongestRefutations),
        "history" => decode_wire(bytes).map(ToolArgumentsV1::History),
        "ledger" => decode_wire(bytes).map(ToolArgumentsV1::Ledger),
        "validate_clauses" => decode_wire(bytes).map(ToolArgumentsV1::ValidateClauses),
        "evaluate_clauses" => decode_wire(bytes).map(ToolArgumentsV1::EvaluateClauses),
        _ => Err(ReplayDivergence {
            path: "$.tool".into(),
            reason: "unknown tool arguments schema".into(),
        }),
    }
}

pub fn decode_tool_response(bytes: &[u8]) -> Result<ToolResponseV1, ReplayDivergence> {
    decode_wire(bytes)
}

fn require_version(actual: u64, expected: u64, path: &str) -> Result<(), ReplayDivergence> {
    if actual == expected {
        Ok(())
    } else {
        Err(ReplayDivergence {
            path: path.into(),
            reason: format!("unsupported wire version {actual}; expected {expected}"),
        })
    }
}

pub fn decode_push(bytes: &[u8]) -> Result<PushV1, ReplayDivergence> {
    let push: PushV1 = decode_wire(bytes)?;
    require_version(
        push.schema_version,
        super::agent::AGENT_HOUDINI_PROTOCOL_VERSION,
        "$.schema_version",
    )?;
    require_version(
        push.feedback.schema_version,
        super::feedback::AGENT_FEEDBACK_SCHEMA_VERSION,
        "$.feedback.schema_version",
    )?;
    require_version(
        push.feedback.presentation.schema_version,
        super::feedback::AGENT_PRESENTATION_SCHEMA_VERSION,
        "$.feedback.presentation.schema_version",
    )?;
    if let Some(correction) = &push.correction {
        require_version(
            correction.schema_version,
            super::agent::AGENT_HOUDINI_PROTOCOL_VERSION,
            "$.correction.schema_version",
        )?;
    }
    Ok(push)
}

pub fn decode_response(bytes: &[u8]) -> Result<ResponseV1, ReplayDivergence> {
    // Replay reads the recorded bytes of a submission the verifier already
    // judged, so it has to reach the same response the envelope did. The
    // envelope drops an empty `clauses`/`dropped` beside a counterexample
    // before the strict grammar sees it and refuses a non-empty one
    // (`agent::reconcile_counterexample_clause_members`); reading them here
    // any other way would leave an admitted response unparsed and rebind
    // nothing in it.
    let mut value = decode_strict_json(bytes, None).map_err(|error| ReplayDivergence {
        path: "$".into(),
        reason: error.to_string(),
    })?;
    if super::agent::reconcile_counterexample_clause_members(&mut value).is_some() {
        return Err(ReplayDivergence {
            path: "$".into(),
            reason: "counterexample response carries clause content".into(),
        });
    }
    let response: ResponseV1 = serde_json::from_value(value).map_err(|error| ReplayDivergence {
        path: "$".into(),
        reason: error.to_string(),
    })?;
    let schema_version = match &response {
        ResponseV1::CandidateClauses { schema_version, .. }
        | ResponseV1::CandidateCounterexample { schema_version, .. } => *schema_version,
    };
    require_version(
        schema_version,
        super::agent::AGENT_HOUDINI_PROTOCOL_VERSION,
        "$.schema_version",
    )?;
    Ok(response)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn clause() -> Value {
        json!({"clause_id": 1, "record_digest": "record", "formula_digest": "formula",
            "canonical_source": "(op_zR = op_zR)", "display": null})
    }

    fn clause_reference() -> Value {
        json!({"clause_id": 1, "record_digest": "record", "formula_digest": "formula"})
    }

    fn drop_reference() -> Value {
        json!({"clause": clause_reference(), "consultation_digest": "consultation", "authorization_digest": "authorization"})
    }

    fn status_variants() -> Vec<Value> {
        vec![
            json!({"kind": "committed", "level": 1}),
            json!({"kind": "pending", "level": 2}),
            json!({"kind": "dead", "cause": "dropped"}),
            json!({"kind": "dead", "cause": "refuted", "reason": {
                "kind": "prophecy_free_initialization_refuted", "attempt": 4,
            }}),
        ]
    }

    fn artifact() -> Value {
        json!({"stable_id": "artifact", "role": "proof", "kind": "proof"})
    }

    fn failure() -> Value {
        json!({"origin": "vampire_proof_search", "kind": "check_timeout", "retryable": true,
            "scope": "lane_local", "has_withheld_detail": true,
            "artifacts": [artifact()], "withheld_artifacts": 1})
    }

    fn routes() -> Vec<Value> {
        vec![
            json!({"kind": "runtime_proof", "profile": "direct", "receipt_digest": "receipt",
                "semantic_vc_digest": "vc", "artifacts": [artifact()]}),
            json!({"kind": "runtime_proof", "profile": "casc_2025", "receipt_digest": "receipt",
                "semantic_vc_digest": "vc", "artifacts": [artifact()]}),
            json!({"kind": "protected_theorem", "target_vc_digest": "vc", "theorem_name": "theorem",
                "artifact": artifact()}),
            json!({"kind": "validated_refutation", "refutation_digest": "refutation",
                "semantic_vc_digest": "vc", "artifacts": [artifact()]}),
            json!({"kind": "retry_progress", "progress_digest": "progress", "semantic_vc_digest": "vc",
                "next_fmb_start_size": null, "previous_proof_allowance_ns": "100", "current_proof_allowance_ns": "200",
                "peer_failure": null, "artifacts": [artifact()]}),
            json!({"kind": "retry_progress", "progress_digest": "progress", "semantic_vc_digest": "vc",
                "next_fmb_start_size": 3, "previous_proof_allowance_ns": "100", "current_proof_allowance_ns": "200",
                "peer_failure": failure(), "artifacts": [artifact()]}),
            json!({"kind": "suspended"}),
        ]
    }

    fn attempt(route: Value) -> Value {
        json!({"kind": "attempt", "row_ordinal": 4, "clause": clause(), "level": 1,
            "role": "maintenance", "request_digest": "request", "partition_digest": "partition",
            "invalidated": false, "result": {"outcome": {"kind": "proved"},
                "route_kind": route["kind"], "route_digest": "route", "route": route,
                "route_summarized": false, "attempt_id": 99},
            "solver_time_nanos": null, "preparation_time_nanos": 100,
            "previous_row_digest": null, "row_digest": "row"})
    }

    fn invalidation() -> Value {
        json!({"kind": "invalidation", "row_ordinal": 5, "invalidated_attempt": 4,
            "target": clause(), "cause": clause(), "reason": "antecedent_clause_deleted",
            "previous_row_digest": "previous", "row_digest": "row"})
    }

    fn model() -> Value {
        json!({"relations": [{"key": "r", "rows": [["a", "b"], ["a", "b"]]}]})
    }

    fn not_retained() -> Value {
        json!({"tuple_count": 0, "limit": "countermodel_retention_tuples", "value": null})
    }

    fn binding() -> Value {
        json!({"task_digest": "task", "scope_digest": "scope", "run_digest": "run",
            "consultation_digest": "consultation", "state_snapshot_digest": "state", "validation_manifest_digest": "manifest"})
    }

    fn correction() -> Value {
        json!({"schema_version": 4,
        "binding": {"consultation_digest": "consultation", "rejected_response_digest": "response", "correction_ordinal": 0},
        "diagnostics": [
            {"code": "wrong", "message": "message", "item_index": null, "path": null},
            {"code": "host_limit", "message": "limit", "item_index": 1, "path": "$.clauses",
                "host_limit": {"limit": "proposal_size", "value": 1, "observed": 2}}
        ]})
    }

    fn push() -> Value {
        let mut push_binding = binding();
        push_binding["validation_ordinal"] = json!(0);
        push_binding["policy_digest"] = json!("policy");
        let triple = json!({"precondition": "pre", "command": "cmd", "postcondition": "post"});
        json!({"schema_version": 4, "operation": "proposer_observation", "binding": push_binding,
            "feedback": {"schema_version": 10, "binding": binding(), "iteration": 0, "remaining_search_budget_ns": "600000000000",
                "presentation": {"schema_version": 16,
                    "task": {"canonical_id": "Example0001", "task_digest": "task", "semantic_version": 1,
                        "encoding_version": 1, "schema": "schema", "original": triple, "preprocessed": triple},
                    "ambient_schema": {"scope_digest": "scope", "relations": [{"key": "r", "arity": 2}],
                        "prophecy_map": [{"program_relation": "r", "prophecy_relation": "p", "arity": 2}]},
                    "host_limits": [{"limit": "pushed_core", "value": 1}],
                    "resource_limits": {"api_packet_bytes": 67108864, "configured": null},
                    "presentation_digest": "presentation"},
                "core": [{"clause": clause(), "source": "edb_precondition_system", "level": 0}],
                "last_round": status_variants().into_iter().map(|status| json!({"clause": clause(), "source": "submitted", "outcome": status})).collect::<Vec<_>>(),
                "pending": [{"clause": clause(), "source": "symbolic", "minimum_level": 0, "current_level": 1,
                    "drop_reference": drop_reference()}, {"clause": clause(), "source": "submitted", "minimum_level": 1,
                    "current_level": 1, "drop_reference": null}],
                "latest": {"kind": "initial"}, "tools": ["countermodel", "strongest_refutations", "history", "ledger", "validate_clauses", "evaluate_clauses"],
                "state_revision": 0, "truncated": {"list": "core", "shown": 1, "total": 2, "limit": "pushed_core"}},
            "correction": correction()})
    }

    fn latest_variants() -> Vec<Value> {
        vec![
            json!({"kind": "initial"}),
            json!({"kind": "postcondition_open", "postcondition_open": {"outcome": "refuted", "attempt": null}}),
            json!({"kind": "postcondition_open", "postcondition_open": {"outcome": "refuted", "attempt": 99}}),
            json!({"kind": "postcondition_open", "postcondition_open": {"outcome": "inconclusive", "reason": "timed_out"}}),
            json!({"kind": "failure", "failure": failure()}),
            json!({"kind": "counterexample_rejected", "counterexample_rejected": {"code": "future_worker_code", "reason": "exact reason"}}),
        ]
    }

    fn successful(tool: &str, result: Value) -> Value {
        json!({"tool": tool, "state_revision": 0, "result": result})
    }

    fn tool_responses() -> Vec<Value> {
        let mut results = Vec::new();
        for (field, payload) in [("model", model()), ("found_not_retained", not_retained())] {
            let mut clause_model =
                json!({"attempt": 99, "clause": clause(), "level": 1, "role": "maintenance"});
            clause_model[field] = payload.clone();
            results.push(successful("countermodel", clause_model));
            let mut termination_model = json!({"attempt": 100, "role": "termination"});
            termination_model[field] = payload.clone();
            results.push(successful("countermodel", termination_model));
            for role in ["initialization", "maintenance", "unknown"] {
                let mut summary =
                    json!({"attempt": 99, "level": 0, "role": role, "premise_count": 3});
                summary[field] = payload.clone();
                results.push(successful("strongest_refutations", json!({"clause": clause(), "refutations": [summary],
                    "truncated": {"list": "refutations", "shown": 1, "total": 2, "limit": "strongest_refutations"}})));
            }
        }
        for route in routes() {
            results.push(successful("ledger", json!({"metadata": {"total_items": 2, "first_index": 0,
                "returned_items": 2, "continuation": null}, "items": [attempt(route), invalidation()]})));
        }
        for status in status_variants() {
            results.push(successful(
                "history",
                json!({"clause": clause(), "origin": "submitted", "protected": false, "status": status, "minimum_level": 0,
                "current_level": null, "attempts": [attempt(routes().remove(0))]}),
            ));
        }
        results.push(successful("evaluate_clauses", json!({"results": [
            {"source": "formula", "admitted": true, "holds": [true, false]},
            {"source": "malformed", "admitted": false, "correctable": {"code": "bad", "message": "message",
                "item_index": null, "path": null, "offset": null}}], "instances": [{"kind":"retained","attempt":99,"source_index":0}, {"kind":"supplied","source_index":1}], "cost": 4,
            "skipped": [{"kind":"retained","source_index":2,"attempt": 100, "tuple_count": 0,"reason":"carrier_unavailable"}]})));
        results.push(successful(
            "validate_clauses",
            json!({"results":[{"source":"formula","admitted":true}]}),
        ));
        results.push(successful("history", json!({"clause":clause(),"origin":"edb_precondition_system","protected":true,"status":null,"minimum_level":0,"current_level":null,"attempts":[]})));
        for tool in [
            "countermodel",
            "strongest_refutations",
            "history",
            "ledger",
            "validate_clauses",
            "evaluate_clauses",
            "intentionally_unknown_tool",
        ] {
            results.push(json!({"tool": tool, "state_revision": 0, "error": {"code": "unknown_skill", "message": "exact message 99"}}));
        }
        results.push(json!({"tool": "validate_clauses", "state_revision": 0, "error": {"code": "host_limit", "message": "limit",
            "host_limit": {"limit": "evaluation_cost", "value": 1, "observed": 2}}}));
        results
    }

    fn object_paths(value: &Value, path: String, result: &mut Vec<String>) {
        match value {
            Value::Object(object) => {
                result.push(path.clone());
                for (key, child) in object {
                    object_paths(
                        child,
                        format!("{path}/{}", key.replace('~', "~0").replace('/', "~1")),
                        result,
                    );
                }
            }
            Value::Array(array) => {
                for (index, child) in array.iter().enumerate() {
                    object_paths(child, format!("{path}/{index}"), result);
                }
            }
            _ => {}
        }
    }

    fn assert_recursively_closed<T: Serialize>(
        value: &Value,
        decode: impl Fn(&[u8]) -> Result<T, ReplayDivergence>,
    ) {
        let parsed = decode(&serde_json::to_vec(value).unwrap()).unwrap();
        assert_eq!(serde_json::to_value(parsed).unwrap(), *value);
        let mut paths = Vec::new();
        object_paths(value, String::new(), &mut paths);
        for path in paths {
            let mut extended = value.clone();
            extended
                .pointer_mut(&path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .insert("future_unreviewed_field".into(), json!({"nested": [1, 2]}));
            assert!(
                decode(&serde_json::to_vec(&extended).unwrap()).is_err(),
                "unknown field accepted at {path}: {extended}"
            );
        }
    }

    #[test]
    fn push_inventory_covers_every_latest_status_and_nested_object() {
        for latest in latest_variants() {
            let mut value = push();
            value["feedback"]["latest"] = latest;
            assert_recursively_closed(&value, decode_push);
        }
        let mut configured = push();
        configured["feedback"]["presentation"]["resource_limits"]["configured"] =
            json!(super::super::resource_limits::CampaignResourceLimits::default());
        assert_recursively_closed(&configured, decode_push);
        let mut value = push();
        value["correction"] = Value::Null;
        value["feedback"]
            .as_object_mut()
            .unwrap()
            .remove("truncated");
        assert_recursively_closed(&value, decode_push);
    }

    #[test]
    fn tool_success_and_error_inventory_rejects_every_unknown_nested_field() {
        for value in tool_responses() {
            assert_recursively_closed(&value, decode_tool_response);
        }
    }

    #[test]
    fn dead_causes_and_evaluation_discriminants_match_the_actual_producers() {
        for status in status_variants() {
            assert_recursively_closed(&status, decode_wire::<StatusV1>);
        }
        for invalid in [
            json!({"kind": "dead", "cause": "dropped", "reason": null}),
            json!({"kind": "dead", "cause": "dropped", "reason": {"kind": "prophecy_free_initialization_refuted", "attempt": 4}}),
            json!({"kind": "dead", "cause": "refuted"}),
            json!({"kind": "dead", "cause": "refuted", "reason": null}),
            json!({"kind": "dead", "cause": "new_cause"}),
            json!({"source": "c", "admitted": false, "holds": []}),
            json!({"source": "c", "admitted": true, "correctable": {"code": "x", "message": "x", "item_index": null, "path": null, "offset": null}}),
        ] {
            assert!(decode_wire::<StatusV1>(&serde_json::to_vec(&invalid).unwrap()).is_err());
            assert!(decode_wire::<EvaluationV1>(&serde_json::to_vec(&invalid).unwrap()).is_err());
        }
    }

    #[test]
    fn tool_arguments_preserve_null_absent_and_ordered_duplicate_references() {
        for (tool, arguments) in [
            ("countermodel", json!({"attempt": 99})),
            ("strongest_refutations", json!({"clause": clause()})),
            ("history", json!({"clause": clause()})),
            // A reference built from the digests alone names the same clause
            // and is recorded exactly as it was sent, without the record's
            // text appearing from nowhere.
            ("history", json!({"clause": clause_reference()})),
            ("ledger", json!({})),
            ("ledger", json!({"cursor": null})),
            ("ledger", json!({"cursor": "0"})),
            ("validate_clauses", json!({"clauses": ["a", "a"]})),
            (
                "evaluate_clauses",
                json!({"clauses": [], "instances": "all_retained"}),
            ),
            (
                "evaluate_clauses",
                json!({"clauses": [], "instances": [{"kind":"retained","attempt":99},{"kind":"retained","attempt":99}]}),
            ),
            (
                "evaluate_clauses",
                json!({"clauses":[],"instances":[{"kind":"supplied","instance":{"carrier_keys":["num:0"],"relations":[]}}]}),
            ),
        ] {
            assert_recursively_closed(&arguments, |bytes| decode_tool_arguments(tool, bytes));
        }
        let absent = decode_tool_arguments("ledger", b"{}").unwrap();
        let null = decode_tool_arguments("ledger", br#"{"cursor":null}"#).unwrap();
        assert_ne!(absent, null);
        let bare = decode_tool_arguments(
            "history",
            &serde_json::to_vec(&json!({"clause": clause_reference()})).unwrap(),
        )
        .unwrap();
        let carried = decode_tool_arguments(
            "history",
            &serde_json::to_vec(&json!({"clause": clause()})).unwrap(),
        )
        .unwrap();
        assert_ne!(bare, carried);
        assert!(decode_tool_arguments("unknown", b"{}").is_err());
        assert!(decode_tool_arguments("countermodel", br#"{"attempt":"99"}"#).is_err());
    }

    #[test]
    fn provider_response_variants_use_the_response_binding_not_the_push_binding() {
        let mut response_binding = binding();
        response_binding["request_digest"] = json!("request");
        response_binding["validation_ordinal"] = json!(0);
        for value in [
            json!({"schema_version": 4, "kind": "candidate_clauses", "binding": response_binding,
                "clauses": ["formula", "formula"], "dropped": [drop_reference()]}),
            json!({"schema_version": 4, "kind": "candidate_counterexample", "binding": response_binding,
                "input": {"relations": [{"name": "r", "rows": [["a", "b"]]}]}}),
        ] {
            assert_recursively_closed(&value, decode_response);
            let mut wrong = value.clone();
            wrong["binding"]["policy_digest"] = json!("policy");
            assert!(decode_response(&serde_json::to_vec(&wrong).unwrap()).is_err());
        }
        let mut wrong = push();
        wrong["binding"]["request_digest"] = json!("request");
        assert!(decode_push(&serde_json::to_vec(&wrong).unwrap()).is_err());
    }

    /// The two members the live envelope tolerates on a counterexample are
    /// tolerated here too, and only while they are empty.
    #[test]
    fn an_empty_clause_member_beside_a_counterexample_decodes_as_the_plain_variant() {
        let mut response_binding = binding();
        response_binding["request_digest"] = json!("request");
        response_binding["validation_ordinal"] = json!(0);
        let plain = json!({"schema_version": 4, "kind": "candidate_counterexample",
            "binding": response_binding, "input": {"relations": []}});
        let expected = decode_response(&serde_json::to_vec(&plain).unwrap()).unwrap();
        for extra in [
            json!({"clauses": []}),
            json!({"dropped": []}),
            json!({"clauses": [], "dropped": []}),
        ] {
            let mut carried = plain.clone();
            for (key, member) in extra.as_object().unwrap() {
                carried[key] = member.clone();
            }
            assert_eq!(
                decode_response(&serde_json::to_vec(&carried).unwrap()).unwrap(),
                expected
            );
        }
        for extra in [
            json!({"clauses": ["formula"]}),
            json!({"dropped": [1]}),
            json!({"clauses": null}),
        ] {
            let mut carried = plain.clone();
            for (key, member) in extra.as_object().unwrap() {
                carried[key] = member.clone();
            }
            assert!(decode_response(&serde_json::to_vec(&carried).unwrap()).is_err());
        }
    }

    #[test]
    fn required_nullable_fields_cannot_be_silently_omitted() {
        let value = push();
        for path in [
            "/correction",
            "/feedback/pending/0/drop_reference",
            "/correction/diagnostics/0/item_index",
            "/correction/diagnostics/0/path",
        ] {
            let mut missing = value.clone();
            let (parent, key) = path.rsplit_once('/').unwrap();
            missing
                .pointer_mut(parent)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .remove(key);
            assert!(
                decode_push(&serde_json::to_vec(&missing).unwrap()).is_err(),
                "missing {path}"
            );
        }
        for response in tool_responses() {
            let mut paths = Vec::new();
            object_paths(&response, String::new(), &mut paths);
            for path in paths {
                for (key, child) in response.pointer(&path).unwrap().as_object().unwrap() {
                    if child.is_null() {
                        let mut missing = response.clone();
                        missing
                            .pointer_mut(&path)
                            .unwrap()
                            .as_object_mut()
                            .unwrap()
                            .remove(key);
                        assert!(
                            decode_tool_response(&serde_json::to_vec(&missing).unwrap()).is_err(),
                            "missing {path}/{key}"
                        );
                    }
                }
            }
        }
        let mut wrong = push();
        wrong["feedback"]["truncated"] = Value::Null;
        assert!(decode_push(&serde_json::to_vec(&wrong).unwrap()).is_err());
    }

    #[test]
    fn skills_are_not_a_successful_semantic_reply_or_argument_schema() {
        let value = successful("get_skill", json!({"id":"fixture","content":"guidance"}));
        assert!(decode_tool_response(&serde_json::to_vec(&value).unwrap()).is_err());
        assert!(decode_tool_arguments("get_skill", br#"{"id":"fixture"}"#).is_err());
        assert!(
            decode_tool_arguments("validate_clauses", br#"{"clauses":[],"instances":[]}"#).is_err()
        );
        for args in [
            json!({"clauses":[]}),
            json!({"clauses":[],"instances":null}),
        ] {
            assert!(
                decode_tool_arguments("evaluate_clauses", &serde_json::to_vec(&args).unwrap())
                    .is_err()
            );
        }
    }

    #[test]
    fn unsupported_success_shapes_and_mixed_envelopes_fail_closed() {
        for value in [
            successful("get_skill", json!({"id":"fixture"})),
            successful("get_skill", json!({"id":17,"content":null})),
            successful(
                "evaluate_clauses",
                json!({"id":"fixture","content":null,"extra":0}),
            ),
            successful("future_tool", json!({})),
            successful("countermodel", json!({"arbitrary": [1]})),
            successful(
                "ledger",
                json!({"metadata": {"total_items": 0, "first_index": 0, "returned_items": 0, "continuation": null},
                "items": [{"kind": "future_row"}]}),
            ),
            json!({"tool": "get_skill", "state_revision": 0, "result": {}, "error": {"code": "unknown_skill", "message": "message"}}),
            successful(
                "history",
                json!({"clause": clause(), "status": {"kind": "pending", "level": 1},
                "origin": "submitted", "protected": false,
                "minimum_level": 0, "current_level": 1, "attempts": [invalidation()]}),
            ),
        ] {
            assert!(decode_tool_response(&serde_json::to_vec(&value).unwrap()).is_err());
        }
        for route in [
            json!({"kind": "test_scaffold"}),
            json!({"kind": "future_route"}),
        ] {
            assert!(decode_wire::<RouteV1>(&serde_json::to_vec(&route).unwrap()).is_err());
        }
    }

    #[test]
    fn duplicate_keys_trailing_data_and_stale_protocols_are_rejected() {
        for bytes in [
            br#"{"clause_id":1,"clause_id":2,"record_digest":"r","formula_digest":"f"}"#.as_slice(),
            br#"{"clause_id":1,"record_digest":"r","formula_digest":"f"} {}"#.as_slice(),
        ] {
            assert!(decode_wire::<ClauseV1>(bytes).is_err());
        }
        for path in [
            "/schema_version",
            "/feedback/schema_version",
            "/feedback/presentation/schema_version",
            "/correction/schema_version",
        ] {
            let mut stale = push();
            *stale.pointer_mut(path).unwrap() = json!(999);
            assert!(
                decode_push(&serde_json::to_vec(&stale).unwrap()).is_err(),
                "{path}"
            );
        }
    }

    #[test]
    fn prior_observation_name_and_feedback_versions_are_rejected() {
        for (path, value) in [
            ("/operation", json!("agent_houdini_push")),
            ("/feedback/schema_version", json!(8)),
            ("/feedback/presentation/schema_version", json!(14)),
        ] {
            let mut stale = push();
            *stale.pointer_mut(path).unwrap() = value;
            assert!(
                decode_push(&serde_json::to_vec(&stale).unwrap()).is_err(),
                "{path}"
            );
        }
    }

    #[test]
    fn profile_names_are_exact_and_attempt_domains_remain_distinct() {
        assert_eq!(
            decode_wire::<ProfileV1>(br#""casc_2025""#).unwrap(),
            ProfileV1::Casc2025
        );
        assert!(decode_wire::<ProfileV1>(br#""casc2025""#).is_err());
        let status =
            decode_wire::<StatusV1>(&serde_json::to_vec(&status_variants().remove(3)).unwrap())
                .unwrap();
        assert!(matches!(
            status,
            StatusV1::Dead {
                reason: Some(DeadReasonV1::ProphecyFreeInitializationRefuted {
                    attempt: LedgerRowOrdinal(4)
                }),
                ..
            }
        ));
        let result = decode_wire::<AttemptResultV1>(
            &serde_json::to_vec(&attempt(routes().remove(0))["result"]).unwrap(),
        )
        .unwrap();
        assert_eq!(result.attempt_id, Some(PhysicalAttemptId(99)));
    }
    #[test]
    fn all_closed_string_vocabularies_match_the_current_producer_inventory() {
        fn check<T: serde::de::DeserializeOwned + Serialize>(names: &[&str]) {
            for name in names {
                let value = json!(name);
                assert_recursively_closed(&value, decode_wire::<T>);
            }
            assert!(decode_wire::<T>(br#""future_unreviewed_variant""#).is_err());
        }
        check::<OriginV1>(&["submitted", "symbolic", "edb_precondition_system"]);
        check::<RoleV1>(&["initialization", "maintenance"]);
        check::<ProfileV1>(&["direct", "casc_2025"]);
        check::<InconclusiveReasonV1>(&[
            "timed_out",
            "solver_unknown",
            "peer_failed",
            "unvalidated_refutation",
            "cancelled",
            "suspended",
        ]);
        check::<InvalidationReasonV1>(&[
            "antecedent_clause_deleted",
            "antecedent_clause_promoted",
            "antecedent_clause_excluded",
            "snapshot_changed",
            "system_clauses_installed",
        ]);
        check::<DeathCauseV1>(&["dropped", "refuted"]);
        check::<FailureScopeV1>(&["lane_local", "run_global"]);
        check::<FailureOriginV1>(&[
            "run_control",
            "artifact_settlement",
            "agent_consultation",
            "response_validation",
            "encoding_preparation",
            "initialization_execution",
            "vampire_proof_search",
            "vampire_finite_model_building",
            "vampire_race",
            "symbolic_race",
            "model_decoding",
            "termination_check",
            "maintenance_execution",
            "maintenance_history",
            "validity_certification",
            "invalidity_certification",
        ]);
        check::<FailureKindV1>(&[
            "overall_timeout",
            "interrupted",
            "consultation_timeout",
            "iteration_limit_exhausted",
            "source_exhausted",
            "correction_exhausted",
            "no_response",
            "transport_failure",
            "validation_infrastructure_failure",
            "unsupported_check",
            "fuel_exhausted",
            "check_timeout",
            "solver_unknown",
            "malformed_result",
            "process_failure",
            "infrastructure_failure",
            "concurrent_worker_failures",
            "certificate_construction_failure",
            "certificate_rejected",
            "certificate_typecheck_failure",
            "manifest_failure",
            "publication_failure",
            "history_log_failure",
            "state_invariant_violation",
        ]);
        check::<ArtifactRoleV1>(&[
            "proof",
            "model",
            "empty_check",
            "route_receipt",
            "validation_receipt",
            "progress_receipt",
            "failure_diagnostic",
        ]);
        check::<ArtifactKindV1>(&[
            "query",
            "proof",
            "model",
            "empty_instance_check",
            "initialization_check",
            "certificate",
            "acceptance_record",
            "witness",
            "failure_diagnostic",
            "runtime_trace",
        ]);
        check::<PushOperationV1>(&["proposer_observation"]);
        check::<ToolV1>(&[
            "countermodel",
            "strongest_refutations",
            "history",
            "ledger",
            "validate_clauses",
            "evaluate_clauses",
        ]);
        check::<CountermodelRetentionLimitV1>(&["countermodel_retention_tuples"]);
        check::<TerminationRoleV1>(&["termination"]);
        check::<SummaryRoleV1>(&["initialization", "maintenance", "unknown"]);
        check::<RouteKindV1>(&[
            "runtime_proof",
            "protected_theorem",
            "validated_refutation",
            "retry_progress",
            "suspended",
        ]);
    }

    #[test]
    fn summarized_routes_nullable_rows_and_each_check_outcome_are_retained_exactly() {
        let mut outcomes = vec![json!({"kind":"proved"}), json!({"kind":"refuted"})];
        outcomes.extend(
            [
                "timed_out",
                "solver_unknown",
                "peer_failed",
                "unvalidated_refutation",
                "cancelled",
                "suspended",
            ]
            .into_iter()
            .map(|reason| json!({"kind":"inconclusive","reason":reason})),
        );
        for outcome in outcomes {
            let mut row = attempt(routes().remove(0));
            row["result"]["outcome"] = outcome;
            row["result"]["route"] = Value::Null;
            row["result"]["route_summarized"] = json!(true);
            row["result"]["attempt_id"] = Value::Null;
            row["solver_time_nanos"] = json!(123);
            row["preparation_time_nanos"] = Value::Null;
            assert_recursively_closed(&row, decode_wire::<LedgerRowV1>);
        }
        let mut row = invalidation();
        row["cause"] = Value::Null;
        row["previous_row_digest"] = Value::Null;
        assert_recursively_closed(&row, decode_wire::<LedgerRowV1>);
        let result = successful(
            "ledger",
            json!({"metadata":{"total_items":3,"first_index":1,"returned_items":1,"continuation":"1"},"items":[row]}),
        );
        assert_recursively_closed(&result, decode_tool_response);
        let mut unavailable = not_retained();
        unavailable["value"] = json!(200);
        assert_recursively_closed(&unavailable, decode_wire::<NotRetainedV1>);
        let corrected = json!({"source":"c", "admitted":false, "correctable":{"code":"bad","message":"exact",
            "item_index":2,"path":"$.clauses[2]","offset":4}});
        assert_recursively_closed(&corrected, decode_wire::<EvaluationV1>);
    }
    #[test]
    fn duration_strings_and_host_limit_names_follow_the_producer_types() {
        for name in super::super::host_limits::HOST_LIMIT_NAMES {
            let value = json!({"limit":name,"value":0});
            assert_recursively_closed(&value, decode_wire::<HostLimitV1>);
        }
        for value in [
            json!({"limit":"future_limit","value":0}),
            json!({"limit":"pushed_core","value":-1}),
        ] {
            assert!(decode_wire::<HostLimitV1>(&serde_json::to_vec(&value).unwrap()).is_err());
        }
        for nanos in [
            json!(0),
            json!("-1"),
            json!("1.5"),
            json!("1e2"),
            json!("01"),
            json!(""),
            json!("340282366920938463463374607431768211456"),
        ] {
            let mut value = push();
            value["feedback"]["remaining_search_budget_ns"] = nanos;
            assert!(decode_push(&serde_json::to_vec(&value).unwrap()).is_err());
        }
        let mut value = push();
        value["feedback"]["remaining_search_budget_ns"] = json!(u128::MAX.to_string());
        assert_recursively_closed(&value, decode_push);
    }
    #[test]
    fn recorded_presentation_and_exclusive_result_shapes_remain_closed() {
        let timing = json!({"coordinates":{"consultation":1,"validation":2,"transport":3},
            "remaining_search_budget_ns":"123", "ledger_timings":[{"row_ordinal":4,"solver_time_nanos":null,"preparation_time_nanos":9}]});
        assert_recursively_closed(&timing, decode_wire::<RecordedPresentationV1>);
        for death in [
            json!({"cause":"dropped"}),
            json!({"cause":"refuted","reason":{"kind":"prophecy_free_initialization_refuted","attempt":4}}),
        ] {
            assert_recursively_closed(&death, decode_wire::<DeathV1>);
        }
        let mut both = json!({"attempt":99,"role":"termination","model":model(),"found_not_retained":not_retained()});
        assert!(
            decode_tool_response(
                &serde_json::to_vec(&successful("countermodel", both.clone())).unwrap()
            )
            .is_err()
        );
        both.as_object_mut().unwrap().remove("found_not_retained");
        both["clause"] = clause();
        assert!(
            decode_tool_response(&serde_json::to_vec(&successful("countermodel", both)).unwrap())
                .is_err()
        );
        let mut wrong = push();
        wrong["correction"]["diagnostics"][0]["offset"] = Value::Null;
        assert!(decode_push(&serde_json::to_vec(&wrong).unwrap()).is_err());
        let missing = json!({"source":"c","admitted":false,"correctable":{"code":"bad","message":"x","item_index":null,"path":null}});
        assert!(decode_wire::<EvaluationV1>(&serde_json::to_vec(&missing).unwrap()).is_err());
    }
}

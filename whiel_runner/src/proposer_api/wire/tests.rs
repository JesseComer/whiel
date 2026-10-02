use super::*;
use serde_json::{Value, json};

fn token() -> String {
    "a".repeat(64)
}

fn request(operation: Operation) -> Frame {
    Frame::new(token(), 1, Some(1), operation)
}

fn decoded(value: Value) -> io::Result<Frame> {
    Frame::decode_header(&serde_json::to_vec(&value).unwrap())
}

#[test]
fn every_operation_round_trips_with_exact_direction_scope_and_attachments() {
    let operations = vec![
        Operation::Hello {
            capabilities: ApiCapabilities::current(["history".into()]),
        },
        Operation::Ready {
            api: NegotiatedApi {
                version: super::super::API_VERSION.into(),
                operations: vec!["history".into()],
            },
        },
        Operation::Request {
            observation_bytes: 10,
            response_example_bytes: 20,
            remaining_request_budget_ns: Some("1000000000".into()),
        },
        Operation::Query {
            query_id: 1,
            name: "history".into(),
            args_bytes: 2,
        },
        Operation::QueryResult {
            query_id: 1,
            result_bytes: 3,
        },
        Operation::Submit { bytes: 4 },
        Operation::Submitted {},
        Operation::Rejected {
            code: TransportRejection::DuplicateSubmission,
        },
        Operation::Complete {
            outcome: RequestOutcome::Response,
        },
        Operation::RequestClosed {},
        Operation::Cancel {
            reason: CancellationReason::Deadline,
        },
        Operation::Shutdown {
            reason: ShutdownReason::Complete,
        },
        Operation::Closed {},
    ];
    for operation in operations {
        let direction = operation.direction();
        let request_id = (!operation.is_endpoint_scoped()).then_some(1);
        let frame = Frame::new(token(), 0, request_id, operation);
        let bytes = frame.encode_header().unwrap();
        assert_eq!(
            header_length((bytes.len() as u32).to_be_bytes()).unwrap(),
            bytes.len()
        );
        assert_eq!(Frame::decode_header(&bytes).unwrap(), frame);
        assert!(frame.validate(&token(), 0, direction).is_ok());
        let opposite = match direction {
            Direction::ToVerifier => Direction::ToProposer,
            Direction::ToProposer => Direction::ToVerifier,
        };
        assert!(frame.validate(&token(), 0, opposite).is_err());
        assert!(frame.validate(&token(), 1, direction).is_err());
        assert!(frame.validate(&"b".repeat(64), 0, direction).is_err());
        let mut wrong_scope = frame.clone();
        wrong_scope.request_id = if request_id.is_some() { None } else { Some(1) };
        assert!(wrong_scope.encode_header().is_err());
    }
}

#[test]
fn required_nullability_and_closed_nested_schemas_are_not_option_defaults() {
    let hello = Frame::new(
        token(),
        0,
        None,
        Operation::Hello {
            capabilities: ApiCapabilities::current([]),
        },
    );
    let mut value = json!(hello);
    assert!(value["request_id"].is_null());
    assert!(decoded(value.clone()).is_ok());
    value.as_object_mut().unwrap().remove("request_id");
    assert!(decoded(value).is_err());

    let pending = request(Operation::Request {
        observation_bytes: 0,
        response_example_bytes: 0,
        remaining_request_budget_ns: None,
    });
    let mut value = json!(pending);
    assert!(decoded(value.clone()).is_ok());
    value["operation"]
        .as_object_mut()
        .unwrap()
        .remove("remaining_request_budget_ns");
    assert!(decoded(value).is_err());
    for pointer in ["", "/operation", "/operation/capabilities"] {
        let mut value = json!(hello);
        value
            .pointer_mut(pointer)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("extra".into(), Value::Null);
        assert!(decoded(value).is_err(), "{pointer}");
    }
}

#[test]
fn strict_json_rejects_duplicate_keys_invalid_utf8_and_trailing_values() {
    let frame = request(Operation::Submit { bytes: 0 });
    let bytes = frame.encode_header().unwrap();
    let text = String::from_utf8(bytes.clone()).unwrap();
    let duplicate = text.replacen(
        "\"wire_version\":3",
        "\"wire_version\":3,\"wire_version\":3",
        1,
    );
    assert!(Frame::decode_header(duplicate.as_bytes()).is_err());
    let duplicate_nested = text.replacen("\"bytes\":0", "\"bytes\":0,\"bytes\":0", 1);
    assert!(Frame::decode_header(duplicate_nested.as_bytes()).is_err());
    assert!(Frame::decode_header(&[0xff]).is_err());
    assert!(Frame::decode_header(format!("{text} null").as_bytes()).is_err());
}

#[test]
fn v2_and_native_message_families_have_no_v3_fallback() {
    let frame = request(Operation::Submit { bytes: 0 });
    let mut value = json!(frame);
    value["wire_version"] = json!(2);
    assert!(decoded(value).is_err());
    for kind in [
        "configure",
        "configured",
        "prepare",
        "prepared",
        "raw_begin",
        "raw_chunk",
        "mcp_result",
        "raw_result",
        "raw_flushed",
        "raw_eof",
    ] {
        let mut value = json!(frame);
        value["operation"] = json!({"kind":kind});
        assert!(decoded(value).is_err(), "{kind}");
    }
    for value in [
        json!("fresh"),
        json!("continuous"),
        json!("codex"),
        json!("claude"),
    ] {
        let mut frame = json!(request(Operation::Complete {
            outcome: RequestOutcome::Response
        }));
        frame["operation"]["outcome"] = value;
        assert!(decoded(frame).is_err());
    }
}

#[test]
fn aggregate_bound_includes_every_attachment_header_and_prefix() {
    let frame = request(Operation::Request {
        observation_bytes: (MAX_PACKET_BYTES / 2) as u32,
        response_example_bytes: (MAX_PACKET_BYTES / 2) as u32,
        remaining_request_budget_ns: None,
    });
    assert!(frame.packet_length(100).is_err());
    assert!(frame.encode_header().is_err());
    let frame = request(Operation::Submit {
        bytes: (MAX_PACKET_BYTES - 104) as u32,
    });
    assert_eq!(frame.packet_length(100).unwrap(), MAX_PACKET_BYTES);
    assert!(frame.packet_length(101).is_err());
    let huge = request(Operation::Submit { bytes: u32::MAX });
    assert!(huge.packet_length(MAX_HEADER_BYTES).is_err());
}

#[test]
fn control_and_metadata_bounds_are_checked_before_reading_payloads() {
    assert!(header_length(0u32.to_be_bytes()).is_err());
    assert!(header_length(((MAX_HEADER_BYTES + 1) as u32).to_be_bytes()).is_err());
    let frame = request(Operation::Complete {
        outcome: RequestOutcome::NoResponse,
    });
    assert!(frame.packet_length(MAX_CONTROL_HEADER_BYTES).is_ok());
    assert!(frame.packet_length(MAX_CONTROL_HEADER_BYTES + 1).is_err());
    let mut padded = frame.encode_header().unwrap();
    padded.resize(MAX_CONTROL_HEADER_BYTES + 1, b' ');
    assert!(Frame::decode_header(&padded).is_err());
    let huge = Frame::new(
        token(),
        0,
        None,
        Operation::Hello {
            capabilities: ApiCapabilities::current(["x".repeat(MAX_HEADER_BYTES)]),
        },
    );
    assert!(huge.encode_header().is_err());
}

#[test]
fn query_ids_request_ids_budgets_and_tokens_have_closed_canonical_shapes() {
    for name in ["", "1tool", "tool-name", "é", "a b"] {
        assert!(
            request(Operation::Query {
                query_id: 1,
                name: name.into(),
                args_bytes: 0
            })
            .encode_header()
            .is_err()
        );
    }
    assert!(
        request(Operation::Query {
            query_id: 0,
            name: "history".into(),
            args_bytes: 0
        })
        .encode_header()
        .is_err()
    );
    assert!(
        request(Operation::QueryResult {
            query_id: 0,
            result_bytes: 0
        })
        .encode_header()
        .is_err()
    );
    for budget in ["", "01", "-1", "+1", " 1", "18446744073709551616"] {
        assert!(
            request(Operation::Request {
                observation_bytes: 0,
                response_example_bytes: 0,
                remaining_request_budget_ns: Some(budget.into())
            })
            .encode_header()
            .is_err()
        );
    }
    for budget in ["0", "1", "18446744073709551615"] {
        assert!(
            request(Operation::Request {
                observation_bytes: 0,
                response_example_bytes: 0,
                remaining_request_budget_ns: Some(budget.into())
            })
            .encode_header()
            .is_ok()
        );
    }
    let mut frame = request(Operation::Submit { bytes: 0 });
    frame.request_id = Some(0);
    assert!(frame.encode_header().is_err());
    for invalid_token in [
        "".into(),
        "a".repeat(63),
        "a".repeat(65),
        "A".repeat(64),
        "g".repeat(64),
    ] {
        assert!(!valid_endpoint_token(&invalid_token));
    }
    assert!(valid_endpoint_token(&token()));
    assert_eq!(next_sequence(0).unwrap(), 1);
    assert!(next_sequence(u64::MAX).is_err());
}

#[test]
fn generic_capability_negotiation_rejects_old_major_and_never_grants_a_query() {
    let mut capabilities = ApiCapabilities::current(["history".into()]);
    assert!(capabilities.negotiate(&[]).unwrap().operations.is_empty());
    capabilities.required_operations = vec!["history".into()];
    assert!(capabilities.negotiate(&[]).is_err());
    capabilities.version = "2.0.3".into();
    assert!(capabilities.negotiate(&["history"]).is_err());
}

#[test]
fn portable_wire_fixture_preserves_packet_bytes_and_independent_sequences() {
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Packet {
        direction: String,
        header: Frame,
        attachments: Vec<String>,
    }
    let fixture: Vec<Packet> =
        serde_json::from_str(include_str!("fixtures/generic-flow.json")).unwrap();
    let mut next_to_verifier = 0;
    let mut next_to_proposer = 0;
    for packet in fixture {
        let (direction, sequence) = match packet.direction.as_str() {
            "to_verifier" => (Direction::ToVerifier, &mut next_to_verifier),
            "to_proposer" => (Direction::ToProposer, &mut next_to_proposer),
            _ => panic!("unknown fixture direction"),
        };
        packet
            .header
            .validate(&token(), *sequence, direction)
            .unwrap();
        *sequence = next_sequence(*sequence).unwrap();
        assert_eq!(
            packet.header.operation.attachment_lengths(),
            packet
                .attachments
                .iter()
                .map(String::len)
                .collect::<Vec<_>>()
        );
        let header = packet.header.encode_header().unwrap();
        assert_eq!(Frame::decode_header(&header).unwrap(), packet.header);
        assert_eq!(
            packet.header.packet_length(header.len()).unwrap(),
            HEADER_PREFIX_BYTES
                + header.len()
                + packet.attachments.iter().map(String::len).sum::<usize>()
        );
    }
    assert_eq!((next_to_verifier, next_to_proposer), (6, 8));
}

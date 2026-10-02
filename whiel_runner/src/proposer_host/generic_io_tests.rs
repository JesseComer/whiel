use super::generic_io::*;
use crate::proposer_api::wire::{
    Frame, HEADER_PREFIX_BYTES, MAX_PACKET_BYTES, Operation, RequestOutcome,
};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

fn token() -> String {
    "a".repeat(64)
}

#[tokio::test]
async fn packet_round_trip_keeps_exact_opaque_bytes_and_actual_accounting() {
    let payload = b"  {\"x\":\"\xce\xbb\"}\n";
    let frame = Frame::new(
        token(),
        1,
        Some(1),
        Operation::Submit {
            bytes: payload.len() as u32,
        },
    );
    let bytes = frame.encode_header().unwrap().len() + HEADER_PREFIX_BYTES + payload.len();
    let sent = Budget::new(ApiTrafficLimits::default());
    let received = Budget::new(ApiTrafficLimits::default());
    let (mut writer, mut reader) = tokio::io::duplex(7);
    let endpoint_token = token();
    let attachments = [payload.as_slice()];
    let (write, read) = tokio::join!(
        write_packet(&mut writer, &frame, &attachments, &sent, false),
        read_packet(&mut reader, &endpoint_token, 1, &received)
    );
    write.unwrap();
    assert_eq!(read.unwrap().attachments, [payload.to_vec()]);
    assert_eq!(
        sent.usage(),
        ApiTrafficUsage {
            bytes: bytes as u64,
            messages: 1
        }
    );
    assert_eq!(received.usage(), sent.usage());
}

#[tokio::test]
async fn header_and_aggregate_limits_precede_attachment_allocation() {
    for payload in [((16_385u32).to_be_bytes().to_vec()), {
        let value = serde_json::json!({"wire_version":3,"endpoint_token":token(),"sequence":1,"request_id":1,
                "operation":{"kind":"submit","bytes":MAX_PACKET_BYTES}});
        let bytes = serde_json::to_vec(&value).unwrap();
        [
            (bytes.len() as u32).to_be_bytes().as_slice(),
            bytes.as_slice(),
        ]
        .concat()
    }] {
        let (mut writer, mut reader) = tokio::io::duplex(32768);
        writer.write_all(&payload).await.unwrap();
        let budget = Budget::new(ApiTrafficLimits::default());
        assert!(
            tokio::time::timeout(
                std::time::Duration::from_millis(100),
                read_packet(&mut reader, &token(), 1, &budget)
            )
            .await
            .unwrap()
            .is_err()
        );
    }
}

#[tokio::test]
async fn partial_payload_is_not_a_packet_and_reservation_is_released() {
    let frame = Frame::new(token(), 1, Some(1), Operation::Submit { bytes: 5 });
    let header = frame.encode_header().unwrap();
    let (mut writer, mut reader) = tokio::io::duplex(1024);
    writer
        .write_all(&(header.len() as u32).to_be_bytes())
        .await
        .unwrap();
    writer.write_all(&header).await.unwrap();
    writer.write_all(b"x").await.unwrap();
    drop(writer);
    let budget = Budget::new(ApiTrafficLimits::default());
    assert!(
        read_packet(&mut reader, &token(), 1, &budget)
            .await
            .is_err()
    );
    assert_eq!(budget.usage().bytes, (header.len() + 5) as u64);
}

#[tokio::test]
async fn budget_failure_is_latched_and_only_closure_controls_can_bypass_it() {
    let budget = Budget::new(ApiTrafficLimits {
        bytes: 1,
        messages: 1,
    });
    let mut output = Vec::new();
    let frame = Frame::new(
        token(),
        1,
        Some(1),
        Operation::Complete {
            outcome: RequestOutcome::Failure,
        },
    );
    assert!(
        write_packet(&mut output, &frame, &[], &budget, false)
            .await
            .is_err()
    );
    assert!(budget.failure().is_some());
    assert!(output.is_empty());
    assert!(
        write_packet(&mut output, &frame, &[], &budget, true)
            .await
            .is_err()
    );
    let shutdown = Frame::new(
        token(),
        1,
        None,
        Operation::Shutdown {
            reason: crate::proposer_api::wire::ShutdownReason::Failure,
        },
    );
    write_packet(&mut output, &shutdown, &[], &budget, true)
        .await
        .unwrap();
    assert_eq!(
        budget.usage(),
        ApiTrafficUsage {
            bytes: output.len() as u64,
            messages: 1
        }
    );
}

#[tokio::test]
async fn cancellation_of_blocked_write_never_spends_unsent_reserved_bytes() {
    let budget = Budget::new(ApiTrafficLimits::default());
    let (mut output, mut input) = tokio::io::duplex(5);
    let frame = Frame::new(token(), 1, Some(1), Operation::Submit { bytes: 2 });
    let result = tokio::time::timeout(
        std::time::Duration::from_millis(30),
        write_packet(&mut output, &frame, &[b"xx"], &budget, false),
    )
    .await;
    assert!(result.is_err());
    assert_eq!(
        budget.usage(),
        ApiTrafficUsage {
            bytes: 5,
            messages: 1
        }
    );
    let mut observed = [0; 5];
    input.read_exact(&mut observed).await.unwrap();
}

#[tokio::test]
async fn partial_header_cancellation_preserves_actual_received_bytes() {
    let budget = Budget::new(ApiTrafficLimits::default());
    let (mut writer, mut reader) = tokio::io::duplex(16);
    writer.write_all(&[0, 0]).await.unwrap();
    assert!(
        tokio::time::timeout(
            std::time::Duration::from_millis(30),
            read_packet(&mut reader, &token(), 1, &budget)
        )
        .await
        .is_err()
    );
    assert_eq!(
        budget.usage(),
        ApiTrafficUsage {
            bytes: 2,
            messages: 1
        }
    );
}

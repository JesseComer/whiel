//! Cancellation of partial writes preserves its cause and joins before restart.
use super::*;
use crate::proposer_api::{AgentToolPolicy, AgentToolResponseFuture};
use serde_json::{Value, json};
use std::os::fd::AsRawFd;
use std::sync::atomic::AtomicUsize;
use tokio::io::AsyncReadExt;

fn config(mode: &str, trace: Option<&std::path::Path>) -> GenericProcessConfig {
    let python = Command::new("python3")
        .args(["-c", "import sys; print(sys.executable)"])
        .output()
        .unwrap();
    assert!(python.status.success());
    let mut arguments = vec![
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("src/proposer_host/fixtures/generic_endpoint.py")
            .into_os_string(),
        mode.into(),
    ];
    if let Some(trace) = trace {
        arguments.push(trace.into());
    }
    let mut config = GenericProcessConfig::new(
        PathBuf::from(String::from_utf8(python.stdout).unwrap().trim()),
        arguments,
    );
    config.startup_timeout = Duration::from_secs(3);
    config.shutdown_timeout = Duration::from_millis(300);
    config.fallback_timeout = Duration::from_secs(3);
    config
}

struct LargeReply(AtomicUsize);
impl AgentToolSurface for LargeReply {
    fn call<'a>(&'a self, name: &'a str, _args: Value) -> AgentToolResponseFuture<'a> {
        Box::pin(async move {
            self.0.fetch_add(1, Ordering::SeqCst);
            AgentToolResponse::ok(name, 7, json!({"data":"x".repeat(2 * 1024 * 1024)}))
        })
    }
}

#[tokio::test]
async fn every_outbound_request_packet_preserves_typed_cancel_after_partial_write() {
    for operation in [
        Operation::Request {
            observation_bytes: 2,
            response_example_bytes: 2,
            remaining_request_budget_ns: None,
        },
        Operation::QueryResult {
            query_id: 1,
            result_bytes: 2,
        },
        Operation::Submitted {},
    ] {
        for external_first in [false, true] {
            let frame = Frame::new("a".repeat(64), 1, Some(1), operation.clone());
            let attachments: Vec<&[u8]> = match operation {
                Operation::Request { .. } => vec![b"{}", b"{}"],
                Operation::QueryResult { .. } => vec![b"{}"],
                _ => vec![],
            };
            let budget = Budget::new(ApiTrafficLimits::default());
            let (mut writer, mut reader) = tokio::io::duplex(7);
            let token = CancellationToken::new();
            let owner = CancellationToken::new();
            let observer = AgentSourceCancellation::new(token.clone());
            let cancel = async {
                while budget.usage().bytes < 7 {
                    tokio::task::yield_now().await;
                }
                let deadline = tokio::time::Instant::now() + Duration::from_millis(20);
                assert!(owner.bind_absolute_deadline(deadline));
                if external_first {
                    owner.cancel();
                }
                tokio::time::sleep_until(deadline + Duration::from_millis(5)).await;
                if !external_first {
                    owner.cancel_for_deadline(deadline);
                }
                token.cancel_from(&owner);
            };
            let (result, ()) = tokio::join!(
                request_write(
                    write_packet(&mut writer, &frame, &attachments, &budget, false),
                    &observer
                ),
                cancel,
            );
            assert!(is_cancelled_write(&result.unwrap_err()));
            assert_eq!(
                observer.reason(),
                if external_first {
                    crate::proposer_api::wire::CancellationReason::Cancelled
                } else {
                    crate::proposer_api::wire::CancellationReason::Deadline
                }
            );
            assert!(budget.failure().is_none());
            drop(writer);
            let mut partial = Vec::new();
            reader.read_to_end(&mut partial).await.unwrap();
            assert_eq!(partial.len(), 7);
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn blocked_request_and_query_reply_join_then_restart_with_new_identity_and_old_budget() {
    for mode in ["blocked_request", "blocked_reply"] {
        for external_first in [false, true] {
            let (trace_root, _) = scratch(std::path::Path::new("/tmp")).unwrap();
            let trace = trace_root.0.join("trace.jsonl");
            let mut provider = GenericProcessProposer::start(
                config(mode, Some(&trace)),
                &AgentToolPolicy::all_enabled().enabled_names(),
                &CancellationToken::new(),
            )
            .await
            .unwrap_or_else(|error| {
                panic!(
                    "{mode}: {error}; {}",
                    std::fs::read_to_string(&trace).unwrap_or_default()
                )
            });
            let retained_cleanup = provider.cleanup_handle();
            let retained_resources = provider.resource_status();
            let root = provider.scratch_directory().to_owned();
            let descriptor = provider
                .connection
                .as_ref()
                .unwrap()
                .writer
                .as_ref()
                .as_raw_fd();
            let size: libc::c_int = 1024;
            // Bound the kernel write window so the real peer can stop a request
            // before its complete typed observation has crossed the socket.
            assert_eq!(
                unsafe {
                    libc::setsockopt(
                        descriptor,
                        libc::SOL_SOCKET,
                        libc::SO_SNDBUF,
                        (&size as *const libc::c_int).cast(),
                        std::mem::size_of_val(&size) as libc::socklen_t,
                    )
                },
                0
            );
            let push = crate::framework2::fixture_push_for_tools(&AgentToolPolicy::all_enabled());
            let tools = LargeReply(AtomicUsize::new(0));
            let mut response = AgentResponseWriter::fixture_for_tests(Some(1024));
            let source = CancellationToken::new();
            let owner = CancellationToken::new();
            let observer = AgentSourceCancellation::new(source.clone());
            let before = provider.api_usage();
            let cancel = async {
                loop {
                    let rows = std::fs::read_to_string(&trace).unwrap_or_default();
                    if rows.contains(&format!("\"event\": \"{mode}\"")) {
                        break;
                    }
                    tokio::time::sleep(Duration::from_millis(1)).await;
                }
                let deadline = tokio::time::Instant::now() + Duration::from_millis(75);
                assert!(owner.bind_absolute_deadline(deadline));
                if external_first {
                    owner.cancel();
                }
                tokio::time::sleep_until(deadline + Duration::from_millis(5)).await;
                if !external_first {
                    owner.cancel_for_deadline(deadline);
                }
                source.cancel_from(&owner);
            };
            let (outcome, ()) = tokio::time::timeout(Duration::from_secs(5), async {
                tokio::join!(
                    provider.consult(&push, &tools, &mut response, observer.clone()),
                    cancel
                )
            })
            .await
            .unwrap();
            assert_eq!(outcome, AgentSourceOutcome::TransportFailure);
            assert!(response.fixture_bytes().is_empty());
            assert!(provider.terminal_failure().is_none(), "{mode}");
            assert!(provider.resource_failure().is_none());
            assert!(
                provider.restart_after_cancel,
                "{mode} did not interrupt its packet write"
            );
            assert_eq!(
                observer.reason(),
                if external_first {
                    crate::proposer_api::wire::CancellationReason::Cancelled
                } else {
                    crate::proposer_api::wire::CancellationReason::Deadline
                }
            );
            provider.quiesce_request().await.unwrap();
            assert!(provider.connection.is_none());
            assert!(provider.child.finished());
            let spent = provider.api_usage();
            assert!(spent.bytes > before.bytes);
            let cumulative_budget = provider.budget.clone();
            let mut next_response = AgentResponseWriter::fixture_for_tests(Some(1024));
            assert_eq!(
                provider
                    .consult(
                        &push,
                        &tools,
                        &mut next_response,
                        AgentSourceCancellation::new(CancellationToken::new())
                    )
                    .await,
                AgentSourceOutcome::Response
            );
            assert_eq!(
                next_response.fixture_bytes(),
                " {opaque exact λ}\n".as_bytes()
            );
            assert_eq!(provider.scratch_directory(), root);
            assert!(provider.api_usage().bytes > spent.bytes);
            assert!(provider.api_usage().messages > spent.messages);
            assert_eq!(provider.api_usage(), cumulative_budget.usage());
            provider.quiesce_request().await.unwrap();
            assert_eq!(retained_resources.usage(), provider.api_usage());
            let replacement_child = provider.child.cleanup();
            if external_first {
                drop(provider);
                retained_cleanup.stop_and_join().await.unwrap();
                assert!(replacement_child.finished());
            } else {
                provider.shutdown(ShutdownReason::Complete).await.unwrap();
            }
            let events = std::fs::read_to_string(&trace)
                .unwrap()
                .lines()
                .map(|line| serde_json::from_str::<Value>(line).unwrap())
                .collect::<Vec<_>>();
            let starts = events
                .iter()
                .filter(|event| event["event"] == "start")
                .collect::<Vec<_>>();
            assert_eq!(starts.len(), 2);
            assert_ne!(starts[0]["token"], starts[1]["token"]);
            assert_ne!(starts[0]["pid"], starts[1]["pid"]);
            assert_eq!(
                events
                    .iter()
                    .filter(|event| event["event"] == "receipt")
                    .count(),
                1
            );
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn shutdown_budget_exhaustion_is_resource_failure_after_successful_fallback() {
    for maximum in [5, 6, 7] {
        let mut config = config("no_response", None);
        config.traffic_limits.messages = maximum;
        let mut provider = GenericProcessProposer::start(
            config,
            &AgentToolPolicy::all_enabled().enabled_names(),
            &CancellationToken::new(),
        )
        .await
        .unwrap();
        let push = crate::framework2::fixture_push_for_tools(&AgentToolPolicy::all_enabled());
        let mut response = AgentResponseWriter::fixture_for_tests(Some(1024));
        assert_eq!(
            provider
                .consult(
                    &push,
                    &LargeReply(AtomicUsize::new(0)),
                    &mut response,
                    AgentSourceCancellation::new(CancellationToken::new())
                )
                .await,
            AgentSourceOutcome::NoResponse
        );
        provider.quiesce_request().await.unwrap();
        assert!(provider.resource_failure().is_none());
        assert_eq!(provider.api_usage().messages, 5);
        let retained_resources = provider.resource_status();
        provider.shutdown(ShutdownReason::Complete).await.unwrap();
        assert_eq!(retained_resources.failure(), provider.resource_failure());
        assert_eq!(provider.resource_failure().is_some(), maximum < 7);
        assert!(provider.child.finished());
        assert!(provider.connection.is_none());
        assert!(provider.terminal_failure().is_none());
    }
}

async fn no_response_before_shutdown(config: GenericProcessConfig) -> GenericProcessProposer {
    let mut provider = GenericProcessProposer::start(
        config,
        &AgentToolPolicy::all_enabled().enabled_names(),
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let push = crate::framework2::fixture_push_for_tools(&AgentToolPolicy::all_enabled());
    let mut response = AgentResponseWriter::fixture_for_tests(Some(1024));
    assert_eq!(
        provider
            .consult(
                &push,
                &LargeReply(AtomicUsize::new(0)),
                &mut response,
                AgentSourceCancellation::new(CancellationToken::new())
            )
            .await,
        AgentSourceOutcome::NoResponse
    );
    provider.quiesce_request().await.unwrap();
    assert!(provider.resource_failure().is_none());
    assert_eq!(provider.api_usage().messages, 5);
    provider
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn shutdown_byte_reservations_keep_resource_cause_on_write_and_read_refusal() {
    let mut calibration = no_response_before_shutdown(config("no_response", None)).await;
    let before_shutdown = calibration.api_usage().bytes;
    calibration
        .shutdown(ShutdownReason::Complete)
        .await
        .unwrap();
    let after_shutdown = calibration.api_usage().bytes;
    let shutdown_bytes = 4 + Frame::new(
        "a".repeat(64),
        3,
        None,
        Operation::Shutdown {
            reason: ShutdownReason::Complete,
        },
    )
    .encode_header()
    .unwrap()
    .len() as u64;
    assert!(after_shutdown > before_shutdown + shutdown_bytes);
    for (allowance, exhausted) in [
        (before_shutdown, true),
        (before_shutdown + shutdown_bytes, true),
        (after_shutdown, false),
    ] {
        let mut config = config("no_response", None);
        config.traffic_limits.bytes = allowance;
        let mut provider = no_response_before_shutdown(config).await;
        assert_eq!(provider.api_usage().bytes, before_shutdown);
        provider.shutdown(ShutdownReason::Complete).await.unwrap();
        assert_eq!(provider.resource_failure().is_some(), exhausted);
        assert!(provider.terminal_failure().is_none());
        assert!(provider.connection.is_none());
        assert!(provider.child.finished());
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn shutdown_resource_refusal_does_not_hide_a_failed_physical_join() {
    let mut config = config("no_response", None);
    config.traffic_limits.messages = 5;
    let mut provider = no_response_before_shutdown(config).await;
    assert!(!provider.child.finished());
    // An actual owned child cannot complete its supervised shutdown in this
    // deliberately insufficient allowance. The test still joins it afterward.
    provider.config.fallback_timeout = Duration::from_nanos(1);
    let cleanup = provider.shutdown(ShutdownReason::Complete).await;
    provider.child.join(Duration::from_secs(3)).await.unwrap();
    assert!(cleanup.is_err());
    assert!(provider.resource_failure().is_some());
    assert_eq!(provider.shutdown(ShutdownReason::Complete).await, cleanup);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn startup_budget_refusal_is_typed_only_after_joined_cleanup() {
    for (bytes, messages) in [(1, 100), (1024 * 1024, 1)] {
        let (trace_root, _) = scratch(std::path::Path::new("/tmp")).unwrap();
        let mut config = config("normal", None);
        config.scratch_parent = trace_root.0.clone();
        config.traffic_limits = ApiTrafficLimits { bytes, messages };
        let error = match GenericProcessProposer::start(
            config,
            &AgentToolPolicy::all_enabled().enabled_names(),
            &CancellationToken::new(),
        )
        .await
        {
            Ok(mut provider) => {
                provider.shutdown(ShutdownReason::Failure).await.unwrap();
                panic!("startup budget unexpectedly allowed the handshake");
            }
            Err(error) => error,
        };
        assert_eq!(
            error
                .get_ref()
                .and_then(|cause| cause.downcast_ref::<GenericProcessStartupError>()),
            Some(&GenericProcessStartupError::ResourceExhausted)
        );
        // The per-endpoint directory remains owned by its child until join.
        assert_eq!(std::fs::read_dir(&trace_root.0).unwrap().count(), 0);
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn startup_resource_refusal_retains_a_real_cleanup_failure() {
    for (bytes, messages) in [(1, 100), (1024 * 1024, 1)] {
        let (root, _) = scratch(std::path::Path::new("/tmp")).unwrap();
        let mut config = config("normal", None);
        config.scratch_parent = root.0.clone();
        config.traffic_limits = ApiTrafficLimits { bytes, messages };
        config.fallback_timeout = Duration::from_nanos(1);
        let error = match GenericProcessProposer::start(
            config,
            &AgentToolPolicy::all_enabled().enabled_names(),
            &CancellationToken::new(),
        )
        .await
        {
            Ok(mut provider) => {
                provider.shutdown(ShutdownReason::Failure).await.unwrap();
                panic!("startup allowance unexpectedly accepted the handshake")
            }
            Err(error) => error,
        };
        // The deliberately inadequate wait is a real join failure. Await the
        // supervisor's eventual release before the test drops its outer root.
        tokio::time::timeout(Duration::from_secs(3), async {
            while std::fs::read_dir(&root.0).unwrap().next().is_some() {
                tokio::time::sleep(Duration::from_millis(1)).await;
            }
        })
        .await
        .unwrap();
        assert!(matches!(
            error
                .get_ref()
                .and_then(|cause| cause.downcast_ref::<GenericProcessStartupError>()),
            Some(GenericProcessStartupError::ResourceExhaustedCleanupFailed(
                _
            ))
        ));
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cancelled_restart_retains_both_startup_resource_and_cleanup_failures() {
    let (trace_root, _) = scratch(std::path::Path::new("/tmp")).unwrap();
    let trace = trace_root.0.join("trace.jsonl");
    let mut configuration = config("blocked_request", Some(&trace));
    // Hello, Ready, a partial Request, then the replacement Hello fit. Its
    // Ready is refused while the replacement child is still alive.
    configuration.traffic_limits.messages = 4;
    let mut provider = GenericProcessProposer::start(
        configuration,
        &AgentToolPolicy::all_enabled().enabled_names(),
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let cleanup = provider.cleanup_handle();
    let resources = provider.resource_status();
    let descriptor = provider
        .connection
        .as_ref()
        .unwrap()
        .writer
        .as_ref()
        .as_raw_fd();
    let size: libc::c_int = 1024;
    assert_eq!(
        unsafe {
            libc::setsockopt(
                descriptor,
                libc::SOL_SOCKET,
                libc::SO_SNDBUF,
                (&size as *const libc::c_int).cast(),
                std::mem::size_of_val(&size) as libc::socklen_t,
            )
        },
        0
    );
    let push = crate::framework2::fixture_push_for_tools(&AgentToolPolicy::all_enabled());
    let tools = LargeReply(AtomicUsize::new(0));
    let mut response = AgentResponseWriter::fixture_for_tests(Some(1024));
    let cancellation = CancellationToken::new();
    let cancel = async {
        while resources.usage().messages < 3 {
            tokio::task::yield_now().await;
        }
        cancellation.cancel();
    };
    let (outcome, ()) = tokio::time::timeout(Duration::from_secs(5), async {
        tokio::join!(
            provider.consult(
                &push,
                &tools,
                &mut response,
                AgentSourceCancellation::new(cancellation.clone())
            ),
            cancel
        )
    })
    .await
    .unwrap();
    assert_eq!(outcome, AgentSourceOutcome::TransportFailure);
    assert!(provider.restart_after_cancel);
    provider.quiesce_request().await.unwrap();
    assert!(provider.child.finished());
    assert!(resources.failure().is_none());
    provider.config.fallback_timeout = Duration::from_nanos(1);
    assert_eq!(
        provider
            .consult(
                &push,
                &tools,
                &mut response,
                AgentSourceCancellation::new(CancellationToken::new())
            )
            .await,
        AgentSourceOutcome::TransportFailure
    );
    // This handle follows the replacement child and owns an adequate wait.
    cleanup.stop_and_join().await.unwrap();
    assert!(provider.cleanup_error.is_some());
    assert!(
        provider
            .shutdown_result
            .is_some_and(|result| result.is_err())
    );
    assert!(resources.failure().is_some());
    assert!(provider.terminal_failure().is_none());
    assert!(response.fixture_bytes().is_empty());
    assert_eq!(
        provider.shutdown(ShutdownReason::Failure).await,
        provider.shutdown_result.unwrap()
    );
}

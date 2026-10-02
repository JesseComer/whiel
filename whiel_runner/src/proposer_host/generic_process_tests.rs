//! Real synthetic endpoint processes exercise only the public wire, without models.
use super::generic_process::{
    GenericProcessConfig, GenericProcessProposer, GenericProcessStartupError,
};
use crate::proposer_api::wire::ShutdownReason;
use crate::proposer_api::{
    AgentProvider, AgentResponseWriter, AgentSourceCancellation, AgentSourceOutcome,
    AgentToolPolicy, AgentToolResponse, AgentToolResponseFuture, AgentToolSurface,
};
use crate::runtime::CancellationToken;
use serde_json::{Value, json};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

struct Queries {
    calls: AtomicUsize,
    cancellation: Option<CancellationToken>,
    completed: AtomicUsize,
}
impl Queries {
    fn new() -> Self {
        Self {
            calls: AtomicUsize::new(0),
            cancellation: None,
            completed: AtomicUsize::new(0),
        }
    }
}
impl AgentToolSurface for Queries {
    fn call<'a>(&'a self, name: &'a str, args: Value) -> AgentToolResponseFuture<'a> {
        Box::pin(async move {
            self.calls.fetch_add(1, Ordering::SeqCst);
            if let Some(token) = &self.cancellation {
                token.cancelled().await;
            }
            if args.get("delay") == Some(&Value::Bool(true)) {
                tokio::time::sleep(Duration::from_millis(80)).await;
            }
            self.completed.fetch_add(1, Ordering::SeqCst);
            AgentToolResponse::ok(name, 7, json!({"entries":[]}))
        })
    }
}
fn config(mode: &str, log: Option<&std::path::Path>) -> GenericProcessConfig {
    let python = std::process::Command::new("python3")
        .args(["-c", "import sys; print(sys.executable)"])
        .output()
        .unwrap();
    assert!(python.status.success());
    let mut args = vec![
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("src/proposer_host/fixtures/generic_endpoint.py")
            .into_os_string(),
        mode.into(),
    ];
    if let Some(path) = log {
        args.push(path.as_os_str().into());
    }
    let mut config = GenericProcessConfig::new(
        PathBuf::from(String::from_utf8(python.stdout).unwrap().trim()),
        args,
    );
    config.startup_timeout = Duration::from_secs(3);
    config.shutdown_timeout = Duration::from_millis(300);
    config.fallback_timeout = Duration::from_secs(3);
    config
}
async fn start(mode: &str) -> GenericProcessProposer {
    GenericProcessProposer::start(
        config(mode, None),
        &AgentToolPolicy::all_enabled().enabled_names(),
        &CancellationToken::new(),
    )
    .await
    .unwrap()
}
async fn request(
    provider: &mut GenericProcessProposer,
    queries: &Queries,
    token: CancellationToken,
    max: usize,
) -> (AgentSourceOutcome, Vec<u8>) {
    let push = crate::framework2::fixture_push_for_tools(&AgentToolPolicy::all_enabled());
    let mut response = AgentResponseWriter::fixture_for_tests(Some(max));
    let outcome = tokio::time::timeout(
        Duration::from_secs(5),
        provider.consult(
            &push,
            queries,
            &mut response,
            AgentSourceCancellation::new(token),
        ),
    )
    .await
    .unwrap();
    (outcome, response.fixture_bytes().to_vec())
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_persistent_requests_keep_endpoint_and_exact_receipted_bytes() {
    for mode in [
        "normal",
        "fragmented",
        "duplicate",
        "empty",
        "queries",
        "invalid_query",
    ] {
        let mut provider = start(mode).await;
        let directory = provider.scratch_directory().to_owned();
        let queries = Queries::new();
        for _ in 0..2 {
            let (outcome, bytes) =
                request(&mut provider, &queries, CancellationToken::new(), 1024).await;
            assert_eq!(outcome, AgentSourceOutcome::Response, "{mode}");
            assert_eq!(
                bytes,
                if mode == "empty" {
                    b"".as_slice()
                } else {
                    " {opaque exact λ}\n".as_bytes()
                },
                "{mode}"
            );
            provider.quiesce_request().await.unwrap();
            assert_eq!(provider.scratch_directory(), directory);
        }
        assert_eq!(
            queries.calls.load(Ordering::SeqCst),
            if mode == "queries" { 4 } else { 0 }
        );
        provider.shutdown(ShutdownReason::Complete).await.unwrap();
        provider.shutdown(ShutdownReason::Complete).await.unwrap();
        assert!(provider.api_usage().messages >= 12);
        assert!(provider.resource_failure().is_none());
        drop(provider);
        assert!(!directory.exists());
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_scratch_lease_outlives_joined_endpoint_until_final_drop() {
    let mut provider = start("normal").await;
    let directory = provider.scratch_directory().to_owned();
    let lease = provider.scratch_lease();
    let clone = lease.clone();
    assert_eq!(lease.path(), directory);
    provider.shutdown(ShutdownReason::Complete).await.unwrap();
    drop(provider);
    assert!(directory.is_dir());
    drop(lease);
    assert!(directory.is_dir());
    drop(clone);
    assert!(!directory.exists());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_no_submission_outcomes_do_not_forge_responses() {
    for (mode, expected) in [
        ("no_response", AgentSourceOutcome::NoResponse),
        ("source_exhausted", AgentSourceOutcome::SourceExhausted),
        ("failure", AgentSourceOutcome::TransportFailure),
    ] {
        let mut provider = start(mode).await;
        let (outcome, bytes) = request(
            &mut provider,
            &Queries::new(),
            CancellationToken::new(),
            1024,
        )
        .await;
        assert_eq!(outcome, expected);
        assert!(bytes.is_empty());
        assert!(provider.terminal_failure().is_none());
        provider.quiesce_request().await.unwrap();
        provider.shutdown(ShutdownReason::Complete).await.unwrap();
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_protocol_failure_or_truncation_discards_all_response_bytes() {
    for mode in [
        "early_eof",
        "wrong_sequence",
        "wrong_scope",
        "repeat_hello",
        "submitted_no_response",
        "query_gap",
        "complete_without_receipt",
        "truncated_submit",
    ] {
        let mut provider = start(mode).await;
        let cleanup = provider.cleanup_handle();
        let (outcome, bytes) = request(
            &mut provider,
            &Queries::new(),
            CancellationToken::new(),
            1024,
        )
        .await;
        assert_eq!(outcome, AgentSourceOutcome::TransportFailure, "{mode}");
        assert!(bytes.is_empty(), "{mode}");
        provider.quiesce_request().await.unwrap();
        assert!(provider.terminal_failure().is_some(), "{mode}");
        provider.shutdown(ShutdownReason::Failure).await.unwrap();
        cleanup.stop_and_join().await.unwrap();
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_cancellation_joins_pending_api_work_before_request_closed() {
    let mut provider = start("cancel").await;
    let token = CancellationToken::new();
    let queries = Queries {
        cancellation: Some(token.clone()),
        ..Queries::new()
    };
    let stop = async {
        while queries.calls.load(Ordering::SeqCst) == 0 {
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
        token.cancel();
    };
    let ((outcome, bytes), ()) =
        tokio::join!(request(&mut provider, &queries, token.clone(), 1024), stop);
    assert_eq!(outcome, AgentSourceOutcome::TransportFailure);
    assert!(bytes.is_empty());
    assert_eq!(queries.completed.load(Ordering::SeqCst), 1);
    provider.quiesce_request().await.unwrap();
    provider.shutdown(ShutdownReason::Cancelled).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_pending_queries_preclude_successful_complete() {
    let mut provider = start("pending_complete").await;
    let token = CancellationToken::new();
    let queries = Queries {
        cancellation: Some(token.clone()),
        ..Queries::new()
    };
    let (outcome, bytes) = request(&mut provider, &queries, token, 1024).await;
    assert_eq!(outcome, AgentSourceOutcome::TransportFailure);
    assert!(bytes.is_empty());
    assert_eq!(queries.completed.load(Ordering::SeqCst), 1);
    provider.shutdown(ShutdownReason::Failure).await.unwrap();
    provider.cleanup_handle().stop_and_join().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_unresponsive_shutdown_reports_failure_and_still_joins_fallback() {
    let mut provider = start("ignore_shutdown").await;
    let (outcome, _) = request(
        &mut provider,
        &Queries::new(),
        CancellationToken::new(),
        1024,
    )
    .await;
    assert_eq!(outcome, AgentSourceOutcome::Response);
    provider.quiesce_request().await.unwrap();
    assert!(provider.shutdown(ShutdownReason::Complete).await.is_err());
    provider.cleanup_handle().stop_and_join().await.unwrap();
}

/// A compatible earlier client revision negotiates down to its own
/// declaration, and the consultation that follows carries that agreement
/// rather than B's constant. Keep this intentional: it is the contract behind
/// "existing 3.0.0 proposers negotiate and work unchanged".
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_lower_revision_endpoint_negotiates_down_and_serves_a_request() {
    let mut provider = start("lower_revision").await;
    let declared = provider.api_capabilities();
    assert_eq!(declared.version, "3.0.0");
    assert_ne!(
        declared.version,
        crate::proposer_api::API_VERSION,
        "this endpoint must declare a revision below the host constant"
    );
    let policy = AgentToolPolicy::all_enabled();
    let negotiated = declared.negotiate(&policy.enabled_names()).unwrap();
    assert_eq!(negotiated.version, "3.0.0");
    let push = crate::framework2::fixture_push_for_negotiated_api(&policy, negotiated);
    let mut response = AgentResponseWriter::fixture_for_tests(Some(1024));
    let outcome = tokio::time::timeout(
        Duration::from_secs(5),
        provider.consult(
            &push,
            &Queries::new(),
            &mut response,
            AgentSourceCancellation::new(CancellationToken::new()),
        ),
    )
    .await
    .unwrap();
    assert_eq!(outcome, AgentSourceOutcome::Response);
    assert_eq!(response.fixture_bytes(), " {opaque exact λ}\n".as_bytes());
    provider.quiesce_request().await.unwrap();
    provider.shutdown(ShutdownReason::Complete).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_setup_rejects_bad_handshake_and_joins_failed_startup() {
    for mode in [
        "wrong_token",
        "bad_major",
        "missing_required",
        "startup_hang",
    ] {
        let mut config = config(mode, None);
        config.startup_timeout = Duration::from_millis(300);
        assert!(
            GenericProcessProposer::start(
                config,
                &AgentToolPolicy::all_enabled().enabled_names(),
                &CancellationToken::new()
            )
            .await
            .is_err(),
            "{mode}"
        );
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_reply_limit_retains_controller_correction_and_endpoint_lifetime() {
    let mut provider = start("normal").await;
    let push = crate::framework2::fixture_push_for_tools(&AgentToolPolicy::all_enabled());
    let mut response = AgentResponseWriter::fixture_for_tests(Some(1));
    let outcome = provider
        .consult(
            &push,
            &Queries::new(),
            &mut response,
            AgentSourceCancellation::new(CancellationToken::new()),
        )
        .await;
    assert_eq!(outcome, AgentSourceOutcome::Response);
    assert_eq!(response.fixture_bytes(), b" ");
    // Even an empty later write must retain the exceeded flag. The controller
    // consumes that flag before looking at source outcome or proposal bytes.
    assert!(response.write_chunk(b"").is_err());
    provider.quiesce_request().await.unwrap();
    assert!(provider.resource_failure().is_none());
    let (outcome, bytes) = request(
        &mut provider,
        &Queries::new(),
        CancellationToken::new(),
        1024,
    )
    .await;
    assert_eq!(outcome, AgentSourceOutcome::Response);
    assert_eq!(bytes, " {opaque exact λ}\n".as_bytes());
    provider.quiesce_request().await.unwrap();
    provider.shutdown(ShutdownReason::Complete).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_drop_has_an_explicit_joinable_process_tree_fallback() {
    let provider = start("normal").await;
    let directory = provider.scratch_directory().to_owned();
    let cleanup = provider.cleanup_handle();
    drop(provider);
    cleanup.stop_and_join().await.unwrap();
    assert!(!directory.exists());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_aggregate_traffic_exhaustion_is_latched_and_discards_submission() {
    let mut config = config("normal", None);
    config.traffic_limits.messages = 4;
    let mut provider = GenericProcessProposer::start(
        config,
        &AgentToolPolicy::all_enabled().enabled_names(),
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let (outcome, bytes) = request(
        &mut provider,
        &Queries::new(),
        CancellationToken::new(),
        1024,
    )
    .await;
    assert_eq!(outcome, AgentSourceOutcome::SourceExhausted);
    assert!(bytes.is_empty());
    assert!(
        provider
            .resource_failure()
            .unwrap()
            .contains("resource_exhausted")
    );
    provider.shutdown(ShutdownReason::Failure).await.unwrap();
    provider.cleanup_handle().stop_and_join().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_shutdown_joins_detached_descendant_after_endpoint_acknowledges() {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let log = std::env::temp_dir().join(format!(
        "whiel-generic-descendants-{}-{}.jsonl",
        std::process::id(),
        COUNTER.fetch_add(1, Ordering::SeqCst)
    ));
    let mut provider = GenericProcessProposer::start(
        config("detached", Some(&log)),
        &AgentToolPolicy::all_enabled().enabled_names(),
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let (outcome, _) = request(
        &mut provider,
        &Queries::new(),
        CancellationToken::new(),
        1024,
    )
    .await;
    assert_eq!(outcome, AgentSourceOutcome::Response);
    provider.quiesce_request().await.unwrap();
    let child = std::fs::read_to_string(&log)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .find(|event| event["event"] == "detached")
        .unwrap()["pid"]
        .as_u64()
        .unwrap();
    provider.shutdown(ShutdownReason::Complete).await.unwrap();
    let status = std::process::Command::new("/bin/ps")
        .args(["-p", &child.to_string(), "-o", "stat="])
        .output()
        .unwrap();
    let status = String::from_utf8(status.stdout).unwrap();
    assert!(
        status.trim().is_empty() || status.trim().starts_with('Z'),
        "detached descendant survived: {status}"
    );
    std::fs::remove_file(log).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_startup_cancellation_has_typed_cause_only_after_joined_cleanup() {
    let token = CancellationToken::new();
    let stop = token.clone();
    let permitted = AgentToolPolicy::all_enabled().enabled_names();
    let (result, ()) = tokio::join!(
        GenericProcessProposer::start(config("startup_hang", None), &permitted, &token),
        async move {
            tokio::time::sleep(Duration::from_millis(50)).await;
            stop.cancel();
        }
    );
    let error = result.err().unwrap();
    assert_eq!(error.kind(), std::io::ErrorKind::Interrupted);
    assert_eq!(
        error
            .get_ref()
            .unwrap()
            .downcast_ref::<GenericProcessStartupError>(),
        Some(&GenericProcessStartupError::Cancelled)
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_startup_timeout_and_protocol_failure_are_not_cancellation() {
    let permitted = AgentToolPolicy::all_enabled().enabled_names();
    let mut launch = config("startup_hang", None);
    launch.startup_timeout = Duration::from_millis(100);
    let error = GenericProcessProposer::start(launch, &permitted, &CancellationToken::new())
        .await
        .err()
        .unwrap();
    assert_eq!(
        error
            .get_ref()
            .unwrap()
            .downcast_ref::<GenericProcessStartupError>(),
        Some(&GenericProcessStartupError::TimedOut)
    );
    let error = GenericProcessProposer::start(
        config("bad_major", None),
        &permitted,
        &CancellationToken::new(),
    )
    .await
    .err()
    .unwrap();
    assert!(
        error
            .get_ref()
            .and_then(|error| error.downcast_ref::<GenericProcessStartupError>())
            .is_none()
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_cancel_wire_preserves_deadline_and_earlier_external_cause() {
    for (external_first, expected) in [(false, "deadline"), (true, "cancelled")] {
        let log = std::env::temp_dir().join(format!(
            "whiel-generic-cancel-reason-{}-{expected}.jsonl",
            std::process::id()
        ));
        let mut provider = GenericProcessProposer::start(
            config("cancel", Some(&log)),
            &AgentToolPolicy::all_enabled().enabled_names(),
            &CancellationToken::new(),
        )
        .await
        .unwrap();
        let owner = CancellationToken::new();
        let source = CancellationToken::new();
        let queries = Queries {
            cancellation: Some(source.clone()),
            ..Queries::new()
        };
        let cancel = async {
            while queries.calls.load(Ordering::SeqCst) == 0 {
                tokio::time::sleep(Duration::from_millis(1)).await;
            }
            let deadline = tokio::time::Instant::now() + Duration::from_millis(40);
            assert!(owner.bind_absolute_deadline(deadline));
            if external_first {
                owner.cancel();
            }
            // Both observers run after expiry. Only the authoritative first
            // cancellation timestamp may distinguish these otherwise equal cases.
            tokio::time::sleep_until(deadline + Duration::from_millis(10)).await;
            if !external_first {
                owner.cancel_for_deadline(deadline);
            }
            source.cancel_from(&owner);
        };
        let ((outcome, bytes), ()) = tokio::join!(
            request(&mut provider, &queries, source.clone(), 1024),
            cancel
        );
        assert_eq!(outcome, AgentSourceOutcome::TransportFailure);
        assert!(bytes.is_empty());
        assert!(provider.terminal_failure().is_none());
        provider.quiesce_request().await.unwrap();
        provider.shutdown(ShutdownReason::Cancelled).await.unwrap();
        let trace = std::fs::read_to_string(&log).unwrap();
        let observed = trace
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .find(|event| event["event"] == "cancel")
            .unwrap();
        assert_eq!(observed["reason"], expected);
        std::fs::remove_file(log).unwrap();
    }
}

//! Tests for persistent pre-certificate AgentHoudini search orchestration.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

use tokio::time::Instant;

use crate::runtime::CancellationToken;

use serde_json::json;

use super::counterexample::{
    COUNTEREXAMPLE_TIMEOUT_CODE, CounterexampleRejection, CounterexampleValidation,
    FrameworkIICounterexampleError, ValidatedCounterexample,
};
use super::search::{
    ConsultationOperation, CounterexampleCall, OverallOperation, PreCertificateAgentHoudiniLimits,
    await_consultation_operation, await_overall_operation, classify_counterexample_call,
    strictly_earlier_consultation_deadline,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};

/// Milestone 7.5 review, finding 6. The consultation bound is a host
/// resource statement, not a contract limit: it is absent by default, so a
/// run's only guards on how long it may go on are the deadlines and the
/// cancellation token (`houdini.tex` Section 4.7). A host that sets one gets
/// a run-global, non-retryable resource fault when it is exhausted, exactly
/// like the run deadline's own — never a verdict on a proposal.
#[test]
fn the_consultation_bound_is_absent_by_default_and_a_resource_statement_when_set() {
    let overall = Duration::from_secs(10);
    let unbounded = PreCertificateAgentHoudiniLimits::new(overall, None, None);
    assert_eq!(
        unbounded.iteration_limit(),
        None,
        "no consultation bound is built in"
    );
    let bounded = PreCertificateAgentHoudiniLimits::new(overall, None, Some(4));
    assert_eq!(bounded.iteration_limit(), Some(4));
    // Every other field is untouched by the bound's presence.
    assert_eq!(unbounded.overall_limit(), bounded.overall_limit());
    assert_eq!(
        unbounded.counterexample_validation_limit(),
        bounded.counterexample_validation_limit()
    );

    // The statement a set bound makes when exhausted.
    let report = FailureReport::try_new(
        FailureOrigin::RunControl,
        FailureKind::IterationLimitExhausted,
        false,
        FailureScope::RunGlobal,
        Some("AgentHoudini exhausted the host's bound of 4 outer consultations".to_string()),
        Vec::new(),
    )
    .unwrap();
    assert_eq!(report.scope(), FailureScope::RunGlobal);
    assert!(!report.retryable());
}

#[test]
fn local_deadline_exists_only_when_strictly_before_overall_deadline() {
    let start = Instant::now();
    let overall = start + Duration::from_secs(10);

    assert_eq!(
        strictly_earlier_consultation_deadline(start, Some(Duration::from_secs(9)), overall,),
        Some(start + Duration::from_secs(9)),
    );
    assert_eq!(
        strictly_earlier_consultation_deadline(start, Some(Duration::from_secs(10)), overall,),
        None,
    );
    assert_eq!(
        strictly_earlier_consultation_deadline(start, Some(Duration::from_secs(11)), overall,),
        None,
    );
    assert_eq!(
        strictly_earlier_consultation_deadline(start, None, overall),
        None,
    );
}

#[tokio::test]
async fn local_timeout_cancels_and_joins_the_consultation_operation() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let operation_cancellation = consultation.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let operation_cleaned = Arc::clone(&cleaned);
    let operation = async move {
        operation_cancellation.cancelled().await;
        tokio::task::yield_now().await;
        operation_cleaned.store(true, Ordering::SeqCst);
    };

    let outcome = await_consultation_operation(
        operation,
        &consultation,
        &run,
        Instant::now() + Duration::from_secs(2),
        Some(Duration::from_millis(5)),
    )
    .await;

    assert!(matches!(
        outcome,
        ConsultationOperation::LocalTimedOutAfterCompletion(())
    ));
    assert!(consultation.is_cancelled());
    assert!(!run.is_cancelled());
    assert!(cleaned.load(Ordering::SeqCst));
}

#[tokio::test]
async fn equal_local_limit_is_owned_by_overall_timeout_and_joined() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let operation_cancellation = consultation.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let operation_cleaned = Arc::clone(&cleaned);
    let limit = Duration::from_millis(10);
    let overall = Instant::now() + limit;
    let operation = async move {
        operation_cancellation.cancelled().await;
        operation_cleaned.store(true, Ordering::SeqCst);
    };

    let outcome =
        await_consultation_operation(operation, &consultation, &run, overall, Some(limit)).await;

    assert!(matches!(
        outcome,
        ConsultationOperation::OverallTimedOutAfterCompletion(())
    ));
    assert!(consultation.is_cancelled());
    assert!(run.is_cancelled());
    assert!(cleaned.load(Ordering::SeqCst));
}

#[tokio::test]
async fn external_cancellation_cancels_and_joins_the_consultation_operation() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let operation_cancellation = consultation.clone();
    let cancellation_trigger = run.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let operation_cleaned = Arc::clone(&cleaned);
    let operation = async move {
        operation_cancellation.cancelled().await;
        tokio::task::yield_now().await;
        operation_cleaned.store(true, Ordering::SeqCst);
    };
    tokio::spawn(async move {
        tokio::task::yield_now().await;
        cancellation_trigger.cancel();
    });

    let outcome = await_consultation_operation(
        operation,
        &consultation,
        &run,
        Instant::now() + Duration::from_secs(2),
        None,
    )
    .await;

    assert!(matches!(outcome, ConsultationOperation::Cancelled));
    assert!(consultation.is_cancelled());
    assert!(cleaned.load(Ordering::SeqCst));
}

#[tokio::test]
async fn external_cancellation_before_overall_remains_owner_after_slow_consultation_cleanup() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let operation_cancellation = consultation.clone();
    let cancellation_trigger = run.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let operation_cleaned = Arc::clone(&cleaned);
    let deadline = Instant::now() + Duration::from_millis(100);
    let operation = async move {
        operation_cancellation.cancelled().await;
        tokio::time::sleep(Duration::from_millis(120)).await;
        operation_cleaned.store(true, Ordering::SeqCst);
    };
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(20)).await;
        cancellation_trigger.cancel();
    });

    let outcome =
        await_consultation_operation(operation, &consultation, &run, deadline, None).await;

    assert!(Instant::now() >= deadline);
    assert!(matches!(outcome, ConsultationOperation::Cancelled));
    assert!(consultation.is_cancelled());
    assert!(cleaned.load(Ordering::SeqCst));
}

#[tokio::test]
async fn overall_supersedes_local_timeout_while_consultation_cleanup_is_still_running() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let operation_cancellation = consultation.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let operation_cleaned = Arc::clone(&cleaned);
    let deadline = Instant::now() + Duration::from_millis(60);
    let operation = async move {
        operation_cancellation.cancelled().await;
        tokio::time::sleep(Duration::from_millis(100)).await;
        operation_cleaned.store(true, Ordering::SeqCst);
    };

    let outcome = await_consultation_operation(
        operation,
        &consultation,
        &run,
        deadline,
        Some(Duration::from_millis(10)),
    )
    .await;

    assert!(matches!(
        outcome,
        ConsultationOperation::OverallTimedOutAfterCompletion(())
    ));
    assert!(consultation.is_cancelled());
    assert!(run.is_cancelled());
    assert!(cleaned.load(Ordering::SeqCst));
}

#[tokio::test]
async fn overall_operation_timeout_cancels_and_joins_before_return() {
    let cancellation = CancellationToken::new();
    let operation_cancellation = cancellation.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let operation_cleaned = Arc::clone(&cleaned);
    let operation = async move {
        operation_cancellation.cancelled().await;
        tokio::task::yield_now().await;
        operation_cleaned.store(true, Ordering::SeqCst);
    };

    let outcome = await_overall_operation(
        operation,
        &cancellation,
        Instant::now() + Duration::from_millis(5),
    )
    .await;

    assert!(matches!(outcome, OverallOperation::TimedOut));
    assert!(cancellation.is_cancelled());
    assert!(cleaned.load(Ordering::SeqCst));
}

#[tokio::test]
async fn external_cancellation_before_deadline_remains_owner_after_slow_overall_cleanup() {
    let cancellation = CancellationToken::new();
    let operation_cancellation = cancellation.clone();
    let cancellation_trigger = cancellation.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let operation_cleaned = Arc::clone(&cleaned);
    let deadline = Instant::now() + Duration::from_millis(100);
    let operation = async move {
        operation_cancellation.cancelled().await;
        tokio::time::sleep(Duration::from_millis(120)).await;
        operation_cleaned.store(true, Ordering::SeqCst);
    };
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(20)).await;
        cancellation_trigger.cancel();
    });

    let outcome = await_overall_operation(operation, &cancellation, deadline).await;

    assert!(Instant::now() >= deadline);
    assert!(matches!(outcome, OverallOperation::Cancelled));
    assert!(cleaned.load(Ordering::SeqCst));
}

#[tokio::test]
async fn expired_overall_deadline_owns_even_an_immediately_ready_operation() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let started = Arc::new(AtomicBool::new(false));
    let operation_started = Arc::clone(&started);
    let outcome = await_consultation_operation(
        std::future::poll_fn(move |_| {
            operation_started.store(true, Ordering::SeqCst);
            std::task::Poll::Ready(17_u8)
        }),
        &consultation,
        &run,
        Instant::now(),
        Some(Duration::ZERO),
    )
    .await;

    assert!(matches!(outcome, ConsultationOperation::OverallTimedOut));
    assert!(consultation.is_cancelled());
    assert!(run.is_cancelled());
    assert!(!started.load(Ordering::SeqCst));
}

#[tokio::test]
async fn simultaneous_consultation_completion_is_owned_by_overall_deadline() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let deadline = Instant::now() + Duration::from_millis(5);
    let operation = async move {
        tokio::time::sleep_until(deadline).await;
        17_u8
    };

    let outcome =
        await_consultation_operation(operation, &consultation, &run, deadline, None).await;

    assert!(matches!(
        outcome,
        ConsultationOperation::OverallTimedOutAfterCompletion(17)
    ));
    assert!(consultation.is_cancelled());
    assert!(run.is_cancelled());
}

#[tokio::test]
async fn overall_deadline_owns_when_one_poll_spans_both_deadlines() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let overall = Instant::now() + Duration::from_millis(10);
    let operation = std::future::poll_fn(|_| {
        std::thread::sleep(Duration::from_millis(15));
        std::task::Poll::Ready(17_u8)
    });

    let outcome = await_consultation_operation(
        operation,
        &consultation,
        &run,
        overall,
        Some(Duration::from_millis(5)),
    )
    .await;

    assert!(matches!(
        outcome,
        ConsultationOperation::OverallTimedOutAfterCompletion(17)
    ));
    assert!(consultation.is_cancelled());
    assert!(run.is_cancelled());
}

#[tokio::test]
async fn simultaneous_overall_operation_completion_is_timeout_owned() {
    let cancellation = CancellationToken::new();
    let deadline = Instant::now() + Duration::from_millis(5);
    let operation = async move {
        tokio::time::sleep_until(deadline).await;
        17_u8
    };

    let outcome = await_overall_operation(operation, &cancellation, deadline).await;

    assert!(matches!(outcome, OverallOperation::TimedOut));
    assert!(cancellation.is_cancelled());
}

#[tokio::test(flavor = "current_thread")]
async fn overall_deadline_cancels_before_repolling_a_cooperative_operation() {
    let cancellation = CancellationToken::new();
    let operation_cancellation = cancellation.clone();
    let steps = Arc::new(AtomicUsize::new(0));
    let operation_steps = Arc::clone(&steps);
    let deadline = Instant::now() + Duration::from_millis(5);
    let operation = async move {
        operation_steps.fetch_add(1, Ordering::SeqCst);
        std::thread::sleep(Duration::from_millis(10));
        tokio::task::yield_now().await;
        if !operation_cancellation.is_cancelled() {
            operation_steps.fetch_add(1, Ordering::SeqCst);
        }
    };

    let outcome = await_overall_operation(operation, &cancellation, deadline).await;

    assert!(matches!(outcome, OverallOperation::TimedOut));
    assert!(cancellation.is_cancelled());
    assert_eq!(steps.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn expired_overall_operation_is_not_started() {
    let cancellation = CancellationToken::new();
    let started = Arc::new(AtomicBool::new(false));
    let operation_started = Arc::clone(&started);
    let operation = std::future::poll_fn(move |_| {
        operation_started.store(true, Ordering::SeqCst);
        std::task::Poll::Ready(())
    });

    let outcome = await_overall_operation(operation, &cancellation, Instant::now()).await;

    assert!(matches!(outcome, OverallOperation::TimedOut));
    assert!(cancellation.is_cancelled());
    assert!(!started.load(Ordering::SeqCst));
}

// ------------------------------------------------------------
// Counterexample Call Arbitration
// ------------------------------------------------------------

fn worker_failure(scope: FailureScope) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::EncodingPreparation,
        FailureKind::InfrastructureFailure,
        false,
        scope,
        Some("counterexample worker failure".to_string()),
        Vec::new(),
    )
    .unwrap()
}

#[test]
fn a_validated_call_ends_the_run_and_a_rejected_one_does_not() {
    let validated = ValidatedCounterexample::for_test(json!({"relations": []}), &"a".repeat(64), 7);
    let call = classify_counterexample_call(
        ConsultationOperation::Completed(Ok(CounterexampleValidation::Validated(validated))),
        Duration::from_secs(30),
    );
    let CounterexampleCall::Validated(validated) = call else {
        panic!("a validated verdict must end the run invalid");
    };
    assert_eq!(validated.fuel_consumed(), 7);

    let call = classify_counterexample_call(
        ConsultationOperation::Completed(Ok(CounterexampleValidation::Rejected(
            CounterexampleRejection::timeout("why"),
        ))),
        Duration::from_secs(30),
    );
    assert!(matches!(call, CounterexampleCall::Rejected(_)));
}

/// The call-local limit is the only outcome that becomes an ordinary
/// rejection; the run's own deadline and cancellation still end the run.
#[test]
fn only_the_call_local_limit_becomes_a_timeout_rejection() {
    for call in [
        ConsultationOperation::LocalTimedOut,
        ConsultationOperation::LocalTimedOutAfterCompletion(Ok(
            CounterexampleValidation::Rejected(CounterexampleRejection::timeout("stale")),
        )),
    ] {
        let classified = classify_counterexample_call(call, Duration::from_secs(30));
        let CounterexampleCall::Rejected(rejection) = classified else {
            panic!("the call-local limit must become a rejection, not a run failure");
        };
        assert_eq!(rejection.code(), COUNTEREXAMPLE_TIMEOUT_CODE);
        assert!(rejection.reason().contains("30s"));
    }

    assert!(matches!(
        classify_counterexample_call(
            ConsultationOperation::OverallTimedOut,
            Duration::from_secs(30)
        ),
        CounterexampleCall::OverallTimedOut
    ));
    assert!(matches!(
        classify_counterexample_call(ConsultationOperation::Cancelled, Duration::from_secs(30)),
        CounterexampleCall::Interrupted
    ));
    assert!(matches!(
        classify_counterexample_call(
            ConsultationOperation::Completed(Err(FrameworkIICounterexampleError::Cancelled)),
            Duration::from_secs(30)
        ),
        CounterexampleCall::Interrupted
    ));
}

#[test]
fn a_worker_failure_keeps_its_own_scope() {
    assert!(matches!(
        classify_counterexample_call(
            ConsultationOperation::Completed(Err(FrameworkIICounterexampleError::Failure(
                worker_failure(FailureScope::RunGlobal)
            ))),
            Duration::from_secs(30)
        ),
        CounterexampleCall::RunFailure(_)
    ));
    assert!(matches!(
        classify_counterexample_call(
            ConsultationOperation::Completed(Err(FrameworkIICounterexampleError::Failure(
                worker_failure(FailureScope::LaneLocal)
            ))),
            Duration::from_secs(30)
        ),
        CounterexampleCall::LaneFailure(_)
    ));
}

/// A stalling worker call is cut off by the call-local limit, the call's own
/// cancellation token fires (which is what terminates the worker process),
/// and the run's cancellation is left alone.
#[tokio::test]
async fn a_stalling_validation_times_out_locally_without_cancelling_the_run() {
    let call_cancellation = CancellationToken::new();
    let run = CancellationToken::new();
    let stalled = call_cancellation.clone();
    let terminated = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&terminated);
    let operation = async move {
        stalled.cancelled().await;
        observed.store(true, Ordering::SeqCst);
        Err::<CounterexampleValidation, _>(FrameworkIICounterexampleError::Cancelled)
    };

    let outcome = await_consultation_operation(
        operation,
        &call_cancellation,
        &run,
        Instant::now() + Duration::from_secs(30),
        Some(Duration::from_millis(5)),
    )
    .await;

    let classified = classify_counterexample_call(outcome, Duration::from_millis(5));
    let CounterexampleCall::Rejected(rejection) = classified else {
        panic!("a stalled validation must become a timeout rejection");
    };
    assert_eq!(rejection.code(), COUNTEREXAMPLE_TIMEOUT_CODE);
    assert!(call_cancellation.is_cancelled());
    assert!(terminated.load(Ordering::SeqCst));
    assert!(!run.is_cancelled());
}

#[tokio::test]
async fn local_deadline_reason_reaches_the_scoped_source_observer() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let parent = consultation.clone();
    let operation = async move {
        parent.cancelled().await;
        let source = CancellationToken::new();
        source.cancel_from(&parent);
        let observer = crate::proposer_api::AgentSourceCancellation::new(source);
        observer.cancelled().await;
        observer.reason()
    };
    let outcome = await_consultation_operation(
        operation,
        &consultation,
        &run,
        Instant::now() + Duration::from_secs(1),
        Some(Duration::from_millis(5)),
    )
    .await;
    assert!(matches!(
        outcome,
        ConsultationOperation::LocalTimedOutAfterCompletion(
            crate::proposer_api::wire::CancellationReason::Deadline
        )
    ));
    assert!(!run.is_cancelled());
}

#[tokio::test]
async fn overall_deadline_reason_reaches_the_scoped_source_observer() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let parent = consultation.clone();
    let operation = async move {
        parent.cancelled().await;
        let source = CancellationToken::new();
        source.cancel_from(&parent);
        let observer = crate::proposer_api::AgentSourceCancellation::new(source);
        observer.cancelled().await;
        observer.reason()
    };
    let outcome = await_consultation_operation(
        operation,
        &consultation,
        &run,
        Instant::now() + Duration::from_millis(5),
        None,
    )
    .await;
    assert!(matches!(
        outcome,
        ConsultationOperation::OverallTimedOutAfterCompletion(
            crate::proposer_api::wire::CancellationReason::Deadline
        )
    ));
    assert!(run.is_cancelled());
}

#[tokio::test]
async fn external_reason_survives_forwarding_after_deadline_and_late_cleanup() {
    let consultation = CancellationToken::new();
    let run = CancellationToken::new();
    let parent = consultation.clone();
    let trigger = run.clone();
    let deadline = Instant::now() + Duration::from_millis(100);
    let seen = Arc::new(std::sync::Mutex::new(None));
    let output = Arc::clone(&seen);
    let operation = async move {
        trigger.cancel();
        parent.cancelled().await;
        // Deliberately forward only after expiry. A new cancellation timestamp
        // here would incorrectly claim that the deadline won.
        tokio::time::sleep_until(deadline + Duration::from_millis(20)).await;
        let source = CancellationToken::new();
        source.cancel_from(&parent);
        let observer = crate::proposer_api::AgentSourceCancellation::new(source);
        observer.cancelled().await;
        *output.lock().unwrap() = Some(observer.reason());
        tokio::time::sleep(Duration::from_millis(5)).await;
    };
    let outcome =
        await_consultation_operation(operation, &consultation, &run, deadline, None).await;
    assert!(matches!(outcome, ConsultationOperation::Cancelled));
    assert_eq!(
        *seen.lock().unwrap(),
        Some(crate::proposer_api::wire::CancellationReason::Cancelled)
    );
    assert!(consultation.cancelled_before(deadline));
}

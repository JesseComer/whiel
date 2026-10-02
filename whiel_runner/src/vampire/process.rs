//! Direct-process supervision and bounded concurrent output capture.

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod unix;

use crate::artifact::BudgetedArtifactWriter;
use std::collections::VecDeque;
use std::io::{Read, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::ExitStatus;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;

use crate::runtime::CancellationToken;

use super::command::Invocation;
use super::protocol::{ProtocolParser, ProtocolStream, ProtocolSummary};

/*
  Each stream has one dedicated blocking reader. The readers parse
  protocol events incrementally and retain bounded diagnostics while
  stdout always streams to its evidence stage. Stderr is staged only
  when full inconclusive capture is enabled.
*/

// ------------------------------------------------------------
// Capture Types And Limits
// ------------------------------------------------------------

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) use unix::StopReason;

/// Process-group launch, supervision, and descendant cleanup, generalized
/// enough (it depends only on an executable path, arguments, and a working
/// directory — never on Vampire's own [`Invocation`]) that
/// [`crate::framework2::leancheck`] reuses it for the pinned leancheck
/// Vampire launch, so a `--mode portfolio` leancheck run gets the same
/// whole-process-group cleanup on timeout or cancellation that every other
/// Vampire launch already gets.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) use unix::{SpawnError, SpawnedProcess};

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StopReason {
    Exited,
    Cancelled,
    CaptureFailed,
}

const READ_BUFFER_BYTES: usize = 16 * 1024;

#[derive(Clone, Copy, Debug)]
pub(super) struct CaptureConfig {
    pub diagnostic_bytes: usize,
    pub protocol_line_bytes: usize,
    pub max_total_output_bytes: Option<u64>,
}

#[derive(Clone)]
struct PumpContext {
    config: CaptureConfig,
    sequence: Arc<AtomicU64>,
    budget: Arc<OutputBudget>,
    capture_failed: Arc<AtomicBool>,
}

#[derive(Debug)]
pub(super) struct CapturedStream {
    pub protocol: ProtocolSummary,
    pub diagnostic: Vec<u8>,
    pub bytes_seen: u64,
    pub bytes_staged: u64,
    pub error: Option<String>,
}

#[derive(Debug)]
pub(super) struct ProcessOutput {
    pub reason: StopReason,
    pub status: Result<ExitStatus, String>,
    pub cleanup_error: Option<String>,
    pub stdout: CapturedStream,
    pub stderr: CapturedStream,
}

#[derive(Debug)]
pub(super) enum ProcessStartError {
    Cancelled,
    Failed(String),
    RunFailure(String),
}

// ------------------------------------------------------------
// Single-Process Execution
// ------------------------------------------------------------

/*
  Supervision runs while both pumps drain concurrently. A pump
  startup failure or panic raises capture_failed before supervision
  waits, so a child blocked on a pipe cannot deadlock this function.
*/

pub(super) fn run(
    invocation: &Invocation,
    stdout_writer: BudgetedArtifactWriter,
    stderr_writer: Option<BudgetedArtifactWriter>,
    cancellation: CancellationToken,
    config: CaptureConfig,
) -> Result<ProcessOutput, ProcessStartError> {
    if cancellation.should_stop() {
        return Err(ProcessStartError::Cancelled);
    }

    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (
            invocation,
            stdout_writer,
            stderr_writer,
            cancellation,
            config,
        );
        return Err(ProcessStartError::Failed(
            "owned Vampire process-tree supervision is not implemented on this platform"
                .to_string(),
        ));
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        let mut process =
            unix::SpawnedProcess::spawn(&invocation.executable, &invocation.args, &invocation.cwd)
                .map_err(|error| match error {
                    unix::SpawnError::Failed(detail) => ProcessStartError::Failed(detail),
                    unix::SpawnError::CleanupFailed(detail) => {
                        ProcessStartError::RunFailure(detail)
                    }
                })?;
        invocation
            .telemetry
            .increment("solver.vampire_process_launches", 1);
        invocation.telemetry.increment(
            format!(
                "solver.vampire_process_launches.{}",
                invocation.telemetry_mode
            ),
            1,
        );
        if matches!(invocation.telemetry_mode, "proof_normal" | "proof_casc") {
            invocation
                .telemetry
                .increment("solver.vampire_process_launches.proof", 1);
        }
        invocation
            .telemetry
            .event_with("vampire_process_launched", || {
                // The premise role belongs here beside the mode: it names
                // which of the two renderings of the same problem this
                // process was launched on, and both lanes of a launch read
                // the one file.
                let premise_role = invocation.premise_role.name();
                match invocation.telemetry_mode {
                    "proof_normal" => {
                        serde_json::json!({
                            "mode": "proof",
                            "proof_strategy": "direct",
                            "premise_role": premise_role,
                        })
                    }
                    "proof_casc" => {
                        serde_json::json!({
                            "mode": "proof",
                            "proof_strategy": "casc_2025",
                            "time_limit_deciseconds": invocation.time_limit_deciseconds,
                            "premise_role": premise_role,
                        })
                    }
                    mode => serde_json::json!({"mode": mode, "premise_role": premise_role}),
                }
            });
        let _process_span = invocation
            .telemetry
            .span("solver.child_process_execution_and_cleanup");
        let _mode_span = invocation.telemetry.span(match invocation.telemetry_mode {
            "proof_normal" | "proof_casc" => "solver.proof_process_execution_and_cleanup",
            "fmb" => "solver.fmb_process_execution_and_cleanup",
            _ => "solver.unknown_process_execution_and_cleanup",
        });
        let _proof_strategy_span = match invocation.telemetry_mode {
            "proof_normal" => Some(
                invocation
                    .telemetry
                    .span("solver.proof_normal_execution_and_cleanup"),
            ),
            "proof_casc" => Some(
                invocation
                    .telemetry
                    .span("solver.proof_casc_execution_and_cleanup"),
            ),
            _ => None,
        };
        let pipes = process.take_pipes().map_err(ProcessStartError::Failed)?;
        let context = PumpContext {
            config,
            sequence: Arc::new(AtomicU64::new(0)),
            budget: Arc::new(OutputBudget::new(config.max_total_output_bytes)),
            capture_failed: Arc::new(AtomicBool::new(false)),
        };

        let stdout_handle = match spawn_pump(
            pipes.stdout,
            Some(stdout_writer),
            context.clone(),
            "stdout",
            ProtocolStream::Stdout,
        ) {
            Ok(handle) => handle,
            Err(error) => {
                context.capture_failed.store(true, Ordering::Release);
                drop(pipes.stderr);
                drop(stderr_writer);
                let supervised = process.supervise(&cancellation, &context.capture_failed);
                return Ok(ProcessOutput {
                    reason: supervised.reason,
                    status: supervised.status.map_err(|error| error.to_string()),
                    cleanup_error: supervised.cleanup_error,
                    stdout: failed_capture(error),
                    stderr: failed_capture(
                        "stderr capture did not start after stdout capture startup failed"
                            .to_string(),
                    ),
                });
            }
        };
        let stderr_handle = match spawn_pump(
            pipes.stderr,
            stderr_writer,
            context.clone(),
            "stderr",
            ProtocolStream::Stderr,
        ) {
            Ok(handle) => handle,
            Err(error) => {
                context.capture_failed.store(true, Ordering::Release);
                let supervised = process.supervise(&cancellation, &context.capture_failed);
                let stdout = join_pump(stdout_handle, "stdout", &context.capture_failed);
                return Ok(ProcessOutput {
                    reason: supervised.reason,
                    status: supervised.status.map_err(|error| error.to_string()),
                    cleanup_error: supervised.cleanup_error,
                    stdout,
                    stderr: failed_capture(error),
                });
            }
        };

        let supervised = process.supervise(&cancellation, &context.capture_failed);
        let stdout = join_pump(stdout_handle, "stdout", &context.capture_failed);
        let stderr = join_pump(stderr_handle, "stderr", &context.capture_failed);
        Ok(ProcessOutput {
            reason: supervised.reason,
            status: supervised.status.map_err(|error| error.to_string()),
            cleanup_error: supervised.cleanup_error,
            stdout,
            stderr,
        })
    }
}

// ------------------------------------------------------------
// Concurrent Pipe Pumps
// ------------------------------------------------------------

fn spawn_pump<R>(
    reader: R,
    writer: Option<BudgetedArtifactWriter>,
    context: PumpContext,
    stream_name: &'static str,
    protocol_stream: ProtocolStream,
) -> Result<thread::JoinHandle<CapturedStream>, String>
where
    R: Read + Send + 'static,
{
    thread::Builder::new()
        .name(format!("vampire-{stream_name}-capture"))
        .spawn(move || {
            let outcome = catch_unwind(AssertUnwindSafe(|| {
                capture_stream(reader, writer, &context, stream_name, protocol_stream)
            }));
            match outcome {
                Ok(capture) => capture,
                Err(_) => {
                    context.capture_failed.store(true, Ordering::Release);
                    failed_capture(format!("{stream_name} capture thread panicked"))
                }
            }
        })
        .map_err(|error| format!("start Vampire {stream_name} capture thread: {error}"))
}

fn join_pump(
    handle: thread::JoinHandle<CapturedStream>,
    stream_name: &str,
    capture_failed: &AtomicBool,
) -> CapturedStream {
    match handle.join() {
        Ok(capture) => capture,
        Err(_) => {
            capture_failed.store(true, Ordering::Release);
            CapturedStream {
                protocol: ProtocolSummary::default(),
                diagnostic: Vec::new(),
                bytes_seen: 0,
                bytes_staged: 0,
                error: Some(format!("{stream_name} capture thread panicked")),
            }
        }
    }
}

fn failed_capture(error: String) -> CapturedStream {
    CapturedStream {
        protocol: ProtocolSummary::default(),
        diagnostic: Vec::new(),
        bytes_seen: 0,
        bytes_staged: 0,
        error: Some(error),
    }
}

fn capture_stream(
    mut reader: impl Read,
    mut writer: Option<BudgetedArtifactWriter>,
    context: &PumpContext,
    stream_name: &str,
    protocol_stream: ProtocolStream,
) -> CapturedStream {
    let mut parser = ProtocolParser::new(context.config.protocol_line_bytes);
    let mut protocol = ProtocolSummary::default();
    let mut diagnostic = BoundedDiagnostic::new(context.config.diagnostic_bytes);
    let mut buffer = [0_u8; READ_BUFFER_BYTES];
    let mut bytes_seen = 0_u64;
    let mut bytes_staged = 0_u64;
    let mut error = None;
    let mut sink_open = true;

    // Keep draining after staging fails. The supervisor observes the
    // failure flag and stops the process tree without leaving a full
    // pipe that can prevent the child from exiting.
    loop {
        match reader.read(&mut buffer) {
            Ok(0) => break,
            Ok(count) => {
                let bytes = &buffer[..count];
                bytes_seen = match bytes_seen.checked_add(count as u64) {
                    Some(total) => total,
                    None => {
                        set_capture_error(
                            &mut error,
                            &context.capture_failed,
                            format!("{stream_name} byte counter overflow"),
                        );
                        u64::MAX
                    }
                };
                diagnostic.push(bytes);
                parser.push(bytes, &mut |event| {
                    if let Some(next) = next_sequence(&context.sequence) {
                        protocol.observe(protocol_stream, next, event);
                    } else {
                        set_capture_error(
                            &mut error,
                            &context.capture_failed,
                            "Vampire protocol event sequence overflow".to_string(),
                        );
                    }
                });

                if sink_open {
                    let allowed = context.budget.reserve(count);
                    if allowed < count {
                        set_capture_error(
                            &mut error,
                            &context.capture_failed,
                            "Vampire output exceeded the configured capture limit".to_string(),
                        );
                        sink_open = false;
                    }
                    if allowed > 0
                        && let Some(writer) = writer.as_mut()
                    {
                        if let Err(write_error) = writer.write_all(&bytes[..allowed]) {
                            set_capture_error(
                                &mut error,
                                &context.capture_failed,
                                format!("write Vampire {stream_name} staging: {write_error}"),
                            );
                            sink_open = false;
                        } else {
                            bytes_staged = bytes_staged.saturating_add(allowed as u64);
                        }
                    }
                }
            }
            Err(read_error) if read_error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(read_error) => {
                set_capture_error(
                    &mut error,
                    &context.capture_failed,
                    format!("read Vampire {stream_name}: {read_error}"),
                );
                break;
            }
        }
    }

    parser.finish(&mut |event| {
        if let Some(next) = next_sequence(&context.sequence) {
            protocol.observe(protocol_stream, next, event);
        } else {
            set_capture_error(
                &mut error,
                &context.capture_failed,
                "Vampire protocol event sequence overflow".to_string(),
            );
        }
    });
    if sink_open
        && let Some(writer) = writer.as_mut()
        && let Err(flush_error) = writer.flush()
    {
        set_capture_error(
            &mut error,
            &context.capture_failed,
            format!("flush Vampire {stream_name} staging: {flush_error}"),
        );
    }
    CapturedStream {
        protocol,
        diagnostic: diagnostic.finish(),
        bytes_seen,
        bytes_staged,
        error,
    }
}

// ------------------------------------------------------------
// Bounded Capture State
// ------------------------------------------------------------

fn set_capture_error(
    destination: &mut Option<String>,
    capture_failed: &AtomicBool,
    message: String,
) {
    if destination.is_none() {
        *destination = Some(message);
    }
    capture_failed.store(true, Ordering::Release);
}

fn next_sequence(sequence: &AtomicU64) -> Option<u64> {
    sequence
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            current.checked_add(1)
        })
        .ok()
}

#[derive(Debug)]
struct OutputBudget {
    limit: Option<u64>,
    used: AtomicU64,
}

impl OutputBudget {
    fn new(limit: Option<u64>) -> Self {
        Self {
            limit,
            used: AtomicU64::new(0),
        }
    }

    fn reserve(&self, requested: usize) -> usize {
        let requested = u64::try_from(requested).unwrap_or(u64::MAX);
        let mut current = self.used.load(Ordering::Acquire);
        loop {
            let available = self
                .limit
                .map(|limit| limit.saturating_sub(current))
                .unwrap_or(u64::MAX.saturating_sub(current));
            let granted = requested.min(available);
            let next = current.saturating_add(granted);
            match self.used.compare_exchange_weak(
                current,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return usize::try_from(granted).unwrap_or(usize::MAX),
                Err(observed) => current = observed,
            }
        }
    }
}

#[derive(Debug)]
struct BoundedDiagnostic {
    first: Vec<u8>,
    last: VecDeque<u8>,
    first_limit: usize,
    last_limit: usize,
}

impl BoundedDiagnostic {
    fn new(limit: usize) -> Self {
        let first_limit = limit.div_ceil(2);
        Self {
            first: Vec::with_capacity(first_limit),
            last: VecDeque::with_capacity(limit - first_limit),
            first_limit,
            last_limit: limit - first_limit,
        }
    }

    fn push(&mut self, mut bytes: &[u8]) {
        let first_remaining = self.first_limit.saturating_sub(self.first.len());
        let first_count = first_remaining.min(bytes.len());
        self.first.extend_from_slice(&bytes[..first_count]);
        bytes = &bytes[first_count..];
        if self.last_limit == 0 {
            return;
        }
        for byte in bytes {
            if self.last.len() == self.last_limit {
                self.last.pop_front();
            }
            self.last.push_back(*byte);
        }
    }

    fn finish(self) -> Vec<u8> {
        let mut result = self.first;
        result.extend(self.last);
        result
    }
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    struct PanicReader;

    impl Read for PanicReader {
        fn read(&mut self, _buffer: &mut [u8]) -> std::io::Result<usize> {
            panic!("capture reader fixture panic")
        }
    }

    #[test]
    fn diagnostics_keep_bounded_head_and_tail() {
        let mut diagnostic = BoundedDiagnostic::new(6);
        diagnostic.push(b"abcdefghij");
        assert_eq!(diagnostic.finish(), b"abchij");
    }

    #[test]
    fn shared_output_budget_never_overbooks() {
        let budget = OutputBudget::new(Some(7));
        assert_eq!(budget.reserve(5), 5);
        assert_eq!(budget.reserve(5), 2);
        assert_eq!(budget.reserve(1), 0);
    }

    #[test]
    fn capture_thread_panic_sets_failure_before_join() {
        let context = PumpContext {
            config: CaptureConfig {
                diagnostic_bytes: 16,
                protocol_line_bytes: 16,
                max_total_output_bytes: None,
            },
            sequence: Arc::new(AtomicU64::new(0)),
            budget: Arc::new(OutputBudget::new(None)),
            capture_failed: Arc::new(AtomicBool::new(false)),
        };
        let handle = spawn_pump(
            PanicReader,
            None,
            context.clone(),
            "panic-fixture",
            ProtocolStream::Stdout,
        )
        .unwrap();
        let capture = handle.join().unwrap();
        assert!(context.capture_failed.load(Ordering::Acquire));
        assert_eq!(
            capture.error.as_deref(),
            Some("panic-fixture capture thread panicked")
        );
    }
}

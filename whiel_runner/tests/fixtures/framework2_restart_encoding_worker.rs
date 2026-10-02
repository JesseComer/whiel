//! First-process fault proxy for stateless fixed-ambient worker requests.
//!
//! The Rust pool appends the worker's required `worker` subcommand as the
//! final argument, so the proxy receives `WORKER STATE MARKER MODE worker`
//! and forwards only the subcommand to the wrapped Lean executable.

use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    let [worker, state, marker, mode, subcommand] = arguments.as_slice() else {
        panic!("usage: proxy WORKER STATE MARKER MODE worker");
    };
    assert_eq!(
        subcommand.to_string_lossy(),
        "worker",
        "the fixed-ambient pool must append the worker subcommand"
    );
    let first = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(state)
        .is_ok();
    let marker = PathBuf::from(marker);
    let mode = mode.to_string_lossy();

    let mut child = Command::new(worker)
        .arg("worker")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("start fixed-ambient encoding worker");
    let mut child_stdin = child.stdin.take().unwrap();
    let mut child_stdout = child.stdout.take().unwrap();
    let mut input = std::io::stdin().lock();
    let mut output = std::io::stdout().lock();

    while let Some(frame) = read_frame(&mut input) {
        let frame_text = String::from_utf8_lossy(&frame);
        let targeted = match mode.as_ref() {
            "fail_clause" | "stall_clause" => {
                frame_text.contains("\"operation\":\"admit_clauses\"")
            }
            // The ops the *ordinary* check path issues and replays after a
            // worker death. Since Pass 7.5d the controller assembles its
            // obligation from cached opaque pieces, so
            // `prepare_exact_obligation` is issued only by the assembly
            // differential and targeting it would prove nothing about the
            // production path. `prepare_clause_pieces` comes first in every
            // run; `check_empty_counterexample` is here so the fixture
            // covers the second worker call the ordinary path makes.
            "stall_prepare" | "fail_after_prepare" => {
                frame_text.contains("\"operation\":\"prepare_clause_pieces\"")
                    || frame_text.contains("\"operation\":\"check_empty_counterexample\"")
            }
            // The agent counterexample call. `capture` records the exact
            // request frame and still forwards it, so a test can prove the
            // opaque instance reached Lean unmodified as a JSON value;
            // `stall_counterexample` never answers, so the host's
            // call-local validation limit has to terminate this worker.
            "capture_counterexample" | "stall_counterexample" => {
                frame_text.contains("\"operation\":\"validate_counterexample\"")
            }
            _ => panic!("unknown proxy mode {mode}"),
        };
        if targeted && mode == "capture_counterexample" && first {
            fs::write(&marker, &frame).expect("record the counterexample request frame");
        }
        if first && targeted && !matches!(mode.as_ref(), "fail_after_prepare" | "capture_counterexample")
        {
            fs::write(&marker, std::process::id().to_string())
                .expect("write fixed-ambient fault marker");
            if mode.starts_with("stall_") {
                loop {
                    thread::sleep(Duration::from_secs(60));
                }
            }
            let _ = child.kill();
            let _ = child.wait();
            return;
        }
        write_frame(&mut child_stdin, &frame);
        let response =
            read_frame(&mut child_stdout).expect("fixed-ambient worker closed before replying");
        if targeted && mode == "fail_after_prepare" {
            if first {
                fs::write(&marker, &response)
                    .expect("record completed pre-death fixed-ambient response");
                let _ = child.kill();
                let _ = child.wait();
                return;
            }
            let replay = marker.with_extension("replayed");
            let _ = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(replay)
                .and_then(|mut file| file.write_all(&response));
        }
        write_frame(&mut output, &response);
        if frame_text.contains("\"operation\":\"shutdown\"") {
            break;
        }
    }
    drop(child_stdin);
    let _ = child.wait();
}

fn read_frame(reader: &mut impl Read) -> Option<Vec<u8>> {
    let mut header = [0_u8; 4];
    match reader.read_exact(&mut header) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::UnexpectedEof => return None,
        Err(error) => panic!("read frame header: {error}"),
    }
    let length = u32::from_be_bytes(header) as usize;
    let mut payload = vec![0_u8; length];
    reader.read_exact(&mut payload).expect("read frame payload");
    Some(payload)
}

fn write_frame(writer: &mut impl Write, payload: &[u8]) {
    writer
        .write_all(&(payload.len() as u32).to_be_bytes())
        .expect("write frame header");
    writer.write_all(payload).expect("write frame payload");
    writer.flush().expect("flush frame");
}

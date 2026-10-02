//! Proxy a real encoding worker but corrupt one gated support reply.

use std::fs;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

fn main() {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    let [worker, gate, fault_marker, context] = arguments.as_slice() else {
        panic!("usage: proxy <worker> <gate> <fault-marker> <context-id>");
    };
    let gate = PathBuf::from(gate);
    let fault_marker = PathBuf::from(fault_marker);

    let mut child = Command::new(worker)
        .arg(context)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("start real encoding worker");
    let mut child_stdin = child.stdin.take().unwrap();
    let mut child_stdout = child.stdout.take().unwrap();
    let mut input = std::io::stdin().lock();
    let mut output = std::io::stdout().lock();

    while let Some(frame) = read_frame(&mut input) {
        let request = String::from_utf8_lossy(&frame);
        if request.contains("\"operation\":\"prepare_support\"")
            && request.contains("\"num:10\"")
            && request.contains("\"str:mixed\"")
        {
            fs::write(&fault_marker, &frame).expect("write support-failure marker");
            let deadline = Instant::now() + Duration::from_secs(60);
            while !gate.exists() {
                assert!(
                    Instant::now() < deadline,
                    "support-failure gate was not opened"
                );
                thread::sleep(Duration::from_millis(5));
            }
            write_frame(&mut output, b"not-json");
            return;
        }
        write_frame(&mut child_stdin, &frame);
        let response =
            read_frame(&mut child_stdout).expect("real encoding worker closed before replying");
        write_frame(&mut output, &response);
        if request.contains("\"operation\":\"shutdown\"") {
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
        Err(error) if error.kind() == std::io::ErrorKind::UnexpectedEof => {
            return None;
        }
        Err(error) => panic!("read frame header: {error}"),
    }
    let mut frame = vec![0_u8; u32::from_be_bytes(header) as usize];
    reader.read_exact(&mut frame).expect("read frame body");
    Some(frame)
}

fn write_frame(writer: &mut impl Write, frame: &[u8]) {
    writer
        .write_all(&(frame.len() as u32).to_be_bytes())
        .expect("write frame header");
    writer.write_all(frame).expect("write frame body");
    writer.flush().expect("flush frame");
}

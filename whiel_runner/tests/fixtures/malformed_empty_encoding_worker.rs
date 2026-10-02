//! Proxy a real encoding worker but corrupt or stall empty-check replies.

use std::fs;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    let (worker, marker, context) = match arguments.as_slice() {
        [worker, context] => (worker, None, context),
        [worker, marker, context] => (worker, Some(PathBuf::from(marker)), context),
        _ => panic!("usage: proxy <worker> [empty-stall-marker] <context-id>"),
    };

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
        if String::from_utf8_lossy(&frame)
            .contains("check_empty_counterexample")
        {
            if let Some(marker) = &marker {
                fs::write(marker, b"empty-check-started").expect("write stall marker");
                loop {
                    thread::sleep(Duration::from_secs(60));
                }
            }
            write_frame(&mut output, b"not-json");
            continue;
        }
        write_frame(&mut child_stdin, &frame);
        let response = read_frame(&mut child_stdout)
            .expect("real encoding worker closed before replying");
        write_frame(&mut output, &response);
        if String::from_utf8_lossy(&frame).contains("\"shutdown\"") {
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

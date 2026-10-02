//! Test-only worker that accepts one frame and then stalls until killed.

use std::fs;
use std::io::Read;
use std::process::Command;
use std::thread;
use std::time::Duration;

fn main() {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    if arguments.first().is_some_and(|value| value == "--child") {
        let marker = arguments
            .get(1)
            .expect("usage: stalling_encoding_worker --child CHILD_MARKER");
        fs::write(marker, std::process::id().to_string()).expect("write child PID marker");
        thread::sleep(Duration::from_secs(60));
        return;
    }

    let marker = arguments
        .first()
        .expect("usage: stalling_encoding_worker MARKER [CHILD_MARKER] CONTEXT");
    let _child = if arguments.len() == 3 {
        let child_marker = &arguments[1];
        let child = Command::new(std::env::current_exe().expect("current worker executable"))
            .arg("--child")
            .arg(child_marker)
            .spawn()
            .expect("spawn descendant fixture");
        for _ in 0..500 {
            if std::path::Path::new(child_marker).exists() {
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
        assert!(
            std::path::Path::new(child_marker).exists(),
            "descendant must publish its PID before the parent marker"
        );
        Some(child)
    } else {
        None
    };
    fs::write(marker, std::process::id().to_string()).expect("write worker PID marker");

    let mut header = [0_u8; 4];
    std::io::stdin()
        .read_exact(&mut header)
        .expect("read request header");
    let length = u32::from_be_bytes(header) as usize;
    let mut payload = vec![0_u8; length];
    std::io::stdin()
        .read_exact(&mut payload)
        .expect("read request payload");
    thread::sleep(Duration::from_secs(60));
}

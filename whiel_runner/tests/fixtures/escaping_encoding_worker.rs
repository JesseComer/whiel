//! Test-only encoding worker with a session-escaping stderr holder.

use std::fs;
use std::io::Read;
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

#[cfg(unix)]
unsafe extern "C" {
    fn setsid() -> i32;
}

fn main() {
    let arguments = std::env::args_os().collect::<Vec<_>>();
    if arguments.get(1).is_some_and(|argument| argument == "--child") {
        escape_and_hold_stderr(&arguments[2]);
    }

    let leader_marker = arguments
        .get(1)
        .expect("usage: escaping_encoding_worker LEADER CHILD CONTEXT");
    let child_marker = arguments
        .get(2)
        .expect("usage: escaping_encoding_worker LEADER CHILD CONTEXT");
    fs::write(leader_marker, std::process::id().to_string()).expect("write leader PID marker");

    let mut child = Command::new(std::env::current_exe().expect("resolve fixture executable"));
    child
        .arg("--child")
        .arg(child_marker)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::inherit());
    child.spawn().expect("spawn session-escaping child");

    let mut header = [0_u8; 4];
    std::io::stdin()
        .read_exact(&mut header)
        .expect("read request header");
    let length = u32::from_be_bytes(header) as usize;
    let mut payload = vec![0_u8; length];
    std::io::stdin()
        .read_exact(&mut payload)
        .expect("read request payload");
    loop {
        thread::sleep(Duration::from_secs(1));
    }
}

fn escape_and_hold_stderr(marker: &std::ffi::OsStr) -> ! {
    #[cfg(unix)]
    {
        let result = unsafe { setsid() };
        assert!(result >= 0, "setsid failed: {}", std::io::Error::last_os_error());
    }
    fs::write(marker, std::process::id().to_string()).expect("write child PID marker");
    loop {
        eprintln!("holding the encoding worker stderr pipe");
        thread::sleep(Duration::from_millis(50));
    }
}

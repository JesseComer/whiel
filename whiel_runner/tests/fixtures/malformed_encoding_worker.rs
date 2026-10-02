//! Test-only worker that returns a length-valid, non-JSON response.

use std::io::{Read, Write};

fn main() {
    let mut header = [0_u8; 4];
    std::io::stdin()
        .read_exact(&mut header)
        .expect("read request header");
    let length = u32::from_be_bytes(header) as usize;
    let mut payload = vec![0_u8; length];
    std::io::stdin()
        .read_exact(&mut payload)
        .expect("read request payload");

    let response = b"not-json";
    let mut stdout = std::io::stdout().lock();
    stdout
        .write_all(&(response.len() as u32).to_be_bytes())
        .expect("write response header");
    stdout.write_all(response).expect("write response payload");
    stdout.flush().expect("flush response");
}

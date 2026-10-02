//! First-process fault proxy followed by a transparent persistent worker.

use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

fn main() {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    let [worker, state, marker, mode, context] = arguments.as_slice() else {
        panic!("usage: proxy WORKER STATE MARKER MODE CONTEXT");
    };
    let first = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(state)
        .is_ok();
    let marker = PathBuf::from(marker);
    let mode = mode.to_string_lossy();

    if !first && mode == "gate_first_partial" {
        let old_pid = fs::read_to_string(marker.join("first_page.ready"))
            .expect("read retained worker PID marker");
        let old_alive = Command::new("kill")
            .args(["-0", old_pid.trim()])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .expect("probe retained worker PID")
            .success();
        if old_alive {
            fs::write(marker.join("replacement.overlap"), b"overlap")
                .expect("record an early replacement launch");
        }
        fs::write(
            marker.join("replacement.started"),
            std::process::id().to_string(),
        )
        .expect("write replacement launch marker");
    }

    if mode == "count" || mode == "synthetic_proposal_count" {
        let mut launches = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&marker)
            .expect("open launch-count marker");
        writeln!(launches, "launch:{}", std::process::id()).expect("record proxy launch");
    }

    if first && mode == "stall" {
        let mut input = std::io::stdin().lock();
        let _request = read_frame(&mut input).expect("read first registration request");
        fs::write(&marker, std::process::id().to_string()).expect("write worker PID marker");
        loop {
            thread::sleep(Duration::from_secs(60));
        }
    }

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
    let mut relayed_partial_page = false;
    let mut corrupted_partial_page = false;

    while let Some(frame) = read_frame(&mut input) {
        let registration = String::from_utf8_lossy(&frame)
            .contains("\"operation\":\"register_reference_proposal\"");
        if mode == "synthetic_proposal_count" && registration {
            let request = String::from_utf8(frame).expect("worker request must be UTF-8 JSON");
            let stage = json_number(&request, "stage");
            let mut events = OpenOptions::new()
                .append(true)
                .open(&marker)
                .expect("open synthetic proposal-count marker");
            writeln!(events, "stage:{}:{stage}", std::process::id())
                .expect("record synthetic proposal stage");
            write_frame(
                &mut output,
                synthetic_empty_proposal_response(&request).as_bytes(),
            );
            continue;
        }
        if mode == "count" && registration {
            let mut events = OpenOptions::new()
                .append(true)
                .open(&marker)
                .expect("open page-count marker");
            writeln!(events, "page").expect("record registration page");
        }
        if first && mode == "stall_after_partial" && registration && relayed_partial_page {
            fs::write(&marker, std::process::id().to_string())
                .expect("write partial-page stall marker");
            loop {
                thread::sleep(Duration::from_secs(60));
            }
        }
        if first
            && mode == "fail_first_prepare"
            && String::from_utf8_lossy(&frame).contains("\"operation\":\"prepare_bodies\"")
        {
            fs::write(&marker, std::process::id().to_string())
                .expect("write failed-prepare marker");
            let _ = child.kill();
            let _ = child.wait();
            return;
        }
        let synthetic_prepare_revision = (mode == "synthetic_proposal_count"
            && String::from_utf8_lossy(&frame).contains("\"operation\":\"prepare_bodies\""))
        .then(|| {
            json_number(
                std::str::from_utf8(&frame).expect("worker request must be UTF-8 JSON"),
                "proposal_revision",
            )
            .to_string()
        });
        let forwarded_frame = match synthetic_prepare_revision.as_ref() {
            Some(_) => replace_json_number(frame.clone(), "proposal_revision", "0"),
            None => frame.clone(),
        };
        write_frame(&mut child_stdin, &forwarded_frame);
        let mut response =
            read_frame(&mut child_stdout).expect("real encoding worker closed before replying");
        if let Some(revision) = synthetic_prepare_revision {
            response = replace_json_number(response, "request_proposal_revision", &revision);
            response = replace_json_number(response, "proposal_revision", &revision);
        }
        if first && mode == "reject_after_partial" && registration && relayed_partial_page {
            response = invalidate_proposal_version(response);
            fs::write(&marker, std::process::id().to_string())
                .expect("write rejected partial-session PID marker");
            write_frame(&mut output, &response);
            loop {
                thread::sleep(Duration::from_secs(60));
            }
        }
        if first
            && mode == "corrupt_partial"
            && registration
            && !corrupted_partial_page
            && (String::from_utf8_lossy(&response).contains("\"complete\":false")
                || String::from_utf8_lossy(&response).contains("\"complete\": false"))
        {
            response = corrupt_first_fragment(response);
            corrupted_partial_page = true;
        }
        if first
            && (mode == "reject" || mode == "reject_concurrent")
            && String::from_utf8_lossy(&frame)
                .contains("\"operation\":\"register_reference_proposal\"")
        {
            response = invalidate_proposal_version(response);
            if mode == "reject_concurrent" {
                fs::write(marker.join("registration.ready"), b"ready")
                    .expect("write registration-ready marker");
                wait_for(&marker.join("registration.release"));
            } else {
                fs::write(&marker, std::process::id().to_string())
                    .expect("write rejected worker PID marker");
            }
            write_frame(&mut output, &response);
            loop {
                thread::sleep(Duration::from_secs(60));
            }
        }
        if first
            && (mode == "stall_after_partial" || mode == "reject_after_partial")
            && registration
        {
            let response_text = String::from_utf8_lossy(&response);
            assert!(
                response_text.contains("\"complete\":false")
                    || response_text.contains("\"complete\": false"),
                "the configured first proposal page must be nonterminal"
            );
            relayed_partial_page = true;
        }
        if first && mode == "gate_first_partial" && registration && !relayed_partial_page {
            let response_text = String::from_utf8_lossy(&response);
            assert!(
                response_text.contains("\"complete\":false")
                    || response_text.contains("\"complete\": false"),
                "the gated first proposal page must be nonterminal"
            );
            fs::create_dir_all(&marker).expect("create first-page gate directory");
            fs::write(
                marker.join("first_page.ready"),
                std::process::id().to_string(),
            )
            .expect("write first-page ready marker");
            wait_for(&marker.join("first_page.release"));
            relayed_partial_page = true;
        }
        if !first
            && mode == "reject_concurrent"
            && String::from_utf8_lossy(&frame).contains("\"operation\":\"prepare_bodies\"")
        {
            fs::write(marker.join("reader.ready"), b"ready").expect("write reader-ready marker");
            wait_for(&marker.join("reader.release"));
        }
        write_frame(&mut output, &response);
        if String::from_utf8_lossy(&frame).contains("\"operation\":\"shutdown\"") {
            break;
        }
    }
    drop(child_stdin);
    let _ = child.wait();
}

fn wait_for(path: &PathBuf) {
    let deadline = Instant::now() + Duration::from_secs(60);
    while !path.exists() {
        assert!(Instant::now() < deadline, "fixture gate was not opened");
        thread::sleep(Duration::from_millis(5));
    }
}

fn invalidate_proposal_version(response: Vec<u8>) -> Vec<u8> {
    let mut text = String::from_utf8(response).expect("worker response must be UTF-8 JSON");
    let key = "\"version\":";
    let start = text
        .find(key)
        .map(|offset| offset + key.len())
        .expect("reference-proposal response lacks its operation-local version");
    let digits_start = start
        + text[start..]
            .find(|character: char| !character.is_ascii_whitespace())
            .expect("reference-proposal version has no value");
    let digits_end = digits_start
        + text[digits_start..]
            .find(|character: char| !character.is_ascii_digit())
            .unwrap_or(text.len() - digits_start);
    assert!(
        digits_end > digits_start,
        "reference-proposal version is not numeric"
    );
    text.replace_range(digits_start..digits_end, "999");
    text.into_bytes()
}

fn corrupt_first_fragment(response: Vec<u8>) -> Vec<u8> {
    let text = String::from_utf8(response).expect("worker response must be UTF-8 JSON");
    for pattern in ["\"fragment\":\"[", "\"fragment\": \"["] {
        if text.contains(pattern) {
            return text
                .replacen(pattern, &pattern.replace('[', "{"), 1)
                .into_bytes();
        }
    }
    panic!("nonterminal reference-proposal response lacks its first fragment");
}

fn synthetic_empty_proposal_response(request: &str) -> String {
    let request_proposal_revision = json_number(request, "proposal_revision");
    let proposal_revision = request_proposal_revision
        .parse::<u64>()
        .expect("parse proposal revision")
        .checked_add(1)
        .expect("advance proposal revision");
    format!(
        concat!(
            "{{",
            "\"format_version\":{},",
            "\"semantic_version\":{},",
            "\"encoding_version\":{},",
            "\"task_canonical_id\":{},",
            "\"task_module\":{},",
            "\"task_namespace\":{},",
            "\"task_source_sha256\":{},",
            "\"request_id\":{},",
            "\"context_id\":{},",
            "\"operation\":\"register_reference_proposal\",",
            "\"request_name_env_revision\":{},",
            "\"name_env_revision\":{},",
            "\"request_proposal_revision\":{},",
            "\"proposal_revision\":{},",
            "\"status\":\"ok\",",
            "\"payload\":{{",
            "\"realization_id\":{},",
            "\"realization_version\":{},",
            "\"version\":{},",
            "\"stage\":{},",
            "\"cursor\":0,",
            "\"next_cursor\":2,",
            "\"complete\":true,",
            "\"raw_occurrences\":0,",
            "\"canonical_formulas\":0,",
            "\"canonical_duplicates\":0,",
            "\"emitted_formulas\":0,",
            "\"fast_work\":[0,0,0,0],",
            "\"fragment\":\"[]\"",
            "}},",
            "\"error\":null",
            "}}"
        ),
        json_number(request, "format_version"),
        json_number(request, "semantic_version"),
        json_number(request, "encoding_version"),
        json_raw(request, "task_canonical_id"),
        json_raw(request, "task_module"),
        json_raw(request, "task_namespace"),
        json_raw(request, "task_source_sha256"),
        json_number(request, "request_id"),
        json_raw(request, "context_id"),
        json_number(request, "name_env_revision"),
        json_number(request, "name_env_revision"),
        request_proposal_revision,
        proposal_revision,
        json_raw(request, "realization_id"),
        json_number(request, "realization_version"),
        json_number(request, "version"),
        json_number(request, "stage"),
    )
}

fn json_number<'a>(json: &'a str, key: &str) -> &'a str {
    let value = json_value_start(json, key);
    let length = value.bytes().take_while(u8::is_ascii_digit).count();
    assert!(length > 0, "JSON field {key:?} is not numeric");
    &value[..length]
}

fn json_raw<'a>(json: &'a str, key: &str) -> &'a str {
    let value = json_value_start(json, key);
    assert!(value.starts_with('"'), "JSON field {key:?} is not a string");
    let mut escaped = false;
    for (offset, character) in value[1..].char_indices() {
        if character == '"' && !escaped {
            return &value[..offset + 2];
        }
        escaped = character == '\\' && !escaped;
        if character != '\\' {
            escaped = false;
        }
    }
    panic!("JSON string field {key:?} is unterminated");
}

fn json_value_start<'a>(json: &'a str, key: &str) -> &'a str {
    let needle = format!("\"{key}\":");
    let start = json
        .find(&needle)
        .map(|offset| offset + needle.len())
        .unwrap_or_else(|| panic!("JSON field {key:?} is missing"));
    json[start..].trim_start()
}

fn replace_json_number(bytes: Vec<u8>, key: &str, replacement: &str) -> Vec<u8> {
    let mut json = String::from_utf8(bytes).expect("worker frame must be UTF-8 JSON");
    let needle = format!("\"{key}\":");
    let start = json
        .find(&needle)
        .map(|offset| offset + needle.len())
        .unwrap_or_else(|| panic!("JSON field {key:?} is missing"));
    let digits_start = start
        + json[start..]
            .find(|character: char| !character.is_ascii_whitespace())
            .expect("JSON number has no value");
    let digits_end = digits_start
        + json[digits_start..]
            .find(|character: char| !character.is_ascii_digit())
            .unwrap_or(json.len() - digits_start);
    assert!(
        digits_end > digits_start,
        "JSON field {key:?} is not numeric"
    );
    json.replace_range(digits_start..digits_end, replacement);
    json.into_bytes()
}

fn read_frame(reader: &mut impl Read) -> Option<Vec<u8>> {
    let mut header = [0_u8; 4];
    match reader.read_exact(&mut header) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::UnexpectedEof => return None,
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

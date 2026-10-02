//! Real public CLI/Lean admission gates for campaign-wide API resource failure.

#![cfg(unix)]

use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

struct Fixture {
    repository: PathBuf,
    root: PathBuf,
    python: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .to_path_buf();
        let python = Command::new("python3")
            .args(["-I", "-c", "import sys; print(sys.executable)"])
            .output()
            .unwrap();
        assert!(python.status.success());
        let python = PathBuf::from(String::from_utf8(python.stdout).unwrap().trim());
        let root = std::env::temp_dir().join(format!(
            "whiel-campaign-api-resource-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        Self {
            repository,
            root,
            python,
        }
    }

    fn run(
        &self,
        label: &str,
        limits: &[&str],
        pad_bytes: u64,
        inputs: &str,
    ) -> (Value, Vec<Value>) {
        let evidence = self.root.join(label);
        fs::create_dir(&evidence).unwrap();
        let campaign = evidence.join("campaign");
        let trace = evidence.join("trace.jsonl");
        let output = Command::new("bash")
            .arg(self.repository.join("scripts/watchdog.sh"))
            .args([
                "4194304",
                env!("CARGO_BIN_EXE_whiel-symbolic"),
                "campaign",
                "run",
            ])
            .arg("--repo")
            .arg(&self.repository)
            .args([
                "--input",
                inputs,
                "--iteration-limit",
                "1",
                "--consultation-limit",
                "60",
                "--search-limit",
                "120",
            ])
            .arg("--destination")
            .arg(&campaign)
            .arg("--worker")
            .arg(
                self.repository
                    .join(".lake/build/bin/fixed_ambient_encoding_worker"),
            )
            .arg("--proposer-executable")
            .arg(&self.python)
            .args(["--proposer-arg", "-I", "--proposer-arg"])
            .arg(
                self.repository
                    .join("whiel_runner/tests/fixtures/generic_campaign_exhausted.py"),
            )
            .arg("--proposer-arg")
            .arg(&trace)
            .arg("--proposer-arg")
            .arg(pad_bytes.to_string())
            .args(limits)
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&self.repository)
            .output()
            .unwrap();
        fs::write(evidence.join("stdout.log"), &output.stdout).unwrap();
        fs::write(evidence.join("stderr.log"), &output.stderr).unwrap();
        assert_eq!(
            output.status.code(),
            Some(3),
            "{}: {output:?}",
            evidence.display()
        );
        let summary: Value =
            serde_json::from_slice(&fs::read(campaign.join("summary.json")).unwrap()).unwrap();
        let events = fs::read_to_string(&trace)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect::<Vec<Value>>();
        println!("campaign API resource evidence: {}", evidence.display());
        (summary, events)
    }

    fn assert_exhausted(&self, label: &str, summary: &Value, events: &[Value], shutdown: bool) {
        assert_eq!(summary["schema_version"], 3);
        assert_eq!(summary["all_certified"], false);
        assert_eq!(summary["interrupted"], false);
        let detail = summary["resource_failure"]
            .as_str()
            .expect("missing API resource cause");
        assert!(detail.contains("API traffic allowance"));
        assert_eq!(summary["results"].as_array().unwrap().len(), 1);
        assert_eq!(summary["results"][0]["status"], "resource_exhausted");
        assert_eq!(summary["results"][0]["detail"], detail);
        assert!(summary["results"][0]["failure_kind"].is_null());
        assert_eq!(summary["unrun_inputs"], serde_json::json!(["Example0013"]));
        assert!(!self.root.join(label).join("campaign/Example0013").exists());
        assert_eq!(
            events
                .iter()
                .filter(|event| event["kind"] == "started")
                .count(),
            1
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| event["kind"] == "request_closed")
                .count(),
            usize::from(shutdown)
        );
        assert!(!events.iter().any(|event| event["kind"] == "shutdown"));
        assert!(
            !self
                .root
                .join(label)
                .join("campaign/Example0001/Certificate")
                .exists()
        );
        for event in events.iter().filter(|event| event["kind"] == "started") {
            let pid = event["pid"].as_i64().unwrap() as libc::pid_t;
            assert_eq!(unsafe { libc::kill(pid, 0) }, -1, "endpoint remains alive");
            assert_eq!(
                std::io::Error::last_os_error().raw_os_error(),
                Some(libc::ESRCH)
            );
        }
    }
}

#[test]
fn message_and_byte_exhaustion_at_shutdown_stop_later_inputs() {
    let fixture = Fixture::new();
    let (control, control_events) = fixture.run("ordinary-exhaustion", &[], 0, "Example0001");
    assert!(control["resource_failure"].is_null());
    assert_eq!(control["results"][0]["status"], "incomplete");
    assert_eq!(
        control["results"][0]["failure_kind"],
        "IterationLimitExhausted"
    );
    assert!(control_events.iter().any(|event| event["kind"] == "closed"));
    let (messages, events) = fixture.run(
        "shutdown-messages",
        &["--api-messages", "5"],
        0,
        "Example0001,Example0013",
    );
    fixture.assert_exhausted("shutdown-messages", &messages, &events, true);
    let closing_bytes = events
        .iter()
        .find(|event| event["kind"] == "request_closed")
        .unwrap()["bytes"]
        .as_u64()
        .unwrap();
    let byte_limit = closing_bytes + 256;
    let byte_text = byte_limit.to_string();
    let (bytes, events) = fixture.run(
        "shutdown-bytes",
        &["--api-traffic-bytes", &byte_text],
        byte_limit,
        "Example0001,Example0013",
    );
    fixture.assert_exhausted("shutdown-bytes", &bytes, &events, true);
    let actual_bytes = events
        .iter()
        .find(|event| event["kind"] == "request_closed")
        .unwrap()["bytes"]
        .as_u64()
        .unwrap();
    assert_eq!(
        actual_bytes + 1,
        byte_limit,
        "shutdown was the first refused packet"
    );
}

#[test]
fn startup_api_exhaustion_stops_later_inputs() {
    let fixture = Fixture::new();
    for (label, limits) in [
        ("startup-messages", ["--api-messages", "1"]),
        ("startup-bytes", ["--api-traffic-bytes", "1"]),
    ] {
        let (summary, events) = fixture.run(label, &limits, 0, "Example0001,Example0013");
        fixture.assert_exhausted(label, &summary, &events, false);
    }
}

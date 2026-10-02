#![allow(dead_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use whiel_runner::SynthesisTask;

// ------------------------------------------------------------
// Shared Test State And Temporary Directories
// ------------------------------------------------------------

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
static TASK_EXPORTS: OnceLock<String> = OnceLock::new();
static FAKE_VAMPIRE: OnceLock<PathBuf> = OnceLock::new();
static EXAMPLE_ENCODING_WORKER: OnceLock<PathBuf> = OnceLock::new();
static STALLING_ENCODING_WORKER: OnceLock<PathBuf> = OnceLock::new();
static MALFORMED_ENCODING_WORKER: OnceLock<PathBuf> = OnceLock::new();
static MALFORMED_EMPTY_ENCODING_WORKER: OnceLock<PathBuf> = OnceLock::new();
static GATED_MALFORMED_SUPPORT_ENCODING_WORKER: OnceLock<PathBuf> = OnceLock::new();
static RESTARTABLE_ENCODING_WORKER: OnceLock<PathBuf> = OnceLock::new();

pub struct TestDir {
    path: PathBuf,
}

impl TestDir {
    pub fn new(label: &str) -> Self {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must follow Unix epoch")
            .as_nanos();
        let sequence = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "whiel_runner_{label}_{}_{}_{}",
            std::process::id(),
            nanos,
            sequence
        ));
        fs::create_dir_all(&path).expect("create test directory");
        Self { path }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

// ------------------------------------------------------------
// Synthetic Task Fixture
// ------------------------------------------------------------

pub fn sample_task() -> SynthesisTask {
    SynthesisTask::from_json(
        r#"{
          "format_version": 3,
          "semantic_version": 1,
          "encoding_version": 1,
          "identity": {
            "canonical_id": "Example0012",
            "module": "Benchmark.Example0012.Input",
            "namespace": "Whiel.Benchmark.Example0012",
            "source_sha256": "6fe56e9493eefa68d69085d1602adda3a0d522d964f1a8bf6ef3996f08cd3195"
          },
          "schema": {"expression":"Whiel.Benchmark.Example0012.programSchema","display":"{R (arity: 2)}"},
          "original": {
            "pre":{"expression":"Whiel.Benchmark.Example0012.inputPre","display":"true"},
            "command":{"expression":"Whiel.Benchmark.Example0012.inputCmd","display":"SKIP"},
            "post":{"expression":"Whiel.Benchmark.Example0012.inputPost","display":"true"}
          },
          "preprocessed": {
            "pre":{"expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre","display":"true"},
            "command":{"expression":"Whiel.Benchmark.Example0012.inputPreproc.loopCmd","display":"WHILE true DO SKIP END"},
            "post":{"expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost","display":"true"}
          },
          "preprocessing_evidence":{"expression":"Whiel.Benchmark.Example0012.inputPreproc"},
          "solver": {
            "schema_relations": [
              {"key":"rel:E:0","arity":2},
              {"key":"rel:T:0","arity":2},
              {"key":"rel:T:1","arity":2},
              {"key":"rel:TBound:0","arity":2}
            ],
            "task_constants": [],
            "preprocessed_pre": {
              "source_id":"task.preprocessed_pre",
              "expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre",
              "no_bound_expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPre_noBound",
              "constants":[],
              "relations":["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"]
            },
            "preprocessed_post": {
              "source_id":"task.preprocessed_post",
              "expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost",
              "no_bound_expression":"Whiel.Benchmark.Example0012.inputPreproc.loopPost_noBound",
              "constants":[],
              "relations":["rel:E:0", "rel:T:0", "rel:TBound:0"]
            },
            "loop_guard": {
              "source_id":"task.loop_guard",
              "constants":[],
              "relations":["rel:T:0", "rel:TBound:0"]
            },
            "negated_loop_guard": {
              "source_id":"task.negated_loop_guard",
              "constants":[],
              "relations":["rel:T:0", "rel:TBound:0"]
            }
          }
        }"#,
    )
    .expect("sample task must be valid")
}

// ------------------------------------------------------------
// Lean Task Export Fixture
// ------------------------------------------------------------

pub fn export_canonical_task() -> SynthesisTask {
    SynthesisTask::from_json(task_export()).expect("Rust must accept the Lean task export")
}

pub fn export_canonical_task_json() -> &'static str {
    task_export()
}

// ------------------------------------------------------------
// Fake Vampire Fixture
// ------------------------------------------------------------

pub fn fake_vampire() -> &'static Path {
    FAKE_VAMPIRE
        .get_or_init(|| {
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let source = manifest.join("tests/fixtures/fake_vampire.rs");
            let output_directory = manifest.join("target/test-fixtures");
            fs::create_dir_all(&output_directory).expect("create fixture output directory");
            // Each integration-test binary has its own `OnceLock`. Give each
            // process a private output path so parallel test binaries cannot
            // overwrite rustc's temporary files while compiling this fixture.
            let executable = output_directory.join(format!("fake-vampire-{}", std::process::id()));
            let output = Command::new("rustc")
                .args(["--edition", "2024"])
                .arg(&source)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("compile fake Vampire fixture");
            assert!(
                output.status.success(),
                "fake Vampire compile failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            executable
        })
        .as_path()
}

// ------------------------------------------------------------
// Persistent Lean Encoding-Worker Fixture
// ------------------------------------------------------------

pub fn example_encoding_worker() -> &'static Path {
    EXAMPLE_ENCODING_WORKER
        .get_or_init(|| {
            let repo = repo_root();
            let build = Command::new("lake")
                .args(["build", "example0012_encoding_worker"])
                .current_dir(&repo)
                .output()
                .expect("build Example0012 encoding worker");
            assert!(
                build.status.success(),
                "Lean encoding-worker build failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&build.stdout),
                String::from_utf8_lossy(&build.stderr)
            );
            repo.join(".lake/build/bin/example0012_encoding_worker")
        })
        .as_path()
}

pub fn stalling_encoding_worker() -> &'static Path {
    STALLING_ENCODING_WORKER
        .get_or_init(|| {
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let source = manifest.join("tests/fixtures/stalling_encoding_worker.rs");
            let output_directory = manifest.join("target/test-fixtures");
            fs::create_dir_all(&output_directory).expect("create fixture output directory");
            let executable =
                output_directory.join(format!("stalling-encoding-worker-{}", std::process::id()));
            let output = Command::new("rustc")
                .args(["--edition", "2024"])
                .arg(&source)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("compile stalling encoding-worker fixture");
            assert!(
                output.status.success(),
                "stalling worker compile failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            executable
        })
        .as_path()
}

pub fn malformed_encoding_worker() -> &'static Path {
    MALFORMED_ENCODING_WORKER
        .get_or_init(|| {
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let source = manifest.join("tests/fixtures/malformed_encoding_worker.rs");
            let output_directory = manifest.join("target/test-fixtures");
            fs::create_dir_all(&output_directory).expect("create fixture output directory");
            let executable =
                output_directory.join(format!("malformed-encoding-worker-{}", std::process::id()));
            let output = Command::new("rustc")
                .args(["--edition", "2024"])
                .arg(&source)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("compile malformed encoding-worker fixture");
            assert!(
                output.status.success(),
                "malformed worker compile failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            executable
        })
        .as_path()
}

pub fn malformed_empty_encoding_worker() -> &'static Path {
    MALFORMED_EMPTY_ENCODING_WORKER
        .get_or_init(|| {
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let source = manifest.join("tests/fixtures/malformed_empty_encoding_worker.rs");
            let output_directory = manifest.join("target/test-fixtures");
            fs::create_dir_all(&output_directory).expect("create fixture output directory");
            let executable = output_directory.join(format!(
                "malformed-empty-encoding-worker-{}",
                std::process::id()
            ));
            let output = Command::new("rustc")
                .args(["--edition", "2024"])
                .arg(&source)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("compile malformed-empty worker fixture");
            assert!(
                output.status.success(),
                "malformed-empty worker compile failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            executable
        })
        .as_path()
}

pub fn gated_malformed_support_encoding_worker() -> &'static Path {
    GATED_MALFORMED_SUPPORT_ENCODING_WORKER
        .get_or_init(|| {
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let source = manifest.join("tests/fixtures/gated_malformed_support_encoding_worker.rs");
            let output_directory = manifest.join("target/test-fixtures");
            fs::create_dir_all(&output_directory).expect("create fixture output directory");
            let executable = output_directory.join(format!(
                "gated-malformed-support-encoding-worker-{}",
                std::process::id()
            ));
            let output = Command::new("rustc")
                .args(["--edition", "2024"])
                .arg(&source)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("compile gated malformed-support worker fixture");
            assert!(
                output.status.success(),
                "gated malformed-support worker compile failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            executable
        })
        .as_path()
}

pub fn restartable_encoding_worker() -> &'static Path {
    RESTARTABLE_ENCODING_WORKER
        .get_or_init(|| {
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let source = manifest.join("tests/fixtures/restartable_encoding_worker.rs");
            let output_directory = manifest.join("target/test-fixtures");
            fs::create_dir_all(&output_directory).expect("create fixture output directory");
            let executable = output_directory.join(format!(
                "restartable-encoding-worker-{}",
                std::process::id()
            ));
            let output = Command::new("rustc")
                .args(["--edition", "2024"])
                .arg(&source)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("compile restartable encoding-worker fixture");
            assert!(
                output.status.success(),
                "restartable worker compile failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            executable
        })
        .as_path()
}

pub fn repository_root() -> PathBuf {
    repo_root()
}

// ------------------------------------------------------------
// Test Process Helpers
// ------------------------------------------------------------

// The Lean task exporter lives under `Whiel/Synthesis/Tests/`; the corpus input
// it reads is an engine fixture under `tests/fixtures/lean/`. Both are built
// before the exporter runs, so a missing dependency fails loudly here.
fn task_export() -> &'static str {
    TASK_EXPORTS.get_or_init(|| {
        let repo = repo_root();
        build_task_exporter(&repo);
        run_task_exporter(&repo)
    })
}

fn repo_root() -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .expect("whiel_runner must be a root-level crate")
        .to_path_buf()
}

fn build_task_exporter(repo: &Path) {
    let build = Command::new("lake")
        .args([
            "build",
            "Whiel.Synthesis.Runtime.Task",
            "Benchmark2.Example0012.Input",
        ])
        .current_dir(repo)
        .output()
        .expect("build Lean task exporter dependency");
    assert!(
        build.status.success(),
        "Lean task module build failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
}

fn run_task_exporter(repo: &Path) -> String {
    let directory = TestDir::new("task_export");
    let output_path = directory.path().join("task.json");
    let mut command = Command::new("lake");
    command
        .args([
            "env",
            "lean",
            "--run",
            "Whiel/Synthesis/Tests/Phase1CExport.lean",
        ])
        .arg(&output_path)
        .current_dir(repo);
    let output = command.output().expect("run Lean task exporter");
    assert!(
        output.status.success(),
        "Lean task export failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    fs::read_to_string(output_path).expect("read Lean task export")
}

// ------------------------------------------------------------
// Settled Run Manifests
// ------------------------------------------------------------

/// The single settled run below one artifact root, as its run root and the
/// frozen `manifest.json` that run left behind.
pub fn settled_run(artifact_root: &Path) -> (PathBuf, serde_json::Value) {
    let mut runs: Vec<PathBuf> = fs::read_dir(artifact_root)
        .unwrap_or_else(|error| panic!("read {}: {error}", artifact_root.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.join("manifest.json").is_file())
        .collect();
    runs.sort();
    assert_eq!(
        runs.len(),
        1,
        "exactly one settled run below {}: {runs:?}",
        artifact_root.display()
    );
    let run = runs.remove(0);
    let manifest =
        serde_json::from_slice(&fs::read(run.join("manifest.json")).expect("read run manifest"))
            .expect("parse run manifest");
    (run, manifest)
}

/// The manifest's records of one kind published under one exact scope, in
/// the backend's own publication order.
pub fn manifest_records<'a>(
    manifest: &'a serde_json::Value,
    kind: &str,
    scope: &[&str],
) -> Vec<&'a serde_json::Value> {
    let mut records: Vec<&serde_json::Value> = manifest["artifacts"]
        .as_array()
        .expect("manifest artifact records")
        .iter()
        .filter(|record| record["kind"] == kind && record["scope"] == serde_json::json!(scope))
        .collect();
    records.sort_by_key(|record| record["id"].as_u64().expect("record id"));
    records
}

/// The retained bytes one manifest record names.
pub fn retained_payload(run_root: &Path, record: &serde_json::Value) -> Vec<u8> {
    assert_eq!(record["retained"], true, "record payload was discarded");
    let path = run_root.join(record["relative_path"].as_str().expect("record path"));
    fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}

/// Decode one published transcript frame into the record it carries.
pub fn transcript_record(frame: &[u8]) -> serde_json::Value {
    let frame: serde_json::Value = serde_json::from_slice(frame).expect("parse transcript frame");
    let payload: Vec<u8> = frame["payload"]
        .as_array()
        .expect("frame payload")
        .iter()
        .map(|byte| u8::try_from(byte.as_u64().expect("payload byte")).expect("payload byte"))
        .collect();
    serde_json::from_slice(&payload).expect("parse transcript record")
}

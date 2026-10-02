//! Independent baseline export/check CLI. Never linked into whiel-symbolic.
//! Version 2 is a file/CLI contract, not an extension of the proposer protocol.

use serde_json::{Value, json};
use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const MAX_FILE: u64 = 64 * 1024 * 1024;

fn require(ok: bool, message: &str) -> Result<()> {
    if ok { Ok(()) } else { Err(message.into()) }
}

fn read(path: &Path, maximum: u64) -> Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(path)?;
    let meta = file.metadata()?;
    require(
        meta.is_file() && meta.len() <= maximum,
        "not a bounded regular file",
    )?;
    let mut bytes = Vec::new();
    file.take(maximum + 1).read_to_end(&mut bytes)?;
    require(bytes.len() as u64 <= maximum, "file grew beyond limit")?;
    Ok(bytes)
}

fn write(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

fn save(path: &Path, value: &Value) -> Result<()> {
    write(path, &serde_json::to_vec_pretty(value)?)
}

fn digest(path: &Path) -> Result<String> {
    let mut child = Command::new("/usr/bin/sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .ok_or("digest pipe missing")?
        .write_all(&read(path, MAX_FILE)?)?;
    let output = child.wait_with_output()?;
    require(output.status.success(), "sha256sum failed")?;
    let text = String::from_utf8(output.stdout)?;
    Ok(text
        .split_whitespace()
        .next()
        .ok_or("digest missing")?
        .to_owned())
}

fn text_output(command: &mut Command) -> Result<String> {
    let out = command.output()?;
    require(out.status.success(), &String::from_utf8_lossy(&out.stderr))?;
    Ok(String::from_utf8(out.stdout)?.trim().to_owned())
}

fn within_file_budget(root: &Path) -> io::Result<bool> {
    let mut pending = vec![root.to_path_buf()];
    let (mut entries, mut bytes) = (0, 0);
    while let Some(path) = pending.pop() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            entries += 1;
            let meta = fs::symlink_metadata(entry.path())?;
            bytes += meta.len();
            if entries > 256 || bytes > MAX_FILE {
                return Ok(false);
            }
            if meta.is_dir() {
                pending.push(entry.path());
            }
        }
    }
    Ok(true)
}

struct ChildGuard {
    child: std::process::Child,
    joined: bool,
}

impl Drop for ChildGuard {
    fn drop(&mut self) {
        if self.joined {
            return;
        }
        unsafe {
            libc::kill(-(self.child.id() as i32), libc::SIGKILL);
        }
        let _ = self.child.wait();
    }
}

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

// The process group is always joined; bwrap's PID namespace kills escaped
// descendants too. Runtime checks have no explicit RSS or Lean memory cap.
fn run(mut command: Command, dir: &Path, label: &str, seconds: u64) -> Result<bool> {
    let stdout = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(dir.join(format!("{label}.stdout")))?;
    let stderr = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(dir.join(format!("{label}.stderr")))?;
    command.stdin(Stdio::null()).stdout(stdout).stderr(stderr);
    let parent = std::process::id() as i32;
    unsafe {
        command.pre_exec(move || {
            if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                return Err(io::Error::last_os_error());
            }
            if libc::getppid() != parent {
                return Err(io::Error::new(io::ErrorKind::Interrupted, "parent exited"));
            }
            if libc::setsid() < 0 {
                return Err(io::Error::last_os_error());
            }
            let limit = libc::rlimit {
                rlim_cur: MAX_FILE,
                rlim_max: MAX_FILE,
            };
            if libc::setrlimit(libc::RLIMIT_FSIZE, &limit) != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut owned = ChildGuard {
        child: command.spawn()?,
        joined: false,
    };
    let child = &mut owned.child;
    let start = Instant::now();
    let success = loop {
        if let Some(status) = child.try_wait()? {
            break status.success();
        }
        if start.elapsed() >= Duration::from_secs(seconds) {
            break false;
        }
        if label == "compile" && !within_file_budget(&dir.join("compile")).unwrap_or(false) {
            break false;
        }
        std::thread::sleep(Duration::from_millis(25));
    };
    unsafe {
        libc::kill(-(child.id() as i32), libc::SIGKILL);
    }
    child.wait()?;
    owned.joined = true;
    Ok(success)
}

fn watched() -> Command {
    let mut command = Command::new(repo().join("scripts/watchdog.sh"));
    command
        .arg("4194304")
        .env("LEAN_NUM_THREADS", "1")
        .current_dir(repo());
    command
}

fn export(out: &Path, inputs: &[String]) -> Result<()> {
    fs::create_dir(out)?;
    fs::set_permissions(out, fs::Permissions::from_mode(0o700))?;
    // The exporter parses all tasks in one minimal environment. Each original
    // input is imported only by its separate, bounded kernel fidelity check.
    let mut command = watched();
    command
        .args([
            "lake",
            "env",
            "lean",
            "--run",
            "Whiel/DirectLean/Export.lean",
        ])
        .arg(out);
    require(
        run(command, out, "libraries", 120)?,
        "library export failed; see logs",
    )?;
    for id in inputs {
        require(
            id.len() == 11
                && id.starts_with("Example")
                && id[7..].bytes().all(|x| x.is_ascii_digit()),
            "invalid case ID",
        )?;
    }
    // Parser/formatter state can retain source buffers: bound each batch too.
    for (index, batch) in inputs.chunks(8).enumerate() {
        let mut command = watched();
        command
            .args([
                "lake",
                "env",
                "lean",
                "--run",
                "Whiel/DirectLean/Export.lean",
            ])
            .arg(out);
        for id in batch {
            command.arg(repo().join("Benchmark").join(id).join("Input.lean"));
        }
        require(
            run(command, out, &format!("tasks-{index}"), 120)?,
            "task export failed; see logs",
        )?;
    }
    let mut cases = Vec::new();
    for id in inputs {
        require(
            id.len() == 11
                && id.starts_with("Example")
                && id[7..].bytes().all(|x| x.is_ascii_digit()),
            "invalid case ID",
        )?;
        let input = repo().join("Benchmark").join(id).join("Input.lean");
        let mut fidelity = format!(
            "import Benchmark.{id}.Input\n{}
",
            String::from_utf8(read(&out.join(id).join("Task.lean"), 256 * 1024)?)?
        );
        for field in ["inputSchema", "inputPre", "inputCmd", "inputPost"] {
            fidelity.push_str(&format!(
                "\nexample : DirectLeanTask.{field} = Whiel.Benchmark.{id}.{field} := rfl\n"
            ));
        }
        let fidelity_path = out.join(format!("{id}-fidelity.lean"));
        write(&fidelity_path, fidelity.as_bytes())?;
        let mut command = watched();
        command.args(["lake", "env", "lean"]).arg(&fidelity_path);
        require(
            run(command, out, &format!("{id}-fidelity"), 120)?,
            "kernel fidelity check failed; see logs",
        )?;
        cases.push(json!({"id": id, "input_sha256": digest(&input)?,
            "task_sha256": digest(&out.join(id).join("Task.lean"))?}));
        println!("fidelity checked {id}");
    }
    let lean = PathBuf::from(text_output(
        Command::new("lake")
            .args(["env", "which", "lean"])
            .current_dir(repo()),
    )?)
    .canonicalize()?;
    let sysroot = lean
        .parent()
        .ok_or("lean bin missing")?
        .parent()
        .ok_or("lean root missing")?;
    let modules: Vec<Value> =
        serde_json::from_slice(&read(&out.join("libraries.json"), MAX_FILE)?)?;
    let library = out.join("lib");
    fs::create_dir(&library)?;
    let mut files = Vec::new();
    for module in modules {
        let name = module["module"].as_str().ok_or("module missing")?;
        require(
            ![
                "Benchmark",
                "Whiel.Synthesis",
                "Whiel.Hoare.Preproc",
                "Whiel.Hoare.Prophecy",
                "VampLean",
            ]
            .iter()
            .any(|p| name.starts_with(p)),
            "forbidden library dependency",
        )?;
        let original =
            PathBuf::from(module["olean"].as_str().ok_or("olean missing")?).canonicalize()?;
        if original.starts_with(sysroot) {
            continue;
        }
        let stem = original.with_extension("");
        for ext in ["olean", "olean.server", "olean.private", "ir"] {
            let src = PathBuf::from(format!("{}.{ext}", stem.display()));
            if !src.exists() {
                continue;
            }
            let relative = format!("{}.{ext}", name.replace('.', "/"));
            let dst = library.join(&relative);
            fs::create_dir_all(dst.parent().unwrap())?;
            // Copy, not hardlink: a later rebuild must not modify this bundle.
            fs::copy(&src, &dst)?;
            files.push(json!({"path": relative, "sha256": digest(&dst)?}));
        }
    }
    let audit = out.join("Audit.lean");
    fs::copy(repo().join("Whiel/DirectLean/Audit.lean"), &audit)?;
    save(
        &out.join("bundle.json"),
        &json!({"schema_version": 1,
        "lean": lean, "lean_version": text_output(Command::new(sysroot.join("bin/lean")).arg("--version"))?,
        "audit_sha256": digest(&audit)?, "reference_sha256": digest(&out.join("reference.txt"))?,
        "cases": cases, "libraries": files}),
    )?;
    Ok(())
}

fn sandbox(
    bundle: &Path,
    task: &Path,
    work: &Path,
    candidate: Option<&Path>,
    lean: &Path,
    args: &[&str],
) -> Result<Command> {
    let root = lean.parent().unwrap().parent().unwrap();
    let mut command = Command::new("/usr/bin/bwrap");
    command.env("LEAN_NUM_THREADS", "2").current_dir(repo());
    command.args([
        "--unshare-all",
        "--new-session",
        "--die-with-parent",
        "--clearenv",
        "--cap-drop",
        "ALL",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--tmpfs",
        "/tmp",
    ]);
    for path in ["/usr/lib", "/lib", "/lib64"] {
        if Path::new(path).exists() {
            command.args(["--ro-bind", path, path]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(root)
        .arg("/lean")
        .arg("--ro-bind")
        .arg(bundle.join("lib"))
        .arg("/library")
        .arg("--ro-bind")
        .arg(bundle.join("Audit.lean"))
        .arg("/Audit.lean")
        .arg("--ro-bind")
        .arg(task)
        .arg("/task")
        .arg("--bind")
        .arg(work)
        .arg("/work");
    if let Some(path) = candidate {
        command.arg("--ro-bind").arg(path).arg("/candidate.olean");
    }
    command.args([
        "--chdir",
        "/work",
        "--setenv",
        "HOME",
        "/tmp",
        "--setenv",
        "PATH",
        "/lean/bin",
        "--setenv",
        "LEAN_PATH",
        "/task:/library",
        "--setenv",
        "LEAN_NUM_THREADS",
        "2",
        "--",
        "/lean/bin/lean",
        "-DmaxHeartbeats=0",
    ]);
    command.args(args);
    Ok(command)
}

fn verify_libraries(bundle: &Path, manifest: &Value) -> Result<()> {
    let entries = manifest["libraries"]
        .as_array()
        .ok_or("libraries missing")?;
    let mut command = Command::new("/usr/bin/sha256sum");
    command.arg("--");
    let mut expected = std::collections::BTreeSet::new();
    for entry in entries {
        let relative = entry["path"].as_str().ok_or("library path missing")?;
        require(
            !relative.starts_with('/') && !relative.split('/').any(|p| p == ".."),
            "invalid library path",
        )?;
        require(
            expected.insert(PathBuf::from(relative)),
            "duplicate library file",
        )?;
        command.arg(bundle.join("lib").join(relative));
    }
    let root = bundle.join("lib");
    let mut pending = vec![root.clone()];
    let mut actual = std::collections::BTreeSet::new();
    while let Some(dir) = pending.pop() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let meta = fs::symlink_metadata(entry.path())?;
            if meta.is_dir() {
                pending.push(entry.path());
            } else {
                require(
                    meta.is_file() && meta.len() <= MAX_FILE,
                    "nonregular library entry",
                )?;
                actual.insert(entry.path().strip_prefix(&root)?.to_path_buf());
            }
        }
    }
    require(expected == actual, "library file inventory changed")?;
    let hashes = text_output(&mut command)?;
    let lines: Vec<_> = hashes.lines().collect();
    require(lines.len() == entries.len(), "library hash count differs")?;
    for (entry, line) in entries.iter().zip(lines) {
        require(
            entry["sha256"].as_str() == line.split_whitespace().next(),
            "library bundle changed",
        )?;
    }
    Ok(())
}

fn validate(bundle: &Path, out: &Path) -> Result<()> {
    let bundle = bundle.canonicalize()?;
    let manifest: Value = serde_json::from_slice(&read(&bundle.join("bundle.json"), MAX_FILE)?)?;
    require(
        manifest["schema_version"] == 1,
        "unsupported bundle version",
    )?;
    verify_libraries(&bundle, &manifest)?;
    let lean = PathBuf::from(manifest["lean"].as_str().ok_or("lean missing")?);
    require(
        manifest["lean_version"] == text_output(Command::new(&lean).arg("--version"))?,
        "Lean version changed",
    )?;
    require(
        manifest["audit_sha256"] == digest(&bundle.join("Audit.lean"))?,
        "audit bundle changed",
    )?;
    fs::create_dir(out)?;
    let out = out.canonicalize()?;
    let cases = manifest["cases"].as_array().ok_or("cases missing")?;
    for case in cases {
        let id = case["id"].as_str().ok_or("case missing")?;
        let task = bundle.join(id);
        require(
            case["task_sha256"] == digest(&task.join("Task.lean"))?,
            "task changed",
        )?;
        let work = out.join(id);
        fs::create_dir(&work)?;
        write(
            &work.join("Task.lean"),
            &read(&task.join("Task.lean"), 256 * 1024)?,
        )?;
        require(
            run(
                sandbox(
                    &bundle,
                    &task,
                    &work,
                    None,
                    &lean,
                    &["-o", "/work/Task.olean", "/work/Task.lean"],
                )?,
                &work,
                "task",
                120,
            )?,
            "task isolation validation failed; see logs",
        )?;
        println!("isolated task compiled {id}");
    }
    save(
        &out.join("validation.json"),
        &json!({"schema_version": 1, "validated_tasks": cases.len(),
        "bundle_sha256": digest(&bundle.join("bundle.json"))?, "network": "unshared", "paid_model_calls": 0}),
    )?;
    Ok(())
}

fn check(bundle: &Path, id: &str, response: &Path, out: &Path, seconds: u64) -> Result<()> {
    require(
        seconds > 0 && seconds <= 3600,
        "check seconds must be 1..3600",
    )?;
    let bundle = bundle.canonicalize()?;
    let manifest: Value = serde_json::from_slice(&read(&bundle.join("bundle.json"), MAX_FILE)?)?;
    require(
        manifest["schema_version"] == 1,
        "unsupported bundle version",
    )?;
    let case = manifest["cases"]
        .as_array()
        .ok_or("cases missing")?
        .iter()
        .find(|c| c["id"] == id)
        .ok_or("unknown task")?;
    let task_source = bundle.join(id).join("Task.lean");
    require(
        case["task_sha256"] == digest(&task_source)?,
        "task bundle changed",
    )?;
    require(
        manifest["audit_sha256"] == digest(&bundle.join("Audit.lean"))?,
        "audit bundle changed",
    )?;
    // Only B-created bundles are accepted; mutable model output never enters
    // these hashes, library paths, trusted source, or the task mount.
    verify_libraries(&bundle, &manifest)?;
    let answer: Value = serde_json::from_slice(&read(response, 256 * 1024)?)?;
    let obj = answer.as_object().ok_or("response must be an object")?;
    require(obj.len() == 2, "response must have verdict and source")?;
    let verdict = answer["verdict"].as_str().ok_or("verdict missing")?;
    require(
        verdict == "valid" || verdict == "invalid",
        "verdict must be valid or invalid",
    )?;
    let source = answer["source"].as_str().ok_or("source missing")?;
    require(!source.trim().is_empty(), "empty submission")?;
    require(
        read(&bundle.join("Audit.lean"), MAX_FILE)?
            == include_bytes!("../../../Whiel/DirectLean/Audit.lean"),
        "submission requires a freshly prepared bundle for this checker",
    )?;
    fs::create_dir(out)?;
    fs::set_permissions(out, fs::Permissions::from_mode(0o700))?;
    let out = out.canonicalize()?;
    let task = out.join("task");
    let compile = out.join("compile");
    let audit = out.join("audit");
    for path in [&task, &compile, &audit] {
        fs::create_dir(path)?;
    }
    write(&task.join("Task.lean"), &read(&task_source, 256 * 1024)?)?;
    let lean = PathBuf::from(manifest["lean"].as_str().ok_or("lean missing")?);
    let started = Instant::now();
    let mut result = json!({"schema_version":1, "case":id, "verdict":verdict,
        "status":"check_failed", "proof_checked":false, "task_sha256":case["task_sha256"],
        "response_sha256":digest(response)?, "check_limit_seconds":seconds,
        "submission_format":"source",
        "failure_stage":"task"});
    // Trusted task compilation uses a separate writable directory. The model
    // can never overwrite this olean or its source.
    let task_ok = run(
        sandbox(
            &bundle,
            &task,
            &task,
            None,
            &lean,
            &["-o", "/work/Task.olean", "/work/Task.lean"],
        )?,
        &out,
        "task",
        seconds,
    )?;
    if !task_ok {
        result["status"] = json!("task_setup_failed");
    } else {
        result["failure_stage"] = json!("compile");
        write(&compile.join("Candidate.lean"), source.as_bytes())?;
        let remaining = seconds.saturating_sub(started.elapsed().as_secs());
        let ok = remaining > 0
            && run(
                sandbox(
                    &bundle,
                    &task,
                    &compile,
                    None,
                    &lean,
                    &["-o", "/work/Candidate.olean", "/work/Candidate.lean"],
                )?,
                &out,
                "compile",
                remaining,
            )?;
        if ok {
            result["failure_stage"] = json!("audit");
            let frozen = out.join("Candidate.olean");
            write(&frozen, &read(&compile.join("Candidate.olean"), MAX_FILE)?)?;
            let remaining = seconds.saturating_sub(started.elapsed().as_secs());
            let ok = remaining > 0
                && run(
                    sandbox(
                        &bundle,
                        &task,
                        &audit,
                        Some(&frozen),
                        &lean,
                        &["--run", "/Audit.lean", "/candidate.olean", verdict],
                    )?,
                    &out,
                    "audit",
                    remaining,
                )?;
            if ok {
                let receipt: Value =
                    serde_json::from_slice(&read(&out.join("audit.stdout"), 65536)?)?;
                require(
                    receipt["proof_checked"] == true && receipt["verdict"] == verdict,
                    "invalid audit receipt",
                )?;
                result["status"] = json!(format!("{verdict}_proof_checked"));
                result["proof_checked"] = json!(true);
                result["failure_stage"] = Value::Null;
                result["axioms"] = receipt["axioms"].clone();
                result["native_rechecked"] = receipt["native_rechecked"].clone();
                result["native_kernel_rechecked"] = receipt["native_kernel_rechecked"].clone();
            }
        }
    }
    if !result["proof_checked"].as_bool().unwrap_or(false) && started.elapsed().as_secs() >= seconds
    {
        result["status"] = json!("check_timeout");
    }
    result["check_seconds"] = json!(started.elapsed().as_secs_f64());
    save(&out.join("result.json"), &result)?;
    println!("{}", serde_json::to_string(&result)?);
    Ok(())
}

fn main() -> Result<()> {
    unsafe {
        if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
            return Err(io::Error::last_os_error().into());
        }
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [mode, bundle, out] if mode == "validate" => validate(Path::new(bundle), Path::new(out)),
        [mode, out, ids @ ..] if mode == "prepare" && !ids.is_empty() =>
            export(&std::path::absolute(out)?, ids),
        [mode, bundle, id, answer, out, seconds] if mode == "check" =>
            check(Path::new(bundle), id, Path::new(answer), Path::new(out), seconds.parse()?),
        _ => Err("usage: whiel-direct-lean prepare OUT ExampleNNNN... | validate BUNDLE OUT | check BUNDLE ID RESPONSE_JSON OUT CHECK_SECONDS".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_reads_and_create_new() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "direct-lean-unit-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_nanos()
        ));
        fs::create_dir(&dir)?;
        let path = dir.join("sample");
        write(&path, b"1234")?;
        assert!(read(&path, 3).is_err());
        assert_eq!(read(&path, 4)?, b"1234");
        assert!(write(&path, b"overwrite").is_err());
        let linked = dir.join("linked");
        std::os::unix::fs::symlink(&path, &linked)?;
        assert!(read(&linked, 4).is_err());
        fs::remove_file(linked)?;
        fs::remove_file(path)?;
        fs::remove_dir(dir)?;
        Ok(())
    }
}

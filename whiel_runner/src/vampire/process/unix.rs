use std::collections::{HashMap, VecDeque};
#[cfg(target_os = "linux")]
use std::fs;
use std::io;
use std::os::unix::process::CommandExt;
use std::process::{Child, ChildStderr, ChildStdout, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use std::ffi::OsString;
use std::path::Path;

use crate::runtime::CancellationToken;

/*
  The direct Vampire child leads a fresh process group. It remains
  unreaped until cleanup finishes, which anchors its PID and process-
  group identity while descendants are signaled and checked.

  The registry also records observed descendant start identities. It
  can therefore stop a descendant that later leaves the process group
  without signaling an unrelated process after PID reuse.
*/

// ------------------------------------------------------------
// Supervised Process Types
// ------------------------------------------------------------

const POLL_INTERVAL: Duration = Duration::from_millis(10);
const TERM_GRACE: Duration = Duration::from_millis(100);
const CLEANUP_GRACE: Duration = Duration::from_millis(750);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StopReason {
    Exited,
    Cancelled,
    CaptureFailed,
}

pub(crate) struct SpawnedProcess {
    child: Option<Child>,
    registry: ProcessRegistry,
    cleaned: bool,
}

pub(crate) struct ProcessPipes {
    pub stdout: ChildStdout,
    pub stderr: ChildStderr,
}

pub(crate) struct SupervisedExit {
    pub reason: StopReason,
    pub status: io::Result<ExitStatus>,
    pub cleanup_error: Option<String>,
}

pub(crate) enum SpawnError {
    Failed(String),
    CleanupFailed(String),
}

// ------------------------------------------------------------
// Spawn, Supervision, And Cleanup
// ------------------------------------------------------------

impl SpawnedProcess {
    /// Spawn `executable` with `args` in a fresh process group rooted at
    /// `cwd`, piping stdout and stderr. Generalized over the caller's
    /// invocation shape (an executable path, arguments, and a working
    /// directory) rather than Vampire's own `Invocation` type, so callers
    /// outside the Vampire worker (the pinned leancheck Vampire launch, in
    /// particular) can reuse the exact same process-group cleanup.
    pub fn spawn(executable: &Path, args: &[OsString], cwd: &Path) -> Result<Self, SpawnError> {
        let mut command = Command::new(executable);
        command
            .args(args)
            .current_dir(cwd)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        Self::spawn_command(command)
    }

    // Reuse the same process-tree ownership for callers with a stdin prompt
    // and a request-specific environment. Every caller still gets a new group.
    pub(crate) fn spawn_command(mut command: Command) -> Result<Self, SpawnError> {
        command.process_group(0);
        let child = command
            .spawn()
            .map_err(|error| SpawnError::Failed(format!("start Vampire process: {error}")))?;
        let pid = child.id();
        let registry = match ProcessRegistry::new(pid) {
            Ok(registry) => registry,
            Err(error) => {
                return Err(cleanup_unregistered_spawn(child, pid, error));
            }
        };
        Ok(Self {
            child: Some(child),
            registry,
            cleaned: false,
        })
    }

    pub fn take_pipes(&mut self) -> Result<ProcessPipes, String> {
        let child = self
            .child
            .as_mut()
            .ok_or_else(|| "Vampire child is no longer owned".to_string())?;
        Ok(ProcessPipes {
            stdout: child
                .stdout
                .take()
                .ok_or_else(|| "Vampire stdout pipe is absent".to_string())?,
            stderr: child
                .stderr
                .take()
                .ok_or_else(|| "Vampire stderr pipe is absent".to_string())?,
        })
    }

    pub fn supervise(
        mut self,
        cancellation: &CancellationToken,
        capture_failed: &AtomicBool,
    ) -> SupervisedExit {
        let reason = loop {
            match observe_exit(self.pid()) {
                Ok(true) => break StopReason::Exited,
                Ok(false) => {}
                Err(error) => {
                    let (_, cleanup_error) = self.cleanup(StopReason::CaptureFailed);
                    return SupervisedExit {
                        reason: StopReason::CaptureFailed,
                        status: Err(error),
                        cleanup_error,
                    };
                }
            }
            self.registry.refresh();
            if capture_failed.load(Ordering::Acquire) {
                break StopReason::CaptureFailed;
            }
            if cancellation.is_cancelled() {
                break StopReason::Cancelled;
            }
            thread::sleep(POLL_INTERVAL);
        };
        let (status, cleanup_error) = self.cleanup(reason);
        SupervisedExit {
            reason,
            status,
            cleanup_error,
        }
    }

    fn pid(&self) -> u32 {
        self.child.as_ref().expect("owned child is present").id()
    }

    fn cleanup(&mut self, reason: StopReason) -> (io::Result<ExitStatus>, Option<String>) {
        if self.cleaned {
            return (
                Err(io::Error::other("Vampire process cleanup repeated")),
                Some("Vampire process cleanup repeated".to_string()),
            );
        }
        self.cleaned = true;
        let mut errors = Vec::new();
        let pid = self.pid();
        self.registry.refresh();
        // The direct Child remains unreaped until the final wait below. That
        // OS-owned zombie/live slot prevents PID and process-group-ID reuse.
        let anchored = true;

        // A normally exited leader can still leave pipe-holding
        // descendants. Stop those before joining the capture pumps.
        if reason == StopReason::Exited {
            signal_owned(
                &mut self.registry,
                pid,
                libc::SIGKILL,
                anchored,
                &mut errors,
            );
        } else {
            signal_owned(
                &mut self.registry,
                pid,
                libc::SIGTERM,
                anchored,
                &mut errors,
            );
            let deadline = Instant::now() + TERM_GRACE;
            while Instant::now() < deadline {
                self.registry.refresh();
                if observe_exit(pid).unwrap_or(false)
                    && owned_live_descendants(pid, &self.registry).is_empty()
                {
                    break;
                }
                thread::sleep(POLL_INTERVAL);
            }
            signal_owned(
                &mut self.registry,
                pid,
                libc::SIGKILL,
                anchored,
                &mut errors,
            );
        }

        // Keep the leader unreaped while verifying descendants. This
        // prevents its process-group ID from being recycled mid-cleanup.
        let exit_deadline = Instant::now() + CLEANUP_GRACE;
        let mut root_exited = false;
        while Instant::now() < exit_deadline {
            match observe_exit(pid) {
                Ok(true) => {
                    root_exited = true;
                    break;
                }
                Ok(false) => thread::sleep(POLL_INTERVAL),
                Err(error) => {
                    errors.push(format!("observe Vampire exit during cleanup: {error}"));
                    break;
                }
            }
        }
        if !root_exited
            && let Err(error) = self.child.as_mut().expect("owned child is present").kill()
            && error.kind() != io::ErrorKind::InvalidInput
        {
            errors.push(format!("kill direct Vampire child: {error}"));
        }

        let descendant_deadline = Instant::now() + CLEANUP_GRACE;
        let mut survivors = owned_live_descendants(pid, &self.registry);
        while !survivors.is_empty() && Instant::now() < descendant_deadline {
            for survivor in &survivors {
                signal_identity(&survivor.identity, libc::SIGKILL, &mut errors);
            }
            if anchored {
                record_group_signal_error(
                    signal_group(pid, libc::SIGKILL),
                    "kill Vampire group",
                    &mut errors,
                );
            }
            thread::sleep(POLL_INTERVAL);
            self.registry.refresh();
            survivors = owned_live_descendants(pid, &self.registry);
        }
        if !survivors.is_empty() {
            errors.push(format!(
                "owned Vampire descendants survived cleanup: {:?}",
                survivors
                    .iter()
                    .map(|process| process.identity.pid)
                    .collect::<Vec<_>>()
            ));
        }

        let status = self.child.as_mut().expect("owned child is present").wait();
        if let Err(error) = &status {
            errors.push(format!("reap direct Vampire child: {error}"));
        }
        self.child = None;
        let error = (!errors.is_empty()).then(|| errors.join("; "));
        (status, error)
    }
}

impl Drop for SpawnedProcess {
    fn drop(&mut self) {
        if self.child.is_some() && !self.cleaned {
            let _ = self.cleanup(StopReason::CaptureFailed);
        }
    }
}

// ------------------------------------------------------------
// Exit Observation And Signaling
// ------------------------------------------------------------

fn observe_exit(pid: u32) -> io::Result<bool> {
    let mut information = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
    let result = unsafe {
        libc::waitid(
            libc::P_PID,
            pid as libc::id_t,
            information.as_mut_ptr(),
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        )
    };
    if result != 0 {
        let error = io::Error::last_os_error();
        if error.kind() == io::ErrorKind::Interrupted {
            return Ok(false);
        }
        return Err(error);
    }
    let information = unsafe { information.assume_init() };
    Ok(unsafe { information.si_pid() } != 0)
}

fn signal_owned(
    registry: &mut ProcessRegistry,
    group: u32,
    signal: i32,
    anchored: bool,
    errors: &mut Vec<String>,
) {
    registry.refresh();
    let mut descendants = registry.live_matching_descendants();
    descendants.sort_by_key(|process| std::cmp::Reverse(process.depth));
    for descendant in descendants {
        signal_identity(&descendant.identity, signal, errors);
    }
    if anchored {
        record_group_signal_error(signal_group(group, signal), "signal Vampire group", errors);
    }
}

fn signal_identity(identity: &ProcessIdentity, signal: i32, errors: &mut Vec<String>) {
    if process_identity(identity.pid).as_ref() != Some(identity) {
        return;
    }
    let result = unsafe { libc::kill(identity.pid as libc::pid_t, signal) };
    if result != 0 {
        record_signal_error(
            Err(io::Error::last_os_error()),
            "signal registered Vampire descendant",
            errors,
        );
    }
}

fn signal_group(group: u32, signal: i32) -> io::Result<()> {
    let result = unsafe { libc::killpg(group as libc::pid_t, signal) };
    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

fn record_signal_error(result: io::Result<()>, label: &str, errors: &mut Vec<String>) {
    if let Err(error) = result
        && error.raw_os_error() != Some(libc::ESRCH)
    {
        errors.push(format!("{label}: {error}"));
    }
}

/*
  Compensating cleanup when a freshly spawned Vampire leader could not
  be identity-registered. The usual trigger is a child that died before
  registration: its zombie still anchors the fresh process-group ID, and
  on macOS `killpg` on a group whose only member is a zombie fails with
  EPERM. The group signal is therefore provisional; the direct reap and
  the grace-polled survivor scan decide whether cleanup succeeded. A
  verified-clean group is an ordinary process-start failure, not a
  run-global cleanup failure.
*/
fn cleanup_unregistered_spawn(mut child: Child, pid: u32, error: String) -> SpawnError {
    let mut cleanup_errors = Vec::new();
    record_group_signal_error(
        signal_group(pid, libc::SIGKILL),
        "kill unregistered Vampire process group",
        &mut cleanup_errors,
    );
    if let Err(kill_error) = child.kill()
        && kill_error.kind() != io::ErrorKind::InvalidInput
    {
        cleanup_errors.push(format!("kill unregistered Vampire child: {kill_error}"));
    }
    if let Err(wait_error) = child.wait() {
        cleanup_errors.push(format!("reap unregistered Vampire child: {wait_error}"));
    }
    let survivor_deadline = Instant::now() + CLEANUP_GRACE;
    let mut survivors = live_group_members(pid);
    while !survivors.is_empty() && Instant::now() < survivor_deadline {
        record_group_signal_error(
            signal_group(pid, libc::SIGKILL),
            "kill unregistered Vampire process group",
            &mut cleanup_errors,
        );
        thread::sleep(POLL_INTERVAL);
        survivors = live_group_members(pid);
    }
    if !survivors.is_empty() {
        cleanup_errors.push(format!(
            "unregistered Vampire process group retains {} live member(s)",
            survivors.len()
        ));
    }
    if cleanup_errors.is_empty() {
        SpawnError::Failed(error)
    } else {
        SpawnError::CleanupFailed(format!("{error}; {}", cleanup_errors.join("; ")))
    }
}

fn record_group_signal_error(result: io::Result<()>, label: &str, errors: &mut Vec<String>) {
    // EPERM is provisional here. The later identity-aware survivor
    // inspection determines whether cleanup actually succeeded.
    if let Err(error) = result
        && !matches!(error.raw_os_error(), Some(libc::ESRCH) | Some(libc::EPERM))
    {
        errors.push(format!("{label}: {error}"));
    }
}

fn owned_live_descendants(group: u32, registry: &ProcessRegistry) -> Vec<RegisteredProcess> {
    let mut processes = registry.live_matching_descendants();
    let mut known = processes
        .iter()
        .map(|process| process.identity.pid)
        .collect::<std::collections::HashSet<_>>();
    for identity in live_group_members(group) {
        if identity.pid != group && known.insert(identity.pid) {
            processes.push(RegisteredProcess { identity, depth: 1 });
        }
    }
    processes
}

// ------------------------------------------------------------
// Descendant Identity Registry
// ------------------------------------------------------------

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct ProcessIdentity {
    pid: u32,
    start_id: u128,
}

#[derive(Clone, Debug)]
struct RegisteredProcess {
    identity: ProcessIdentity,
    depth: usize,
}

#[derive(Debug)]
struct ProcessRegistry {
    root_pid: u32,
    // Absent when the leader answered and exited before its first identity
    // read. Its unreaped exit still anchors the process-group ID, and group
    // membership still finds any descendant left behind, so the registry has
    // no identity to verify rather than no owner.
    root_identity: Option<ProcessIdentity>,
    processes: HashMap<u32, RegisteredProcess>,
}

impl ProcessRegistry {
    fn new(root_pid: u32) -> Result<Self, String> {
        let deadline = Instant::now() + Duration::from_millis(100);
        let root_identity = loop {
            if let Some(identity) = process_identity(root_pid) {
                break Some(identity);
            }
            // A short solver can answer and exit first. Process inspection
            // need not resolve an exited-but-unreaped leader, so registering
            // one is a normal outcome whose output the caller still reads.
            if observe_exit(root_pid).unwrap_or(false) {
                break None;
            }
            if Instant::now() >= deadline {
                return Err("read Vampire leader process identity".to_string());
            }
            thread::sleep(Duration::from_millis(1));
        };
        let mut registry = Self {
            root_pid,
            root_identity,
            processes: HashMap::new(),
        };
        registry.refresh();
        Ok(registry)
    }

    fn refresh(&mut self) {
        self.processes.retain(|_, process| {
            process_identity(process.identity.pid).as_ref() == Some(&process.identity)
        });
        let mut queue = VecDeque::new();
        if let Some(root_identity) = &self.root_identity
            && process_identity(self.root_pid).as_ref() == Some(root_identity)
        {
            queue.push_back(RegisteredProcess {
                identity: root_identity.clone(),
                depth: 0,
            });
        }
        queue.extend(self.processes.values().cloned());
        let mut visited = HashMap::new();
        while let Some(process) = queue.pop_front() {
            if visited.get(&process.identity.pid) == Some(&process.identity.start_id) {
                continue;
            }
            if process_identity(process.identity.pid).as_ref() != Some(&process.identity) {
                continue;
            }
            visited.insert(process.identity.pid, process.identity.start_id);
            self.processes.insert(process.identity.pid, process.clone());
            for child_pid in direct_child_pids(process.identity.pid) {
                if let Some(identity) = process_identity(child_pid) {
                    queue.push_back(RegisteredProcess {
                        identity,
                        depth: process.depth + 1,
                    });
                }
            }
        }
    }

    fn live_matching_descendants(&self) -> Vec<RegisteredProcess> {
        self.processes
            .values()
            .filter(|process| {
                process.identity.pid != self.root_pid
                    && process_identity(process.identity.pid).as_ref() == Some(&process.identity)
                    && !process_is_zombie(process.identity.pid)
            })
            .cloned()
            .collect()
    }
}

// ------------------------------------------------------------
// macOS Process Inspection
// ------------------------------------------------------------

#[cfg(target_os = "macos")]
const PROC_PIDTBSDINFO: i32 = 3;

#[cfg(target_os = "macos")]
#[repr(C)]
#[derive(Clone, Copy)]
struct ProcBsdInfo {
    pbi_flags: u32,
    pbi_status: u32,
    pbi_xstatus: u32,
    pbi_pid: u32,
    pbi_ppid: u32,
    pbi_uid: u32,
    pbi_gid: u32,
    pbi_ruid: u32,
    pbi_rgid: u32,
    pbi_svuid: u32,
    pbi_svgid: u32,
    rfu_1: u32,
    pbi_comm: [i8; 16],
    pbi_name: [i8; 32],
    pbi_nfiles: u32,
    pbi_pgid: u32,
    pbi_pjobc: u32,
    e_tdev: u32,
    e_tpgid: u32,
    pbi_nice: i32,
    pbi_start_tvsec: u64,
    pbi_start_tvusec: u64,
}

#[cfg(target_os = "macos")]
unsafe extern "C" {
    fn proc_listallpids(buffer: *mut std::ffi::c_void, buffer_size: i32) -> i32;
    fn proc_listchildpids(ppid: i32, buffer: *mut std::ffi::c_void, buffer_size: i32) -> i32;
    fn proc_pidinfo(
        pid: i32,
        flavor: i32,
        arg: u64,
        buffer: *mut std::ffi::c_void,
        buffer_size: i32,
    ) -> i32;
}

#[cfg(target_os = "macos")]
fn macos_info(pid: u32) -> Option<ProcBsdInfo> {
    let mut info = std::mem::MaybeUninit::<ProcBsdInfo>::uninit();
    let expected = std::mem::size_of::<ProcBsdInfo>() as i32;
    let read = unsafe {
        proc_pidinfo(
            pid as i32,
            PROC_PIDTBSDINFO,
            0,
            info.as_mut_ptr().cast(),
            expected,
        )
    };
    (read == expected).then(|| unsafe { info.assume_init() })
}

#[cfg(target_os = "macos")]
fn process_identity(pid: u32) -> Option<ProcessIdentity> {
    let info = macos_info(pid)?;
    Some(ProcessIdentity {
        pid: info.pbi_pid,
        start_id: (u128::from(info.pbi_start_tvsec) << 64) | u128::from(info.pbi_start_tvusec),
    })
}

#[cfg(target_os = "macos")]
fn process_is_zombie(pid: u32) -> bool {
    macos_info(pid).is_some_and(|info| info.pbi_status == 5)
}

#[cfg(target_os = "macos")]
fn direct_child_pids(pid: u32) -> Vec<u32> {
    let capacity = unsafe { proc_listchildpids(pid as i32, std::ptr::null_mut(), 0) };
    if capacity <= 0 {
        return Vec::new();
    }
    let mut pids = vec![0_i32; capacity as usize + 16];
    let bytes = (pids.len() * std::mem::size_of::<i32>()) as i32;
    let count = unsafe { proc_listchildpids(pid as i32, pids.as_mut_ptr().cast(), bytes) };
    if count <= 0 {
        return Vec::new();
    }
    pids.truncate((count as usize).min(pids.len()));
    pids.into_iter()
        .filter(|pid| *pid > 0)
        .map(|pid| pid as u32)
        .collect()
}

#[cfg(target_os = "macos")]
fn live_group_members(group: u32) -> Vec<ProcessIdentity> {
    let capacity = unsafe { proc_listallpids(std::ptr::null_mut(), 0) };
    if capacity <= 0 {
        return Vec::new();
    }
    let mut pids = vec![0_i32; capacity as usize + 64];
    let bytes = (pids.len() * std::mem::size_of::<i32>()) as i32;
    let count = unsafe { proc_listallpids(pids.as_mut_ptr().cast(), bytes) };
    if count <= 0 {
        return Vec::new();
    }
    pids.truncate((count as usize).min(pids.len()));
    pids.into_iter()
        .filter(|pid| *pid > 0)
        .filter_map(|pid| macos_info(pid as u32))
        .filter(|info| info.pbi_pgid == group && info.pbi_status != 5)
        .map(|info| ProcessIdentity {
            pid: info.pbi_pid,
            start_id: (u128::from(info.pbi_start_tvsec) << 64) | u128::from(info.pbi_start_tvusec),
        })
        .collect()
}

// ------------------------------------------------------------
// Linux Process Inspection
// ------------------------------------------------------------

#[cfg(target_os = "linux")]
fn linux_info(pid: u32) -> Option<(ProcessIdentity, u32, bool)> {
    let stat = fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
    let fields = stat
        .rsplit_once(')')?
        .1
        .split_whitespace()
        .collect::<Vec<_>>();
    let zombie = *fields.first()? == "Z";
    let group = fields.get(2)?.parse::<u32>().ok()?;
    let start_id = fields.get(19)?.parse::<u128>().ok()?;
    Some((ProcessIdentity { pid, start_id }, group, zombie))
}

#[cfg(target_os = "linux")]
fn process_identity(pid: u32) -> Option<ProcessIdentity> {
    linux_info(pid).map(|(identity, _, _)| identity)
}

#[cfg(target_os = "linux")]
fn process_is_zombie(pid: u32) -> bool {
    linux_info(pid).is_some_and(|(_, _, zombie)| zombie)
}

#[cfg(target_os = "linux")]
fn direct_child_pids(pid: u32) -> Vec<u32> {
    fs::read_to_string(format!("/proc/{pid}/task/{pid}/children"))
        .unwrap_or_default()
        .split_whitespace()
        .filter_map(|child| child.parse::<u32>().ok())
        .collect()
}

#[cfg(target_os = "linux")]
fn live_group_members(group: u32) -> Vec<ProcessIdentity> {
    let Ok(entries) = fs::read_dir("/proc") else {
        return Vec::new();
    };
    entries
        .flatten()
        .filter_map(|entry| entry.file_name().to_str()?.parse::<u32>().ok())
        .filter_map(linux_info)
        .filter(|(_, process_group, zombie)| *process_group == group && !zombie)
        .map(|(identity, _, _)| identity)
        .collect()
}

// ------------------------------------------------------------
// Other Unix Process Inspection
// ------------------------------------------------------------

/*
  This fallback is retained for future Unix support. The public
  Phase 2A boundary currently compiles supervision only on macOS
  and Linux and fails closed elsewhere.
*/

#[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
fn process_identity(pid: u32) -> Option<ProcessIdentity> {
    let output = Command::new("ps")
        .args(["-p", &pid.to_string(), "-o", "lstart="])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let mut start_id = 0_u128;
    for byte in output.stdout {
        start_id = start_id.wrapping_mul(257).wrapping_add(u128::from(byte));
    }
    Some(ProcessIdentity { pid, start_id })
}

#[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
fn process_is_zombie(pid: u32) -> bool {
    Command::new("ps")
        .args(["-p", &pid.to_string(), "-o", "state="])
        .output()
        .ok()
        .is_some_and(|output| output.status.success() && output.stdout.starts_with(b"Z"))
}

#[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
fn direct_child_pids(pid: u32) -> Vec<u32> {
    let output = match Command::new("pgrep")
        .args(["-P", &pid.to_string()])
        .output()
    {
        Ok(output) if output.status.success() => output,
        _ => return Vec::new(),
    };
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .filter_map(|child| child.parse::<u32>().ok())
        .collect()
}

#[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
fn live_group_members(group: u32) -> Vec<ProcessIdentity> {
    let output = match Command::new("ps")
        .args(["-axo", "pid=,pgid=,state="])
        .output()
    {
        Ok(output) if output.status.success() => output,
        _ => return Vec::new(),
    };
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace();
            let pid = fields.next()?.parse::<u32>().ok()?;
            let process_group = fields.next()?.parse::<u32>().ok()?;
            let state = fields.next()?;
            (process_group == group && !state.starts_with('Z'))
                .then(|| process_identity(pid))
                .flatten()
        })
        .collect()
}

// ------------------------------------------------------------
// Unregistered-Spawn Cleanup Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn spawn_grouped(script: &str) -> Child {
        let mut command = Command::new("/bin/sh");
        command
            .arg("-c")
            .arg(script)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .process_group(0);
        command.spawn().expect("spawn grouped test child")
    }

    fn wait_until_group_is_quiet(pid: u32) {
        let deadline = Instant::now() + Duration::from_secs(5);
        while !live_group_members(pid).is_empty() {
            assert!(Instant::now() < deadline, "test child did not exit");
            thread::sleep(POLL_INTERVAL);
        }
    }

    /*
      A solver which answers and exits before the supervisor's first
      identity read is an ordinary outcome, not a start failure: the
      leader is still ours to reap, so its captured output and exit
      status classify the run exactly as a slower solver's would.

      Only macOS discriminates here. Where process inspection resolves an
      exited-but-unreaped process, registration takes its first branch and
      this passes whether or not the exited-leader branch exists.
    */
    #[test]
    fn leader_that_exits_before_registration_keeps_its_output() {
        let mut command = Command::new("/bin/sh");
        command
            .arg("-c")
            .arg("printf 'answered\\n'")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .process_group(0);
        let child = command.spawn().expect("spawn grouped test child");
        let pid = child.id();
        wait_until_group_is_quiet(pid);
        let registry = ProcessRegistry::new(pid).expect("register a leader which already exited");
        assert!(registry.live_matching_descendants().is_empty());
        let mut process = SpawnedProcess {
            child: Some(child),
            registry,
            cleaned: false,
        };
        let mut pipes = process.take_pipes().expect("own the leader's pipes");
        let mut captured = String::new();
        std::io::Read::read_to_string(&mut pipes.stdout, &mut captured)
            .expect("read the exited leader's output");
        let exit = process.supervise(&CancellationToken::new(), &AtomicBool::new(false));
        assert_eq!(captured, "answered\n");
        assert_eq!(exit.reason, StopReason::Exited);
        assert!(exit.status.expect("reap the exited leader").success());
        assert_eq!(exit.cleanup_error, None);
    }

    /*
      A group whose only member is an unreaped zombie either accepts
      the signal or fails with ESRCH or EPERM (macOS reports EPERM).
      All three are provisional for cleanup and record no error.
    */
    #[test]
    fn zombie_only_group_signal_is_provisional() {
        let child = spawn_grouped("exit 0");
        let pid = child.id();
        wait_until_group_is_quiet(pid);
        let result = signal_group(pid, libc::SIGKILL);
        if let Err(error) = &result {
            assert!(
                matches!(error.raw_os_error(), Some(libc::ESRCH) | Some(libc::EPERM)),
                "unexpected zombie-group errno: {error}"
            );
        }
        let mut errors = Vec::new();
        record_group_signal_error(
            result,
            "kill unregistered Vampire process group",
            &mut errors,
        );
        assert!(errors.is_empty(), "provisional signal recorded {errors:?}");
        cleanup_unregistered_spawn(child, pid, "registration".to_string());
    }

    /*
      A child that died before identity registration is reaped and its
      empty group verified; the result is an ordinary start failure,
      never a run-global cleanup failure.
    */
    #[test]
    fn dead_unregistered_child_is_an_ordinary_failure() {
        let child = spawn_grouped("exit 0");
        let pid = child.id();
        wait_until_group_is_quiet(pid);
        match cleanup_unregistered_spawn(child, pid, "identity read failed".to_string()) {
            SpawnError::Failed(detail) => {
                assert_eq!(detail, "identity read failed");
            }
            SpawnError::CleanupFailed(detail) => {
                panic!("verified-clean group escalated: {detail}");
            }
        }
    }

    /*
      A live unregistered child is killed, reaped, and verified gone;
      still an ordinary start failure.
    */
    #[test]
    fn live_unregistered_child_is_an_ordinary_failure() {
        let child = spawn_grouped("sleep 30");
        let pid = child.id();
        match cleanup_unregistered_spawn(child, pid, "identity read failed".to_string()) {
            SpawnError::Failed(detail) => {
                assert_eq!(detail, "identity read failed");
            }
            SpawnError::CleanupFailed(detail) => {
                panic!("killable live group escalated: {detail}");
            }
        }
        assert!(live_group_members(pid).is_empty());
    }
}

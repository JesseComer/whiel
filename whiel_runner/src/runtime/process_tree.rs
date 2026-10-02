//! Caller-neutral process-tree identity and descendant discovery.
//!
//! A registry records process start identities, not bare PIDs.  A caller can
//! therefore retain ownership of an observed descendant after it leaves the
//! leader's process group without signaling an unrelated process after PID
//! reuse.

#[cfg(target_os = "linux")]
use std::collections::HashSet;
use std::collections::{HashMap, VecDeque};
#[cfg(target_os = "linux")]
use std::fs;
use std::io;
use std::time::{Duration, Instant};

// ------------------------------------------------------------
// Process Identity Registry
// ------------------------------------------------------------

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct ProcessIdentity {
    pub(crate) pid: u32,
    start_id: u128,
}

#[derive(Clone, Debug)]
pub(crate) struct RegisteredProcess {
    pub(crate) identity: ProcessIdentity,
    pub(crate) depth: usize,
}

#[derive(Debug)]
pub(crate) struct ProcessRegistry {
    root_pid: u32,
    root_identity: ProcessIdentity,
    processes: HashMap<u32, RegisteredProcess>,
}

impl ProcessRegistry {
    pub(crate) fn new(root_pid: u32) -> Result<Self, String> {
        let deadline = Instant::now() + Duration::from_millis(100);
        let root_identity = loop {
            if let Some(identity) = process_identity(root_pid) {
                break identity;
            }
            if Instant::now() >= deadline {
                return Err("read process leader identity".to_string());
            }
            std::thread::sleep(Duration::from_millis(1));
        };
        let mut registry = Self {
            root_pid,
            root_identity,
            processes: HashMap::new(),
        };
        registry.refresh();
        Ok(registry)
    }

    pub(crate) fn refresh(&mut self) {
        self.processes.retain(|_, process| {
            process_identity(process.identity.pid).as_ref() == Some(&process.identity)
        });
        let mut queue = VecDeque::new();
        if process_identity(self.root_pid).as_ref() == Some(&self.root_identity) {
            queue.push_back(RegisteredProcess {
                identity: self.root_identity.clone(),
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

    pub(crate) fn live_matching_descendants(&self) -> Vec<RegisteredProcess> {
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

    pub(crate) fn owned_live_descendants(&self, group: u32) -> Vec<RegisteredProcess> {
        let mut processes = self.live_matching_descendants();
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
}

// ------------------------------------------------------------
// Identity-Aware Signaling
// ------------------------------------------------------------

pub(crate) fn signal_identity(identity: &ProcessIdentity, signal: i32) -> io::Result<()> {
    if process_identity(identity.pid).as_ref() != Some(identity) {
        return Ok(());
    }
    let result = unsafe { libc::kill(identity.pid as libc::pid_t, signal) };
    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

pub(crate) fn signal_group(group: u32, signal: i32) -> io::Result<()> {
    let result = unsafe { libc::killpg(group as libc::pid_t, signal) };
    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
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
    // Linux records children per spawning thread. Reading only the process
    // leader's file misses a worker created by another thread, including one
    // that immediately leaves the inherited process group or session.
    let Ok(tasks) = fs::read_dir(format!("/proc/{pid}/task")) else {
        return Vec::new();
    };
    let mut children = HashSet::new();
    for task in tasks.flatten() {
        let contents = fs::read_to_string(task.path().join("children")).unwrap_or_default();
        children.extend(
            contents
                .split_whitespace()
                .filter_map(|child| child.parse::<u32>().ok()),
        );
    }
    children.into_iter().collect()
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

#[cfg(all(test, target_os = "linux"))]
mod linux_tests {
    use std::process::Command;
    use std::sync::mpsc;
    use std::thread;
    use std::time::{Duration, Instant};

    use super::direct_child_pids;

    #[test]
    fn discovers_a_child_spawned_by_a_nonleader_thread() {
        let (pid_sender, pid_receiver) = mpsc::channel();
        let (release_sender, release_receiver) = mpsc::channel();
        let child_thread = thread::spawn(move || {
            let mut child = Command::new("/bin/sleep")
                .arg("60")
                .spawn()
                .expect("start child from nonleader thread");
            pid_sender.send(child.id()).unwrap();
            release_receiver.recv().unwrap();
            let _ = child.kill();
            child.wait().expect("reap nonleader-thread child");
        });
        let child_pid = pid_receiver.recv().unwrap();
        let deadline = Instant::now() + Duration::from_secs(1);
        let discovered = loop {
            if direct_child_pids(std::process::id()).contains(&child_pid) {
                break true;
            }
            if Instant::now() >= deadline {
                break false;
            }
            thread::sleep(Duration::from_millis(5));
        };
        release_sender.send(()).unwrap();
        child_thread.join().unwrap();
        assert!(discovered, "child of a nonleader thread was not discovered");
    }
}

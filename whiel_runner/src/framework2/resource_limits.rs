//! Operational I/O allowances, not semantic candidate limits or total RSS bounds.
use serde::{Deserialize, Serialize};
use std::io;
use std::sync::{Arc, Mutex};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CampaignResourceLimits {
    pub api_traffic_bytes: u64,
    pub api_messages: u64,
    pub artifact_bytes: u64,
    pub artifact_files: u64,
    pub workspace_bytes: u64,
    pub workspace_files: u64,
    pub minimum_free_bytes: u64,
    pub workspace_entries: u64,
    pub workspace_directories: u64,
}
impl Default for CampaignResourceLimits {
    fn default() -> Self {
        Self {
            api_traffic_bytes: 1024 * 1024 * 1024,
            api_messages: 16_384,
            artifact_bytes: 4 * 1024 * 1024 * 1024,
            artifact_files: 50_000,
            workspace_bytes: 8 * 1024 * 1024 * 1024,
            workspace_files: 100_000,
            minimum_free_bytes: 2 * 1024 * 1024 * 1024,
            workspace_entries: 200_000,
            workspace_directories: 25_000,
        }
    }
}

/// Workspace-guard defaults under `--retention all` when the caller gave no
/// explicit `--workspace-*` flag for the limit in question.
///
/// The workspace guard counts a whole campaign's live material, not one
/// input's, so under `all` retention every earlier input's ledger,
/// consultation records and artifacts are still on the count when a later
/// input runs. The ordinary per-input defaults therefore stop a long run
/// partway through, against its predecessors' residue rather than anything
/// the current input did; these raised figures give a retained run the room
/// its own retention requires.
pub const RETAINED_WORKSPACE_BYTES: u64 = 68_719_476_736;
pub const RETAINED_WORKSPACE_FILES: u64 = 1_000_000;
pub const RETAINED_WORKSPACE_ENTRIES: u64 = 2_000_000;
pub const RETAINED_WORKSPACE_DIRECTORIES: u64 = 250_000;

/// Which of the five workspace-guard flags (`--workspace-bytes`,
/// `--workspace-files`, `--minimum-free-bytes`, `--workspace-entries`,
/// `--workspace-directories`) a `campaign certify` invocation gave
/// explicitly, as opposed to leaving the field to some default.
///
/// A standalone `campaign certify --run DIR` needs this to tell "this
/// figure is the ordinary `--retention`-keyed default" from "the operator
/// asked for this exact number", when it considers adopting the run's own
/// recorded limits for whichever fields were left to default.
/// `campaign run --certify deferred` never makes that decision — it
/// inherits a live guard instead of resolving its own — so its own config
/// marks every field given.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkspaceLimitsGiven {
    pub workspace_bytes: bool,
    pub workspace_files: bool,
    pub minimum_free_bytes: bool,
    pub workspace_entries: bool,
    pub workspace_directories: bool,
}
impl WorkspaceLimitsGiven {
    /// Every field was given explicitly, or its resolution is otherwise not
    /// this caller's decision to make (the deferred path, which inherits a
    /// live guard instead).
    pub const ALL: Self = Self {
        workspace_bytes: true,
        workspace_files: true,
        minimum_free_bytes: true,
        workspace_entries: true,
        workspace_directories: true,
    };
    /// Whether every one of the five flags was given, i.e. there is nothing
    /// left for a recorded run's own settings to fill in.
    pub fn all_given(&self) -> bool {
        self.workspace_bytes
            && self.workspace_files
            && self.minimum_free_bytes
            && self.workspace_entries
            && self.workspace_directories
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn api_resource_names_round_trip_and_reject_native_traffic_fields() {
        let limits = CampaignResourceLimits::default();
        let value = serde_json::to_value(&limits).unwrap();
        assert_eq!(
            serde_json::from_value::<CampaignResourceLimits>(value.clone()).unwrap(),
            limits
        );
        for (current, old) in [
            ("api_traffic_bytes", "provider_traffic_bytes"),
            ("api_messages", "provider_messages"),
        ] {
            let mut stale = value.clone();
            let field = stale.as_object_mut().unwrap().remove(current).unwrap();
            stale[old] = field;
            assert!(serde_json::from_value::<CampaignResourceLimits>(stale).is_err());
        }
    }
}

// Sampled workspace protection complements exact artifact writes. It is not a
// filesystem quota: direct child writes may overshoot between observations.
use crate::runtime::CancellationToken;
use std::collections::HashSet;
use std::ffi::CString;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::Condvar;

/// How many times one observation is attempted when the tree changes under
/// the scan, and the pause before each retry (scaled by the attempt, capped).
const SCAN_ATTEMPTS: u32 = 12;
const SCAN_RETRY_PAUSE: std::time::Duration = std::time::Duration::from_millis(25);

#[derive(Debug)]
pub struct SpaceGuard {
    limits: CampaignResourceLimits,
    roots: Mutex<Vec<PathBuf>>,
    failure: Mutex<Option<String>>,
    cancellation: CancellationToken,
    scan: Mutex<()>,
}
impl SpaceGuard {
    pub(crate) fn new(
        limits: &CampaignResourceLimits,
        root: PathBuf,
        cancellation: CancellationToken,
    ) -> Arc<Self> {
        Arc::new(Self {
            limits: limits.clone(),
            roots: Mutex::new(vec![root]),
            failure: Mutex::new(None),
            cancellation,
            scan: Mutex::new(()),
        })
    }
    pub(crate) fn register(&self, path: PathBuf) {
        let mut roots = self.roots.lock().unwrap_or_else(|p| p.into_inner());
        if !roots.iter().any(|root| path.starts_with(root)) {
            roots.retain(|root| !root.starts_with(&path));
            if roots.len() as u64 >= self.limits.workspace_entries {
                drop(roots);
                self.latch("owned-root entry allowance exceeded".into());
                return;
            }
            roots.push(path);
        }
    }
    pub(crate) fn failure(&self) -> Option<String> {
        self.failure
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .clone()
    }
    fn latch(&self, detail: String) -> String {
        let mut failure = self.failure.lock().unwrap_or_else(|p| p.into_inner());
        let detail =
            failure.get_or_insert_with(|| format!("resource_exhausted: workspace guard: {detail}"));
        self.cancellation.cancel();
        detail.clone()
    }
    fn cancelled_scan(&self) -> String {
        self.failure()
            .unwrap_or_else(|| "cancelled: workspace scan stopped".into())
    }
    #[cfg(test)]
    fn check(&self) -> Result<(), String> {
        self.check_with_stop(|| false)
    }
    fn check_with_stop(&self, stopped: impl Fn() -> bool) -> Result<(), String> {
        self.check_with_probe(stopped, free_bytes)
    }
    fn check_with_probe(
        &self,
        stopped: impl Fn() -> bool,
        mut available: impl FnMut(&Path) -> io::Result<u64>,
    ) -> Result<(), String> {
        let stopped = || self.cancellation.is_cancelled() || stopped();
        // A queued observation must also be cancellable while another scan owns
        // the lock. Individual filesystem calls remain OS-blocking operations.
        let _scan = loop {
            if let Some(failure) = self.failure() {
                return Err(failure);
            }
            if stopped() {
                return Err(self.cancelled_scan());
            }
            match self.scan.try_lock() {
                Ok(lock) => break lock,
                Err(std::sync::TryLockError::Poisoned(error)) => break error.into_inner(),
                Err(std::sync::TryLockError::WouldBlock) => {
                    std::thread::park_timeout(std::time::Duration::from_millis(5));
                }
            }
        };
        let roots = self.roots.lock().unwrap_or_else(|p| p.into_inner()).clone();
        // Atomic publication and cleanup may invalidate a directory snapshot.
        // Retry the entire observation; never treat missing metadata as zero.
        // A tree that is being written quickly can invalidate several
        // snapshots in a row, so the retries are patient and spaced: giving
        // up early turns ordinary file churn into a resource refusal, which
        // stops the run it was meant to protect.
        for attempt in 0..SCAN_ATTEMPTS {
            if stopped() {
                return Err(self.cancelled_scan());
            }
            if attempt > 0 {
                std::thread::sleep(SCAN_RETRY_PAUSE * attempt.min(8));
            }
            let outcome = scan_space(&roots, &self.limits, &mut available, &stopped);
            if stopped() {
                return Err(self.cancelled_scan());
            }
            match outcome {
                Ok(()) => return Ok(()),
                Err(error)
                    if error.kind() == io::ErrorKind::NotFound && attempt + 1 < SCAN_ATTEMPTS =>
                {
                    continue;
                }
                Err(error) => return Err(self.latch(error.to_string())),
            }
        }
        unreachable!()
    }
    pub(crate) async fn checkpoint(self: &Arc<Self>) -> Result<(), String> {
        self.checkpoint_with_cancellation(&self.cancellation).await
    }
    pub(crate) async fn checkpoint_with_cancellation(
        self: &Arc<Self>,
        cancellation: &CancellationToken,
    ) -> Result<(), String> {
        let guard = Arc::clone(self);
        let cancellation = cancellation.clone();
        tokio::task::spawn_blocking(move || guard.check_with_stop(|| cancellation.is_cancelled()))
            .await
            .map_err(|error| self.latch(format!("space scan worker failed: {error}")))?
    }
}

pub(crate) struct SpaceMonitor {
    stop: Arc<(Mutex<bool>, Condvar)>,
    thread: Option<std::thread::JoinHandle<()>>,
}
impl SpaceMonitor {
    pub(crate) fn start(guard: Arc<SpaceGuard>) -> io::Result<Self> {
        let stop = Arc::new((Mutex::new(false), Condvar::new()));
        let signal = Arc::clone(&stop);
        let thread = std::thread::Builder::new()
            .name("campaign-space-guard".into())
            .spawn(move || {
                loop {
                    if guard
                        .check_with_stop(|| *signal.0.lock().unwrap_or_else(|p| p.into_inner()))
                        .is_err()
                    {
                        return;
                    }
                    let (lock, changed) = &*signal;
                    let stopped = lock.lock().unwrap_or_else(|p| p.into_inner());
                    if *stopped {
                        return;
                    }
                    let (stopped, _) = changed
                        .wait_timeout(stopped, std::time::Duration::from_secs(1))
                        .unwrap_or_else(|p| p.into_inner());
                    if *stopped {
                        return;
                    }
                }
            })?;
        Ok(Self {
            stop,
            thread: Some(thread),
        })
    }
}
impl Drop for SpaceMonitor {
    fn drop(&mut self) {
        let (lock, changed) = &*self.stop;
        *lock.lock().unwrap_or_else(|p| p.into_inner()) = true;
        changed.notify_all();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn free_bytes(path: &Path) -> io::Result<u64> {
    let path = CString::new(path.as_os_str().as_bytes())
        .map_err(|_| io::Error::other("space path contains NUL"))?;
    let mut statistics = std::mem::MaybeUninit::<libc::statvfs>::uninit();
    // statvfs initializes the structure only on success; pathname is NUL terminated.
    if unsafe { libc::statvfs(path.as_ptr(), statistics.as_mut_ptr()) } != 0 {
        return Err(io::Error::other(format!(
            "free-space query failed: {}",
            io::Error::last_os_error()
        )));
    }
    let statistics = unsafe { statistics.assume_init() };
    u64::try_from(statistics.f_bavail as u128 * statistics.f_frsize as u128)
        .map_err(|_| io::Error::other("free-space count overflow"))
}

fn scan_space(
    roots: &[PathBuf],
    limits: &CampaignResourceLimits,
    mut available: impl FnMut(&Path) -> io::Result<u64>,
    mut stopped: impl FnMut() -> bool,
) -> io::Result<()> {
    let mut visited = 0_u64;
    let mut directories = 0_u64;
    let mut files = 0_u64;
    let mut bytes = 0_u64;
    let mut devices = HashSet::new();
    let mut stack = Vec::new();
    let inspect = |path: &Path| {
        std::fs::symlink_metadata(path).map_err(|error| {
            io::Error::new(
                error.kind(),
                format!("metadata {}: {error}", path.display()),
            )
        })
    };
    let mut running = || {
        if stopped() {
            Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "workspace scan stopped",
            ))
        } else {
            Ok(())
        }
    };
    for root in roots {
        running()?;
        if stack.len() as u64 >= limits.workspace_entries {
            return Err(io::Error::other("visited-entry allowance exceeded"));
        }
        let metadata = inspect(root)?;
        if !metadata.is_dir() || metadata.file_type().is_symlink() {
            return Err(io::Error::other(format!(
                "owned root is not a directory: {}",
                root.display()
            )));
        }
        stack.push(root.clone());
    }
    while let Some(path) = stack.pop() {
        running()?;
        visited = visited
            .checked_add(1)
            .ok_or_else(|| io::Error::other("visited-entry count overflow"))?;
        if visited > limits.workspace_entries {
            return Err(io::Error::other("visited-entry allowance exceeded"));
        }
        let metadata = inspect(&path)?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        running()?;
        if devices.insert(metadata.dev()) && available(&path)? < limits.minimum_free_bytes {
            return Err(io::Error::other(format!(
                "free space below {} bytes",
                limits.minimum_free_bytes
            )));
        }
        if metadata.is_file() {
            files = files
                .checked_add(1)
                .ok_or_else(|| io::Error::other("file count overflow"))?;
            bytes = bytes
                .checked_add(metadata.len())
                .ok_or_else(|| io::Error::other("workspace byte count overflow"))?;
            if files > limits.workspace_files || bytes > limits.workspace_bytes {
                return Err(io::Error::other(
                    "live workspace byte/file allowance exceeded",
                ));
            }
        } else if metadata.is_dir() {
            directories = directories
                .checked_add(1)
                .ok_or_else(|| io::Error::other("directory count overflow"))?;
            if directories > limits.workspace_directories {
                return Err(io::Error::other("directory allowance exceeded"));
            }
            running()?;
            for entry in std::fs::read_dir(&path).map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!("read directory {}: {error}", path.display()),
                )
            })? {
                running()?;
                let entry = entry.map_err(|error| {
                    io::Error::new(error.kind(), format!("read directory entry: {error}"))
                })?;
                // Bound pending paths too, before allocating an unbounded traversal queue.
                if visited.saturating_add(stack.len() as u64) >= limits.workspace_entries {
                    return Err(io::Error::other("visited-entry allowance exceeded"));
                }
                stack.push(entry.path());
            }
        }
    }
    running()?;
    Ok(())
}

#[cfg(test)]
mod space_tests {
    use super::*;
    fn scan_space(
        roots: &[PathBuf],
        limits: &CampaignResourceLimits,
        available: impl FnMut(&Path) -> io::Result<u64>,
    ) -> io::Result<()> {
        super::scan_space(roots, limits, available, || false)
    }
    struct Directory(PathBuf);
    impl Directory {
        fn new(label: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "whiel-space-{label}-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    #[test]
    fn space_scan_limits_bytes_files_directories_entries_and_free_space() {
        let directory = Directory::new("limits");
        std::fs::write(directory.0.join("payload"), b"1234").unwrap();
        let limits = CampaignResourceLimits {
            workspace_bytes: 4,
            workspace_files: 1,
            workspace_entries: 2,
            workspace_directories: 1,
            minimum_free_bytes: 10,
            ..Default::default()
        };
        scan_space(std::slice::from_ref(&directory.0), &limits, |_| Ok(10)).unwrap();
        for changed in [
            CampaignResourceLimits {
                workspace_bytes: 3,
                ..limits.clone()
            },
            CampaignResourceLimits {
                workspace_files: 0,
                ..limits.clone()
            },
            CampaignResourceLimits {
                workspace_entries: 1,
                ..limits.clone()
            },
            CampaignResourceLimits {
                workspace_directories: 0,
                ..limits.clone()
            },
        ] {
            assert!(scan_space(std::slice::from_ref(&directory.0), &changed, |_| Ok(10)).is_err());
        }
        assert!(
            scan_space(std::slice::from_ref(&directory.0), &limits, |_| Ok(9))
                .unwrap_err()
                .to_string()
                .contains("free space")
        );
        assert!(
            scan_space(std::slice::from_ref(&directory.0), &limits, |_| Err(
                io::Error::other("fixture statvfs failure")
            ))
            .unwrap_err()
            .to_string()
            .contains("fixture statvfs failure")
        );
    }
    #[test]
    fn scans_do_not_follow_symlinks_and_missing_metadata_is_not_zero() {
        let directory = Directory::new("links");
        let outside = Directory::new("outside");
        std::fs::write(outside.0.join("large"), vec![0; 100]).unwrap();
        std::os::unix::fs::symlink(&outside.0, directory.0.join("linked")).unwrap();
        scan_space(
            std::slice::from_ref(&directory.0),
            &CampaignResourceLimits {
                workspace_bytes: 1,
                ..Default::default()
            },
            |_| Ok(u64::MAX),
        )
        .unwrap();
        assert_eq!(
            scan_space(&[directory.0.join("missing")], &Default::default(), |_| Ok(
                u64::MAX
            ))
            .unwrap_err()
            .kind(),
            io::ErrorKind::NotFound
        );
        let cancel = CancellationToken::new();
        let guard = SpaceGuard::new(
            &Default::default(),
            directory.0.join("missing"),
            cancel.clone(),
        );
        assert!(guard.check().unwrap_err().contains("metadata"));
        assert!(cancel.is_cancelled());
        std::fs::create_dir(directory.0.join("missing")).unwrap();
        assert!(
            guard.check().is_err(),
            "resource failure must remain latched"
        );
    }
    #[test]
    fn cancellation_stops_between_roots_and_directory_entries() {
        let directory = Directory::new("cancel-traversal");
        std::fs::write(directory.0.join("one"), b"1").unwrap();
        std::fs::write(directory.0.join("two"), b"2").unwrap();
        for stop_at in [2, 6] {
            let cancellation = CancellationToken::new();
            let mut visits = 0;
            let roots = if stop_at == 2 {
                vec![directory.0.clone(), directory.0.join("missing")]
            } else {
                vec![directory.0.clone()]
            };
            let error = super::scan_space(
                &roots,
                &Default::default(),
                |_| Ok(u64::MAX),
                || {
                    visits += 1;
                    if visits == stop_at {
                        cancellation.cancel();
                    }
                    cancellation.is_cancelled()
                },
            )
            .unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::Interrupted);
            assert_eq!(visits, stop_at);
        }
    }
    #[test]
    fn a_tree_that_changes_under_several_scans_in_a_row_is_not_a_refusal() {
        let directory = Directory::new("churn");
        let campaign = CancellationToken::new();
        let guard = SpaceGuard::new(&Default::default(), directory.0.clone(), campaign.clone());
        let mut probes = 0;
        guard
            .check_with_probe(
                || false,
                |_| {
                    probes += 1;
                    if probes <= 5 {
                        Err(io::Error::new(
                            io::ErrorKind::NotFound,
                            "transient fixture rename",
                        ))
                    } else {
                        Ok(u64::MAX)
                    }
                },
            )
            .unwrap();
        assert_eq!(probes, 6);
        assert!(!campaign.is_cancelled());
        assert!(guard.failure().is_none());
    }
    #[test]
    fn cancellation_before_retry_does_not_latch_a_resource_failure() {
        let directory = Directory::new("cancel-retry");
        let campaign = CancellationToken::new();
        let phase = CancellationToken::new();
        let guard = SpaceGuard::new(&Default::default(), directory.0.clone(), campaign.clone());
        let mut probes = 0;
        let error = guard
            .check_with_probe(
                || phase.is_cancelled(),
                |_| {
                    probes += 1;
                    phase.cancel();
                    Err(io::Error::new(
                        io::ErrorKind::NotFound,
                        "transient fixture rename",
                    ))
                },
            )
            .unwrap_err();
        assert!(error.starts_with("cancelled:"));
        assert_eq!(probes, 1);
        assert!(guard.failure().is_none());
        assert!(!campaign.is_cancelled());
    }
    #[test]
    fn queued_scan_cancellation_returns_without_waiting_for_active_scan() {
        let directory = Directory::new("cancel-queued");
        let guard = SpaceGuard::new(
            &Default::default(),
            directory.0.clone(),
            CancellationToken::new(),
        );
        let held = guard.scan.lock().unwrap();
        let phase = CancellationToken::new();
        let (entered_tx, entered_rx) = std::sync::mpsc::channel();
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let worker_guard = Arc::clone(&guard);
        let worker_phase = phase.clone();
        let worker = std::thread::spawn(move || {
            let error = worker_guard
                .check_with_probe(
                    || {
                        let _ = entered_tx.send(());
                        worker_phase.is_cancelled()
                    },
                    |_| panic!("cancelled queued scan must never visit a root"),
                )
                .unwrap_err();
            done_tx.send(error).unwrap();
        });
        entered_rx
            .recv_timeout(std::time::Duration::from_secs(1))
            .unwrap();
        phase.cancel();
        let error = done_rx.recv_timeout(std::time::Duration::from_secs(1));
        drop(held);
        worker.join().unwrap();
        assert!(error.unwrap().starts_with("cancelled:"));
        assert!(guard.failure().is_none());
    }
    #[test]
    fn monitor_stop_interrupts_a_queued_scan_and_joins() {
        let directory = Directory::new("stop-queued");
        let cancellation = CancellationToken::new();
        let guard = SpaceGuard::new(
            &Default::default(),
            directory.0.clone(),
            cancellation.clone(),
        );
        let held = guard.scan.lock().unwrap();
        let monitor = SpaceMonitor::start(Arc::clone(&guard)).unwrap();
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            drop(monitor);
            done_tx.send(()).unwrap();
        });
        let joined = done_rx.recv_timeout(std::time::Duration::from_secs(1));
        drop(held);
        worker.join().unwrap();
        joined.unwrap();
        assert!(guard.failure().is_none());
        assert!(!cancellation.is_cancelled());
    }
    #[test]
    fn monitor_stop_during_traversal_does_not_latch() {
        let directory = Directory::new("stop-traversal");
        std::fs::write(directory.0.join("payload"), b"1").unwrap();
        let cancellation = CancellationToken::new();
        let guard = SpaceGuard::new(
            &Default::default(),
            directory.0.clone(),
            cancellation.clone(),
        );
        let signal = Arc::new((Mutex::new(false), Condvar::new()));
        let error = guard
            .check_with_probe(
                || *signal.0.lock().unwrap(),
                |_| {
                    *signal.0.lock().unwrap() = true;
                    Ok(u64::MAX)
                },
            )
            .unwrap_err();
        assert!(error.starts_with("cancelled:"));
        assert!(guard.failure().is_none());
        assert!(!cancellation.is_cancelled());
    }
    #[tokio::test]
    async fn phase_cancelled_checkpoint_skips_missing_root_without_resource_failure() {
        let directory = Directory::new("phase-checkpoint");
        let campaign = CancellationToken::new();
        let phase = CancellationToken::new();
        let guard = SpaceGuard::new(
            &Default::default(),
            directory.0.join("missing"),
            campaign.clone(),
        );
        phase.cancel();
        assert!(
            guard
                .checkpoint_with_cancellation(&phase)
                .await
                .unwrap_err()
                .starts_with("cancelled:")
        );
        assert!(guard.failure().is_none());
        assert!(!campaign.is_cancelled());
    }
    #[tokio::test]
    async fn sampled_child_scratch_growth_cancels_and_joins_monitor() {
        let directory = Directory::new("campaign");
        let scratch = Directory::new("child");
        let cancel = CancellationToken::new();
        let guard = SpaceGuard::new(
            &CampaignResourceLimits {
                workspace_bytes: 4,
                minimum_free_bytes: 1,
                ..Default::default()
            },
            directory.0.clone(),
            cancel.clone(),
        );
        guard.register(scratch.0.clone());
        guard.checkpoint().await.unwrap();
        let monitor = SpaceMonitor::start(Arc::clone(&guard)).unwrap();
        let path = scratch.0.join("child-output");
        let status = std::process::Command::new("/bin/sh")
            .args(["-c", "printf 12345 > \"$1\"", "fixture"])
            .arg(&path)
            .status()
            .unwrap();
        assert!(status.success());
        tokio::time::timeout(std::time::Duration::from_secs(3), cancel.cancelled())
            .await
            .unwrap();
        assert!(guard.failure().unwrap().contains("live workspace"));
        drop(monitor);
        std::fs::remove_file(path).unwrap();
        assert!(guard.checkpoint().await.is_err());
    }
}

//! Filesystem ownership for cooperating certificate writers.
//!
//! A unique name is only a candidate: ownership starts at successful exclusive
//! creation. Output leases use persistent lock files (unlinking a lock would
//! let a third process lock a different inode). Final promotion also refuses
//! replacement in the filesystem operation itself, including nonparticipants.

use std::fs::{File, OpenOptions};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// An exclusively created directory, removed on drop unless retained.
#[derive(Debug)]
pub(crate) struct OwnedDirectory {
    path: PathBuf,
    retained: bool,
}

impl OwnedDirectory {
    pub(crate) fn create(path: PathBuf) -> io::Result<Self> {
        std::fs::create_dir(&path)?;
        Ok(Self {
            path,
            retained: false,
        })
    }

    pub(crate) fn fresh(parent: &Path, prefix: &str) -> io::Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        std::fs::create_dir_all(parent)?;
        for _ in 0..128 {
            let sequence = NEXT
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
                .map_err(|_| io::Error::other("owned directory sequence exhausted"))?;
            let path = parent.join(format!("{prefix}-{}-{sequence}", std::process::id()));
            match Self::create(path) {
                Ok(directory) => return Ok(directory),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error),
            }
        }
        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "owned directory collision limit reached",
        ))
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) fn preserve(&mut self) {
        self.retained = true;
    }

    /// Leave evidence for the enclosing, already owned job/staging tree.
    pub(crate) fn retain(mut self) -> PathBuf {
        self.preserve();
        self.path.clone()
    }
}

impl Drop for OwnedDirectory {
    fn drop(&mut self) {
        if !self.retained
            && let Err(error) = std::fs::remove_dir_all(&self.path)
            && error.kind() != io::ErrorKind::NotFound
        {
            eprintln!(
                "warning: remove owned directory {}: {error}",
                self.path.display()
            );
        }
    }
}

/// Nonblocking cross-process ownership of one destination or shared record.
/// Closing the file releases ownership, including after process termination.
#[derive(Debug)]
pub(crate) struct PathLease {
    _file: File,
}

impl PathLease {
    pub(crate) fn acquire(path: &Path) -> io::Result<Self> {
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            let _ = path;
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "output locking requires macOS or Linux",
            ))
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            use std::os::fd::AsRawFd;
            use std::os::unix::fs::OpenOptionsExt;
            let parent = path
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."));
            let name = path.file_name().ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidInput, "output path has no file name")
            })?;
            std::fs::create_dir_all(parent)?;
            // Canonicalize the parent so relative paths and symlink aliases use
            // the same lock inode. The destination itself may not exist yet.
            let parent = std::fs::canonicalize(parent)?;
            let identity = parent.join(name);
            let digest = crate::encoding::bytes_sha256(identity.as_os_str().as_encoded_bytes());
            let lock = parent.join(format!(".whiel-output-{digest}.lock"));
            let file = OpenOptions::new()
                .create(true)
                .truncate(false)
                .read(true)
                .write(true)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(lock)?;
            if !file.metadata()?.is_file() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "output lock is not a regular file",
                ));
            }
            // Each acquisition opens its own file description, so flock also
            // excludes competing writers in this same process.
            if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(Self { _file: file })
        }
    }
}

/// Whether any directory entry exists, including a dangling symlink.
pub(crate) fn entry_exists(path: &Path) -> io::Result<bool> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

/// One atomic same-filesystem rename, never replacing an existing entry.
/// Unsupported kernels/filesystems fail closed; there is no copy fallback.
pub(crate) fn rename_noreplace(from: &Path, to: &Path) -> io::Result<()> {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        use std::ffi::CString;
        use std::os::unix::ffi::OsStrExt;
        let from = CString::new(from.as_os_str().as_bytes())?;
        let to = CString::new(to.as_os_str().as_bytes())?;
        #[cfg(target_os = "macos")]
        let result = unsafe { libc::renamex_np(from.as_ptr(), to.as_ptr(), libc::RENAME_EXCL) };
        #[cfg(target_os = "linux")]
        let result = unsafe {
            libc::syscall(
                libc::SYS_renameat2,
                libc::AT_FDCWD,
                from.as_ptr(),
                libc::AT_FDCWD,
                to.as_ptr(),
                libc::RENAME_NOREPLACE,
            )
        };
        if result == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (from, to);
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "exclusive rename requires macOS or Linux",
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{BufRead, Write};
    use std::process::{Command, Stdio};
    use std::sync::{Arc, Barrier};

    #[test]
    fn exclusive_creation_preserves_existing_tree_and_dangling_symlink() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-owned-create").unwrap();
        let path = root.path().join("attempt");
        let first = OwnedDirectory::create(path.clone()).unwrap();
        std::fs::write(path.join("sentinel"), b"owner").unwrap();
        assert_eq!(
            OwnedDirectory::create(path.clone()).unwrap_err().kind(),
            io::ErrorKind::AlreadyExists
        );
        assert_eq!(std::fs::read(path.join("sentinel")).unwrap(), b"owner");
        drop(first);
        assert!(!path.exists());
        let retry = OwnedDirectory::create(path.clone()).unwrap();
        drop(retry);
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(root.path().join("absent"), &path).unwrap();
            assert!(entry_exists(&path).unwrap());
            assert_eq!(
                OwnedDirectory::create(path.clone()).unwrap_err().kind(),
                io::ErrorKind::AlreadyExists
            );
            assert!(
                std::fs::symlink_metadata(&path)
                    .unwrap()
                    .file_type()
                    .is_symlink()
            );
        }
    }

    #[test]
    fn concurrent_promotions_have_one_winner_and_preserve_the_losing_source() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-owned-promote").unwrap();
        let destination = root.path().join("Certificate");
        let barrier = Arc::new(Barrier::new(2));
        let handles: Vec<_> = (0..2)
            .map(|index| {
                let source = root.path().join(format!("source-{index}"));
                std::fs::create_dir(&source).unwrap();
                std::fs::write(source.join("owner"), index.to_string()).unwrap();
                let destination = destination.clone();
                let barrier = barrier.clone();
                std::thread::spawn(move || {
                    barrier.wait();
                    (
                        index,
                        source.clone(),
                        rename_noreplace(&source, &destination),
                    )
                })
            })
            .collect();
        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert_eq!(results.iter().filter(|r| r.2.is_ok()).count(), 1);
        let winner = results.iter().find(|r| r.2.is_ok()).unwrap();
        let loser = results.iter().find(|r| r.2.is_err()).unwrap();
        assert_eq!(
            loser.2.as_ref().unwrap_err().kind(),
            io::ErrorKind::AlreadyExists
        );
        assert_eq!(
            std::fs::read_to_string(destination.join("owner")).unwrap(),
            winner.0.to_string()
        );
        assert_eq!(
            std::fs::read_to_string(loser.1.join("owner")).unwrap(),
            loser.0.to_string()
        );
        assert!(!winner.1.exists());
    }

    #[test]
    fn promotion_refuses_even_an_empty_destination_or_dangling_symlink() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-owned-existing").unwrap();
        let source = root.path().join("source");
        std::fs::create_dir(&source).unwrap();
        std::fs::write(source.join("proof"), b"checked").unwrap();
        let destination = root.path().join("destination");
        std::fs::create_dir(&destination).unwrap();
        assert_eq!(
            rename_noreplace(&source, &destination).unwrap_err().kind(),
            io::ErrorKind::AlreadyExists
        );
        assert!(source.join("proof").exists());
        assert_eq!(std::fs::read_dir(&destination).unwrap().count(), 0);
        #[cfg(unix)]
        {
            std::fs::remove_dir(&destination).unwrap();
            std::os::unix::fs::symlink(root.path().join("absent"), &destination).unwrap();
            assert_eq!(
                rename_noreplace(&source, &destination).unwrap_err().kind(),
                io::ErrorKind::AlreadyExists
            );
            assert!(
                std::fs::symlink_metadata(&destination)
                    .unwrap()
                    .file_type()
                    .is_symlink()
            );
        }
    }

    #[test]
    fn lease_child() {
        let Some(path) = std::env::var_os("WHIEL_OWNED_PATH_CHILD") else {
            return;
        };
        let _lease = PathLease::acquire(Path::new(&path)).unwrap();
        println!("lease-acquired");
        std::io::stdout().flush().unwrap();
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();
    }

    #[test]
    fn leases_exclude_other_processes_and_release_after_exit_or_kill() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-owned-process").unwrap();
        let destination = root.path().join("Certificate");
        for kill in [false, true] {
            let mut child = Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "runtime::owned_path::tests::lease_child",
                    "--nocapture",
                ])
                .env("WHIEL_OWNED_PATH_CHILD", &destination)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .unwrap();
            let mut output = std::io::BufReader::new(child.stdout.take().unwrap());
            let mut line = String::new();
            loop {
                assert_ne!(
                    output.read_line(&mut line).unwrap(),
                    0,
                    "child ended before owning the path"
                );
                if line.contains("lease-acquired") {
                    break;
                }
                line.clear();
            }
            assert_eq!(
                PathLease::acquire(&destination).unwrap_err().kind(),
                io::ErrorKind::WouldBlock
            );
            let independent = PathLease::acquire(&root.path().join("OtherCertificate")).unwrap();
            drop(independent);
            if kill {
                child.kill().unwrap();
            } else {
                child.stdin.take().unwrap().write_all(b"release\n").unwrap();
            }
            let status = child.wait().unwrap();
            assert_eq!(status.success(), !kill);
            drop(PathLease::acquire(&destination).unwrap());
        }
    }

    #[test]
    fn leases_treat_parent_aliases_as_the_same_output() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-owned-alias").unwrap();
        let _lease = PathLease::acquire(&root.path().join("Certificate")).unwrap();
        assert_eq!(
            PathLease::acquire(&root.path().join("./Certificate"))
                .unwrap_err()
                .kind(),
            io::ErrorKind::WouldBlock
        );
        #[cfg(unix)]
        {
            let alias = root.path().join("alias");
            std::os::unix::fs::symlink(root.path(), &alias).unwrap();
            assert_eq!(
                PathLease::acquire(&alias.join("Certificate"))
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::WouldBlock
            );
        }
    }

    #[tokio::test]
    async fn cancelling_a_waiting_attempt_releases_only_its_owned_paths() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-owned-cancel").unwrap();
        let destination = root.path().join("Certificate");
        let attempt = root.path().join("attempt");
        let foreign = root.path().join("foreign");
        std::fs::create_dir(&foreign).unwrap();
        std::fs::write(foreign.join("sentinel"), b"keep").unwrap();
        let (ready, wait_ready) = tokio::sync::oneshot::channel();
        let path = destination.clone();
        let private = attempt.clone();
        let task = tokio::spawn(async move {
            let _lease = PathLease::acquire(&path).unwrap();
            let _owned = OwnedDirectory::create(private).unwrap();
            ready.send(()).unwrap();
            std::future::pending::<()>().await;
        });
        wait_ready.await.unwrap();
        assert_eq!(
            PathLease::acquire(&destination).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        task.abort();
        assert!(task.await.unwrap_err().is_cancelled());
        assert!(!attempt.exists());
        assert!(!destination.exists());
        assert_eq!(std::fs::read(foreign.join("sentinel")).unwrap(), b"keep");
        drop(PathLease::acquire(&destination).unwrap());
        drop(OwnedDirectory::create(attempt).unwrap());
    }
}

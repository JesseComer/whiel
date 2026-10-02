//! Provider-neutral endpoint process ownership. No child output is interpreted.

use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use tokio::task::JoinHandle;

use crate::proposer_api::wire::ProposerCleanupError;
use crate::runtime::CancellationToken;
use crate::vampire::process::{SpawnError, SpawnedProcess};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Exit {
    pub(crate) successful: bool,
    pub(crate) cleaned: bool,
}

pub(crate) struct OwnedDirectory(pub(crate) PathBuf);

impl Drop for OwnedDirectory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct ChildState {
    worker: Option<JoinHandle<Exit>>,
    exit: Option<Exit>,
}

#[derive(Clone)]
pub(crate) struct ChildCleanup {
    cancellation: CancellationToken,
    state: Arc<tokio::sync::Mutex<ChildState>>,
    finished: Arc<AtomicBool>,
}

impl ChildCleanup {
    pub(crate) fn stop(&self) {
        self.cancellation.cancel();
    }

    pub(crate) fn finished(&self) -> bool {
        self.finished.load(Ordering::Acquire)
    }

    pub(crate) async fn join(&self, limit: Duration) -> Result<Exit, ProposerCleanupError> {
        tokio::time::timeout(limit, async {
            let mut state = self.state.lock().await;
            if let Some(exit) = state.exit {
                return Ok(exit);
            }
            let Some(worker) = state.worker.as_mut() else {
                return Err(ProposerCleanupError::Failed);
            };
            let exit = worker.await;
            state.worker = None;
            let exit = exit.unwrap_or(Exit {
                successful: false,
                cleaned: false,
            });
            state.exit = Some(exit);
            Ok(exit)
        })
        .await
        .map_err(|_| ProposerCleanupError::TimedOut)?
    }
}

pub(crate) struct EndpointChild(ChildCleanup);

impl EndpointChild {
    pub(crate) fn start(mut command: Command, directory: Arc<OwnedDirectory>) -> Self {
        command
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let cancellation = CancellationToken::new();
        let stop = cancellation.clone();
        let finished = Arc::new(AtomicBool::new(false));
        let done = Arc::clone(&finished);
        let worker = tokio::task::spawn_blocking(move || {
            let _directory = directory;
            let result = supervise(command, &stop);
            done.store(true, Ordering::Release);
            result
        });
        Self(ChildCleanup {
            cancellation,
            state: Arc::new(tokio::sync::Mutex::new(ChildState {
                worker: Some(worker),
                exit: None,
            })),
            finished,
        })
    }
    pub(crate) fn cleanup(&self) -> ChildCleanup {
        self.0.clone()
    }
    pub(crate) fn stop(&self) {
        self.0.stop();
    }
    pub(crate) fn finished(&self) -> bool {
        self.0.finished()
    }
    pub(crate) async fn join(&self, limit: Duration) -> Result<Exit, ProposerCleanupError> {
        self.0.join(limit).await
    }
}

impl Drop for EndpointChild {
    fn drop(&mut self) {
        self.stop();
    }
}

fn supervise(command: Command, cancellation: &CancellationToken) -> Exit {
    let mut child = match SpawnedProcess::spawn_command(command) {
        Ok(child) => child,
        Err(SpawnError::Failed(_)) => {
            return Exit {
                successful: false,
                cleaned: true,
            };
        }
        Err(SpawnError::CleanupFailed(_)) => {
            return Exit {
                successful: false,
                cleaned: false,
            };
        }
    };
    let pipes = match child.take_pipes() {
        Ok(pipes) => pipes,
        Err(_) => {
            return Exit {
                successful: false,
                cleaned: false,
            };
        }
    };
    let failed = AtomicBool::new(false);
    let stop_capture = AtomicBool::new(false);
    std::thread::scope(|scope| {
        let out = scope.spawn(|| drain(pipes.stdout, &stop_capture, &failed));
        let err = scope.spawn(|| drain(pipes.stderr, &stop_capture, &failed));
        let exit = child.supervise(cancellation, &failed);
        stop_capture.store(true, Ordering::Release);
        let stdout = out.join().unwrap_or(false);
        let stderr = err.join().unwrap_or(false);
        let captures = stdout && stderr;
        Exit {
            successful: captures && exit.status.is_ok_and(|status| status.success()),
            cleaned: captures && exit.cleanup_error.is_none(),
        }
    })
}

// Child output has no protocol meaning. Nonblocking drains cannot strand the
// supervisor on an inherited pipe after process cleanup finishes or fails.
fn drain(mut input: impl Read + AsRawFd, stop: &AtomicBool, failed: &AtomicBool) -> bool {
    let descriptor = input.as_raw_fd();
    let flags = unsafe { libc::fcntl(descriptor, libc::F_GETFL) };
    if flags < 0 || unsafe { libc::fcntl(descriptor, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0
    {
        failed.store(true, Ordering::Release);
        return false;
    }
    let mut bytes = [0; 8192];
    let mut after_stop = 0usize;
    loop {
        match input.read(&mut bytes) {
            Ok(0) => return true,
            Ok(read) => {
                if stop.load(Ordering::Acquire) {
                    after_stop += read;
                    if after_stop > 1024 * 1024 {
                        return false;
                    }
                }
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                if stop.load(Ordering::Acquire) {
                    return false;
                }
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(_) => {
                failed.store(true, Ordering::Release);
                return false;
            }
        }
    }
}

use std::io;
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::Duration;

/*
  Process-global interrupt state for the campaign runner.

  Vampire children run in their own process groups so the runtime can
  kill whole solver trees; the same isolation makes them invisible to a
  terminal SIGINT, and default signal disposition would terminate the
  runner without running any owned cleanup. The installed handler is
  async-signal-safe: the first SIGINT or SIGTERM records its signal
  number in one atomic, and a repeated signal hard-exits with the
  conventional 128-plus-signal code. Everything else polls the atomic.
*/

static REQUESTED_SIGNAL: AtomicI32 = AtomicI32::new(0);

const POLL_INTERVAL: Duration = Duration::from_millis(25);

extern "C" fn record_interrupt(signal: libc::c_int) {
    let previous = REQUESTED_SIGNAL.swap(signal, Ordering::SeqCst);
    if previous != 0 {
        // Second signal: the operator wants out now. `_exit` is
        // async-signal-safe; owned solver trees are abandoned.
        unsafe { libc::_exit(128 + signal) };
    }
}

/// Install the SIGINT and SIGTERM recorder for this process.
pub fn install() -> io::Result<()> {
    for signal in [libc::SIGINT, libc::SIGTERM] {
        // SAFETY: the handler only swaps one atomic and may `_exit`,
        // both async-signal-safe; the sigaction value is fully
        // initialized before registration.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = record_interrupt as usize;
            libc::sigemptyset(&mut action.sa_mask);
            action.sa_flags = libc::SA_RESTART;
            if libc::sigaction(signal, &action, std::ptr::null_mut()) != 0 {
                return Err(io::Error::last_os_error());
            }
        }
    }
    Ok(())
}

/// The recorded interrupt signal, if one arrived.
pub fn requested() -> Option<i32> {
    match REQUESTED_SIGNAL.load(Ordering::SeqCst) {
        0 => None,
        signal => Some(signal),
    }
}

/// Forget a recorded interrupt. Call once at campaign start.
pub fn clear() {
    REQUESTED_SIGNAL.store(0, Ordering::SeqCst);
}

/// Record an interrupt without an OS signal. Test seam.
pub fn simulate(signal: i32) {
    REQUESTED_SIGNAL.store(signal, Ordering::SeqCst);
}

/// Resolve with the signal number once an interrupt is recorded.
pub async fn wait() -> i32 {
    loop {
        if let Some(signal) = requested() {
            return signal;
        }
        tokio::time::sleep(POLL_INTERVAL).await;
    }
}

// ------------------------------------------------------------
// Interrupt Recording Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /*
      One test owns the global atomic end to end so parallel test
      threads never observe each other's interrupt state.
    */
    #[test]
    fn signals_record_once_and_clear() {
        clear();
        assert_eq!(requested(), None);

        install().expect("install interrupt handler");
        // SAFETY: raising SIGINT with the recorder installed only
        // swaps the atomic; a single raise cannot reach `_exit`.
        unsafe {
            libc::raise(libc::SIGINT);
        }
        assert_eq!(requested(), Some(libc::SIGINT));

        clear();
        assert_eq!(requested(), None);

        simulate(libc::SIGTERM);
        assert_eq!(requested(), Some(libc::SIGTERM));
        clear();
    }
}

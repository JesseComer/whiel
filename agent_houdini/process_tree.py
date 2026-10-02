# Author: Fangzhu Shen
"""Owned native processes, bounded pipe pumps and joined process-group cleanup.

Each native leader starts its own session, so C signals and joins the whole
group it created. A descendant that leaves that group on purpose is B's
provider-neutral cleanup fallback, not C's to chase. Pipe pumps are nonblocking
work in the same async owner, not detached threads.
"""

import asyncio
from dataclasses import dataclass
import errno
import os
import signal
import subprocess
import sys
import time

from .runtime_types import CleanupError
from .stop import joined


POLL_SECONDS = 0.01
TERM_SECONDS = 0.1
CLEANUP_SECONDS = 0.75
PUMP_BYTES = 256 * 1024


def _signal_group(pid, sig):
    try:
        os.killpg(pid, sig)
    except OSError as error:
        # macOS can reject a group containing only the unreaped zombie leader.
        # The subsequent exit check, not this provisional result, decides.
        if error.errno not in (errno.ESRCH, errno.EPERM):
            raise


def _exited(pid):
    return os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None


@dataclass(frozen=True, slots=True)
class ProcessResult:
    returncode: int
    reason: str
    stdout: bytes
    stderr: bytes
    stdout_bytes: int
    stderr_bytes: int
    capture_failed: bool
    prompt_written: bool


class OwnedProcess:
    """Exactly one async owner; shutdown is idempotent after a successful join."""

    def __init__(self, process, prompt, stdout_limit, stderr_limit, observer):
        self.process = process
        self.prompt = memoryview(prompt)
        self.offset = 0
        self.stdout_limit = stdout_limit
        self.stderr_limit = stderr_limit
        self.stdout = bytearray()
        self.stderr = bytearray()
        self.stdout_bytes = self.stderr_bytes = 0
        self.capture_failed = False
        self.observer = observer
        self.joined = False
        self.cleanup_error = None
        self.returncode = None
        self.stop_requested = False
        for pipe in (process.stdin, process.stdout, process.stderr):
            os.set_blocking(pipe.fileno(), False)

    @classmethod
    async def start(cls, argv, environment, cwd, *, prompt=b"", stdout_limit=65536,
                    stderr_limit=65536, observer=None):
        if sys.platform not in ("darwin", "linux"):
            raise RuntimeError("native process supervision requires macOS or Linux")
        process = subprocess.Popen(tuple(argv), env=dict(environment), cwd=cwd,
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True, bufsize=0)
        return cls(process, prompt, stdout_limit, stderr_limit, observer)

    def _read(self, name):
        pipe = getattr(self.process, name)
        if pipe.closed:
            return
        retained = getattr(self, name)
        limit = getattr(self, name + "_limit")
        remaining = PUMP_BYTES
        while remaining:
            try:
                chunk = os.read(pipe.fileno(), min(8192, remaining))
            except BlockingIOError:
                return
            except OSError:
                self.capture_failed = True
                pipe.close()
                return
            if not chunk:
                pipe.close()
                return
            remaining -= len(chunk)
            setattr(self, name + "_bytes", getattr(self, name + "_bytes") + len(chunk))
            retained.extend(chunk[:max(0, limit - len(retained))])
            if name == "stdout" and self.observer is not None:
                try:
                    self.observer.feed(chunk)
                except Exception:
                    self.capture_failed = True

    def _pump(self):
        self._read("stdout")
        self._read("stderr")
        pipe = self.process.stdin
        if not pipe.closed:
            if self.offset == len(self.prompt):
                pipe.close()
            else:
                try:
                    self.offset += os.write(pipe.fileno(), self.prompt[self.offset:self.offset + 65536])
                except BlockingIOError:
                    pass
                except OSError:
                    self.capture_failed = True
                    pipe.close()

    def request_stop(self):
        self.stop_requested = True

    def exited(self):
        return self.joined or _exited(self.process.pid)

    async def run(self, stop=None, *, timeout=None,
                  fail_on_stdout_overflow=False, fail_on_stderr_overflow=False):
        deadline = None if timeout is None else time.monotonic() + timeout
        reason = "exited"
        try:
            while True:
                self._pump()
                if stop is not None and stop.requested():
                    reason = await stop.wait()
                    break
                if deadline is not None and time.monotonic() >= deadline:
                    reason = "deadline"
                    break
                if (self.capture_failed or
                        (fail_on_stdout_overflow and self.stdout_bytes > self.stdout_limit)
                        or (fail_on_stderr_overflow and self.stderr_bytes > self.stderr_limit)):
                    self.capture_failed = True
                    reason = "capture_failed"
                    break
                if _exited(self.process.pid):
                    break
                if self.stop_requested:
                    reason = "cancelled"
                    break
                await asyncio.sleep(POLL_SECONDS)
        except BaseException:
            await self._finish_shielded()
            raise
        await self._finish_shielded(grace=reason != "exited")
        return ProcessResult(self.returncode, reason, bytes(self.stdout), bytes(self.stderr),
                             self.stdout_bytes, self.stderr_bytes, self.capture_failed,
                             self.offset == len(self.prompt))

    async def _finish_shielded(self, *, grace=True):
        await joined(asyncio.create_task(self.close_and_join(grace=grace)))

    async def close_and_join(self, *, grace=True):
        if self.joined:
            if self.cleanup_error:
                raise CleanupError(self.cleanup_error)
            return
        pid = self.process.pid
        errors = []

        def signal_group(sig):
            try:
                _signal_group(pid, sig)
            except OSError:
                errors.append("native process group signal failed")

        if grace:
            signal_group(signal.SIGTERM)
            deadline = time.monotonic() + TERM_SECONDS
            while time.monotonic() < deadline and not _exited(pid):
                self._pump()
                await asyncio.sleep(POLL_SECONDS)
        signal_group(signal.SIGKILL)
        deadline = time.monotonic() + CLEANUP_SECONDS
        quiet = False
        while time.monotonic() < deadline:
            self._pump()
            signal_group(signal.SIGKILL)
            if _exited(pid):
                quiet = True
                break
            await asyncio.sleep(POLL_SECONDS)
        if not quiet:
            raise CleanupError("native process leader did not exit within its cleanup bound")
        # Drain what the exited leader left in the pipe buffers, then close C's
        # own ends. A descendant still holding them is B's fallback case.
        self._pump()
        for pipe in (self.process.stdin, self.process.stdout, self.process.stderr):
            pipe.close()
        self.returncode = self.process.wait(timeout=0)
        self.joined = True
        if self.observer is not None:
            try:
                self.observer.finish()
            except Exception:
                self.capture_failed = True
        if errors:
            self.cleanup_error = errors[0]
            raise CleanupError(self.cleanup_error)

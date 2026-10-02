# Author: Fangzhu Shen
"""One C stop signal and the shielded join every C owner uses.

A stop latches the first cause requested, preserving B's exact cause when B
supplied one. Joining shields owned work so a cancelled caller still leaves a
joined process, socket or task behind.
"""

import asyncio


class Stop:
    """A latched stop cause with an awaitable; a later cause never replaces it."""

    def __init__(self):
        self.reason = None
        self.exit_status = None
        self._event = asyncio.Event()

    def requested(self):
        return self.reason is not None

    def set(self, reason, exit_status=None):
        if self.reason is None:
            self.reason, self.exit_status = reason, exit_status
            self._event.set()

    async def wait(self):
        await self._event.wait()
        return self.reason


class AnyStop:
    """The first of several stop signals, preferring the earlier source."""

    def __init__(self, *sources):
        self._sources = sources

    def requested(self):
        return any(source.requested() for source in self._sources)

    def _reason(self):
        for source in self._sources:
            if source.requested():
                return source
        return None

    async def wait(self):
        source = self._reason()
        if source is not None:
            return await source.wait()
        tasks = [asyncio.create_task(source.wait()) for source in self._sources]
        try:
            done, _ = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
            source = self._reason()
            return await source.wait() if source is not None else next(iter(done)).result()
        finally:
            for task in tasks:
                if not task.done():
                    task.cancel()
            await asyncio.gather(*tasks, return_exceptions=True)


async def joined(task, *, on_cancel=None):
    """Join owned work even while this caller is cancelled, then re-raise.

    A cleanup failure from the owned task outranks the caller's cancellation.
    """
    cancelled = False
    while not task.done():
        try:
            await asyncio.shield(task)
        except asyncio.CancelledError:
            cancelled = True
            if on_cancel is not None:
                on_cancel()
    result = task.result()
    if cancelled:
        raise asyncio.CancelledError
    return result

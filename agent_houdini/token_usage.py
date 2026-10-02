"""C diagnostics: observed provider counters, never estimates from prompt size.

Codex rollout token_count.total_token_usage is cumulative within one fresh
consultation. Retain snapshots, but aggregate only its final total. A stopped
turn may have an unreported in-flight response; partial is never called zero
or exact billing. Raw rollouts remain in scratch and are removed at shutdown.
"""

import json
import os
from pathlib import Path
import stat


USAGE_ENV = "WHIEL_AGENT_TOKEN_USAGE"
MODES = ("off", "codex-rollout")
FIELDS = ("input_tokens", "cached_input_tokens", "output_tokens",
          "reasoning_output_tokens", "cache_write_input_tokens", "total_tokens")
MAX_BYTES = 64 * 1024 * 1024
MAX_LINE = 4 * 1024 * 1024
PRICING = {'model': 'gpt-5.5', 'as_of': '2026-09-22',
           'source': 'https://developers.openai.com/api/docs/models/gpt-5.5',
           'usd_per_million': {'uncached_input': 5, 'cached_input': 0.5, 'output': 30},
           'meaning': 'Standard API-equivalent estimate for observed tokens only; '
                      'not ChatGPT subscription billing. Reasoning is included in output. '
                      'No batch, priority, residency, or other account adjustments.'}
LUNA_PRICING = {
    'model': 'gpt-5.6-luna', 'as_of': '2026-09-25',
    'source': 'https://developers.openai.com/api/docs/models/gpt-5.6-luna',
    'usd_per_million': {'uncached_input': 0.20, 'cached_input': 0.02, 'output': 1.20},
    'meaning': PRICING['meaning'] + ' No estimate for nonzero reported cache writes '
               'or requests crossing the 272K input threshold; per-response tier totals '
               'are not retained. Missing cache-write counters are not separately charged.'}
SOL_PRICING = {
    'model': 'gpt-5.6-sol', 'as_of': '2026-09-26',
    'source': 'https://developers.openai.com/api/docs/models/gpt-5.6-sol',
    'usd_per_million': {'uncached_input': 4, 'cached_input': 0.4, 'output': 20},
    'meaning': LUNA_PRICING['meaning'] + ' Dated promotional Sol rates; '
               'do not reinterpret historical runs using future prices.'}


def pricing_for(model):
    # Exact model IDs only. These diagnostic prices do not restrict launch.
    return {PRICING['model']: PRICING, LUNA_PRICING['model']: LUNA_PRICING,
            SOL_PRICING['model']: SOL_PRICING}.get(model)


def counts(value):
    if not isinstance(value, dict):
        return None
    result = {key: value.get(key) for key in FIELDS}
    if any(type(result[key]) is not int or result[key] < 0 for key in FIELDS[:3]):
        return None
    if any(v is not None and (type(v) is not int or v < 0) for v in result.values()):
        return None
    if result['cached_input_tokens'] > result['input_tokens']:
        return None
    if (result['reasoning_output_tokens'] is not None
            and result['reasoning_output_tokens'] > result['output_tokens']):
        return None
    return result


class RolloutUsage:
    def __init__(self, directory, record):
        self.directory = Path(directory)
        self.record = record
        self.path = None
        self.offset = 0
        self.pending = b""
        self.total = None
        self.snapshots = 0
        self.invalid = False
        self.finished = False
        self.max_response_input = None

    def poll(self):
        """Read only bounded regular rollout files under this fresh request."""
        if self.invalid:
            return
        try:
            paths = []
            for base, directories, files in os.walk(self.directory, followlinks=False):
                directories[:] = [name for name in directories
                                  if not (Path(base) / name).is_symlink()]
                paths.extend(Path(base) / name for name in files
                             if name.startswith('rollout-') and name.endswith('.jsonl'))
                if len(paths) > 1:
                    self.invalid = True
                    return
            if not paths:
                return
            path = paths[0]
            if self.path is not None and self.path != path:
                self.invalid = True
                return
            self.path = path
            fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            with os.fdopen(fd, 'rb') as stream:
                info = os.fstat(stream.fileno())
                if (not stat.S_ISREG(info.st_mode) or info.st_nlink != 1
                        or info.st_uid != os.getuid() or info.st_size > MAX_BYTES
                        or info.st_size < self.offset):
                    self.invalid = True
                    return
                stream.seek(self.offset)
                data = stream.read(MAX_BYTES - self.offset + 1)
                self.offset += len(data)
            lines = (self.pending + data).split(b'\n')
            self.pending = lines.pop()
            if len(self.pending) > MAX_LINE:
                self.invalid = True
                return
            for line in lines:
                if len(line) > MAX_LINE:
                    self.invalid = True
                    return
                self.observe(json.loads(line))
        except (OSError, ValueError, TypeError):
            self.invalid = True

    def observe(self, event):
        if not isinstance(event, dict) or event.get('type') != 'event_msg':
            return
        payload = event.get('payload')
        if not isinstance(payload, dict):
            return
        if payload.get('type') in ('task_complete', 'turn_complete'):
            self.finished = True
        if payload.get('type') != 'token_count':
            return
        info = payload.get('info')
        if info is None:  # rate-limit-only event, not zero usage
            return
        total = counts(info.get('total_token_usage') if isinstance(info, dict) else None)
        if total is None:
            self.invalid = True
            return
        last = counts(info.get('last_token_usage'))
        if last is not None:
            self.max_response_input = max(self.max_response_input or 0, last['input_tokens'])
        if self.total is not None:
            if any(total[key] is not None and self.total[key] is not None
                   and total[key] < self.total[key] for key in FIELDS):
                self.invalid = True
                return
            if total == self.total:
                return
        self.total = total
        self.snapshots += 1
        self.record.usage({'schema_version': 1, 'type': 'snapshot',
                           'source': 'codex_rollout', 'ordinal': self.snapshots,
                           'cumulative': total, 'max_response_input_tokens': self.max_response_input})

    def finish(self, *, natural_completion=False):
        self.poll()
        coverage = ('unknown' if self.total is None else
                    'complete' if natural_completion and self.finished and not self.invalid
                    and not self.pending else 'partial')
        result = {'schema_version': 1, 'type': 'summary', 'source': 'codex_rollout',
                  'coverage': coverage, 'cumulative': self.total,
                  'snapshots': self.snapshots, 'parse_error': self.invalid,
                  'max_response_input_tokens': self.max_response_input,
                  'unreported_inflight_possible': coverage != 'complete'}
        self.record.usage(result)
        return result


def equivalent_cost(usage, model):
    total = counts(usage.get('cumulative'))
    maximum = usage.get('max_response_input_tokens')
    pricing = pricing_for(model)
    if (total is None or pricing is None or type(maximum) is not int
            or total['cache_write_input_tokens'] not in (None, 0)):
        return None
    if model in (LUNA_PRICING['model'], SOL_PRICING['model']) and maximum > 272000:
        # These models' documented multiplier is per request. A consultation may
        # contain responses on both sides of the threshold; its maximum and
        # cumulative total cannot reconstruct each tier's billable tokens.
        return None
    # The documented >272K input threshold affects the full session. Every
    # consultation is a fresh session; apply the multiplier to that total.
    long = maximum > 272000
    price = pricing['usd_per_million']
    return round(((total['input_tokens'] - total['cached_input_tokens'])
                  * price['uncached_input'] * (2 if long else 1)
                  + total['cached_input_tokens'] * price['cached_input'] * (2 if long else 1)
                  + total['output_tokens'] * price['output'] * (1.5 if long else 1)) / 1000000, 9)


def usage_report(root, *, model):
    from .run_records import USAGE_FILE, read_entries

    root = Path(root)
    requests = []
    for directory in sorted(root.rglob('request-*')):
        if directory.is_symlink() or not directory.is_dir():
            continue
        entries = list(read_entries(directory / USAGE_FILE, maximum=20000))
        snapshots = [e for e in entries if e.get('type') in ('snapshot', 'summary')]
        final = snapshots[-1] if snapshots else {}
        total = counts(final.get('cumulative'))
        coverage = final.get('coverage', 'partial') if total is not None else 'unknown'
        requests.append({'request': directory.relative_to(root).as_posix(),
                         'coverage': coverage, 'cumulative': total,
                         'api_equivalent_usd_observed': equivalent_cost(final, model)})
    known = [entry for entry in requests if entry['cumulative'] is not None]
    totals = {key: (sum(e['cumulative'][key] for e in known if e['cumulative'][key] is not None)
                   if any(e['cumulative'][key] is not None for e in known) else None)
              for key in FIELDS}
    costs = [e['api_equivalent_usd_observed'] for e in requests
             if e['api_equivalent_usd_observed'] is not None]
    return {'schema_version': 1, 'model': model, 'requests': requests,
            'coverage': {key: sum(e['coverage'] == key for e in requests)
                         for key in ('complete', 'partial', 'unknown')},
            'observed_tokens': totals,
            'api_equivalent_usd_observed': round(sum(costs), 9) if costs else None,
            'requests_with_cost_estimate': len(costs), 'pricing': pricing_for(model),
            'warning': 'Observed usage may omit interrupted/in-flight responses and unreported retries. '
                       'Missing usage is unknown, not zero. Old runs cannot be backfilled. '
                       'Snapshots are cumulative within a request; never sum all snapshots.'}


def write_usage_report(root, *, model):
    root = Path(root)
    report = usage_report(root, model=model)
    temporary = root / 'token-usage.json.tmp'
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    temporary.replace(root / 'token-usage.json')
    return report


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Rebuild observed usage totals without model calls.')
    parser.add_argument('run_directory')
    parser.add_argument('--model', required=True)
    options = parser.parse_args()
    report = write_usage_report(options.run_directory, model=options.model)
    print(json.dumps({key: value for key, value in report.items() if key != 'requests'}, indent=2))

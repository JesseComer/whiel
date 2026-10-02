import json
from pathlib import Path
import tempfile
import unittest

from agent_houdini.run_records import ConsultationRecord
from agent_houdini.token_usage import RolloutUsage, counts, equivalent_cost, pricing_for, usage_report


def tokens(n=1):
    return {'input_tokens': 100 * n, 'cached_input_tokens': 20 * n,
            'output_tokens': 10 * n, 'reasoning_output_tokens': 5 * n,
            'cache_write_input_tokens': 0, 'total_tokens': 110 * n}


def event(n=1):
    return {'type': 'event_msg', 'payload': {'type': 'token_count', 'info': {
        'total_token_usage': tokens(n), 'last_token_usage': tokens()}}}


class UsageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.sessions = self.root / 'sessions'
        self.sessions.mkdir()
        self.request = self.root / 'agent' / 'Example0001' / 'request-1'
        self.request.mkdir(parents=True)
        self.record = ConsultationRecord('fixture', self.request)
        self.addCleanup(self.record.close)
        self.meter = RolloutUsage(self.sessions, self.record)

    def test_cumulative_not_double_counted_reasoning_subset_and_cached_discount(self):
        for n in (1, 1, 2):
            self.meter.observe(event(n))
        summary = self.meter.finish()
        self.assertEqual(summary['snapshots'], 2)
        self.assertEqual(summary['coverage'], 'partial')
        report = usage_report(self.root, model='gpt-5.5')
        self.assertEqual(report['observed_tokens'], tokens(2))
        self.assertEqual(report['api_equivalent_usd_observed'], .00142)
        self.assertEqual(report['coverage'], {'complete': 0, 'partial': 1, 'unknown': 0})

    def test_unknown_is_null_not_zero(self):
        self.meter.observe({'type': 'event_msg', 'payload': {'type': 'token_count', 'info': None}})
        self.assertEqual(self.meter.finish()['coverage'], 'unknown')
        report = usage_report(self.root, model='gpt-5.5')
        self.assertIsNone(report['observed_tokens']['input_tokens'])
        self.assertIsNone(report['api_equivalent_usd_observed'])

    def test_natural_completion_and_truncated_final_line(self):
        path = self.sessions / 'rollout-fixture.jsonl'
        path.write_text(json.dumps(event()) + '\n' + json.dumps(
            {'type': 'event_msg', 'payload': {'type': 'task_complete'}}) + '\n')
        self.assertEqual(self.meter.finish(natural_completion=True)['coverage'], 'complete')
        with path.open('a') as stream:
            stream.write('{')
        self.assertEqual(self.meter.finish(natural_completion=True)['coverage'], 'partial')

    def test_rate_limit_duplicates_and_counter_reset_fail_closed(self):
        self.meter.observe(event(2))
        self.meter.observe(event(1))
        summary = self.meter.finish(natural_completion=True)
        self.assertTrue(summary['parse_error'])
        self.assertEqual(summary['cumulative'], tokens(2))
        self.assertEqual(summary['coverage'], 'partial')

    def test_symlink_and_multiple_rollouts_rejected(self):
        outside = self.root / 'outside.jsonl'
        outside.write_text(json.dumps(event()) + '\n')
        path = self.sessions / 'rollout-fixture.jsonl'
        path.symlink_to(outside)
        self.assertTrue(self.meter.finish()['parse_error'])
        path.unlink()
        path.write_text(json.dumps(event()) + '\n')
        (self.sessions / 'rollout-second.jsonl').write_text('')
        meter = RolloutUsage(self.sessions, self.record)
        self.assertTrue(meter.finish()['parse_error'])

    def test_invalid_numeric_fields_rejected(self):
        for patch in ({'input_tokens': True}, {'input_tokens': -1},
                      {'cached_input_tokens': 200}, {'reasoning_output_tokens': 200},
                      {'output_tokens': '10'}):
            with self.subTest(patch=patch):
                self.assertIsNone(counts({**tokens(), **patch}))

    def test_live_snapshot_is_partial_and_cost_not_assumed_for_other_model(self):
        self.meter.observe(event())
        report = usage_report(self.root, model='another-model')
        self.assertEqual(report['coverage']['partial'], 1)
        self.assertEqual(report['observed_tokens'], tokens())
        self.assertIsNone(report['api_equivalent_usd_observed'])

    def test_long_context_session_rate_and_unknown_cache_write(self):
        usage = {'cumulative': tokens(), 'max_response_input_tokens': 272001}
        self.assertEqual(equivalent_cost(usage, 'gpt-5.5'), .00127)
        usage['cumulative']['cache_write_input_tokens'] = 1
        self.assertIsNone(equivalent_cost(usage, 'gpt-5.5'))

    def test_luna_price_is_separate_and_does_not_guess_other_models(self):
        usage = {'cumulative': tokens(), 'max_response_input_tokens': 100}
        self.assertEqual(equivalent_cost(usage, 'gpt-5.6-luna'), .0000284)
        self.assertEqual(equivalent_cost(usage, 'gpt-5.5'), .00071)
        for model in ('gpt-6-luna', 'gpt-5.6', 'gpt-5.6-luna-unknown', 'another-model'):
            self.assertIsNone(equivalent_cost(usage, model))
            self.assertIsNone(pricing_for(model))
        usage['max_response_input_tokens'] = 272001
        self.assertIsNone(equivalent_cost(usage, 'gpt-5.6-luna'))
        usage['max_response_input_tokens'] = 272000
        self.assertEqual(equivalent_cost(usage, 'gpt-5.6-luna'), .0000284)
        usage['cumulative']['cache_write_input_tokens'] = 1
        self.assertIsNone(equivalent_cost(usage, 'gpt-5.6-luna'))

    def test_luna_report_retains_the_same_counts_and_sourced_prices(self):
        self.meter.observe(event(2))
        self.meter.finish()
        report = usage_report(self.root, model='gpt-5.6-luna')
        self.assertEqual(report['observed_tokens'], tokens(2))
        self.assertEqual(report['api_equivalent_usd_observed'], .0000568)
        self.assertEqual(report['requests_with_cost_estimate'], 1)
        self.assertEqual(report['pricing']['model'], 'gpt-5.6-luna')
        self.assertEqual(report['pricing']['as_of'], '2026-09-25')
        self.assertEqual(report['pricing']['source'],
                         'https://developers.openai.com/api/docs/models/gpt-5.6-luna')
        self.assertIn('not ChatGPT subscription billing', report['pricing']['meaning'])

    def test_usage_never_retains_foreign_text_or_auth_fields(self):
        message = event()
        message['payload']['auth'] = 'synthetic_secret'
        message['payload']['info']['total_token_usage']['text'] = 'synthetic_prompt'
        self.meter.observe(message)
        self.meter.finish()
        self.record.close()
        retained = (self.request / 'usage.jsonl').read_text()
        self.assertNotIn('synthetic', retained)

    def test_sol_price_is_exact_model_only_and_other_prices_unchanged(self):
        usage = {'cumulative': tokens(), 'max_response_input_tokens': 100}
        self.assertEqual(equivalent_cost(usage, 'gpt-5.6-sol'), .000528)
        self.assertEqual(equivalent_cost(usage, 'gpt-5.5'), .00071)
        self.assertEqual(equivalent_cost(usage, 'gpt-5.6-luna'), .0000284)
        for model in ('gpt-5.6', 'gpt-5.6-sol-unknown', 'gpt-6-sol'):
            self.assertIsNone(equivalent_cost(usage, model))
            self.assertIsNone(pricing_for(model))

    def test_sol_unknown_tiers_and_cache_writes_remain_unknown(self):
        usage = {'cumulative': tokens(), 'max_response_input_tokens': 272001}
        self.assertIsNone(equivalent_cost(usage, 'gpt-5.6-sol'))
        usage['max_response_input_tokens'] = 272000
        self.assertEqual(equivalent_cost(usage, 'gpt-5.6-sol'), .000528)
        usage['cumulative']['cache_write_input_tokens'] = 1
        self.assertIsNone(equivalent_cost(usage, 'gpt-5.6-sol'))

    def test_sol_report_retains_counters_and_dated_model_price(self):
        self.meter.observe(event(2))
        self.meter.finish()
        report = usage_report(self.root, model='gpt-5.6-sol')
        self.assertEqual(report['observed_tokens'], tokens(2))
        self.assertEqual(report['api_equivalent_usd_observed'], .001056)
        self.assertEqual(report['pricing']['model'], 'gpt-5.6-sol')
        self.assertEqual(report['pricing']['as_of'], '2026-09-26')
        self.assertEqual(report['pricing']['source'],
                         'https://developers.openai.com/api/docs/models/gpt-5.6-sol')
        self.assertEqual(report['coverage'], {'complete': 0, 'partial': 1, 'unknown': 0})


if __name__ == '__main__':
    unittest.main()

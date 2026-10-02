"""PAPER REPRODUCTION CODE: synthetic integration checks, without builds/models."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import signal
import tempfile
import unittest
from unittest.mock import patch

from scripts import paper_repro_common as common
from scripts import paper_repro_certify as cert
from scripts import reproduce_paper as cli


class ReproductionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name).resolve()
        self.out = self.repo / 'artifacts/paper-reproduction'
        self.trial = self.out / 'runs/synthetic'
        self.trial.mkdir(parents=True)
        self.data = {'schema_version':1, 'state':'running', 'inputs':['Example0001'],
                     'search':[{'arm':arm,'model':model,'state':'pending','inputs':None,'cases':[]}
                               for arm in common.ARMS for model in common.MODELS],
                     'direct_lean':{'state':'pending'},
                     'certification':{'state':'pending','expected_pairs':None,'attempts':[]},
                     'commands':[], 'source_sha256':{}, 'trial':'artifacts/paper-reproduction/runs/synthetic'}
        self.ctx = common.Context(self.repo,self.out,self.trial,self.data)
        self.ctx.save()

    def source(self, identity='Example0001', arm='whiel'):
        run=self.trial/'search'/arm/identity
        case=run/'verifier'/identity
        case.mkdir(parents=True)
        (case/'Accepted.json').write_text('{"accepted":true}')
        (case/'Core.json').write_text('{"clauses":[]}')
        common.atomic_json(case/'result.json',{'input':identity,'status':'valid_uncertified'})
        common.atomic_json(run/'verifier/summary.json',{'selected_inputs':[identity]})
        source=self.repo/'Benchmark'/identity/'Input.lean'
        source.parent.mkdir(parents=True,exist_ok=True)
        source.write_text('synthetic input')
        self.data['source_sha256'][f'Benchmark/{identity}/Input.lean']=common.digest(source)
        return {'input':identity,'arm':arm,'model':'gpt-5.5','status':'valid_uncertified',
                'run_directory':self.ctx.rel(run)}

    def publication(self, attempt):
        job=common.read_json(self.ctx.path(attempt['job']))
        case=self.ctx.path(attempt['directory'])/'verifier'/job['input']
        (case/'Certificate').mkdir()
        (case/'Certificate/Valid.lean').write_text('synthetic proof placeholder')
        result={'input':job['input'],'status':'valid','certificate':'Certificate',
                'axioms':sorted(common.STD3),
                'certificate_module':f"Benchmark.{job['input']}.Certificate.Valid",
                'certificate_theorem':f"Whiel.Benchmark.{job['input']}.Certificate.input_hoare_triple_valid"}
        common.atomic_json(case/'result.json',result)
        common.atomic_json(case.parent/'summary.json',{'selected_inputs':[job['input']],
                           'all_certified':True,'all_accepted':True,'results':[result]})
        common.atomic_json(case/'Certificate/certificate-build-settings.json',
                           {'kind':'whiel_certificate_build_settings','version':1,
                            'solver_jobs':12,'compiler':'lake','lean_num_threads':'12'})
        return job,case

    def measurement(self, outcome='finished'):
        return {'outcome':outcome,'exit_code':0,'cleanup_ok':True,'inspection_error':None,
                'elapsed_seconds':2,'peak_process_rss_kb':100,'peak_tree_rss_kb':200}

    def test_core_selection_respects_affinity_and_smt(self):
        topology='\n'.join(f'{i},{i%24},0,Y' for i in range(48))
        lanes=cert.select_cores(topology,set(range(48)))
        self.assertEqual(lanes,[list(range(12)),list(range(12,24))])
        lanes=cert.select_cores(topology,set(range(24,48)))
        self.assertEqual(lanes,[list(range(24,36)),list(range(36,48))])
        with self.assertRaises(common.ReproError): cert.select_cores(topology,set(range(23)))
        with self.assertRaises(common.ReproError): cert.select_cores('0,-,0,Y',{0})

    def test_paths_fresh_trials_and_no_external_output(self):
        self.assertEqual(common.output_directory(self.repo),self.out)
        for value in ('README.md','artifacts','../escape',str(self.repo/'other')):
            with self.assertRaises(common.ReproError): common.output_directory(self.repo,value)
        source=self.source()
        cert.prepare_attempt(self.ctx,source,list(range(12)))
        with self.assertRaises(FileExistsError): cert.prepare_attempt(self.ctx,source,list(range(12)))

    def test_cert_copy_preserves_source_and_frozen_answer(self):
        source=self.source()
        original=self.ctx.path(source['run_directory'])/'verifier/Example0001/result.json'
        before=original.read_bytes()
        attempt=cert.prepare_attempt(self.ctx,source,list(range(12)))
        job,case=self.publication(attempt)
        evidence=cert.check_publication(self.repo,job)
        self.assertEqual(evidence['campaign_result']['status'],'valid')
        self.assertEqual(original.read_bytes(),before)
        (case/'Core.json').write_text('changed')
        with self.assertRaises(common.ReproError): cert.check_publication(self.repo,job)

    def test_cert_rejects_wrong_target_axioms_settings_and_summary(self):
        job,case=self.publication(cert.prepare_attempt(self.ctx,self.source(),list(range(12))))
        for field,value in [('certificate_theorem','Other.answer'),('axioms',['sorryAx']),('input','Example9999')]:
            path=case/'result.json'; old=path.read_bytes(); data=json.loads(old); data[field]=value
            common.atomic_json(path,data)
            with self.assertRaises(common.ReproError): cert.check_publication(self.repo,job)
            path.write_bytes(old)
        settings=case/'Certificate/certificate-build-settings.json'
        data=common.read_json(settings); data['solver_jobs']=1; common.atomic_json(settings,data)
        with self.assertRaises(common.ReproError): cert.check_publication(self.repo,job)

    def test_failure_classification_never_trusts_exit_alone(self):
        attempt=cert.prepare_attempt(self.ctx,self.source(),list(range(12)))
        job=common.read_json(self.ctx.path(attempt['job']))
        with self.assertRaises(common.ReproError): cert.classify_result(self.repo,job,self.measurement())
        for cause in ('timeout','process_memory_limit','memory_limit'):
            self.assertEqual(cert.classify_result(self.repo,job,self.measurement(cause))[0],cause)
        measured=self.measurement('timeout'); measured['cleanup_ok']=False
        with self.assertRaises(common.ReproError): cert.classify_result(self.repo,job,measured)

    def test_single_helper_passes_exact_original_controls(self):
        attempt=cert.prepare_attempt(self.ctx,self.source(),list(range(12)))
        job,case=self.publication(attempt)
        with patch.object(cert,'watched_run',return_value=self.measurement()) as watcher:
            self.assertEqual(cert.run_one(self.repo,self.ctx.path(attempt['job'])),0)
        args,kwargs=watcher.call_args
        self.assertEqual(kwargs,{'limit':300,'memory_kb':96*1024**2,'process_memory_kb':10*1024**2})
        self.assertEqual(args[0][-6:],['--certification-limit','300','--certificate-solver-limit','300','--retention','all'])
        self.assertEqual(args[2]['WHIEL_CERTIFICATE_SOLVER_JOBS'],'12')
        self.assertEqual(common.read_json(case.parent.parent/'supervisor.json')['outcome'],'certified')

    def test_single_helper_interruption_is_never_success(self):
        attempt=cert.prepare_attempt(self.ctx,self.source(),list(range(12)))
        with patch.object(cert,'watched_run',side_effect=KeyboardInterrupt):
            self.assertEqual(cert.run_one(self.repo,self.ctx.path(attempt['job'])),130)
        receipt=common.read_json(self.ctx.path(attempt['directory'])/'supervisor.json')
        self.assertEqual(receipt['outcome'],'interrupted')
        self.assertNotIn('measurement',receipt)

    def test_cert_queue_two_slots_and_no_retry(self):
        sources=[self.source(f'Example{i:04}') for i in range(1,6)]
        calls=[]
        class Process:
            def __init__(inner,argv,**kwargs):
                job=common.read_json(self.ctx.path(argv[-1])); calls.append(job)
                inner.pid=100+len(calls)
                common.atomic_json(self.ctx.path(job['directory'])/'supervisor.json',
                                   {'input':job['input'],'arm':job['arm'],'outcome':'timeout'})
            def poll(inner): return 0
            def wait(inner): return 0
        with patch.object(cert,'successful_search_cases',return_value=sources),patch.object(cert.subprocess,'Popen',Process),redirect_stdout(io.StringIO()):
            cert.run_certification(self.ctx,[list(range(12)),list(range(12,24))])
        self.assertEqual(len(calls),5)
        self.assertEqual(self.data['certification']['state'],'complete')
        self.assertEqual(self.data['certification']['outcomes'],{'timeout':5})
        with self.assertRaises(common.ReproError): cert.run_certification(self.ctx,[])

    def test_cert_fatal_stops_before_next_pair(self):
        sources=[self.source(f'Example{i:04}') for i in range(1,6)]
        calls=[]
        class Process:
            def __init__(inner,argv,**kwargs):
                job=common.read_json(self.ctx.path(argv[-1])); calls.append(job); inner.pid=100+len(calls)
                common.atomic_json(self.ctx.path(job['directory'])/'supervisor.json',
                                   {'input':job['input'],'arm':job['arm'],'outcome':'infrastructure_failure'})
            def poll(inner): return 2
            def wait(inner): return 2
        with patch.object(cert,'successful_search_cases',return_value=sources),patch.object(cert.subprocess,'Popen',Process),self.assertRaises(common.ReproError):
            cert.run_certification(self.ctx,[list(range(12)),list(range(12,24))])
        self.assertLessEqual(len(calls),2)
        self.assertEqual(self.data['certification']['state'],'failed')

    def test_stale_and_partial_reports_not_complete(self):
        with redirect_stdout(io.StringIO()): self.assertEqual(cli.report(self.ctx),1)
        self.assertIn('stale running record',(self.trial/'report.md').read_text())
        self.data['state']='complete'; self.data['search']=[]
        with redirect_stdout(io.StringIO()): self.assertEqual(cli.report(self.ctx),1)
        self.assertIn('Expected arm/model stages',(self.trial/'report.md').read_text())

    def test_common_interrupt_forwards_and_waits_before_raise(self):
        handlers={}; process_state={'done':False,'signals':[]}
        def install(sig,handler):
            old=handlers.get(sig,signal.SIG_DFL); handlers[sig]=handler; return old
        class Process:
            pid=123
            def __init__(inner,*args,**kwargs): pass
            def poll(inner): return 130 if process_state['done'] else None
            def send_signal(inner,sig): process_state['signals'].append(sig)
            def wait(inner):
                handlers[signal.SIGINT](signal.SIGINT,None)
                process_state['done']=True
                return 130
        with patch.object(common.signal,'signal',side_effect=install),patch.object(common.subprocess,'Popen',Process),redirect_stdout(io.StringIO()),self.assertRaises(common.Interrupted):
            common.command(self.ctx,['synthetic'],self.trial/'process.log')
        self.assertTrue(process_state['done'])
        self.assertEqual(process_state['signals'],[signal.SIGTERM])
        self.assertEqual(self.data['commands'][0]['state'],'interrupted')


    def test_owned_tree_interrupt_keeps_graceful_leader_then_cleans_descendants(self):
        handlers = {}
        events = []
        class Tree:
            def __init__(inner, pid): events.append(("tree", pid))
            def refresh(inner): events.append("refresh")
            def stop(inner): events.append("cleanup"); return True
        class Process:
            pid = 123
            done = False
            def __init__(inner, *args, **kwargs): pass
            def poll(inner): return 130 if inner.done else None
            def send_signal(inner, sig): events.append(("signal", sig))
            def wait(inner, timeout=None):
                self.assertEqual(timeout, 0.2)
                handlers[signal.SIGINT](signal.SIGINT, None)
                inner.done = True
                events.append("joined")
                return 130
        def install(sig, handler):
            old = handlers.get(sig, signal.SIG_DFL)
            handlers[sig] = handler
            return old
        with patch.object(common.signal, "signal", side_effect=install), patch.object(common.subprocess, "Popen", Process), patch("scripts.compare_certificate_builds.ProcessTree", Tree), redirect_stdout(io.StringIO()), self.assertRaises(common.Interrupted):
            common.command(self.ctx, ["synthetic"], self.trial / "owned.log", cleanup_tree=True)
        self.assertLess(events.index("joined"), events.index("cleanup"))
        self.assertIn(("signal", signal.SIGTERM), events)
        self.assertTrue(self.data["commands"][0]["cleanup_ok"])
        self.assertEqual(handlers[signal.SIGINT], signal.SIG_DFL)

    def test_cleanup_inspection_error_still_restores_handlers_and_records_failure(self):
        handlers = {}
        class Tree:
            def __init__(inner, pid): pass
            def refresh(inner): pass
            def stop(inner): raise OSError("synthetic inspection failure")
        class Process:
            pid = 123
            def __init__(inner, *args, **kwargs): pass
            def poll(inner): return 0
            def wait(inner, timeout=None): return 0
        def install(sig, handler):
            old = handlers.get(sig, signal.SIG_DFL)
            handlers[sig] = handler
            return old
        with patch.object(common.signal, "signal", side_effect=install), patch.object(common.subprocess, "Popen", Process), patch("scripts.compare_certificate_builds.ProcessTree", Tree), redirect_stdout(io.StringIO()), self.assertRaisesRegex(common.ReproError, "cleanup failed"):
            common.command(self.ctx, ["synthetic"], self.trial / "failed-cleanup.log", cleanup_tree=True)
        self.assertEqual(handlers[signal.SIGTERM], signal.SIG_DFL)
        self.assertFalse(self.data["commands"][0]["cleanup_ok"])
        self.assertEqual(self.data["commands"][0]["state"], "failed")

    def test_finished_no_submission_is_not_incomplete_execution(self):
        self.data["state"] = "complete"
        for stage in self.data["search"]:
            stage.update(state="complete", inputs=["Example0001"])
            run = self.trial / "search" / stage["arm"] / stage["model"]
            common.atomic_json(run / "verifier/Example0001/result.json", {"status": "search_timeout"})
            stage["cases"] = [{"input": "Example0001", "status": "search_timeout", "run_directory": self.ctx.rel(run)}]
        baseline = self.trial / "direct-lean/run"
        common.atomic_json(baseline / "run.json", {"cases": ["Example0001"]})
        common.atomic_json(baseline / "summary.json", {"total": 1, "finished": 1, "proof_checked": 0})
        self.data["direct_lean"].update(state="complete", run=self.ctx.rel(baseline))
        self.data["certification"].update(state="complete", expected_pairs=[])
        with redirect_stdout(io.StringIO()): self.assertEqual(cli.report(self.ctx), 0)
        audit = common.read_json(self.trial / "direct-lean-audit.json")
        self.assertEqual(audit["counts"]["missing_or_inconsistent_evidence"], 1)
        self.assertIn("coverage is incomplete", (self.trial / "report.md").read_text())
        self.data["certification"]["state"] = "pending"
        with redirect_stdout(io.StringIO()): self.assertEqual(cli.report(self.ctx), 1)

    def test_cli_help_is_nonlaunching(self):
        with patch.object(cli,'execute') as run,redirect_stdout(io.StringIO()),self.assertRaises(SystemExit) as exit:
            cli.main(['--help'])
        self.assertEqual(exit.exception.code,0)
        run.assert_not_called()


if __name__=='__main__': unittest.main()

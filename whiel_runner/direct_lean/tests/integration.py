"""Explicit zero-token real-bwrap/Lean gates, using synthetic tasks only."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--checker', type=Path, required=True)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--only', nargs='+', help='Run selected fixture names')
    args = parser.parse_args()
    args.out.mkdir(mode=0o700)
    fixtures = Path(__file__).parent / 'fixtures'
    bundles = {}
    for kind in ('Valid', 'Invalid'):
        bundle = args.out / kind
        bundle.mkdir()
        (bundle / 'Toy').mkdir()
        (bundle / 'lib').symlink_to(args.bundle.resolve() / 'lib', target_is_directory=True)
        shutil.copyfile(Path(__file__).resolve().parents[3] / 'Whiel/DirectLean/Audit.lean', bundle / 'Audit.lean')
        shutil.copyfile(fixtures / (kind + 'Task.lean'), bundle / 'Toy' / 'Task.lean')
        manifest = json.loads((args.bundle / 'bundle.json').read_text())
        manifest['audit_sha256'] = digest(bundle / 'Audit.lean')
        manifest['cases'] = [{'id': 'Toy', 'task_sha256': digest(bundle / 'Toy' / 'Task.lean')}]
        (bundle / 'bundle.json').write_text(json.dumps(manifest))
        bundles[kind] = bundle
    repo = Path(__file__).resolve().parents[3]
    hidden_paths = [str(repo / 'Benchmark'), str(Path.home() / '.codex/auth.json'),
                    str(repo / 'artifacts/runs'), str(repo)]
    hidden_proof = ('by\n  run_tac do\n    for p in ' + json.dumps(hidden_paths)
        + ' do\n      if ← System.FilePath.pathExists p then\n'
        + '        throwError "host file exposed"\n'
        + '  intro I J h hs\n  cases hs\n  exact h')
    valid = 'by intro I J h hs; cases hs; exact h'
    invalid = '''by
  intro h
  let I : Instance Data inputSchema := Instance.empty inputSchema
  have hp : Whiel.toAssertion inputPre I := by
    exact ⟨I, (by intro X hX; rfl), True.intro⟩
  have hn := h I I hp (Whiel.Cmd.BigStep.skip I)
  exact hn.choose_spec.2'''
    tests = [
        ('valid', 'Valid', 'valid', valid, True),
        ('invalid', 'Invalid', 'invalid', invalid, True),
        ('wrong-type', 'Valid', 'valid', 'True.intro', False),
        ('wrong-verdict', 'Invalid', 'valid', valid, False),
        ('excluded-middle', 'Valid', 'valid', 'Classical.em goal', False),
        ('sorry', 'Invalid', 'valid', 'by sorry', False),
        ('new-axiom', 'Invalid', 'valid',
         'by sorry)\naxiom fabricated : False\nexample : False := fabricated\nexample : True := (by trivial', False),
        ('forged-stdout', 'Invalid', 'valid',
         'by run_tac Lean.logInfo "proof_checked: true"; sorry', False),
        ('hidden-files', 'Valid', 'valid', hidden_proof, True),
        ('answer-import', 'Invalid', 'valid',
         'Whiel.Benchmark.Example0001.Certificate.valid', False),
    ]
    prefix = 'import Task\nopen Whiel Whiel.Concrete\n'
    recursion = '''def countdown : Nat → Nat
  | 0 => 0
  | n + 1 => countdown n
theorem countdown_zero (n : Nat) : countdown n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
'''
    false_native_answer = '''theorem contradiction : False := by
  have h : logicalFalse = true := by native_decide
  change false = true at h
  cases h
theorem DirectLeanTask.answer : DirectLeanTask.goal := False.elim contradiction
'''
    full = [
        ('file-recursive-helper', 'Valid', 'valid', prefix + recursion +
         f'theorem DirectLeanTask.answer : DirectLeanTask.goal := {valid}', True),
        ('file-native-recursive', 'Valid', 'valid', prefix + recursion +
         'theorem computation : countdown 8 = 0 := by native_decide\n' +
         f'theorem DirectLeanTask.answer : DirectLeanTask.goal := {valid}', True),
        ('file-native-recursive-false', 'Invalid', 'valid', prefix + recursion +
         'def nativeLie : Bool := true\n' +
         '@[implemented_by nativeLie] def logicalFalse : Bool := countdown 2 == 1\n' +
         false_native_answer, False),
        ('file-unsafe-answer', 'Invalid', 'valid', prefix +
         'unsafe def DirectLeanTask.answer : DirectLeanTask.goal := unsafeCast True.intro', False),
        ('file-unsafe-native-false', 'Invalid', 'valid', prefix +
         'unsafe def nativeLie : Bool := true\n' +
         '@[implemented_by nativeLie] def logicalFalse : Bool := false\n' +
         false_native_answer, False),
        ('file-partial-native-false', 'Invalid', 'valid', prefix +
         'partial def nativeLie (_ : Unit) : Bool := true\n' +
         '@[implemented_by nativeLie] def logicalFalseFn (_ : Unit) : Bool := false\n' +
         'def logicalFalse : Bool := logicalFalseFn ()\n' +
         false_native_answer, False),
        ('file-helpers', 'Valid', 'valid', prefix +
         'structure Helper where\n  proof : DirectLeanTask.goal\n' +
         f'def helper : Helper := ⟨{valid}⟩\n' +
         'theorem DirectLeanTask.answer : DirectLeanTask.goal := helper.proof', True),
        ('file-native', 'Valid', 'valid', prefix +
         'def twice (n : Nat) := n + n\n' +
         'theorem computation : twice 2 = 4 := by native_decide\n' +
         f'theorem DirectLeanTask.answer : DirectLeanTask.goal := {valid}', True),
        ('file-native-structure', 'Valid', 'valid', prefix +
         'structure Pair where\n  x : Nat\n  y : Nat\n' +
         'def total (p : Pair) := p.x + p.y\n' +
         'theorem computation : total ⟨2, 3⟩ = 5 := by native_decide\n' +
         f'theorem DirectLeanTask.answer : DirectLeanTask.goal := {valid}', True),
        ('file-native-match', 'Valid', 'valid', prefix +
         'def runSkip (c : Cmd Data DirectLeanTask.inputSchema) : Bool :=\n' +
         '  match c with\n  | .skip => true\n  | _ => false\n' +
         'theorem computation : runSkip .skip = true := by native_decide\n' +
         f'theorem DirectLeanTask.answer : DirectLeanTask.goal := {valid}', True),
        ('file-native-match-false', 'Invalid', 'valid', prefix +
         'def runSkip (c : Cmd Data DirectLeanTask.inputSchema) : Bool :=\n' +
         '  match c with\n  | .skip => true\n  | _ => false\n' +
         'axiom _native.fake : (! runSkip .skip) = true\n' +
         'theorem DirectLeanTask.answer : DirectLeanTask.goal := by\n' +
         '  have h := _native.fake\n  change false = true at h\n  cases h', False),
        ('file-native-false', 'Invalid', 'valid', prefix +
         'def nativeLie : Bool := true\n' +
         '@[implemented_by nativeLie] def logicalFalse : Bool := false\n' +
         'theorem contradiction : False := by\n' +
         '  have h : logicalFalse = true := by native_decide\n' +
         '  change false = true at h\n  cases h\n' +
         'theorem DirectLeanTask.answer : DirectLeanTask.goal := False.elim contradiction', False),
        ('file-forged-native', 'Invalid', 'valid', prefix +
         'axiom _native.native_decide.ax_1 : false = true\n' +
         'theorem DirectLeanTask.answer : DirectLeanTask.goal := by\n' +
         '  have h := _native.native_decide.ax_1\n  cases h', False),
        ('file-custom-axiom', 'Invalid', 'valid', prefix +
         'axiom invented : DirectLeanTask.goal\n' +
         'theorem DirectLeanTask.answer : DirectLeanTask.goal := invented', False),
        ('file-sorry', 'Invalid', 'valid', prefix +
         'theorem helper : DirectLeanTask.goal := by sorry\n' +
         'theorem DirectLeanTask.answer : DirectLeanTask.goal := helper', False),
        ('file-wrong-goal', 'Invalid', 'valid', prefix +
         'theorem DirectLeanTask.answer : True := True.intro', False),
        ('file-invalid', 'Invalid', 'invalid', prefix +
         'open DirectLeanTask\n' +
         f'theorem DirectLeanTask.answer : ¬ DirectLeanTask.goal := {invalid}', True),
    ]
    terms = tests
    tests = []
    for name, kind, verdict, proof, expected in terms:
        target = 'goal' if verdict == 'valid' else '¬ goal'
        source = (prefix + 'namespace DirectLeanTask\n' +
                  f'theorem answer : {target} :=\n({proof})\nend DirectLeanTask\n')
        tests.append((name, kind, verdict, source, expected))
    tests += full
    if args.only:
        assert set(args.only) <= {row[0] for row in tests}, args.only
        tests = [row for row in tests if row[0] in args.only]
    results = []
    for name, kind, verdict, source, expected in tests:
        response = args.out / (name + '.json')
        response.write_text(json.dumps({'verdict': verdict, 'source': source}))
        directory = args.out / ('check-' + name)
        child = subprocess.run([str(args.checker.resolve()), 'check', str(bundles[kind]), 'Toy',
                                str(response), str(directory), '90'], capture_output=True, text=True)
        (args.out / (name + '.stdout')).write_text(child.stdout)
        (args.out / (name + '.stderr')).write_text(child.stderr)
        result = json.loads((directory / 'result.json').read_text()) if (directory / 'result.json').exists() else {}
        actual = result.get('proof_checked', False)
        if name == 'file-native-match' and actual:
            assert result.get('native_kernel_rechecked'), result
        if name in ('file-native', 'file-native-recursive') and actual:
            assert result.get('native_rechecked'), result
        if name in {'file-recursive-helper', 'file-native-recursive',
                    'file-native-recursive-false', 'file-unsafe-answer',
                    'file-unsafe-native-false', 'file-partial-native-false'}:
            assert result.get('failure_stage') in (None, 'audit'), result
        print(name, actual, 'expected', expected, flush=True)
        results.append({'test': name, 'expected': expected, 'actual': actual,
                        'exit_code': child.returncode, 'result': result})
    (args.out / 'summary.json').write_text(json.dumps(results, indent=2))
    assert all(row['exit_code'] == 0 and row['actual'] == row['expected']
               and row['result'].get('status') in
               ('valid_proof_checked', 'invalid_proof_checked', 'check_failed')
               for row in results), results


if __name__ == '__main__':
    main()

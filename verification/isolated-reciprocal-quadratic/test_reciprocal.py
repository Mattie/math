"""Test isolated-run preparation and fail-closed decisions without checking proofs."""
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import textwrap
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import reciprocal as r


class ReciprocalHarnessTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def workflow_step(self, title):
        workflow = (r.REPO / '.github/workflows/isolated-irrationality.yml').read_text()
        step = workflow.split('      - name: '+title+'\n', 1)[1].split('      - ', 1)[0]
        return textwrap.dedent(step.split('        run: |\n', 1)[1])

    def test_actual_workflow_routes_only_requested_case(self):
        """Run the actual dispatch shell with a harmless Python-command recorder."""
        shell = self.workflow_step('Check isolation and verify selected frozen source')
        binary = self.root / 'bin'
        binary.mkdir()
        (binary / 'python3').write_text('#!/bin/bash\nprintf "%s\\n" "$@" > "$ARGUMENTS"\n')
        (binary / 'python3').chmod(0o755)
        cases = {
            'reciprocal-quadratic': 'verification/isolated-reciprocal-quadratic/reciprocal.py',
            'quadratic-periods': 'verification/isolated-quadratic-periods/quadratic.py',
            'log': 'verification/isolated-irrationality/verify.py',
            'arctan': 'verification/isolated-irrationality/verify.py',
            'imaginary': 'verification/isolated-irrationality/verify.py',
        }
        for case, runner in cases.items():
            with self.subTest(case=case):
                work = self.root / case
                (work / 'isolated-irrationality/evidence').mkdir(parents=True)
                args = work / 'args.txt'
                env = dict(os.environ, PATH=str(binary)+os.pathsep+os.environ['PATH'],
                           VERIFICATION_CASE=case, RUNNER_TEMP=str(work), ARGUMENTS=str(args))
                result = subprocess.run(['/bin/bash', '-c', shell], cwd=r.REPO, env=env,
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                actual = args.read_text().splitlines()
                self.assertEqual(actual[:2], ['-B', runner])
                self.assertIn(str(work / 'isolated-irrationality'), actual)
                if case in {'log', 'arctan', 'imaginary'}:
                    self.assertEqual(actual[2:4], ['--case', case])
                else:
                    self.assertNotIn('--case', actual)

    def test_capacity_helper_is_checked_before_execution(self):
        """The reciprocal branch must reject changed cleanup code before running it."""
        shell = self.workflow_step('Reserve disk before installing tools').split('# Cleanup', 1)[0]
        relative = 'verification/publication/prepare-independent-runner.sh'
        original = (r.REPO / relative).read_bytes()
        for changed in (False, True):
            with self.subTest(changed=changed):
                root = self.root / str(changed)
                helper = root / relative
                helper.parent.mkdir(parents=True)
                helper.write_bytes(original + (b'\n# changed\n' if changed else b''))
                (root / 'isolated-irrationality/evidence').mkdir(parents=True)
                binary = root / 'bin'
                binary.mkdir()
                (binary / 'bash').write_text('#!/bin/bash\nprintf executed > "$MARKER"\n')
                (binary / 'bash').chmod(0o755)
                marker = root / 'executed'
                env = dict(os.environ, PATH=str(binary)+os.pathsep+os.environ['PATH'],
                           VERIFICATION_CASE='reciprocal-quadratic', RUNNER_TEMP=str(root), MARKER=str(marker))
                result = subprocess.run(['/bin/bash', '-c', shell], cwd=root, env=env,
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, not changed, result.stderr)
                self.assertEqual(marker.exists(), not changed)

    def test_real_frozen_input_inventory_and_proof_selection(self):
        _, sources = r.check_inputs()
        modules = r.proof_modules(sources)
        self.assertEqual(len(modules), 984)
        self.assertIn('PositiveSolution', modules)
        self.assertIn('ClassificationSolution', modules)
        self.assertNotIn('PositiveChallenge', modules)
        self.assertNotIn('ClassificationChallenge', modules)
        self.assertNotIn('lakefile', modules)
        self.assertEqual(len(r.TARGETS), 7)
        self.assertEqual(len(set(r.TARGETS)), 7)

    def test_unreviewed_helpers_cannot_execute(self):
        """Mutate each pinned helper in an isolated copy and attempt runner import."""
        runner = self.root / 'verification/isolated-reciprocal-quadratic/reciprocal.py'
        runner.parent.mkdir(parents=True)
        shutil.copyfile(r.HERE / 'reciprocal.py', runner)
        for name in r.REVIEWED_SUPPORT:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(r.REPO / name, target)
        for name in r.REVIEWED_SUPPORT:
            with self.subTest(helper=name):
                helper = self.root / name
                original = helper.read_bytes()
                marker = self.root / 'unreviewed-code-executed'
                helper.write_bytes(original + f'\nfrom pathlib import Path\nPath({str(marker)!r}).touch()\n'.encode())
                result = subprocess.run([sys.executable, '-B', str(runner)], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('Reviewed supporting script changed', result.stderr)
                self.assertFalse(marker.exists())
                helper.write_bytes(original)

    def fake_run(self):
        return SimpleNamespace(work=self.root, evidence=self.root, lean=Path('/lean'), comparator=Path('/comparator'),
                               env={name: '/tools/'+name for name in
                                    ('PATH', 'HOME', 'COMPARATOR_LANDRUN', 'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_NANODA')},
                               receipt={'checks': {}, 'resources': {}, 'retained_files': {}},
                               flush=Mock(), command=Mock(), collect=Mock())

    def test_all_candidate_loads_keep_protected_boundary_and_limits(self):
        run = self.fake_run()
        candidate = Path('/candidate')
        comparison = r.comparison_command(run, candidate)
        build = r.build_command(run, candidate, ['build', 'ClassificationSolution'], r.SWEEP_SECONDS)
        for command in (comparison, build):
            for expected in ('--user', '--wait', '--pipe', '--collect',
                             '--property=RestrictAddressFamilies=~AF_UNIX',
                             '--property=MemoryMax=12G', '--property=CPUQuota=400%'):
                self.assertIn(expected, command)
        self.assertIn('--property=RuntimeMaxSec=7200', comparison)
        self.assertIn('--property=RuntimeMaxSec=3600', build)
        self.assertEqual(build[build.index('--rwx')+1], '/candidate/.lake')
        self.assertEqual(comparison[-1], 'config.json')

    def test_incomplete_retention_is_not_accepted(self):
        with self.assertRaises(RuntimeError):
            r.collect(self.fake_run(), required=True)

    def test_initial_work_accepts_workflow_diagnostics_but_not_old_builds(self):
        work = self.root / 'workflow'
        r.validate_initial_work(work)
        evidence = work / 'evidence'
        evidence.mkdir(parents=True)
        for name in ('started.txt', 'capacity-input.log', 'capacity.log', 'console.log'):
            (evidence / name).write_text('initial diagnostic')
        r.validate_initial_work(work)
        for location in (work / 'candidate-positive', evidence / 'receipt.json', evidence / 'logs'):
            location.mkdir()
            with self.subTest(location=location), self.assertRaises(RuntimeError):
                r.validate_initial_work(work)
            location.rmdir()

    def test_collect_excludes_live_console_but_hashes_closed_logs(self):
        run = self.fake_run()
        (self.root / 'console.log').write_text('still growing')
        (self.root / 'closed.log').write_text('complete')
        r.collect(run)
        self.assertNotIn('console.log', run.receipt['retained_files'])
        self.assertEqual(run.receipt['retained_files']['closed.log'], r.digest(self.root / 'closed.log'))

    def test_both_configs_reject_missing_targets_and_weakened_policies(self):
        for group, spec in r.GROUPS.items():
            config = json.loads((r.SOURCE / spec['config']).read_text())
            r.check_configuration(config, group)
            alternatives = [{'theorem_names': list(spec['targets'][:-1])},
                            {'theorem_names': [*spec['targets'], 'Other.target']},
                            {'enable_nanoda': False}, {'permitted_axioms': [*r.AXIOMS, 'sorryAx']},
                            {'challenge_module': spec['solution']}, {'solution_module': 'Other'},
                            {'allow_sorry': True}]
            for change in alternatives:
                with self.subTest(group=group, change=change), self.assertRaises(RuntimeError):
                    r.check_configuration({**config, **change}, group)

    def test_both_comparisons_require_all_targets_and_both_kernels(self):
        for group, spec in r.GROUPS.items():
            good = f"Building {spec['solution']}\n" + '\n'.join(spec['targets']) + '\nYour solution is okay!\nLean default kernel accepts the solution\nnanoda kernel accepts the solution'
            omissions = ['Lean default kernel accepts the solution', 'nanoda kernel accepts the solution',
                         spec['targets'][-1], f"Building {spec['solution']}"]
            for omitted in omissions:
                run = self.fake_run()
                run.command.return_value = (0, good.replace(omitted, ''))
                with self.subTest(group=group, omitted=omitted), patch.object(r, 'check_capacity'), self.assertRaises(RuntimeError):
                    r.check_comparison(run, self.root / 'candidate', group)
                self.assertNotIn(group+'_comparison_and_kernels', run.receipt['checks'])
            run = self.fake_run()
            run.command.return_value = (0, good)
            with patch.object(r, 'check_capacity'):
                r.check_comparison(run, self.root / 'candidate', group)
            self.assertEqual(run.receipt['checks'][group+'_comparison_and_kernels'], 'passed')

    def test_real_preparation_has_two_fresh_trees_and_no_proof_verdict(self):
        work = self.root / 'prepared'
        (work / 'evidence').mkdir(parents=True)
        (work / 'evidence/started.txt').write_text('workflow starting')
        with patch.dict(os.environ, RUNNER_TEMP=str(self.root)), \
                patch.object(sys, 'argv', ['reciprocal.py', '--prepare-only', '--work-dir', str(work)]), \
                patch.object(r.Preflight, 'setup') as setup, patch.object(r.Preflight, 'command') as command:
            self.assertEqual(r.main(), 0)
        setup.assert_not_called()
        command.assert_not_called()
        receipt = json.loads((work / 'evidence/receipt.json').read_text())
        self.assertEqual(receipt['status'], 'preparation-only')
        self.assertEqual(receipt['checks'], {'input_preparation': 'complete'})
        self.assertEqual(receipt['commands'], [])
        for group, spec in r.GROUPS.items():
            candidate = work / ('candidate-'+group)
            self.assertEqual(set(p.name for p in (candidate / '.lake').iterdir()), {'packages'})
            self.assertEqual((candidate / '.lake/packages').resolve(), work / 'empty-dependencies')
            self.assertEqual((candidate / 'config.json').read_bytes(), (r.SOURCE / spec['config']).read_bytes())
            self.assertNotEqual((candidate / 'lakefile.lean').read_bytes(), (r.SOURCE / 'lakefile.lean').read_bytes())
            self.assertEqual(receipt['candidates'][group]['initial_compiled_modules'], 0)
        with patch.dict(os.environ, RUNNER_TEMP=str(self.root)), \
                patch.object(sys, 'argv', ['reciprocal.py', '--prepare-only', '--work-dir', str(work)]), \
                self.assertRaises(RuntimeError):
            r.main()

    def test_input_failure_stops_before_tool_setup(self):
        work = self.root / 'failed-run'
        with patch.dict(os.environ, RUNNER_TEMP=str(self.root)), \
                patch.object(sys, 'argv', ['reciprocal.py', '--work-dir', str(work)]), \
                patch.object(r, 'check_inputs', side_effect=RuntimeError('changed source')), \
                patch.object(r.Preflight, 'setup') as setup, patch.object(sys, 'stderr', io.StringIO()):
            self.assertEqual(r.main(), 1)
        setup.assert_not_called()
        receipt = json.loads((work / 'evidence/receipt.json').read_text())
        self.assertEqual(receipt['status'], 'failed')
        self.assertIn('changed source', receipt['error'])


if __name__ == '__main__':
    unittest.main()

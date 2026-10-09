"""Exercise failure boundaries without downloading tools or rebuilding proofs."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import verify


class VerificationTests(unittest.TestCase):
    def configuration_fixture(self, root):
        """Create a small frozen project for configuration-race regressions."""
        repo = root / 'repo'
        lean = repo / 'pkg/lean'
        lean.mkdir(parents=True)
        (lean / 'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'mathlib', 'rev': 'frozen'}]}))
        (lean / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1')
        (lean / 'Fixture.lean').write_text('theorem fixture : True := by trivial\n')
        case = dict(package='pkg', module='Fixture', theorem='fixture',
                    files={f'lean/{p.name}': verify.digest(p) for p in lean.iterdir()})
        pins = dict(audited_revision='fixture', mathlib='frozen', cases={'log': case})
        return repo, lean, pins

    def test_configuration_change_between_validation_and_snapshot_rejected(self):
        for name in ['lake-manifest.json', 'lean-toolchain']:
            with self.subTest(file=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                repo, lean, pins = self.configuration_fixture(root)
                verify.validate_sources(repo, pins['cases'])
                (lean / name).write_text('changed after initial validation')
                run = verify.Run(root / 'work', pins, ['log'])
                with patch.object(verify, 'REPO', repo), self.assertRaisesRegex(ValueError, 'Frozen configuration mismatch'):
                    run.snapshot_configuration()

    def test_projects_reuse_verified_configuration_after_checkout_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, lean, pins = self.configuration_fixture(root)
            run = verify.Run(root / 'work', pins, ['log'])
            with patch.object(verify, 'REPO', repo):
                run.snapshot_configuration()
                for name in ['lake-manifest.json', 'lean-toolchain']:
                    (lean / name).write_text('changed checkout configuration')
                solution = run.project(run.root / 'solution', ['Fixture'])
                # Even changes to an earlier generated project cannot leak into later ones.
                (solution / 'lake-manifest.json').write_text('{}')
                challenge = run.project(run.root / 'challenge', ['Challenge'])
                for name in ['lake-manifest.json', 'lean-toolchain']:
                    self.assertEqual(verify.digest(challenge / name), pins['cases']['log']['files'][f'lean/{name}'])

    def test_changed_actual_and_live_expected_lock_still_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, lean, pins = self.configuration_fixture(root)
            run = verify.Run(root / 'work', pins, ['log'])
            def change_both_locks(args, label, cwd=None):
                self.assertEqual(label, 'fetch-mathlib-cache')
                changed = json.dumps({'packages': [{'name': 'mathlib', 'rev': 'changed'}]})
                (cwd / 'lake-manifest.json').write_text(changed)
                (lean / 'lake-manifest.json').write_text(changed)
            with patch.object(verify, 'REPO', repo):
                run.snapshot_configuration()
                with patch.object(run, 'command', side_effect=change_both_locks), \
                     self.assertRaisesRegex(ValueError, 'Lake changed the frozen dependency lock'):
                    run.cases()

    def test_modified_cached_tool_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            tool = work / 'tools/example'
            tool.mkdir(parents=True)
            subprocess.run(['git', 'init', '-q', str(tool)], check=True)
            source = tool / 'source.txt'
            source.write_text('pinned source\n')
            subprocess.run(['git', '-C', str(tool), 'add', 'source.txt'], check=True)
            subprocess.run(['git', '-C', str(tool), '-c', 'user.name=Fixture',
                            '-c', 'user.email=fixture@example.invalid', 'commit', '-qm', 'fixture'], check=True)
            revision = subprocess.check_output(['git', '-C', str(tool), 'rev-parse', 'HEAD'], text=True).strip()
            run = verify.Run(work, {'audited_revision': 'fixture'}, ['log'])
            self.assertEqual(run.checkout('example', 'unused', revision), tool)
            source.write_text('modified source\n')
            with self.assertRaisesRegex(ValueError, 'Modified cached'):
                run.checkout('example', 'unused', revision)

    def test_changed_or_missing_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'package').mkdir()
            source = root / 'package/Statement.lean'
            source.write_text('theorem statement : True := by trivial\n')
            cases = {'test': {'package': 'package', 'files': {'Statement.lean': verify.digest(source)}}}
            verify.validate_sources(root, cases)
            source.write_text('axiom statement : False\n')
            with self.assertRaisesRegex(ValueError, 'Frozen source mismatch'):
                verify.validate_sources(root, cases)
            source.unlink()
            with self.assertRaisesRegex(ValueError, 'Frozen source mismatch'):
                verify.validate_sources(root, cases)

    def test_fresh_runs_never_reuse_success(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            first = verify.Run(work, {'audited_revision': 'fixture'}, ['log'])
            first.receipt['status'] = 'passed'
            first.flush()
            second = verify.Run(work, {'audited_revision': 'fixture'}, ['log'])
            self.assertNotEqual(first.root, second.root)
            self.assertEqual(second.receipt['status'], 'running')
            with self.assertRaisesRegex(RuntimeError, 'incomplete'):
                second.finish()
            self.assertNotEqual(json.loads((second.root / 'receipt.json').read_text())['status'], 'passed')

    def test_unrelated_failure_is_not_a_rejection_control_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            run = verify.Run(Path(directory), {'audited_revision': 'fixture'}, ['log'])
            with self.assertRaisesRegex(RuntimeError, 'expected diagnostic'):
                run.command([sys.executable, '-c', 'raise RuntimeError("missing input")'],
                            'wrong-reason', reject='Illegal axiom detected')
            run.command([sys.executable, '-c', 'import sys; print("Illegal axiom detected"); sys.exit(1)'],
                        'right-reason', reject='Illegal axiom detected')

    def test_changed_source_main_writes_failed_receipt_before_downloads(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory) / 'work'
            fake_repo = Path(directory) / 'source'
            case = json.loads((verify.HERE / 'pins.json').read_text())['cases']['log']
            changed = fake_repo / case['package'] / next(iter(case['files']))
            changed.parent.mkdir(parents=True)
            changed.write_text('changed source input\n')
            argv = ['verify.py', '--case', 'log', '--work-dir', str(work)]
            with patch.object(verify, 'REPO', fake_repo), patch.object(sys, 'argv', argv), \
                 patch.object(verify.Run, 'tools') as tools, \
                 contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(verify.main(), 1)
                tools.assert_not_called()
            receipts = list(work.glob('runs/*/receipt.json'))
            self.assertEqual(len(receipts), 1)
            receipt = json.loads(receipts[0].read_text())
            self.assertEqual(receipt['status'], 'failed')
            self.assertIn('Frozen source mismatch', receipt['error'])

    def test_wrong_target_or_extra_axiom_is_not_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'export.ndjson'
            rows = [{'meta': {'lean': {'githash': 'fixture'}}}]
            for index, name in enumerate([*verify.AXIOMS, 'target'], 1):
                rows.append({'in': index, 'str': {'pre': 0, 'str': name}})
                rows.append({'axiom' if index < 4 else 'thm': {'name': index}})
            path.write_text(''.join(json.dumps(row) + '\n' for row in rows))
            result = verify.inventory(path, 'target', 'fixture')
            self.assertEqual(result['declarations'], 4)
            self.assertEqual(result['sha256'], verify.digest(path))
            with self.assertRaisesRegex(ValueError, 'inventory failed'):
                verify.inventory(path, 'other-target', 'fixture')
            rows += [{'in': 5, 'str': {'pre': 0, 'str': 'extra'}}, {'axiom': {'name': 5}}]
            path.write_text(''.join(json.dumps(row) + '\n' for row in rows))
            with self.assertRaisesRegex(ValueError, 'inventory failed'):
                verify.inventory(path, 'target', 'fixture')


if __name__ == '__main__':
    unittest.main()

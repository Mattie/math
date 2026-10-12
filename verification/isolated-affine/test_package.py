"""Regression checks for package boundaries and retained axiom evidence; no Lean run."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[2]
PROOF = REPO / 'formalizations/AffineLogarithms'
PAPER = REPO / 'preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class PackageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temp.cleanup)
        cls.root = Path(cls.temp.name)
        cls.proof = cls.root / PROOF.relative_to(REPO)
        cls.paper = cls.root / PAPER.relative_to(REPO)
        for source, destination in [(PROOF, cls.proof), (PAPER, cls.paper)]:
            shutil.copytree(source, destination,
                            ignore=shutil.ignore_patterns('.lake', '.work', 'release-assets', '__pycache__'))
        result = Path('verification/isolated-affine/results/2026-10-11.json')
        (cls.root / result).parent.mkdir(parents=True)
        shutil.copy2(REPO / result, cls.root / result)

    def command(self, path, *args):
        return subprocess.run([sys.executable, '-I', '-B', str(path), *args], cwd=self.root,
                              capture_output=True, text=True)

    def test_clean_packages_and_named_runtime_outputs_pass(self):
        for root, script in [(self.proof, 'check.py'), (self.paper, 'check-publication.py')]:
            with self.subTest(root=root.name):
                work = root / '.work'
                work.mkdir(exist_ok=True)
                (work / 'generated.log').write_text('runtime output')
                result = self.command(root / 'scripts' / script)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_unlisted_files_are_rejected_before_shadow_import(self):
        for root, script in [(self.proof, 'check.py'), (self.paper, 'check-publication.py')]:
            for name in ['unexpected.txt', 'scripts/json.py']:
                with self.subTest(root=root.name, name=name):
                    injected = root / name
                    marker = self.root / 'shadow-import-executed'
                    injected.write_text('from pathlib import Path\nPath(' + repr(str(marker)) + ').touch()\n')
                    try:
                        result = self.command(root / 'scripts' / script)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn('inventory mismatch', result.stdout + result.stderr)
                        self.assertIn(name, result.stdout + result.stderr)
                        self.assertFalse(marker.exists(), 'Unlisted code ran before inventory validation')
                        unsafe = subprocess.run([sys.executable, str(root / 'scripts' / script)],
                                                cwd=self.root, capture_output=True, text=True)
                        self.assertNotEqual(unsafe.returncode, 0)
                        self.assertIn('isolated mode', unsafe.stdout + unsafe.stderr)
                        self.assertFalse(marker.exists())
                    finally:
                        injected.unlink()

    def test_build_rejects_changed_lake_inputs_before_external_commands(self):
        build = load('affine_build_test', PROOF / 'scripts/build.py')
        with patch.object(build, 'ROOT', self.proof), patch.object(build.package_check, 'ROOT', self.proof), \
                patch.object(sys, 'argv', ['build.py', '--skip-cache-download']), \
                patch.object(build.subprocess, 'check_output') as command:
            for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
                with self.subTest(name=name):
                    path = self.proof / name
                    original = path.read_bytes()
                    try:
                        path.write_bytes(original + b'\nchanged\n')
                        with self.assertRaisesRegex(RuntimeError, 'Package file changed: ' + name):
                            build.main()
                        command.assert_not_called()
                    finally:
                        path.write_bytes(original)

    def test_replay_rejects_additions_before_import_or_checker_execution(self):
        script = self.proof / 'scripts/replay.py'
        marker = self.root / 'replay-shadow-import-executed'
        for name in ['unexpected.txt', 'scripts/json.py']:
            injected = self.proof / name
            injected.write_text('from pathlib import Path\nPath(' + repr(str(marker)) + ').touch()\n')
            try:
                args = ['--controls-only', '--nanoda', 'missing-nanoda', '--lean-reader', 'missing-reader']
                result = self.command(script, *args)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('inventory mismatch', result.stdout + result.stderr)
                unsafe = subprocess.run([sys.executable, str(script), *args], cwd=self.root,
                                        capture_output=True, text=True)
                self.assertNotEqual(unsafe.returncode, 0)
                self.assertIn('isolated mode', unsafe.stdout + unsafe.stderr)
                self.assertFalse(marker.exists())
            finally:
                injected.unlink()

    def test_replay_rejects_changed_control_before_checker_execution(self):
        replay = load('affine_replay_test', PROOF / 'scripts/replay.py')
        fixture = self.proof / 'controls/positive.ndjson'
        original = fixture.read_bytes()
        try:
            fixture.write_bytes(original + b'\nchanged\n')
            with patch.object(replay.package_check, 'ROOT', self.proof), \
                    patch.object(sys, 'argv', ['replay.py', '--controls-only', '--nanoda', 'missing', '--lean-reader', 'missing']), \
                    patch.object(replay.subprocess, 'run') as command:
                with self.assertRaisesRegex(RuntimeError, 'Package file changed: controls/positive.ndjson'):
                    replay.main()
                command.assert_not_called()
        finally:
            fixture.write_bytes(original)

    def test_axiom_controls_reject_shadow_imports_and_changed_policy_before_commands(self):
        script = self.proof / 'scripts/audit_controls.py'
        marker = self.root / 'controls-shadow-import-executed'
        for name in ['scripts/json.py', 'scripts/subprocess.py']:
            injected = self.proof / name
            injected.write_text('from pathlib import Path\nPath(' + repr(str(marker)) + ').touch()\n')
            try:
                result = self.command(script)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('inventory mismatch', result.stdout + result.stderr)
                unsafe = subprocess.run([sys.executable, str(script)], cwd=self.root,
                                        capture_output=True, text=True)
                self.assertNotEqual(unsafe.returncode, 0)
                self.assertIn('isolated mode', unsafe.stdout + unsafe.stderr)
                self.assertFalse(marker.exists())
            finally:
                injected.unlink()
        controls = load('affine_controls_test', PROOF / 'scripts/audit_controls.py')
        policy = self.proof / 'scripts/audit_axioms.py'
        original = policy.read_bytes()
        try:
            policy.write_bytes(original + b'\n# modified\n')
            with patch.object(controls.package_check, 'ROOT', self.proof), \
                    patch.object(controls.subprocess, 'check_output') as command:
                with self.assertRaisesRegex(RuntimeError, 'Package file changed: scripts/audit_axioms.py'):
                    controls.main()
                command.assert_not_called()
        finally:
            policy.write_bytes(original)

    def test_updated_manifests_cannot_reuse_a_stale_axiom_log(self):
        paths = [self.proof / name for name in
                 ['PairedAffine/Main.lean', 'evidence/source-sha256.json', 'manifest-sha256.json']]
        originals = [path.read_bytes() for path in paths]
        try:
            paths[0].write_bytes(originals[0] + b'\naxiom review_regression : False\n')
            sources = json.loads(paths[1].read_text())
            sources['PairedAffine/Main.lean'] = hashlib.sha256(paths[0].read_bytes()).hexdigest()
            paths[1].write_text(json.dumps(sources))
            inventory = json.loads(paths[2].read_text())
            for name in ['PairedAffine/Main.lean', 'evidence/source-sha256.json']:
                inventory[name] = hashlib.sha256((self.proof / name).read_bytes()).hexdigest()
            paths[2].write_text(json.dumps(inventory))
            integrity = self.command(self.proof / 'scripts/check.py')
            self.assertEqual(integrity.returncode, 0, integrity.stdout + integrity.stderr)
            evidence = self.proof / 'evidence/full-module-sweep-2026-10-11'
            result = self.command(self.proof / 'scripts/audit_axioms.py',
                                  '--log', str(evidence / 'build.log'),
                                  '--targets', str(self.proof / 'evidence/target-map.json'),
                                  '--receipt', str(evidence / 'receipt.json'),
                                  '--source-manifest', str(paths[1]))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Retained audit identity mismatch: source_manifest_sha256', result.stderr)
        finally:
            for path, original in zip(paths, originals):
                path.write_bytes(original)


class AxiomEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.audit = load('affine_audit_test', PROOF / 'scripts/audit_axioms.py')
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.map = {'public_declarations': [{'public_declaration': 'public_result'}],
                    'standard_endpoints': ['standard_result']}

    def test_standard_endpoint_reports_are_required_and_audited(self):
        targets = self.audit.target_names(self.map)
        public = "'public_result' depends on axioms: [propext]\n"
        with self.assertRaisesRegex(ValueError, 'Missing axiom report for standard_result'):
            self.audit.inspect(public, targets)
        with self.assertRaisesRegex(ValueError, 'Unexpected axioms for standard_result: forbidden'):
            self.audit.inspect(public + "'standard_result' depends on axioms: [forbidden]\n", targets)
        self.assertEqual(len(self.audit.inspect(public + "'standard_result' does not depend on any axioms\n", targets)), 2)

    def test_retained_log_is_bound_to_source_manifest_targets_and_success(self):
        paths = {name: self.root / name for name in ['source.json', 'targets.json', 'build.log', 'receipt.json']}
        paths['source.json'].write_text('{"Proof.lean":"checked-source"}')
        paths['targets.json'].write_text(json.dumps(self.map))
        paths['build.log'].write_text("'public_result' does not depend on any axioms\n")
        receipt = {'status': 'passed'}
        for key, name in [('source_manifest_sha256','source.json'), ('target_map_sha256','targets.json'), ('log_sha256','build.log')]:
            receipt[key] = hashlib.sha256(paths[name].read_bytes()).hexdigest()
        paths['receipt.json'].write_text(json.dumps(receipt))
        args = [paths[n] for n in ['receipt.json','source.json','targets.json','build.log']]
        self.audit.check_receipt(*args)
        for name in ['source.json','targets.json','build.log']:
            original = paths[name].read_bytes()
            try:
                paths[name].write_bytes(original + b' changed')
                with self.assertRaisesRegex(ValueError, 'Retained audit identity mismatch'):
                    self.audit.check_receipt(*args)
            finally:
                paths[name].write_bytes(original)
        receipt['status'] = 'failed'
        paths['receipt.json'].write_text(json.dumps(receipt))
        with self.assertRaisesRegex(ValueError, 'did not pass'):
            self.audit.check_receipt(*args)


if __name__ == '__main__':
    unittest.main()

"""Preparation only: check real route configuration and fail-closed bookkeeping."""
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch
import verify


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_pinned_shared_runner_and_policy(self):
        self.assertEqual(verify.digest(verify.LEGACY_PATH), verify.LEGACY_SHA256)
        pins, _, _ = verify.legacy.check_inputs()
        self.assertEqual(json.loads((verify.HERE / 'pins.json').read_text()), pins)
        config = json.loads((verify.HERE / 'config.json').read_text())
        self.assertEqual(config['permitted_axioms'], verify.legacy.preflight.AXIOMS)
        self.assertTrue(config['enable_nanoda'])
        self.assertEqual(len(set(config['theorem_names'])), 6)

    def test_manual_workflow_uses_new_adapter_and_reviewed_boundary_setup(self):
        text = (verify.REPO / '.github/workflows/isolated-affine-denominators.yml').read_text()
        self.assertIn('workflow_dispatch:', text)
        self.assertNotIn('pull_request:', text)
        self.assertNotIn('push:', text)
        self.assertIn('contents: read', text)
        self.assertIn('persist-credentials: false', text)
        self.assertIn('verification/isolated-affine-denominators/verify.py --run', text)
        self.assertIn('--work-dir "$RUNNER_TEMP/isolated-affine-denominators"', text)
        cleanup = 'verification/publication/prepare-independent-runner.sh'
        cleanup_hash = verify.legacy.BASELINE[cleanup]
        self.assertLess(text.index(cleanup_hash + '  ' + cleanup), text.index('bash ' + cleanup))
        self.assertLess(text.index('bash ' + cleanup), text.index('actions/setup-go@'))
        self.assertIn('if: always()', text)
        self.assertIn('retention-days: 90', text)

    def test_registered_dispatch_workflow_routes_denominator_case(self):
        text = (verify.REPO / '.github/workflows/isolated-irrationality.yml').read_text()
        self.assertIn('workflow_dispatch:', text)
        self.assertNotIn('pull_request:', text)
        self.assertNotIn('push:', text)
        self.assertIn('contents: read', text)
        self.assertIn('persist-credentials: false', text)
        self.assertIn('          - affine-denominators', text)
        # Other cases can share the budget; this case need not be last in the OR list.
        case = r"inputs\.case == '[a-z-]+'"
        condition = (rf"\((?:{case} \|\| )*inputs\.case == 'affine-denominators'"
                     rf"(?: \|\| {case})*\)")
        self.assertRegex(text, rf"timeout-minutes: \$\{{\{{ {condition} && 360 \|\| 240 \}}\}}")
        branch = text.split('elif [[ "$VERIFICATION_CASE" == affine-denominators ]]; then')[1].split('elif ')[0]
        self.assertIn('python3 -I -B verification/isolated-affine-denominators/verify.py --run', branch)
        self.assertIn('--work-dir "$RUNNER_TEMP/isolated-irrationality"', branch)
        cleanup = 'verification/publication/prepare-independent-runner.sh'
        self.assertLess(text.index(verify.legacy.BASELINE[cleanup] + '  ' + cleanup), text.index('bash ' + cleanup))
        self.assertLess(text.index('bash ' + cleanup), text.index('actions/setup-go@'))
        self.assertRegex(text, rf"if: always\(\) && {condition}(?:\r?\n|$)")
        self.assertIn('retention-days: 90', text)

    def test_memory_diagnostics_are_values_and_require_complete_units(self):
        path = self.root / 'meminfo'
        path.write_text('MemTotal: 100 kB\nMemAvailable: 50 kB\nSwapTotal: 20 kB\nSwapFree: 10 kB\nOther: 99 kB\n')
        self.assertEqual(verify.memory_snapshot(path), {
            'MemTotal_bytes': 102400, 'MemAvailable_bytes': 51200,
            'SwapTotal_bytes': 20480, 'SwapFree_bytes': 10240})
        for text in ('MemTotal: 100 kB\n', 'MemTotal: 100 MB\n'):
            path.write_text(text)
            with self.assertRaises(RuntimeError):
                verify.memory_snapshot(path)

    def test_absent_freeze_rejects_execution(self):
        with patch.object(verify, 'MANIFEST', self.root / 'absent.json'):
            with self.assertRaisesRegex(RuntimeError, 'Source freeze pending'):
                verify.check_inputs()

    def test_frozen_inputs_do_not_silently_refresh(self):
        manifest = self.root / 'manifest.json'
        manifest.write_text('{"overlay": {"Pilot.lean": "old"}}')
        with patch.object(verify, 'MANIFEST', manifest), patch.object(verify, 'inventory', return_value={}):
            with self.assertRaisesRegex(RuntimeError, 'Frozen denominator inputs changed'):
                verify.check_inputs()
        self.assertIn('old', manifest.read_text())

    def test_actual_imported_admission_route_has_policy_and_sandbox(self):
        run = SimpleNamespace(work=self.root, lean=Path('/lean'), comparator=Path('/comparator'),
            env={k: '/value' for k in ('PATH', 'HOME', 'COMPARATOR_LANDRUN', 'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_NANODA')},
            receipt={'pins': {'lean_version': '4.34.1'}, 'checks': {}}, flush=Mock(),
            command=Mock(side_effect=[(0, ''), (1, "Building Solution\nIllegal axiom detected: 'sorryAx'")]))
        verify.legacy.imported_admission(run)
        args = run.command.call_args.args[1]
        self.assertIn('--property=RestrictAddressFamilies=~AF_UNIX', args)
        self.assertEqual(args[-1], 'config.json')
        config = json.loads((self.root / 'imported-admission/config.json').read_text())
        self.assertEqual(config['permitted_axioms'], verify.legacy.preflight.AXIOMS)
        self.assertTrue(config['enable_nanoda'])
        self.assertIn('import Admitted', (self.root / 'imported-admission/Solution.lean').read_text())
        self.assertEqual(run.receipt['checks'], {'imported-admission': 'passed'})

    def test_forbidden_axiom_and_imported_admission_require_intended_failure(self):
        verify.legacy.preflight.check_comparator('axiom', 1, "Illegal axiom detected: 'forbidden_control'")
        for code, text in [(0, "Illegal axiom detected: 'sorryAx'"), (1, 'timeout'),
                           (1, "Illegal axiom detected: 'sorryAx'\nYour solution is okay!")]:
            with self.assertRaises(RuntimeError):
                verify.legacy.preflight.check_comparator('axiom', code, text)

    def test_exact_targets_and_both_kernels_are_required(self):
        targets = json.loads((verify.HERE / 'config.json').read_text())['theorem_names']
        text = '\n'.join(['Building Challenge', 'Building Solution', *verify.legacy.preflight.ACCEPTANCE,
            *('Exporting #[' + ', '.join(targets) + '] from ' + m for m in ('Challenge', 'Solution'))])
        verify.legacy.check_proof_output(0, text, targets)
        for invalid in (text.replace(targets[-1], 'missing'),
                        text.replace('nanoda kernel accepts the solution', ''),
                        text.replace('Lean default kernel accepts the solution', '')):
            with self.assertRaises(RuntimeError):
                verify.legacy.check_proof_output(0, invalid, targets)

    def test_trusted_spec_does_not_import_candidate_or_custom_target_alias(self):
        text = (verify.HERE / 'Challenge.lean').read_text(encoding='utf-8')
        imports = [line for line in text.splitlines() if line.startswith('import ')]
        self.assertTrue(all(line.startswith('import Mathlib.') for line in imports))
        self.assertIn('Real.log ((3 : ℝ) / 2)', text)
        self.assertIn('∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧', text)
        self.assertIn('∀ p : ℤ, ∀ q : ℕ, Q ≤ q →', text)
        self.assertIn('¬ LiouvilleWith', text)
        solution = (verify.HERE / 'Solution.lean').read_text(encoding='utf-8')
        self.assertNotIn('import Challenge', solution)
        self.assertNotIn('sorry', solution)


if __name__ == '__main__':
    unittest.main()

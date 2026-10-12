"""Preparation and fail-closed tests; no Lean, network or hosted execution."""
import io
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

    def test_actual_frozen_inventory_and_affine_tool_pins(self):
        pins, files, config = verify.check_inputs()
        self.assertEqual(len(files), 969)
        self.assertEqual(len(config["theorem_names"]), 15)
        self.assertEqual(sum(t.endswith("standard_exponent_le_four") for t in config["theorem_names"]), 3)
        self.assertEqual(pins["comparator"], "ca04cfc72b550331658ec314bf47685281bfd4bf")
        self.assertEqual(pins["exporter"], "05d43a2bc773b40ecfdebb32294192a5ef756951")
        self.assertEqual(verify.preflight.PINS, verify.PINS)

    def test_changed_helpers_are_rejected_before_either_import_executes(self):
        names = ['verification/isolated-6942/verify.py', 'verification/isolated-preflight/preflight.py']
        for name in names:
            destination = self.root / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((verify.REPO / name).read_bytes())
        marker = self.root / 'executed'
        for name in names:
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                try:
                    path.write_text('from pathlib import Path\nPath(' + repr(str(marker)) + ').touch()\n')
                    with patch.object(verify, 'REPO', self.root), \
                            patch.object(verify.importlib.util, 'spec_from_file_location') as loader:
                        with self.assertRaisesRegex(RuntimeError, 'Reviewed helper changed before import'):
                            verify.load_shared()
                        loader.assert_not_called()
                    self.assertFalse(marker.exists())
                finally:
                    path.write_bytes(original)

    def test_disk_preparation_is_pinned_before_execution_in_both_workflows(self):
        name = 'verification/publication/prepare-independent-runner.sh'
        sha = verify.BASELINE[name]
        self.assertEqual(verify.digest(verify.REPO / name), sha)
        for workflow in ['isolated-affine.yml', 'isolated-irrationality.yml']:
            text = (verify.REPO / '.github/workflows' / workflow).read_text()
            self.assertLess(text.index(sha + '  ' + name), text.index('bash ' + name))
            if workflow == 'isolated-irrationality.yml':
                self.assertIn('"$VERIFICATION_CASE" == affine', text[:text.index(sha)])

    def test_inventory_rejects_changed_missing_extra_and_escape(self):
        file = self.root / "Main.lean"
        file.write_text("-- frozen\n")
        files = {"Main.lean": verify.digest(file)}
        verify.validate_sources(self.root, files)
        file.write_text("-- changed\n")
        with self.assertRaisesRegex(RuntimeError, "mismatch"):
            verify.validate_sources(self.root, files)
        file.unlink()
        with self.assertRaisesRegex(RuntimeError, "inventory"):
            verify.validate_sources(self.root, files)
        file.write_text("-- frozen\n")
        (self.root / "Extra.lean").write_text("-- unexpected\n")
        with self.assertRaisesRegex(RuntimeError, "inventory"):
            verify.validate_sources(self.root, files)
        with self.assertRaisesRegex(RuntimeError, "Unsafe"):
            verify.regular(self.root, "../outside")

    def test_candidate_freshness_and_byte_identity(self):
        pins, files, config = verify.check_inputs()
        evidence = self.root / "evidence"
        evidence.mkdir()
        packages = self.root / "dependencies/packages"
        packages.mkdir(parents=True)
        (packages / "cached.olean").write_bytes(b"upstream only")
        run = SimpleNamespace(work=self.root, evidence=evidence)
        try:
            path, protected = verify.prepare_candidate(run, pins, files, packages)
        except OSError as error:
            self.skipTest(f"Symlinks unavailable: {error}")
        self.assertEqual({p.name for p in (path / ".lake").iterdir()}, {"packages"})
        self.assertEqual((path / ".lake/packages").resolve(), packages.resolve())
        for name, sha in files.items():
            self.assertEqual(verify.digest(path / name), sha)
        self.assertEqual(json.loads((path / "config.json").read_text()), config)
        self.assertEqual(len(protected), 972)
        self.assertNotIn("replay-reader/Main.lean", protected)
        with self.assertRaises(FileExistsError):
            verify.prepare_candidate(run, pins, files, packages)

    def test_generated_lake_config_does_not_copy_submitted_code(self):
        source = self.root / "source"
        source.mkdir()
        for name in ("lean-toolchain", "lake-manifest.json"):
            (source / name).write_text("frozen input")
        (source / "lakefile.lean").write_text("UNTRUSTED BUILD CODE")
        path = self.root / "project"
        verify.project(path, source, "fixed-mathlib-revision", ["Challenge"])
        text = (path / "lakefile.lean").read_text(encoding="utf-8")
        self.assertNotIn("UNTRUSTED", text)
        self.assertIn('fixedToolchain := true', text)
        self.assertIn('@ "fixed-mathlib-revision"', text)
        self.assertNotIn("lean_lib Solution", text)

    def test_workdir_rejects_reuse_and_preserves_diagnostics(self):
        work = self.root / "work"
        with patch.dict(verify.os.environ, {"RUNNER_TEMP": str(self.root)}):
            self.assertEqual(verify.fresh_work(work), work.resolve())
            (work / "evidence").mkdir(parents=True)
            (work / "evidence/capacity.log").write_text("measured")
            self.assertEqual(verify.fresh_work(work), work.resolve())
            (work / "affine").mkdir()
            with self.assertRaisesRegex(RuntimeError, "not fresh"):
                verify.fresh_work(work)
            with self.assertRaisesRegex(RuntimeError, "absolute"):
                verify.fresh_work(Path("relative"))
            with self.assertRaisesRegex(RuntimeError, "subdirectory"):
                verify.fresh_work(self.root)

    def test_proof_output_requires_all_targets_in_each_export_and_both_kernels(self):
        targets = verify.check_inputs()[2]["theorem_names"]
        output = "\n".join(["Building Challenge", "Building Solution", *verify.preflight.ACCEPTANCE,
            *("Exporting #[" + ", ".join(targets) + "] from " + module for module in ("Challenge", "Solution"))])
        verify.check_proof_output(0, output, targets)
        invalid = [output.replace(targets[-1], "unrelated"),
                   output.replace("nanoda kernel accepts the solution", ""),
                   output.replace("Lean default kernel accepts the solution", ""),
                   output.replace("] from Solution", "] from Other"),
                   output.replace("Building Solution", ""),
                   output + "\nExporting #[other] from Solution"]
        for text in invalid:
            with self.subTest(text=text[-70:]), self.assertRaises(RuntimeError):
                verify.check_proof_output(0, text, targets)
        with self.assertRaises(RuntimeError):
            verify.check_proof_output(1, output, targets)

    def test_historical_affine_diagnostics_match_required_frontend_interface(self):
        targets = verify.check_inputs()[2]["theorem_names"]
        output = (verify.SOURCE / "evidence/comparator.log").read_text(encoding="utf-8")
        verify.check_proof_output(0, output, targets)
        rejected = (verify.SOURCE / "evidence/pre-pr/comparator-controls/03-admitted-comparator.log").read_text()
        verify.preflight.check_comparator("axiom", 1, rejected)
        self.assertIn("Illegal axiom detected: 'sorryAx'", rejected)

    def test_actual_route_imported_control_is_not_a_source_scan(self):
        run = SimpleNamespace(work=self.root, lean=Path("/lean"), comparator=Path("/comparator"),
            env={key: "/value" for key in ("PATH", "HOME", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")},
            receipt={"pins": {"lean_version": "4.34.1"}, "checks": {}}, flush=Mock(),
            command=Mock(side_effect=[(0, ""), (1, "Building Solution\nIllegal axiom detected: 'sorryAx'")]))
        verify.imported_admission(run)
        self.assertEqual(run.receipt["checks"], {"imported-admission": "passed"})
        self.assertIn("import Admitted", (self.root / "imported-admission/Solution.lean").read_text())
        args = run.command.call_args.args[1]
        self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", args)
        self.assertEqual(args[-1], "config.json")

    def test_imported_control_rejects_unrelated_failure_or_conflicting_success(self):
        for n, output in enumerate(("syntax error", "Illegal axiom detected: 'different'",
                                    "Illegal axiom detected: 'sorryAx'\nYour solution is okay!")):
            work = self.root / str(n)
            work.mkdir()
            run = SimpleNamespace(work=work, lean=Path("/lean"), comparator=Path("/comparator"),
                env={key: "/value" for key in ("PATH", "HOME", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")},
                receipt={"pins": {"lean_version": "4.34.1"}, "checks": {}}, flush=Mock(),
                command=Mock(side_effect=[(0, ""), (1, "Building Solution\n" + output)]))
            with self.assertRaises(RuntimeError):
                verify.imported_admission(run)
            self.assertEqual(run.receipt["checks"], {})

    def test_resource_command_keeps_boundary_and_records_new_budget(self):
        run = SimpleNamespace(lean=Path("/lean"), comparator=Path("/comparator"),
            env={key: "/value" for key in ("PATH", "HOME", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")})
        args = verify.proof_command(run, Path("/candidate"))
        for option in ("--user", "--wait", "--pipe", "--collect", "--property=RestrictAddressFamilies=~AF_UNIX",
                       "--property=RuntimeMaxSec=18000", "--property=MemoryMax=12G", "--property=CPUQuota=400%",
                       "--setenv=LEAN_NUM_THREADS=4"):
            self.assertIn(option, args)

    def test_low_disk_failure_retains_receipt_without_tool_setup(self):
        work = self.root / "work"
        with patch.dict(verify.os.environ, {"RUNNER_TEMP": str(self.root)}), \
                patch.object(verify.sys, "argv", ["verify.py", "--work-dir", str(work)]), \
                patch.object(verify.sys, "stderr", io.StringIO()), \
                patch.object(verify.shared.shutil, "disk_usage", return_value=SimpleNamespace(free=0)), \
                patch.object(verify.Preflight, "setup") as setup:
            self.assertEqual(verify.main(), 1)
            setup.assert_not_called()
        receipt = json.loads((work / "evidence/receipt.json").read_text())
        self.assertEqual(receipt["status"], "failed")
        self.assertIn("35 GiB", receipt["error"])
        self.assertEqual(len(receipt["targets"]), 15)


if __name__ == "__main__":
    unittest.main()

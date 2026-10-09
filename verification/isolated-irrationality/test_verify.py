"""Local preparation tests: no downloads, tool builds, or proof execution."""
import hashlib
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
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        (self.source / "lean/Arctangent").mkdir(parents=True)
        contents = {"lean/Arctangent/FormalConjectures.lean": b"-- candidate bytes\n",
                    "lean/lakefile.lean": b"-- submitted configuration must never be copied\n",
                    "lean/lean-toolchain": b"leanprover/lean4:v4.34.1\n",
                    "lean/lake-manifest.json": b'{"packages": []}\n'}
        self.case = {"files": {}}
        for name, value in contents.items():
            (self.source / name).write_bytes(value)
            self.case["files"][name] = hashlib.sha256(value).hexdigest()

    def test_invalid_work_directory_is_rejected_before_evidence_creation(self):
        repo = self.root / "repo"
        temp = self.root / "runner-temp"
        cases = [
            (Path("relative-work"), str(temp), "absolute work"),
            (repo / "work", str(self.root), "outside the repository"),
            (repo, str(self.root), "outside the repository"),
            (self.root / "outside", str(temp), "subdirectory of RUNNER_TEMP"),
            (temp, str(temp), "subdirectory of RUNNER_TEMP"),
            (temp / "work", "", "RUNNER_TEMP must be an absolute"),
            (temp / "work", "relative-temp", "RUNNER_TEMP must be an absolute"),
        ]
        before = set(self.root.rglob("*"))
        for work, runner_temp, message in cases:
            with self.subTest(work=work, runner_temp=runner_temp), \
                    patch.object(verify, "REPO", repo), \
                    patch.dict(verify.os.environ, {"RUNNER_TEMP": runner_temp}), \
                    patch.object(verify.sys, "argv", ["verify.py", "--case", "arctan", "--work-dir", str(work)]), \
                    patch.object(verify, "Preflight") as preflight:
                with self.assertRaisesRegex(RuntimeError, message):
                    verify.main()
                preflight.assert_not_called()
                self.assertEqual(set(self.root.rglob("*")), before)

    def test_valid_work_directory_is_resolved_without_creating_it(self):
        temp = self.root / "runner-temp"
        work = temp / "unused/../work"
        with patch.object(verify, "REPO", self.root / "repo"), \
                patch.dict(verify.os.environ, {"RUNNER_TEMP": str(temp)}):
            self.assertEqual(verify.validate_work_dir(work), (temp / "work").resolve())
        self.assertFalse(temp.exists())

    def test_work_directory_symlink_escape_is_rejected_before_evidence_creation(self):
        temp = self.root / "runner-temp"
        temp.mkdir()
        link = temp / "escape"
        try:
            link.symlink_to(self.source, target_is_directory=True)
        except OSError as error:
            self.skipTest(f"Symlink creation unavailable: {error}")
        with patch.object(verify, "REPO", self.root / "repo"), \
                patch.dict(verify.os.environ, {"RUNNER_TEMP": str(temp)}), \
                patch.object(verify.sys, "argv", ["verify.py", "--case", "arctan", "--work-dir", str(link / "work")]), \
                patch.object(verify, "Preflight") as preflight:
            with self.assertRaisesRegex(RuntimeError, "subdirectory of RUNNER_TEMP"):
                verify.main()
            preflight.assert_not_called()
        self.assertFalse((self.source / "work").exists())

    def test_inventory_accepts_exact_sources_and_rejects_extra(self):
        verify.validate_sources(self.source, self.case)
        (self.source / "lean/Extra.lean").write_text("axiom extra : False\n")
        with self.assertRaisesRegex(RuntimeError, "inventory"):
            verify.validate_sources(self.source, self.case)

    def test_inventory_rejects_changed_and_missing_source(self):
        path = self.source / "lean/Arctangent/FormalConjectures.lean"
        path.write_text("-- changed\n")
        with self.assertRaisesRegex(RuntimeError, "mismatch"):
            verify.validate_sources(self.source, self.case)
        path.unlink()
        with self.assertRaisesRegex(RuntimeError, "inventory"):
            verify.validate_sources(self.source, self.case)

    def test_manifest_paths_cannot_escape(self):
        with self.assertRaisesRegex(RuntimeError, "Unsafe"):
            verify.regular(self.source, "../outside")
        with self.assertRaisesRegex(RuntimeError, "Unsafe"):
            verify.regular(self.source, str(self.root / "absolute"))

    def test_generated_config_uses_pinned_mathlib_without_submitted_config(self):
        target = self.root / "trusted"
        verify.project(target, self.source, "test-pin", ["Challenge"])
        self.assertEqual((target / "lean-toolchain").read_bytes(),
                         (self.source / "lean/lean-toolchain").read_bytes())
        self.assertEqual((target / "lake-manifest.json").read_bytes(),
                         (self.source / "lean/lake-manifest.json").read_bytes())
        config = (target / "lakefile.lean").read_text(encoding="utf-8")
        self.assertIn('@ "test-pin"', config)
        self.assertNotIn("submitted configuration", config)
        self.assertNotIn("lean_lib Arctangent", config)

    def test_candidate_is_byte_identical_and_has_no_prebuilt_proof(self):
        work = self.root / "work"
        evidence = work / "evidence"
        evidence.mkdir(parents=True)
        packages = work / "dependencies/packages"
        packages.mkdir(parents=True)
        run = SimpleNamespace(work=work, evidence=evidence)
        try:
            target, protected = verify.prepare_candidate(run, {"mathlib": "test-pin"},
                                                        self.case, self.source, packages, "arctan")
        except OSError as error:
            self.skipTest(f"Symlink creation unavailable: {error}")
        self.assertEqual((target / "Arctangent/FormalConjectures.lean").read_bytes(),
                         (self.source / "lean/Arctangent/FormalConjectures.lean").read_bytes())
        self.assertEqual(set(p.name for p in (target / ".lake").iterdir()), {"packages"})
        self.assertEqual((target / ".lake/packages").resolve(), packages.resolve())
        config = json.loads((target / "config.json").read_text())
        self.assertEqual(config["theorem_names"], [verify.TARGETS["arctan"]["theorem"]])
        self.assertEqual(config["solution_module"], verify.TARGETS["arctan"]["module"])
        self.assertTrue(config["enable_nanoda"])
        self.assertIn("Challenge.lean", protected)

    def test_dependency_inventory_detects_modified_and_added_artifacts(self):
        deps = self.root / "deps"
        deps.mkdir()
        (deps / "source.lean").write_text("-- dependency\n")
        initial = verify.tree_identity(deps)
        (deps / "source.olean").write_bytes(b"compiled")
        self.assertNotEqual(verify.tree_identity(deps), initial)
        next_state = verify.tree_identity(deps)
        (deps / "source.olean").write_bytes(b"modified")
        self.assertNotEqual(verify.tree_identity(deps), next_state)

    def test_proof_command_keeps_tested_guards_and_resource_limits(self):
        run = SimpleNamespace(lean=Path("/lean"), comparator=Path("/comparator"),
                              env={key: "/test/" + key for key in
                                   ("PATH", "HOME", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")})
        args = verify.proof_command(run, Path("/proof"))
        for option in ("--user", "--wait", "--collect", "--pipe",
                       "--property=RestrictAddressFamilies=~AF_UNIX", "--property=RuntimeMaxSec=7200",
                       "--property=MemoryMax=12G", "--property=CPUQuota=400%"):
            self.assertIn(option, args)
        self.assertEqual(args[-4:], [str(Path("/lean/bin/lake")), "env", str(Path("/comparator")), "config.json"])

    def test_insufficient_or_unreadable_capacity_stops_before_setup(self):
        for label, usage in (("low", SimpleNamespace(free=14 * 1024**3)),
                             ("unreadable", OSError("disk measurement unavailable"))):
            work = self.root / label
            with self.subTest(label=label), \
                    patch.dict(verify.os.environ, {"RUNNER_TEMP": str(self.root)}), \
                    patch.object(verify.sys, "argv", ["verify.py", "--case", "arctan", "--work-dir", str(work)]), \
                    patch.object(verify.sys, "stderr", io.StringIO()), \
                    patch.object(verify.shutil, "disk_usage", side_effect=[usage]), \
                    patch.object(verify.Preflight, "setup") as setup, \
                    patch.object(verify, "prepare_dependencies") as dependencies:
                self.assertEqual(verify.main(), 1)
                setup.assert_not_called()
                dependencies.assert_not_called()
            receipt = json.loads((work / "evidence/receipt.json").read_text())
            self.assertEqual(receipt["status"], "failed")
            if label == "low":
                self.assertIn("35 GiB", receipt["error"])
                self.assertEqual(receipt["resources"]["free_bytes_before_setup"], 14 * 1024**3)
            else:
                self.assertIn("disk measurement unavailable", receipt["error"])

    def test_capacity_thresholds_and_measurements_are_retained(self):
        run = SimpleNamespace(work=self.root, receipt={}, flush=Mock())
        for phase, required in (("setup", 35), ("proof", 10)):
            with self.subTest(phase=phase), \
                    patch.object(verify.shutil, "disk_usage",
                                 return_value=SimpleNamespace(free=required * 1024**3)):
                verify.check_capacity(run, phase, required)
        self.assertEqual(run.receipt["resources"]["free_bytes_before_setup"], 35 * 1024**3)
        self.assertEqual(run.receipt["resources"]["required_bytes_before_proof"], 10 * 1024**3)

    def test_low_capacity_stops_before_candidate_build(self):
        for free in (5 * 1024**3, 10 * 1024**3 - 1):
            run = SimpleNamespace(work=self.root, receipt={}, flush=Mock(), command=Mock())
            with self.subTest(free=free), \
                    patch.object(verify.shutil, "disk_usage", return_value=SimpleNamespace(free=free)):
                with self.assertRaisesRegex(RuntimeError, "10 GiB free before proof"):
                    verify.run_proof(run, self.root / "candidate", {}, self.root / "deps", {}, "arctan")
            run.command.assert_not_called()
            self.assertEqual(run.receipt["resources"]["free_bytes_before_proof"], free)

    def test_existing_pins_and_exact_case_are_still_valid(self):
        pins, case, _ = verify.check_inputs("arctan")
        self.assertEqual(case["theorem"], verify.TARGETS["arctan"]["theorem"])
        self.assertEqual(pins["lean_version"], "4.34.1")

    def test_selector_is_required_and_rejects_unprepared_cases_before_setup(self):
        for selection in ([], ["--case", "all"], ["--case", "realnorm"], ["--case", "unknown"]):
            with self.subTest(selection=selection), \
                    patch.object(verify.sys, "argv", ["verify.py", "--work-dir", str(self.root / "work"), *selection]), \
                    patch.object(verify.sys, "stderr", io.StringIO()), \
                    patch.object(verify, "Preflight") as preflight:
                with self.assertRaises(SystemExit) as failure:
                    verify.main()
                self.assertEqual(failure.exception.code, 2)
                preflight.assert_not_called()

    def test_all_frozen_cases_prepare_exact_sources_and_independent_challenges(self):
        for key, expected in verify.TARGETS.items():
            with self.subTest(case=key):
                pins, case, source = verify.check_inputs(key)
                work = self.root / key
                evidence = work / "evidence"
                evidence.mkdir(parents=True)
                packages = work / "dependencies/packages"
                packages.mkdir(parents=True)
                run = SimpleNamespace(work=work, evidence=evidence)
                target, protected = verify.prepare_candidate(run, pins, case, source, packages, key)
                config = json.loads((target / "config.json").read_text())
                self.assertEqual(config["theorem_names"], [expected["theorem"]])
                self.assertEqual(config["solution_module"], expected["module"])
                self.assertEqual(config["permitted_axioms"], verify.AXIOMS)
                self.assertIs(config["enable_nanoda"], True)
                self.assertEqual((target / "Challenge.lean").read_bytes(), verify.challenge(key).read_bytes())
                for name, sha in case["files"].items():
                    if not name.endswith(".lean") or name == "lean/lakefile.lean":
                        continue
                    relative = "CertifiedBridge.lean" if name == verify.BRIDGE else name.removeprefix("lean/")
                    self.assertEqual(verify.digest(target / relative), sha, relative)
                    self.assertEqual(protected[relative], sha)
                self.assertEqual((target / ".lake/packages").resolve(), packages.resolve())
                self.assertEqual(set(p.name for p in (target / ".lake").iterdir()), {"packages"})
                lake = (target / "lakefile.lean").read_text(encoding="utf-8")
                for library in expected["libraries"]:
                    self.assertIn(f"lean_lib {library}\n", lake)
                verify.collect(SimpleNamespace(evidence=evidence, receipt={"retained_files": {}}, collect=Mock()))

    def test_log_bridge_is_hashed_and_must_not_collide_with_lean_source(self):
        bridge = self.source / verify.BRIDGE
        bridge.parent.mkdir(parents=True)
        bridge.write_bytes(b"-- frozen bridge\n")
        self.case["files"][verify.BRIDGE] = verify.digest(bridge)
        verify.validate_sources(self.source, self.case)
        bridge.write_bytes(b"-- changed bridge\n")
        with self.assertRaisesRegex(RuntimeError, "Frozen source mismatch"):
            verify.validate_sources(self.source, self.case)
        self.case["files"][verify.BRIDGE] = verify.digest(bridge)
        collision = self.source / "lean/CertifiedBridge.lean"
        collision.write_bytes(b"-- competing bridge\n")
        self.case["files"]["lean/CertifiedBridge.lean"] = verify.digest(collision)
        work = self.root / "work"
        work.mkdir()
        packages = work / "deps"
        packages.mkdir()
        with self.assertRaisesRegex(RuntimeError, "Duplicate candidate destination"):
            verify.prepare_candidate(SimpleNamespace(work=work), {"mathlib": "test-pin"},
                                     self.case, self.source, packages, "log")


if __name__ == "__main__":
    unittest.main()

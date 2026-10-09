"""Local preparation tests: no downloads, tool builds, or proof execution."""
import hashlib
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import verify


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        (self.source / "lean/RealNorm").mkdir(parents=True)
        contents = {"lean/RealNorm/FormalConjectures.lean": b"-- candidate bytes\n",
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
                    patch.object(verify.sys, "argv", ["verify.py", "--work-dir", str(work)]), \
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
                patch.object(verify.sys, "argv", ["verify.py", "--work-dir", str(link / "work")]), \
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
        path = self.source / "lean/RealNorm/FormalConjectures.lean"
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
        self.assertNotIn("lean_lib RealNorm", config)

    def test_candidate_is_byte_identical_and_has_no_prebuilt_proof(self):
        work = self.root / "work"
        evidence = work / "evidence"
        evidence.mkdir(parents=True)
        packages = work / "dependencies/packages"
        packages.mkdir(parents=True)
        run = SimpleNamespace(work=work, evidence=evidence)
        try:
            target, protected = verify.prepare_candidate(run, {"mathlib": "test-pin"},
                                                        self.case, self.source, packages)
        except OSError as error:
            self.skipTest(f"Symlink creation unavailable: {error}")
        self.assertEqual((target / "RealNorm/FormalConjectures.lean").read_bytes(),
                         (self.source / "lean/RealNorm/FormalConjectures.lean").read_bytes())
        self.assertEqual(set(p.name for p in (target / ".lake").iterdir()), {"packages"})
        self.assertEqual((target / ".lake/packages").resolve(), packages.resolve())
        config = json.loads((target / "config.json").read_text())
        self.assertEqual(config["theorem_names"], [verify.THEOREM])
        self.assertEqual(config["solution_module"], verify.MODULE)
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

    def test_existing_pins_and_exact_case_are_still_valid(self):
        pins, case, _ = verify.check_inputs()
        self.assertEqual(case["theorem"], verify.THEOREM)
        self.assertEqual(pins["lean_version"], "4.34.1")


if __name__ == "__main__":
    unittest.main()

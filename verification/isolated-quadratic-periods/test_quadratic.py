"""Exercise new hosted-case boundaries without compiling or rechecking old proofs."""
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import quadratic as q


class HostedFamilyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.config = {"challenge_module": "Challenge", "solution_module": "Solution",
                       "theorem_names": list(q.TARGETS), "permitted_axioms": q.AXIOMS, "enable_nanoda": True}

    def test_config_requires_all_six_targets_and_both_kernel_policy(self):
        q.check_configuration(self.config)
        alternatives = [{"theorem_names": list(q.TARGETS[:-1])},
                        {"theorem_names": [*q.TARGETS, "unreviewed"]},
                        {"enable_nanoda": False}, {"permitted_axioms": [*q.AXIOMS, "sorryAx"]},
                        {"challenge_module": "Solution"}, {"solution_module": "Other"},
                        {"allow_sorry": True}]
        for change in alternatives:
            with self.subTest(change=change), self.assertRaises(RuntimeError):
                q.check_configuration({**self.config, **change})

    def test_manifest_selects_source_modules_without_inventing_library_roots(self):
        sources = {name: "sha" for name in ("OAI/Nested/Proof.lean", "Solution.lean", "Audit.lean",
                                              "Challenge.lean", "lakefile.lean", "lean-toolchain")}
        self.assertEqual(q.proof_modules(sources), ["Audit", "OAI.Nested.Proof", "Solution"])
        self.assertNotIn("OAI", q.proof_modules(sources))

    def prepare_fixture(self):
        package = self.root / "package"
        source = package / "lean"
        (source / "OAI").mkdir(parents=True)
        values = {"lean-toolchain": "leanprover/lean4:v4.34.1\n", "lake-manifest.json": '{"packages": []}\n',
                  "lakefile.lean": "-- untrusted config must not execute\n", "Challenge.lean": "theorem expected : True := by sorry\n",
                  "Solution.lean": "import OAI.Proof\n", "OAI/Proof.lean": "theorem proven : True := True.intro\n",
                  "Audit.lean": "import Solution\n", "comparison.json": json.dumps(self.config)}
        for name, value in values.items():
            (source / name).write_text(value, encoding="utf-8")
        sources = {name: q.digest(source / name) for name in values}
        (source / "source-manifest.json").write_text(json.dumps([{"path": n, "sha256": sha} for n, sha in sources.items()]))
        work = self.root / "work"
        evidence = work / "evidence"
        evidence.mkdir(parents=True)
        deps = work / "dependencies/packages"
        deps.mkdir(parents=True)
        run = SimpleNamespace(work=work, evidence=evidence, receipt={}, flush=Mock())
        return package, source, sources, deps, run

    def test_preparation_copies_bytes_and_starts_without_compiled_candidate(self):
        package, source, sources, deps, run = self.prepare_fixture()
        with patch.object(q, "PACKAGE", package), patch.object(q, "SOURCE", source):
            candidate, protected = q.prepare_candidate(run, {"mathlib": "pinned"}, sources, deps)
        self.assertEqual((candidate / "config.json").read_bytes(), (source / "comparison.json").read_bytes())
        self.assertEqual(set(p.name for p in (candidate / ".lake").iterdir()), {"packages"})
        self.assertEqual((candidate / ".lake/packages").resolve(), deps.resolve())
        self.assertNotIn("untrusted config", (candidate / "lakefile.lean").read_text())
        for name in ("Solution.lean", "Challenge.lean", "OAI/Proof.lean", "Audit.lean"):
            self.assertEqual(q.digest(candidate / name), sources[name])
            self.assertEqual(protected[name], sources[name])
        self.assertEqual(run.receipt["candidate"]["initial_compiled_modules"], 0)
        self.assertEqual(run.receipt["candidate"]["targets"], list(q.TARGETS))

    def test_dependencies_inside_writable_candidate_are_rejected(self):
        package, source, sources, _, run = self.prepare_fixture()
        wrong = run.work / "quadratic-periods/.lake/dependencies"
        with patch.object(q, "PACKAGE", package), patch.object(q, "SOURCE", source), \
                self.assertRaisesRegex(RuntimeError, "outside candidate writable"):
            q.prepare_candidate(run, {"mathlib": "pinned"}, sources, wrong)

    def fake_run(self):
        return SimpleNamespace(work=self.root, evidence=self.root, lean=Path("/lean"), comparator=Path("/comparator"),
                               env={name: "/tools/" + name for name in
                                    ("PATH", "HOME", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")},
                               receipt={}, flush=Mock(), command=Mock())

    def test_all_candidate_loading_commands_keep_the_protected_boundary(self):
        run = self.fake_run()
        candidate = Path("/candidate")
        compare = q.comparison_command(run, candidate)
        build = q.build_command(run, candidate, ["build", "OAI.Nested.Proof", "Solution"], q.SWEEP_SECONDS)
        for command in (compare, build):
            for required in ("--user", "--wait", "--pipe", "--collect", "--property=RestrictAddressFamilies=~AF_UNIX",
                             "--property=MemoryMax=12G", "--property=CPUQuota=400%"):
                self.assertIn(required, command)
        self.assertIn("--property=RuntimeMaxSec=14400", compare)
        self.assertIn("--property=RuntimeMaxSec=3600", build)
        self.assertEqual(build[build.index("--rwx") + 1], "/candidate/.lake")
        executable_roots = [build[i + 1] for i, item in enumerate(build) if item == "--rox"]
        self.assertEqual(executable_roots, ["/lean", "/usr"])
        self.assertEqual(build[-4:], ["/lean/bin/lake", "build", "OAI.Nested.Proof", "Solution"])

    def test_missing_kernel_or_target_diagnostics_stop_before_supplementary_build(self):
        good = "Building Solution\n" + "\n".join(q.TARGETS) + "\nYour solution is okay!\nLean default kernel accepts the solution\nnanoda kernel accepts the solution"
        outputs = [good.replace("Lean default kernel accepts the solution", ""), good.replace(q.TARGETS[-1], "")]
        for output in outputs:
            run = self.fake_run()
            run.command.return_value = (0, output)
            with self.subTest(output=output), patch.object(q, "check_capacity"), self.assertRaises(RuntimeError):
                run.receipt["resources"] = {}
                q.check_proof(run, self.root / "candidate", {})
            self.assertEqual(run.command.call_count, 1)

    def test_missing_compiled_module_cannot_count_as_complete(self):
        run = self.fake_run()
        run.receipt = {"resources": {}, "checks": {}}
        good = "Building Solution\n" + "\n".join(q.TARGETS) + "\nYour solution is okay!\nLean default kernel accepts the solution\nnanoda kernel accepts the solution"
        run.command.return_value = (0, good)
        with patch.object(q, "check_capacity"), self.assertRaisesRegex(RuntimeError, "regular file"):
            q.check_proof(run, self.root / "candidate", {"Solution.lean": "source-sha"})
        self.assertNotIn("all_packaged_modules_built", run.receipt["checks"])

    def test_incomplete_retention_is_not_accepted(self):
        run = self.fake_run()
        run.collect = Mock()
        run.receipt["retained_files"] = {}
        with self.assertRaisesRegex(RuntimeError, "Required evidence missing"):
            q.collect(run, required=True)

    def test_input_failure_stops_before_tool_setup_and_leaves_failed_receipt(self):
        work = self.root / "hosted"
        with patch.dict(q.os.environ, {"RUNNER_TEMP": str(self.root)}), \
                patch.object(q.sys, "argv", ["quadratic.py", "--work-dir", str(work)]), \
                patch.object(q, "check_inputs", side_effect=RuntimeError("changed source")), \
                patch.object(q.Preflight, "setup") as setup, patch.object(q.sys, "stderr", io.StringIO()):
            self.assertEqual(q.main(), 1)
        setup.assert_not_called()
        self.assertEqual(json.loads((work / "evidence/receipt.json").read_text())["status"], "failed")


if __name__ == "__main__":
    unittest.main()

import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("pi_verifier", Path(__file__).with_name("verify.py"))
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


class PreparationTests(unittest.TestCase):
    def test_stage_only_frozen_source_and_trusted_configuration(self):
        _, frozen = verify.check_inputs()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "candidate"
            protected = verify.stage(path, frozen)
            self.assertEqual(len(list((path / "PiTwoCaseBridge").glob("*.lean"))), 27)
            self.assertNotIn(".lake", {p.name for p in path.iterdir()})
            self.assertFalse((path / "build-overlay.sh").exists())
            lock = verify.read(path / "lake-manifest.json")
            trusted, *inherited = lock["packages"]
            self.assertEqual(trusted["dir"], "../trusted")
            self.assertTrue(all(dep["inherited"] for dep in inherited))
            self.assertEqual(protected["Challenge.lean"]["sha256"], frozen["spec"]["Challenge.lean"])
            self.assertEqual(verify.read(path / "config.json")["theorem_names"], verify.TARGETS)

    def test_modified_freeze_fails_closed(self):
        frozen = verify.inventory()
        frozen["spec"]["Challenge.lean"] = "0" * 64
        with patch.object(verify, "inventory", return_value=frozen):
            with self.assertRaisesRegex(RuntimeError, "Frozen candidate or trusted specification changed"):
                verify.check_inputs()

    def test_staging_rejects_a_stale_specification(self):
        _, frozen = verify.check_inputs()
        frozen["spec"]["Challenge.lean"] = "0" * 64
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(RuntimeError, "Staged specification changed"):
                verify.stage(Path(tmp) / "candidate", frozen)


if __name__ == "__main__":
    unittest.main()

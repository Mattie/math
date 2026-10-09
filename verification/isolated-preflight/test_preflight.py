"""Local fail-closed tests; never download tools, build Lean, or run a sandbox."""
import errno
import unittest
from pathlib import Path

from preflight import ACCEPTANCE, LABELS, check_boundary, check_comparator, systemd_command


class PreflightTests(unittest.TestCase):
    def test_boundary_requires_every_operation(self):
        result = {name: errno.EACCES for name in LABELS}
        result.update(allowed=0, unix_stream=errno.EAFNOSUPPORT, unix_dgram=errno.EAFNOSUPPORT)
        check_boundary(result, isolated=True)
        for name in LABELS:
            missing = dict(result)
            del missing[name]
            with self.subTest(missing=name), self.assertRaises(RuntimeError):
                check_boundary(missing, isolated=True)

    def test_disabled_isolation_and_unrelated_errors_fail(self):
        for failure in (0, errno.ENOENT, errno.EIO):
            with self.subTest(errno=failure), self.assertRaises(RuntimeError):
                check_boundary({name: failure for name in LABELS}, isolated=True)

    def test_each_protected_operation_must_be_denied(self):
        result = {name: errno.EACCES for name in LABELS}
        result["allowed"] = 0
        for name in LABELS - {"allowed"}:
            for failure in (0, errno.ENOENT):
                wrong = dict(result, **{name: failure})
                with self.subTest(name=name, errno=failure), self.assertRaises(RuntimeError):
                    check_boundary(wrong, isolated=True)

    def test_baseline_must_actually_be_unrestricted(self):
        check_boundary(dict.fromkeys(LABELS, 0), isolated=False)
        with self.assertRaises(RuntimeError):
            check_boundary(dict.fromkeys(LABELS, errno.EPERM), isolated=False)

    def test_positive_requires_both_kernels(self):
        check_comparator("valid", 0, "\n".join(ACCEPTANCE))
        for omitted in ACCEPTANCE:
            with self.subTest(omitted=omitted), self.assertRaises(RuntimeError):
                check_comparator("valid", 0, "\n".join(x for x in ACCEPTANCE if x != omitted))
        with self.assertRaises(RuntimeError):
            check_comparator("valid", 1, "\n".join(ACCEPTANCE))

    def test_rejection_is_not_an_arbitrary_failure(self):
        for case, diagnostic in (("mismatch", "theorem statement do not match"),
                                 ("axiom", "Illegal axiom detected")):
            check_comparator(case, 1, diagnostic)
            for code, output in ((0, diagnostic), (-9, diagnostic), (1, "missing exporter"),
                                 (1, diagnostic + "\nYour solution is okay!")):
                with self.subTest(case=case, code=code, output=output), self.assertRaises(RuntimeError):
                    check_comparator(case, code, output)

    def test_invocation_keeps_systemd_guard_and_explicit_tools(self):
        env = {key: "/test/" + key for key in
               ("PATH", "HOME", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")}
        command = systemd_command(Path("/project"), Path("/lean"), Path("/tools/comparator"), env)
        self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", command)
        self.assertIn("--user", command)
        self.assertIn("--wait", command)
        self.assertEqual(command[-4:], [str(Path("/lean") / "bin/lake"), "env",
                                      str(Path("/tools/comparator")), "config.json"])
        for key, value in env.items():
            self.assertIn(f"--setenv={key}={value}", command)


if __name__ == "__main__":
    unittest.main()

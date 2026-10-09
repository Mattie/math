#!/usr/bin/env python3
"""Exercise the hosted-runner capacity gate with mocked df/sudo and no deletion."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('prepare-independent-runner.sh')
GIB = 1024 ** 3


class CapacityTests(unittest.TestCase):
    def run_gate(self, before, after, hosted=True):
        """Run the real gate with a fake filesystem measurement and cleanup command."""
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            df = root / 'df'
            df.write_text("#!/bin/bash\nvalue=$FAKE_BEFORE\nif [[ -f $FAKE_CLEANUP ]]; then value=$FAKE_AFTER; fi\nprintf 'Filesystem 1B-blocks Used Available Use%% Mounted\n/dev/fake 999999999999 0 %s 0%% /\n' \"$value\"\n")
            sudo = root / 'sudo'
            sudo.write_text("#!/bin/bash\nprintf '%s\\n' \"$*\" > \"$FAKE_CLEANUP\"\n")
            df.chmod(0o755)
            sudo.chmod(0o755)
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ['PATH'],
                GITHUB_ACTIONS='true', RUNNER_ENVIRONMENT='github-hosted' if hosted else 'self-hosted',
                RUNNER_OS='Linux', ImageOS='ubuntu24', RUNNER_TEMP=str(root),
                FAKE_BEFORE=str(before), FAKE_AFTER=str(after), FAKE_CLEANUP=str(root / 'cleanup'))
            result = subprocess.run(['bash', str(SCRIPT)], env=env, text=True, capture_output=True)
            cleanup = (root / 'cleanup').read_text().strip() if (root / 'cleanup').exists() else None
            return result, cleanup

    def test_sufficient_space_skips_cleanup(self):
        result, cleanup = self.run_gate(35 * GIB, 35 * GIB)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIsNone(cleanup)

    def test_reclaims_only_named_unused_sdks(self):
        result, cleanup = self.run_gate(14 * GIB, 40 * GIB)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(cleanup, 'rm -rf -- /usr/local/lib/android /usr/share/dotnet /opt/ghc /opt/hostedtoolcache')

    def test_insufficient_space_fails_before_build(self):
        result, cleanup = self.run_gate(14 * GIB, 34 * GIB)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('needs at least 35 GiB', result.stderr)

    def test_refuses_non_disposable_host(self):
        result, cleanup = self.run_gate(14 * GIB, 40 * GIB, hosted=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIsNone(cleanup)
        self.assertIn('Refusing SDK cleanup', result.stderr)

    def test_unknown_capacity_is_not_accepted(self):
        result, cleanup = self.run_gate('unknown', 40 * GIB)
        self.assertNotEqual(result.returncode, 0)
        self.assertIsNone(cleanup)
        self.assertIn('Could not determine', result.stderr)


if __name__ == '__main__':
    unittest.main()

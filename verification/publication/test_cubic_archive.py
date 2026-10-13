"""Check rejection of damaged or incomplete retained hosted evidence."""

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'preprints/The-irrationality-exponent-of-log-2-plus-cuberoot2-is-at-most-6-October-12-2026'
spec = importlib.util.spec_from_file_location('cubic_publication', PAPER / 'scripts/check-publication.py')
publication = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publication)


def identity(data):
    """Describe the exact bytes used in a synthetic evidence member."""
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'evidence.zip'
        self.members = {'receipt.json': b'{}', 'logs/check.log': b'accepted\n'}
        self.index = json.dumps({'files': {name: identity(data) for name, data in self.members.items()}}).encode()

    def write_archive(self, members):
        """Write transport bytes while keeping the original evidence index fixed."""
        with zipfile.ZipFile(self.path, 'w') as archive:
            archive.writestr('evidence-index.json', self.index)
            for name, data in members.items():
                archive.writestr(name, data)
        info = identity(self.path.read_bytes())
        return {'artifact': {'size_in_bytes': info['bytes'], 'digest': 'sha256:' + info['sha256']},
                'evidence_index_sha256': identity(self.index)['sha256'],
                'receipt_sha256': identity(b'{}')['sha256']}

    def test_published_archive_matches_original_audit(self):
        verifier = ROOT / 'verification/isolated-affine-cubic'
        audit = json.loads((verifier / 'results/hosted-audit-2026-10-13.json').read_text())
        self.assertEqual(publication.check_archive(verifier / 'evidence/hosted-2026-10-13.zip', audit), 101)

    def test_valid_fixture_and_changed_download(self):
        audit = self.write_archive(self.members)
        self.assertEqual(publication.check_archive(self.path, audit), 2)
        with self.path.open('ab') as stream:
            stream.write(b'changed')
        with self.assertRaisesRegex(ValueError, 'audited download'):
            publication.check_archive(self.path, audit)

    def test_unindexed_member_is_rejected(self):
        audit = self.write_archive(self.members | {'unexpected.txt': b'extra'})
        with self.assertRaisesRegex(ValueError, 'member inventory'):
            publication.check_archive(self.path, audit)

    def test_missing_member_is_rejected(self):
        audit = self.write_archive({'receipt.json': b'{}'})
        with self.assertRaisesRegex(ValueError, 'member inventory'):
            publication.check_archive(self.path, audit)

    def test_changed_member_is_rejected_even_with_matching_transport_hash(self):
        audit = self.write_archive(self.members | {'logs/check.log': b'rejected\n'})
        with self.assertRaisesRegex(ValueError, 'member changed'):
            publication.check_archive(self.path, audit)


if __name__ == '__main__':
    unittest.main()

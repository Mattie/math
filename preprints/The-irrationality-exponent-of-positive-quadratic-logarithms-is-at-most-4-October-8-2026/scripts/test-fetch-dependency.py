"""Exercise dependency extraction and preservation of existing files without network access."""
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch
import io
import json
import runpy
import tempfile
import unittest
import zipfile

SCRIPT = Path(__file__).with_name('fetch-dependency.py')
PIN = json.loads((SCRIPT.parent.parent / 'evidence/dependency-pin.json').read_text())


class FetchTests(unittest.TestCase):
    def run_fetch(self, target, entries=(), network_allowed=True):
        """Run the actual CLI with a synthetic archive and capture network calls."""
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as archive:
            for name, value in entries:
                archive.writestr('snapshot/' + PIN['project'] + '/' + name, value)
        response = io.BytesIO(stream.getvalue())
        with patch('sys.argv', [str(SCRIPT), str(target)]), \
                patch('urllib.request.urlopen', return_value=response,
                      side_effect=None if network_allowed else AssertionError('Unexpected network call')) as fetch, \
                redirect_stdout(io.StringIO()):
            runpy.run_path(str(SCRIPT), run_name='__main__')
        return fetch

    def test_fresh_extraction_and_existing_project_reuse(self):
        with tempfile.TemporaryDirectory() as folder:
            target = Path(folder) / 'project'
            self.run_fetch(target, [('lakefile.lean', 'config'), ('nested/proof.lean', 'proof')])
            self.assertEqual((target / 'nested/proof.lean').read_text(), 'proof')
            fetch = self.run_fetch(target, [('lakefile.lean', 'replacement')])
            fetch.assert_not_called()
            self.assertEqual((target / 'lakefile.lean').read_text(), 'config')

    def test_partial_target_is_unchanged_without_network(self):
        with tempfile.TemporaryDirectory() as folder:
            target = Path(folder)
            existing = target / 'proof.lean'
            existing.write_bytes(b'original')
            with self.assertRaisesRegex(SystemExit, 'must be empty'):
                self.run_fetch(target, [('proof.lean', 'replacement')], network_allowed=False)
            self.assertEqual(existing.read_bytes(), b'original')
            self.assertEqual(list(target.iterdir()), [existing])

    def test_empty_target_is_allowed(self):
        with tempfile.TemporaryDirectory() as folder:
            self.run_fetch(Path(folder), [('lakefile.lean', 'config')])
            self.assertEqual((Path(folder) / 'lakefile.lean').read_text(), 'config')

    def test_colliding_archive_entries_do_not_overwrite(self):
        with tempfile.TemporaryDirectory() as folder:
            target = Path(folder)
            with self.assertRaises(FileExistsError):
                self.run_fetch(target, [('proof.lean', 'original'), ('./proof.lean', 'replacement')])
            self.assertEqual((target / 'proof.lean').read_text(), 'original')


if __name__ == '__main__':
    unittest.main()

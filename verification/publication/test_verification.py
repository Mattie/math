"""Regression checks for publication verification, without Lean or network access."""
from pathlib import Path
import importlib.util
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
PACKAGES = sorted((ROOT/'preprints').iterdir())

def load(path):
    spec=importlib.util.spec_from_file_location(path.stem,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

audit = load(PACKAGES[0]/'scripts/check-axioms.py')
upstream = load(Path(__file__).with_name('check-upstream.py'))
assets = load(Path(__file__).with_name('check-release-assets.py'))

class VerificationTests(unittest.TestCase):
    def test_helpers_identical(self):
        contents=[(p/'scripts/check-axioms.py').read_bytes() for p in PACKAGES]
        self.assertEqual(len(contents),6)
        self.assertEqual(len(set(contents)),1)

    def test_permitted_subsets_and_multiline(self):
        for text in ["'target' depends on axioms: [propext,\n Classical.choice, Quot.sound]",
                     "'target' depends on axioms: []", "'target' does not depend on any axioms"]:
            self.assertEqual(audit.check(text,{'target'}),1)

    def test_forbidden_axioms(self):
        for name in ['sorryAx','Test.extra','Lean.ofReduceBool']:
            with self.assertRaisesRegex(ValueError,'Unpermitted'):
                audit.check(f"'target' depends on axioms: [{name}]",{'target'})

    def test_missing_and_malformed_reports(self):
        for text in ['',"'other' depends on axioms: []", "'target' depends on axioms: [propext",
                     "'target' depends on axioms: [propext,]", "'target' depends on axioms: [propext] trailing depends on axioms: broken"]:
            with self.assertRaises(ValueError):
                audit.check(text,{'target'})
        with self.assertRaises(ValueError): audit.check('',set())

    def test_inventory_and_content_changes(self):
        for actual in [{},{'a':'one','b':'two'},{'a':'changed'}]:
            with self.assertRaises(ValueError):upstream.compare({'a':'one'},actual)
        upstream.compare({'a':'one'},{'a':'one'})

    def test_audit_cli_fails_closed(self):
        import sys
        with tempfile.TemporaryDirectory() as temporary:
            p=Path(temporary)/'audit.log';p.write_text("'target' depends on axioms: [sorryAx]")
            result=subprocess.run([sys.executable,str(PACKAGES[0]/'scripts/check-axioms.py'),str(p),'--expect','target'],capture_output=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn(b'sorryAx',result.stderr)

    def test_export_identity_checks(self):
        import gzip, hashlib
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);p=root/'proof.gz';raw=b'known export bytes'
            data=gzip.compress(raw,mtime=0);p.write_bytes(data)
            row={'file':p.name,'compressed_bytes':len(data),'compressed_sha256':hashlib.sha256(data).hexdigest(),
                 'uncompressed_bytes':len(raw),'uncompressed_sha256':hashlib.sha256(raw).hexdigest()}
            assets.verify(root,[row])
            with self.assertRaises(ValueError):assets.verify(root,[row|{'uncompressed_sha256':'bad'}])
            p.write_bytes(data+b'changed')
            with self.assertRaises(ValueError):assets.verify(root,[row])

    def test_generated_markdown_is_ignored(self):
        import sys
        # These are disposable generated artifacts; no tracked source is touched.
        for package in PACKAGES:
            generated=package/'lean/.lake/publication-regression'
            generated.mkdir(parents=True,exist_ok=True)
            document=generated/'README.md'
            self.assertFalse(document.exists())
            try:
                document.write_text('[dependency link](missing-lean-toolchain)')
                result=subprocess.run([sys.executable,str(package/'scripts/check-publication.py')],capture_output=True,text=True)
                self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            finally:
                document.unlink();generated.rmdir()

if __name__ == '__main__':
    unittest.main()

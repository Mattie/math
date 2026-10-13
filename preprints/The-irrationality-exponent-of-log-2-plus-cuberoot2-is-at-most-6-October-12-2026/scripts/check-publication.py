#!/usr/bin/env python3
"""Check publication bytes, links, frozen proof inputs, and retained evidence."""

import sys

if __name__ == '__main__' and not sys.flags.isolated:
    raise SystemExit('Run with Python isolated mode: python3 -I scripts/check-publication.py')

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile

PAPER = Path(__file__).resolve().parents[1]
REPO = PAPER.parents[1]
VERIFIER = REPO / 'verification/isolated-affine-cubic'


def digest(data):
    """Return the SHA-256 identity of an in-memory file."""
    return hashlib.sha256(data).hexdigest()


def check_archive(path, audit):
    """Match the original hosted archive and every indexed member without extracting."""
    data = path.read_bytes()
    if (len(data) != audit['artifact']['size_in_bytes'] or
            'sha256:' + digest(data) != audit['artifact']['digest']):
        raise ValueError('Hosted archive differs from the audited download')
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        index_bytes = archive.read('evidence-index.json')
        if digest(index_bytes) != audit['evidence_index_sha256']:
            raise ValueError('Hosted evidence index changed')
        index = json.loads(index_bytes)['files']
        if len(names) != len(set(names)) or set(names) != set(index) | {'evidence-index.json'}:
            raise ValueError('Hosted archive member inventory changed')
        for name, expected in index.items():
            relative = PurePosixPath(name)
            if relative.is_absolute() or '..' in relative.parts or '\\' in name:
                raise ValueError('Invalid archive member path: ' + name)
            member = archive.read(name)
            if len(member) != expected['bytes'] or digest(member) != expected['sha256']:
                raise ValueError('Hosted evidence member changed: ' + name)
        if digest(archive.read('receipt.json')) != audit['receipt_sha256']:
            raise ValueError('Hosted receipt changed')
    return len(index)


def main():
    """Validate the public package without a PDF rebuild or new proof execution."""
    manifest = json.loads((PAPER / 'package-manifest.json').read_text(encoding='utf-8'))
    files = manifest['files']
    prefix = PAPER.relative_to(REPO).as_posix()
    required = {f'{prefix}/{name}' for name in (
        'paper.pdf', 'build/main.tex', 'build/receipt.json', 'theorem-map.json',
        'README.md', 'VERIFY.md', 'LICENSES.md', 'CITATION.cff',
        'scripts/build.py', 'scripts/check-publication.py')}
    if not required <= files.keys():
        raise ValueError('Publication manifest omits a required paper file')
    for name, expected in files.items():
        relative = PurePosixPath(name)
        if relative.is_absolute() or '..' in relative.parts or '\\' in name:
            raise ValueError('Invalid publication path: ' + name)
        path = REPO / name
        if path.is_symlink() or not path.resolve().is_relative_to(REPO.resolve()):
            raise ValueError('Publication path escapes its checkout: ' + name)
        data = path.read_bytes()
        if len(data) != expected['bytes'] or digest(data) != expected['sha256']:
            raise ValueError('Publication file changed: ' + name)
        if path.suffix == '.md':
            for target in re.findall(r'\]\(([^\s)]+)\)', data.decode('utf-8')):
                if '://' in target or target.startswith('#'):
                    continue
                if not (path.parent / target.split('#', 1)[0]).exists():
                    raise ValueError(f'Missing local link in {name}: {target}')
    receipt = json.loads((PAPER / 'build/receipt.json').read_text(encoding='utf-8'))
    if (digest((PAPER / 'build/main.tex').read_bytes()) != receipt['source_sha256'] or
            digest((PAPER / 'paper.pdf').read_bytes()) != receipt['pdf_sha256']):
        raise ValueError('Manuscript bytes differ from the build receipt')
    if not (PAPER / 'paper.pdf').read_bytes().startswith(b'%PDF-'):
        raise ValueError('Invalid PDF header')
    audit = json.loads((VERIFIER / 'results/hosted-audit-2026-10-13.json').read_text())
    count = check_archive(VERIFIER / 'evidence/hosted-2026-10-13.zip', audit)
    subprocess.run([sys.executable, '-I', '-B', str(VERIFIER / 'verify.py'), '--check'], check=True)
    print(f'Publication integrity passed: {len(files)} files and {count} indexed evidence members.')


if __name__ == '__main__':
    main()

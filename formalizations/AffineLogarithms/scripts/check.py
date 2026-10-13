#!/usr/bin/env python3
"""Check packaged files and, when requested, the exact retained proof export."""
import sys

# Do not let unlisted siblings such as scripts/json.py shadow the standard library.
if __name__ == '__main__' and not sys.flags.isolated:
    raise SystemExit('Run this checker with Python isolated mode: python3 -I scripts/check.py')

from pathlib import Path, PurePosixPath
import argparse
import gzip
import hashlib
import json
import os

ROOT = Path(__file__).resolve().parents[1]
RUNTIME_DIRS = {'.lake', '.work', 'release-assets', 'replay-reader/.lake',
                'scripts/__pycache__'}


def digest(path):
    """Return the SHA-256 of a file without loading it into memory."""
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def check_sources():
    """Require every frozen source and specification file to match its digest."""
    manifest = json.loads((ROOT / 'evidence/source-sha256.json').read_text())
    for name, expected in manifest.items():
        if digest(ROOT / name) != expected:
            raise RuntimeError('Frozen source changed: ' + name)
    print(f'All {len(manifest)} frozen proof/specification files match.')


def check_package():
    """Require the complete distributed tree, apart from named runtime outputs."""
    manifest = json.loads((ROOT / 'manifest-sha256.json').read_text())
    for name in manifest:
        relative = PurePosixPath(name)
        if relative.is_absolute() or '..' in relative.parts or '\\' in name:
            raise RuntimeError('Invalid package inventory path: ' + name)
    actual = set()
    for directory, dirs, files in os.walk(ROOT):
        parent = Path(directory)
        for name in dirs + files:
            if (parent / name).is_symlink():
                # Lake's runtime tree may contain dependency symlinks; it is pruned below.
                if (parent / name).relative_to(ROOT).as_posix() not in RUNTIME_DIRS:
                    raise RuntimeError('Symlink in package inventory: ' + str(parent / name))
        dirs[:] = [name for name in dirs
                   if (parent / name).relative_to(ROOT).as_posix() not in RUNTIME_DIRS]
        actual.update((parent / name).relative_to(ROOT).as_posix() for name in files)
    expected = set(manifest) | {'manifest-sha256.json'}
    if actual != expected:
        raise RuntimeError('Package inventory mismatch; unlisted: ' + ', '.join(sorted(actual - expected))
                           + '; missing: ' + ', '.join(sorted(expected - actual)))
    for name, expected_hash in manifest.items():
        if digest(ROOT / name) != expected_hash:
            raise RuntimeError('Package file changed: ' + name)
    print(f'All {len(manifest)} package inventory files match.')


def check_export(path):
    """Hash the uncompressed export, accepting either NDJSON or gzip input."""
    expected = json.loads((ROOT / 'evidence/checker-receipt.json').read_text())['export']
    hasher, size = hashlib.sha256(), 0
    opener = gzip.open if path.suffix == '.gz' else open
    with opener(path, 'rb') as stream:
        while block := stream.read(1024 * 1024):
            hasher.update(block)
            size += len(block)
    if size != expected['bytes'] or hasher.hexdigest() != expected['sha256']:
        raise RuntimeError('Export differs from the checked artifact.')
    print(f'Exact checked export matches: {size} uncompressed bytes.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--export', type=Path, help='Also verify a retained NDJSON or gzip export.')
    args = parser.parse_args()
    check_package()
    check_sources()
    if args.export:
        check_export(args.export)


if __name__ == '__main__':
    main()

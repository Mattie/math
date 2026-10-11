#!/usr/bin/env python3
"""Check packaged files and, when requested, the exact retained proof export."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


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
    check_sources()
    manifest = json.loads((ROOT / 'manifest-sha256.json').read_text())
    for name, expected in manifest.items():
        if digest(ROOT / name) != expected:
            raise RuntimeError('Package file changed: ' + name)
    print(f'All {len(manifest)} package inventory files match.')
    if args.export:
        check_export(args.export)


if __name__ == '__main__':
    main()

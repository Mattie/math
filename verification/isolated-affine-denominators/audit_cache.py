"""Identify reusable inherited source/cache bytes without modifying the old project.

Matching source hashes does not authenticate compiled objects. Their own hashes
identify exactly what was reused; exported-body replay supplies separate evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    expected = json.loads(args.manifest.read_text())
    actual = {p.relative_to(args.project).as_posix()
              for library in ('OAI', 'Logarithm', 'AlgebraicLog', 'PairedAffine')
              for p in (args.project / library).rglob('*.lean')}
    actual.add('StandardBridge.lean')
    if actual != set(expected):
        raise RuntimeError('Selected inherited source inventory has missing or extra files')
    mismatch = [name for name, digest in expected.items()
                if not (args.project / name).is_file() or sha(args.project / name) != digest]
    if mismatch:
        raise RuntimeError('Inherited source mismatch: ' + repr(mismatch))
    cache = {}
    for area in ('lib/lean', 'ir'):
        for library in ('OAI', 'Logarithm', 'AlgebraicLog', 'PairedAffine'):
            directory = args.project / '.lake/build' / area / library
            if not directory.is_dir():
                raise RuntimeError('Missing inherited compiled library: ' + str(directory))
            for path in directory.rglob('*'):
                if path.is_file():
                    cache[path.relative_to(args.project).as_posix()] = sha(path)
    result = {'status': 'passed', 'scope': 'Inherited source equality and compiled-cache identity only',
              'time_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
              'project': str(args.project), 'source_manifest_sha256': sha(args.manifest),
              'sources': expected, 'cache': cache,
              'packages_resolved': str((args.project / '.lake/packages').resolve())}
    with args.output.open('x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': 'passed', 'sources': len(expected), 'compiled_files': len(cache),
                      'receipt_sha256': sha(args.output)}))


if __name__ == '__main__':
    main()

"""Hash a completed local evidence directory without changing its original receipt."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    receipt = json.loads((root / 'receipt.json').read_text())
    if receipt['status'] not in ('passed', 'failed'):
        raise RuntimeError('Do not index a running evidence set')
    output = root / 'evidence-index.json'
    files = {}
    for path in sorted(root.rglob('*')):
        if path.is_symlink():
            raise RuntimeError('Evidence must contain regular files, not symbolic links')
        if path.is_file() and path != output:
            with path.open('rb') as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
            files[path.relative_to(root).as_posix()] = {'sha256': digest, 'bytes': path.stat().st_size}
    with output.open('x', encoding='utf-8') as stream:
        json.dump({'status': receipt['status'], 'scope': 'Completed local evidence file identity only',
                   'files': files}, stream, indent=2)
        stream.write('\n')
    print(f'Indexed {len(files)} evidence files.')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Verify downloaded transport archives against both recorded byte identities."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json

def verify(directory, assets):
    """Stream archives, rejecting changed compressed or uncompressed contents."""
    for asset in assets:
        name = asset['file']
        if Path(name).name != name:
            raise ValueError('Asset filename must not contain a directory.')
        path = directory/name
        with path.open('rb') as stream:
            compressed = hashlib.file_digest(stream,'sha256').hexdigest()
        if path.stat().st_size != asset['compressed_bytes'] or compressed != asset['compressed_sha256']:
            raise ValueError('Compressed asset identity mismatch: '+name)
        digest = hashlib.sha256(); size = 0
        with gzip.open(path,'rb') as stream:
            for block in iter(lambda:stream.read(1024*1024),b''):
                digest.update(block); size += len(block)
        if size != asset['uncompressed_bytes'] or digest.hexdigest() != asset['uncompressed_sha256']:
            raise ValueError('Uncompressed export identity mismatch: '+name)
        print('PASS:',name)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    args=parser.parse_args()
    inventory=json.loads(Path(__file__).with_name('release-assets.json').read_text())
    if len(inventory['assets']) != 6 or len({a['file'] for a in inventory['assets']}) != 6:
        raise ValueError('Expected six distinct release assets.')
    verify(args.directory,inventory['assets'])

if __name__ == '__main__':
    main()

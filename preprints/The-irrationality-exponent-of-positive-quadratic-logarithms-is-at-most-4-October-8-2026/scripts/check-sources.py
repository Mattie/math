#!/usr/bin/env python3
"""Reject any change to the reviewed proof files or the pinned dependency source."""
from pathlib import Path
import hashlib
import json
import sys

package = Path(__file__).resolve().parents[1]
dependency = Path(sys.argv[1])
metadata = json.loads((package / 'evidence/checker-metadata.json').read_text())
sets = [(package / 'lean', metadata['source_files']),
        (dependency, json.loads((package / 'evidence/dependency-source-sha256.json').read_text())),
        (dependency, json.loads((package / 'evidence/dependency-config-sha256.json').read_text()))]
for root, manifest in sets:
    for name, expected in manifest.items():
        with (root / name).open('rb') as stream:
            actual = hashlib.file_digest(stream, 'sha256').hexdigest()
        if actual != expected:
            raise SystemExit('Source digest mismatch: ' + name)
print('All reviewed proof, dependency, and configuration digests match.')

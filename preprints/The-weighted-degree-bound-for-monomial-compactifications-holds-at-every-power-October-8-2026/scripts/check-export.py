#!/usr/bin/env python3
"""Check the exact uncompressed selected proof export against the recorded run."""
from pathlib import Path
import hashlib
import json
import sys

package = Path(__file__).resolve().parents[1]
expected = json.loads((package / 'evidence/checker-metadata.json').read_text())
path = Path(sys.argv[1])
with path.open('rb') as stream:
    digest = hashlib.file_digest(stream, 'sha256').hexdigest()
if path.stat().st_size != expected['export_size_bytes'] or digest != expected['export_sha256']:
    raise SystemExit('Export identity differs from the recorded artifact; audit it as a new run.')
print('Selected export matches the recorded artifact.')

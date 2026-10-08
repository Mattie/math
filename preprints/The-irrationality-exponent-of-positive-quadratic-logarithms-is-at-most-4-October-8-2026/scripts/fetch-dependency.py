#!/usr/bin/env python3
"""Fetch only the pinned Lean dependency project into an ignored work directory.

The script prints the project path on stdout for use by verify.sh. Network and
extraction failures abort; no existing project files are overwritten.
"""
from pathlib import Path, PurePosixPath
import io
import json
import sys
import urllib.request
import zipfile

package = Path(__file__).resolve().parents[1]
pin = json.loads((package / 'evidence/dependency-pin.json').read_text())
target = Path(sys.argv[1]).resolve()
if not (target / 'lakefile.lean').exists():
    if target.exists() and (not target.is_dir() or any(target.iterdir())):
        raise SystemExit('Dependency target must be empty or an existing project; use a new directory.')
    url = pin['repository'] + '/archive/' + pin['commit'] + '.zip'
    with urllib.request.urlopen(url) as response:
        archive = zipfile.ZipFile(io.BytesIO(response.read()))
    suffix = '/' + pin['project'] + '/'
    members = [m for m in archive.infolist() if suffix in m.filename and not m.is_dir()]
    if not members:
        raise SystemExit('The pinned archive contains no dependency project.')
    target.mkdir(parents=True, exist_ok=True)
    for member in members:
        relative = PurePosixPath(member.filename.split(suffix, 1)[1])
        if relative.is_absolute() or '..' in relative.parts:
            raise SystemExit('Unexpected archive path.')
        output = target.joinpath(*relative.parts)
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open('xb') as destination:
            destination.write(archive.read(member))
print(target)

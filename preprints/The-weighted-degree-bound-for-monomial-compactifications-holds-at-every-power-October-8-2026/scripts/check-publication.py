#!/usr/bin/env python3
"""Check publication inputs, local links, proof identities, and accidental private text.

Run from any directory. Generated builds and the ignored proof-export transport
file are excluded from the source tree, and are described by separate receipts.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

package = Path(__file__).resolve().parents[1]
required = ['paper.pdf', 'README.md', 'VERIFY.md', 'CITATION.cff', 'LICENSE',
            'LICENSES.md', 'NOTICE', 'build/main.tex', 'build/manuscript.md',
            'evidence/preparation.json', 'evidence/release-assets.json',
            'evidence/checker-results.json', 'evidence/source-manifest.json']
failures = []
for name in required:
    if not (package / name).is_file():
        failures.append('Missing publication file: ' + name)

metadata = json.loads((package / 'evidence/checker-metadata.json').read_text())
for name, expected in metadata['source_files'].items():
    actual = hashlib.sha256((package / 'lean' / name).read_bytes()).hexdigest()
    if actual != expected:
        failures.append('Reviewed Lean source changed: ' + name)

manifest = json.loads((package / 'evidence/source-manifest.json').read_text())
for name, expected in manifest['sha256'].items():
    actual = hashlib.sha256((package / name).read_bytes()).hexdigest()
    if actual != expected:
        failures.append('Publication source changed: ' + name)

private = re.compile(r'(?i)([CD]:[/\\](?:Users|Dev|Temp)[/\\]|/mnt/[cd]/|/home/mattie/|'
                     r'codex-task-log-|'
                     r'<analysis>|<assistant>|api[_-]?key\s*=)')
for path in package.rglob('*'):
    relative = path.relative_to(package)
    if any(part in {'.verification', '.lake', '__pycache__'} for part in relative.parts) or not path.is_file():
        continue
    if relative.parts[0] == 'release-assets' and path.name != 'README.md':
        continue
    if path.suffix not in {'.md', '.tex', '.json', '.lean', '.py', '.sh', '.cff', '.toml', '.txt'}:
        continue
    # Generated TeX diagnostics are deliberately ignored by Git.
    text = path.read_text(encoding='utf-8')
    # The scanner itself contains the blocked patterns, so it is not its own subject.
    if path.resolve() != Path(__file__).resolve() and private.search(text):
        failures.append('Private or excluded text detected: ' + relative.as_posix())
    if path.suffix == '.md':
        for link in re.findall(r'\[[^\]]*\]\(([^)]+)\)', text):
            if re.match(r'^[a-z]+:', link) or link.startswith('#'):
                continue
            destination = (path.parent / link.split('#', 1)[0]).resolve()
            if not destination.exists():
                failures.append('Broken local link in ' + relative.as_posix() + ': ' + link)
if failures:
    print('\n'.join(failures), file=sys.stderr)
    raise SystemExit(1)
print('Publication inventory, source digests, local links, and text scan passed.')

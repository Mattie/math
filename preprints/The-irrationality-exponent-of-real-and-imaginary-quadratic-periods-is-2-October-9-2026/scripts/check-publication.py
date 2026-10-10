"""Validate the complete frozen source inventory, imports, links and public hygiene."""
from pathlib import Path
import hashlib
import json
import re
from urllib.parse import unquote

root = Path(__file__).resolve().parents[1]
lean = root / 'lean'
rows = json.loads((lean / 'source-manifest.json').read_text(encoding='utf-8'))
errors = []
expected = {r['path'] for r in rows}
if len(expected) != len(rows):
    errors.append('Duplicate source manifest paths')
expected_sums = ''.join(r['sha256'] + '  ' + r['path'] + '\n' for r in rows)
if (lean / 'sources.sha256').read_text(encoding='utf-8') != expected_sums:
    errors.append('SHA-256 list differs from source manifest')
actual = {p.relative_to(lean).as_posix() for p in lean.rglob('*')
          if p.is_file() and '.lake' not in p.parts and
          (p.suffix == '.lean' or p.name in {'lean-toolchain', 'lake-manifest.json', 'comparison.json'})}
if actual != expected:
    errors.append('Source/config inventory mismatch: ' + repr(sorted(actual ^ expected)))
for row in rows:
    file = lean / row['path']
    if not file.is_file() or file.stat().st_size != row['bytes'] or hashlib.sha256(file.read_bytes()).hexdigest() != row['sha256']:
        errors.append('Source identity failed: ' + row['path'])
for file in lean.rglob('*.lean'):
    if '.lake' in file.parts:
        continue
    text = file.read_text(encoding='utf-8')
    for line in text.splitlines():
        if line.startswith('import '):
            for module in line[7:].split():
                if module.split('.')[0] not in {'Mathlib','Lean','Lake','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','Plausible'} and not (lean / (module.replace('.', '/') + '.lean')).is_file():
                    errors.append('Missing local import: ' + module)
    if file.name != 'Challenge.lean' and re.search(r'\b(sorry|admit)\b', text):
        # Comments are audited separately; inherited comment vocabulary is not a proof hole.
        cleaned = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
        cleaned = re.sub(r'--[^\n]*', '', cleaned)
        if re.search(r'\b(sorry|admit)\b', cleaned):
            errors.append('Proof hole outside specification: ' + file.relative_to(lean).as_posix())
    if re.search(r'^import (?:Integral|Challenge)\s*$', text, flags=re.M):
        errors.append('Excluded or specification import: ' + file.name)
for file in root.rglob('*.md'):
    if '.lake' in file.parts:
        continue
    text = file.read_text(encoding='utf-8')
    text = re.sub(r'\\\[.*?\\\]|\\\(.*?\\\)|\$\$.*?\$\$', '', text, flags=re.S)
    for link in re.findall(r'\]\(([^)]+)\)', text):
        if '://' in link or link.startswith(('mailto:', '#')):
            continue
        target = unquote(link.split('#')[0])
        if not (file.parent / target).exists():
            errors.append('Missing link in ' + file.relative_to(root).as_posix() + ': ' + target)
# Search only intended small text artifacts; caches and build products are excluded.
for file in root.rglob('*'):
    if not file.is_file() or any(x in file.parts for x in ['.lake','__pycache__','verification-output']) or file.name == 'check-publication.py' or file.suffix not in {'.md','.json','.lean','.py','.sh','.cff','.tex'}:
        continue
    text = file.read_text(encoding='utf-8')
    if re.search(r'(?:[A-Za-z]:[/\\]Users[/\\]|/home/|/mnt/[cd]/Users/|/srv/projects/)', text):
        errors.append('Private filesystem path: ' + file.relative_to(root).as_posix())
if errors:
    raise SystemExit('\n'.join(errors))
print(f'PASS: {len(rows)} source/config identities, complete local import graph, local Markdown links and public text path scan.')

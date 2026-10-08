"""Check frozen proof identity and publication links without building Lean."""
from pathlib import Path
import hashlib, json, re
from urllib.parse import unquote
root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'lean/source-manifest.json').read_text(encoding='utf-8'))
errors = []
for row in manifest:
    path = root / 'lean' / row['path']
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
        errors.append(f"Source identity failed: {row['path']}")
actual = {str(p.relative_to(root / 'lean')).replace('\\', '/') for p in (root/'lean').rglob('*.lean') if '.lake' not in p.parts and p.name != 'lakefile.lean'}
expected = {r['path'] for r in manifest}
if actual != expected:
    errors.append('Proof source inventory differs from the manifest')
for path in root.rglob('*.md'):
    if '.lake' in path.parts: continue
    text = path.read_text(encoding='utf-8')
    text = re.sub(r'\\\[.*?\\\]', '', text, flags=re.S)
    text = re.sub(r'\\\(.*?\\\)', '', text, flags=re.S)
    text = re.sub(r'\$\$.*?\$\$', '', text, flags=re.S)
    for link in re.findall(r'\]\(([^)]+)\)', text):
        if '://' in link or link.startswith(('mailto:', '#')): continue
        target = unquote(link.split('#')[0])
        if not (path.parent / target).exists(): errors.append(f'Missing link in {path.relative_to(root)}: {target}')
for path in (root/'lean/Imaginary').glob('*.lean'):
    if re.search(r'\b(sorry|admit|axiom|unsafe|extern|implemented_by)\b', path.read_text(encoding='utf-8')):
        errors.append(f'Forbidden source token: {path.name}')
asset = json.loads((root/'evidence/release-assets.json').read_text())
archive = root / asset['file']
if archive.exists():
    if archive.stat().st_size != asset['compressed_bytes'] or hashlib.file_digest(archive.open('rb'),'sha256').hexdigest() != asset['compressed_sha256']:
        errors.append('Compressed export identity failed')
if errors: raise SystemExit('\n'.join(errors))
print(f'PASS: {len(manifest)} proof files, local Markdown links, source scan, and available export identity')
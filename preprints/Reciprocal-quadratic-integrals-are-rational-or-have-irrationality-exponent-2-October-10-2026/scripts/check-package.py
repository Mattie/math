"""Validate frozen source hashes, imports, evidence identities, and local links."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root/'lean/source-manifest.json').read_text())
paths = {r['path'] for r in manifest['files']}
external = {'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','ImportGraph','Plausible','ProofWidgets','LeanSearchClient'}
for record in manifest['files']:
    p = root/record['path']
    assert p.stat().st_size == record['bytes'], p
    assert hashlib.sha256(p.read_bytes()).hexdigest() == record['sha256'], p
    for line in p.read_text(encoding='utf-8').splitlines():
        if line.startswith('import '):
            for module in line.split('--')[0].split()[1:]:
                assert module.split('.')[0] in external or 'lean/'+module.replace('.','/')+'.lean' in paths, (p,module)
for name in ['positive-integralcheck','classification-check']:
    receipt = json.loads((root/'evidence'/f'{name}.json').read_text())
    assert receipt['status'] == 'passed'
    assert receipt['nanoda'] == receipt['lean_kernel_replay'] == 'accepted'
    for record in receipt['candidate_sources']:
        p = root/'lean'/record['path'].removeprefix('project/')
        assert hashlib.sha256(p.read_bytes()).hexdigest() == record['sha256'], p
for p in root.glob('*.md'):
    text = p.read_text(encoding='utf-8')
    for link in re.findall(r'\]\(([^)]+)\)',text):
        if '://' not in link and not link.startswith('#'):
            assert (p.parent/link.split('#')[0]).exists(), (p,link)
    assert not re.search(r'[A-Z]:[\\/]|/home/|/mnt/[a-z]/',text), p
print(f"PASS: {len(paths)} source hashes/imports, both historical candidate sets, and documentation links")

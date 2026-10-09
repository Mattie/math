"""Check frozen proof identities, local document links, and optional release assets."""
from pathlib import Path
import hashlib, json, re

root=Path(__file__).resolve().parents[1]
manifest=json.loads((root/'lean/source-manifest.json').read_text())
assert manifest['counts']=={'Arctangent':14,'Logarithm':55,'OAI':869}
for name,digest in manifest['source_sha256'].items():
    assert hashlib.sha256((root/'lean'/name).read_bytes()).hexdigest()==digest,name
supplement={}
for line in (root/'lean/formal-conjectures-sources.sha256').read_text().splitlines():
    digest,name=line.split(maxsplit=1)
    supplement[name]=digest
    assert hashlib.sha256((root/'lean'/name).read_bytes()).hexdigest()==digest,name
assert set(supplement)=={'Arctangent/FormalConjectures.lean'}
for group,count in manifest['counts'].items():
    additions=sum(name.startswith(group+'/') for name in supplement)
    assert len(list((root/'lean'/group).rglob('*.lean')))==count+additions,group
for path in root.rglob('*.md'):
    if any(part in {'.lake', '.verification', '__pycache__'} for part in path.relative_to(root).parts): continue
    text=path.read_text(encoding='utf-8')
    text=re.sub(r'\\\[.*?\\\]|\\\(.*?\\\)', '', text, flags=re.S)
    for target in re.findall(r'\[[^\]\n]+\]\(([^)]+)\)',text):
        if '://' in target or target.startswith('#'): continue
        assert (path.parent/target.split('#')[0]).exists(),(path,target)
assets=json.loads((root/'evidence/release-assets.json').read_text())['assets']
for asset in assets:
    path=root/'release-assets'/asset['file']
    if path.exists():
        assert path.stat().st_size==asset['bytes']
        with path.open('rb') as stream:
            assert hashlib.file_digest(stream,'sha256').hexdigest()==asset['sha256']
assert (root/'paper.pdf').read_bytes().startswith(b'%PDF-')
for file in ['README.md','NOTICE','CITATION.cff','build/manuscript.md']:
    assert 'Ryan Matthew Casper' in (root/file).read_text() or file=='CITATION.cff'
assert 'AI use disclosure' in (root/'build/manuscript.md').read_text()
print(f"PASS: {sum(manifest['counts'].values())} frozen proof modules and {len(supplement)} supplementary module, source manifests, local links, authorship, PDF, and present release assets")

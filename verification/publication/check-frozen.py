#!/usr/bin/env python3
"""Check protected publication bytes against the pre-repair public commit."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT=Path(__file__).resolve().parents[2]
BASE='13003dc8ebcce9dd4f76b73cfd99b181d1523135'
MUTABLE_ENTRIES={'lean/verify.sh','scripts/check-publication.py','scripts/check-axioms.py',
                 'scripts/dependency-targets.py','README.md','VERIFY.md','release-assets/README.md'}

def protected(name):
    """Keep mathematical sources, checker sources, pins, and past evidence immutable."""
    return (name.endswith(('.lean','.pdf','.tex','.sha256','.toml')) or '/build/' in name or
            '/evidence/' in name and not name.endswith('/source-manifest.json') or
            '/lean/source-manifest.json' in name or name.endswith(('lean-toolchain','lake-manifest.json')) or
            '/reference-reader/' in name or '/review/' in name)

def main():
    listing=subprocess.check_output(['git','ls-tree','-r',BASE],cwd=ROOT).decode().splitlines()
    manifests=[];count=0
    for line in listing:
        _,kind,sha,name=line.split(None,3)
        if protected(name):
            path=ROOT/name
            if not path.is_file():raise ValueError('Missing frozen artifact: '+name)
            data=path.read_bytes()
            actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            if actual!=sha:raise ValueError('Frozen artifact changed: '+name)
            count+=1
        elif name.endswith('/evidence/source-manifest.json'):
            manifests.append(name)
    for name in manifests:
        before=json.loads(subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT))
        after=json.loads((ROOT/name).read_text())
        if {k:v for k,v in before.items() if k!='sha256'}!={k:v for k,v in after.items() if k!='sha256'}:
            raise ValueError('Publication manifest metadata changed: '+name)
        for key in before['sha256'].keys() | after['sha256'].keys():
            if before['sha256'].get(key)!=after['sha256'].get(key) and key not in MUTABLE_ENTRIES:
                raise ValueError('Frozen manifest entry changed: '+name+' / '+key)
    print(f'PASS: {count} frozen artifacts and all protected manifest entries unchanged from {BASE}.')

if __name__=='__main__':main()

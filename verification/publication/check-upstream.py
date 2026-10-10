#!/usr/bin/env python3
"""Compare vendored modules and dependency pins with the recorded upstream revision."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
UPSTREAM = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'

def compare(expected, actual):
    """Reject missing, extra, and changed files rather than comparing overlaps."""
    if expected != actual:
        missing = sorted(expected.keys() - actual.keys())
        extra = sorted(actual.keys() - expected.keys())
        changed = sorted(k for k in expected.keys() & actual.keys() if expected[k] != actual[k])
        raise ValueError(f'Upstream mismatch: missing={missing}, extra={extra}, changed={changed}')

def upstream_tree():
    """Walk to the pinned subtree before recursively listing its bounded inventory."""
    def tree(sha, recursive=False):
        url = 'https://api.github.com/repos/openai/math/git/trees/' + sha
        if recursive:
            url += '?recursive=1'
        headers = {'User-Agent': 'math-publication-verification'}
        token = os.environ.get('GITHUB_TOKEN')
        if token:
            headers['Authorization'] = 'Bearer ' + token
        request = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(request, timeout=60) as response:
            data = json.load(response)
        if data.get('truncated'):
            raise ValueError('Incomplete upstream tree response.')
        return data['tree']
    sha = UPSTREAM
    for part in ['lean','OAI','NumberTheory','PiExponent']:
        sha = next(row['sha'] for row in tree(sha) if row['path']==part and row['type']=='tree')
    result = {row['path']:row['sha'] for row in tree(sha, True) if row['type']=='blob' and row['path'].endswith('.lean')}
    if len(result) != 869:
        raise ValueError('Unexpected upstream inventory.')
    return result

def blob_hash(data):
    """Compute the Git blob identity of exact file bytes."""
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def check_dependency(package):
    """Verify the recorded dependency tree/configuration from its exact Git commit."""
    pin = json.loads((package/'evidence/dependency-pin.json').read_text())
    if pin['repository'] != 'https://github.com/Mattie/math' or pin['openai_commit'] != UPSTREAM:
        raise ValueError('Unexpected dependency origin.')
    expected = json.loads((package/'evidence/dependency-source-sha256.json').read_text())
    configuration = json.loads((package/'evidence/dependency-config-sha256.json').read_text())
    prefix = pin['project'] + '/'
    files = subprocess.check_output(['git','ls-tree','-r','--name-only',pin['commit'],'--',pin['project']],cwd=ROOT).decode().splitlines()
    actual_names = {p[len(prefix):] for p in files if p.endswith('.lean') and p[len(prefix):].startswith(('OAI/','Logarithm/'))}
    if actual_names != set(expected) or len(expected)!=pin['source_file_count']:
        raise ValueError('Pinned dependency inventory changed.')
    process = subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    hashes, oai = {}, {}
    try:
        for name, digest in (expected | configuration).items():
            process.stdin.write((pin['commit']+':'+prefix+name+'\n').encode());process.stdin.flush()
            header=process.stdout.readline().decode().split()
            if len(header)!=3 or header[1]!='blob':
                raise ValueError('Missing pinned dependency file: '+name)
            data=process.stdout.read(int(header[2]));process.stdout.read(1)
            if hashlib.sha256(data).hexdigest()!=digest:
                raise ValueError('Pinned dependency digest mismatch: '+name)
            if name.startswith('OAI/NumberTheory/PiExponent/'):
                oai[name.removeprefix('OAI/NumberTheory/PiExponent/')]=blob_hash(data)
    finally:
        process.stdin.close();process.stdout.close();process.wait()
    return oai

def main():
    expected = upstream_tree()
    count = 0
    for package in sorted((ROOT/'preprints').iterdir()):
        source = package/'lean/OAI/NumberTheory/PiExponent'
        if source.is_dir():
            actual = {p.relative_to(source).as_posix():blob_hash(p.read_bytes()) for p in source.rglob('*.lean')}
        elif (package/'evidence/dependency-pin.json').exists():
            actual = check_dependency(package)
        else:
            continue
        compare(expected,actual);count+=1
        print('PASS:',package.name)
    if count != 7:
        raise ValueError('Expected seven publication packages.')
    print('All seven packages trace to the unchanged 869-module upstream tree at '+UPSTREAM)

if __name__ == '__main__':
    main()

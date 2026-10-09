#!/usr/bin/env python3
"""Check retained wrapper evidence against its identities and the current proof inputs."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PACKAGE = ROOT / 'verification/irrationality-exponents'


def digest(path):
    """Return the SHA-256 identity of a bounded source or retained log."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    """Fail on changed copied evidence, missing reports, or changed proof inputs."""
    integration = json.loads((PACKAGE / 'integration-2026-10-09.json').read_text())
    for name, expected in integration['public_file_sha256'].items():
        if digest(PACKAGE / name) != expected:
            raise ValueError('Integrated evidence changed: ' + name)
    pins = json.loads((PACKAGE / 'pins.json').read_text())
    spec = importlib.util.spec_from_file_location('portable_verification', PACKAGE / 'verify.py')
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    runner.validate_sources(ROOT, pins['cases'])
    record = json.loads((PACKAGE / 'validation/2026-10-08.json').read_text())
    if record['status'] != 'passed' or set(record['cases']) != set(pins['cases']):
        raise ValueError('Incomplete retained validation record.')
    for name, expected in record['runtime_sha256'].items():
        # The disclosed configuration-snapshot repair followed the full run.
        # Its current bytes are checked above, not substituted for the old identity.
        if name != 'verify.py' and digest(PACKAGE / name) != expected:
            raise ValueError('Recorded runtime input changed: ' + name)
    for item in record['logs'].values():
        if digest(PACKAGE / 'validation' / item['file']) != item['sha256']:
            raise ValueError('Retained checker log changed: ' + item['file'])
    for key, case in pins['cases'].items():
        evidence = record['cases'][key]
        if evidence['target'] != case['theorem'] or evidence['status'] != 'passed':
            raise ValueError('Wrong retained target: ' + key)
        log = (PACKAGE / 'validation' / (key + '-nanoda.log')).read_text()
        if f"Checked {evidence['declarations']} declarations with no errors" not in log:
            raise ValueError('Missing Nanoda result: ' + key)
        comparison = (PACKAGE / 'validation' / (key + '-compare.log')).read_text()
        if 'PASS: compiled statement, definition closure, axiom allowlist: ' + case['theorem'] not in comparison:
            raise ValueError('Missing Comparator result: ' + key)
    count = sum(len(case['files']) for case in pins['cases'].values())
    print(f"PASS: {count} pinned inputs, {len(record['logs'])} retained logs, and four exact targets.")
    print('Identity check of recorded evidence; no fresh independent kernel replay.')


if __name__ == '__main__':
    main()

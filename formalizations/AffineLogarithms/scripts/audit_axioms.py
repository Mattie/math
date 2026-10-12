#!/usr/bin/env python3
"""Enforce complete, unambiguous Lean axiom reports for the requested targets.

The standard policy permits only propext, Classical.choice, and Quot.sound.
This checks trusted Lean diagnostic output; it is not a substitute for structured
name checks and proof-body replay of an untrusted exported environment.
"""
import sys

if __name__ == '__main__' and not sys.flags.isolated:
    raise SystemExit('Run this audit with Python isolated mode: python3 -I scripts/audit_axioms.py')

from pathlib import Path
import argparse
import hashlib
import json
import re

PERMITTED = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = re.compile(r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")


def target_names(raw):
    """Include the standard Mathlib endpoints when reading a package target map."""
    if isinstance(raw, dict):
        return [entry['public_declaration'] for entry in raw['public_declarations']] + raw['standard_endpoints']
    return raw


def check_receipt(receipt_path, source_manifest, targets_path, log_path):
    """Bind retained diagnostics to the current source inventory and target map."""
    receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
    if receipt['status'] != 'passed':
        raise ValueError('Retained audit did not pass')
    for key, path in [('source_manifest_sha256', source_manifest),
                      ('target_map_sha256', targets_path), ('log_sha256', log_path)]:
        if hashlib.sha256(path.read_bytes()).hexdigest() != receipt[key]:
            raise ValueError('Retained audit identity mismatch: ' + key)


def inspect(text, targets):
    """Return each requested target's axiom set, rejecting gaps and conflicts."""
    if not targets or len(targets) != len(set(targets)):
        raise ValueError('Expected a nonempty list of distinct targets')
    reports = {}
    for match in REPORT.finditer(text):
        name, body = match.groups()
        if name not in targets:
            continue
        axioms = set() if body is None or not body.strip() else {a.strip() for a in body.split(',')}
        if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', a) for a in axioms):
            raise ValueError('Malformed axiom report for ' + name)
        if name in reports and reports[name] != axioms:
            raise ValueError('Conflicting axiom reports for ' + name)
        reports[name] = axioms
    # A malformed later diagnostic must not be masked by an earlier good one.
    for name in targets:
        starts = list(re.finditer(re.escape("'" + name + "'") + r'\s+(?:depends on axioms|does not depend on any axioms)', text))
        complete = [m for m in REPORT.finditer(text) if m.group(1) == name]
        if len(starts) != len(complete):
            raise ValueError('Malformed axiom report for ' + name)
        if name not in reports:
            raise ValueError('Missing axiom report for ' + name)
        extra = reports[name] - PERMITTED
        if extra:
            raise ValueError('Unexpected axioms for ' + name + ': ' + ', '.join(sorted(extra)))
    return {name: sorted(reports[name]) for name in targets}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', type=Path, required=True)
    parser.add_argument('--targets', type=Path, required=True,
                        help='JSON array of theorem names, or the package target-map.json.')
    parser.add_argument('--receipt', type=Path,
                        help='For retained evidence, require the successful build receipt and its identities.')
    parser.add_argument('--source-manifest', type=Path,
                        help='Current source inventory; required with --receipt.')
    args = parser.parse_args()
    if bool(args.receipt) != bool(args.source_manifest):
        parser.error('--receipt and --source-manifest must be used together')
    if args.receipt:
        check_receipt(args.receipt, args.source_manifest, args.targets, args.log)
    raw = json.loads(args.targets.read_text(encoding='utf-8'))
    targets = target_names(raw)
    result = inspect(args.log.read_text(encoding='utf-8'), targets)
    print(json.dumps({'status': 'passed', 'targets_checked': len(result), 'axioms': result}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('Axiom audit rejected: ' + str(error), file=sys.stderr)
        raise SystemExit(1)

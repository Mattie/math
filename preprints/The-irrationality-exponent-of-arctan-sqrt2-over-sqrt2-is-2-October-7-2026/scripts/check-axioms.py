#!/usr/bin/env python3
"""Reject incomplete axiom audits or assumptions outside the stated foundation."""
import argparse
from pathlib import Path
import re

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = re.compile(r"'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")

def check(text, expected):
    """Require each expected declaration and reject every reported extra axiom."""
    if not expected:
        raise ValueError('No expected declarations supplied.')
    found = {}
    matches = list(REPORT.finditer(text))
    remainder = REPORT.sub('', text)
    if 'depends on axioms' in remainder or 'does not depend on any axioms' in remainder:
        raise ValueError('Malformed axiom report.')
    for match in matches:
        name, raw = match.groups()
        names = [] if not raw or not raw.strip() else [item.strip() for item in raw.split(',')]
        if any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', item) for item in names):
            raise ValueError('Malformed axiom list for ' + name)
        axioms = set(names)
        if axioms - ALLOWED:
            raise ValueError('Unpermitted axioms for ' + name + ': ' + ', '.join(sorted(axioms - ALLOWED)))
        if name in found and found[name] != axioms:
            raise ValueError('Conflicting axiom reports for ' + name)
        found[name] = axioms
    missing = set(expected) - found.keys()
    if missing:
        raise ValueError('Missing axiom reports: ' + ', '.join(sorted(missing)))
    return len(set(expected))

def main():
    """Check a fresh Lean log against explicit names and frozen audit commands."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--source', action='append', type=Path, default=[])
    parser.add_argument('--expect', action='append', default=[])
    args = parser.parse_args()
    expected = set(args.expect)
    for source in args.source:
        names = re.findall(r'^\s*#print axioms\s+(\S+)\s*$', source.read_text(encoding='utf-8'), re.M)
        if not names:
            parser.error('No axiom audit declarations in ' + str(source))
        expected.update(names)
    try:
        count = check(args.log.read_text(encoding='utf-8'), expected)
    except ValueError as error:
        parser.exit(1, str(error) + '\n')
    print(f'PASS: {count} required axiom reports; only the three permitted foundational axioms.')

if __name__ == '__main__':
    main()

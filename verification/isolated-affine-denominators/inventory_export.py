"""Check target bodies and structured axiom names in the retained new export.

This establishes export identity and coverage, not proof-body correctness.
Both kernel replays and semantic comparison remain separate required evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PUBLIC = ['OAI.DenominatorAffine.log_three_halves_add_sqrt_two_' + suffix for suffix in
          ('eventualLowerBound', 'explicit_bound', 'irrational',
           'irrationalityExponent_le_four', 'standard_exponent_le_four')]
PUBLIC.append('OAI.DenominatorAffine.Endpoint.paired_eventualLowerBound')


def inspect(path, targets):
    """Stream the export, retaining name structure rather than flattening names."""
    expected = {tuple(name.split('.')): name for name in targets}
    names, found, axioms, declarations = {0: ()}, {}, [], set()
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for line in stream:
            digest.update(line)
            record = json.loads(line)
            if 'in' in record:
                node = record.get('str', record.get('num'))
                if record['in'] in names:
                    raise RuntimeError('Duplicate structured name index')
                names[record['in']] = names[node['pre']] + (node.get('str', node.get('i')),)
            for kind in ('axiom', 'thm', 'def', 'opaque', 'inductive', 'ctor', 'recursor', 'quot'):
                declaration = record.get(kind)
                if not isinstance(declaration, dict) or 'name' not in declaration:
                    continue
                name = names[declaration['name']]
                if name in declarations:
                    raise RuntimeError('Duplicate declaration')
                declarations.add(name)
                if kind == 'axiom':
                    axioms.append(name)
                if name in expected:
                    if kind != 'thm' or 'value' not in declaration:
                        raise RuntimeError('Endpoint has no theorem body')
                    found[expected[name]] = {'kind': kind, 'type': declaration['type'], 'value': declaration['value']}
    if set(found) != set(targets):
        raise RuntimeError('Missing target bodies: ' + ', '.join(sorted(set(targets) - set(found))))
    if set(axioms) != {('propext',), ('Quot', 'sound'), ('Classical', 'choice')}:
        raise RuntimeError('Unexpected structured axiom names: ' + repr(axioms))
    return {'status': 'passed', 'scope': 'Identity, target body inventory and structured axiom names only',
            'export_sha256': digest.hexdigest(), 'bytes': path.stat().st_size,
            'declaration_records': len(declarations), 'targets': found,
            'structured_axiom_names': axioms}


def main():
    """Record a new inventory without replacing any previous result."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--export', dest='export_path', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    targets = PUBLIC + json.loads((HERE / 'config.json').read_text())['theorem_names']
    result = inspect(args.export_path, targets)
    with args.output.open('x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'targets'}))


if __name__ == '__main__':
    main()

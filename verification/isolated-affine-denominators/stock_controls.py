"""Record the new 4.34.1 stock reader provenance and actual body-mode controls.

Uses the retained tiny positive/one-body-mutation exports from the earlier affine
verification. A policy failure is distinct from the required typed rejection.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--tools', type=Path, required=True)
    args = parser.parse_args()
    root, tools = args.root.resolve(), args.tools.resolve()
    stock = root / 'stock-reader'
    kernel = stock / '.lake/build/bin/kernel'
    out = root / 'stock-controls'
    out.mkdir()
    receipt = {'status': 'running', 'scope': 'Separately built Lean 4.34.1 reader and tiny proof-body controls',
               'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'commands': []}

    def save():
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    def command(label, argv, cwd=stock):
        log = out / (label + '.log')
        with log.open('wb') as stream:
            result = subprocess.run([str(a) for a in argv], cwd=cwd, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=300)
        receipt['commands'].append({'label': label, 'argv': [str(a) for a in argv], 'cwd': str(cwd),
                                    'exit': result.returncode, 'log': log.name, 'sha256': sha(log)})
        save()
        return result.returncode, log.read_text(errors='replace')

    try:
        original = root / 'controls'
        positive, negative = original / 'positive.ndjson', original / 'ill-typed.ndjson'
        a = [json.loads(line) for line in positive.read_text().splitlines()]
        b = [json.loads(line) for line in negative.read_text().splitlines()]
        if len(a) != len(b):
            raise RuntimeError('Negative control changed record count')
        changes = [(x, y) for x, y in zip(a, b) if x != y]
        if len(changes) != 1:
            raise RuntimeError('Negative control is not a single body mutation')
        before, after = changes[0]
        if set(before) != {'thm'} or set(after) != {'thm'}:
            raise RuntimeError('Unexpected mutation kind')
        before_body, after_body = before['thm'].copy(), after['thm'].copy()
        before_body.pop('value')
        value = after_body.pop('value')
        if before_body != after_body or value != after_body['type']:
            raise RuntimeError('Expected proof replaced by its type expression')
        receipt['mutation'] = 'Only validation_control proof value becomes its type expression; name/type/axioms unchanged.'
        receipt['inputs'] = {str(p.relative_to(root)): sha(p) for p in
            [positive, negative, kernel, root / 'stock-build.log', *[stock / n for n in
                ('Main.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]]}
        receipt['binaries'] = {str(p): sha(p) for p in [tools / 'lean/bin/lean', tools / 'lean/bin/lake', tools / 'nanoda_bin']}
        for label, argv, marker in [
            ('lean-version', [tools / 'lean/bin/lean', '--version'], '4.34.1'),
            ('exporter-revision', ['git', '-C', stock / '.lake/packages/lean4export', 'rev-parse', 'HEAD'], '05d43a2bc773b40ecfdebb32294192a5ef756951'),
            ('linkage', ['ldd', kernel], ''),
            ('positive', [kernel, positive], 'Accepted '),
            ('negative-parses', [kernel, '--parse-only', negative], 'Parse successful.')]:
            code, text = command(label, argv)
            if code != 0 or marker not in text:
                raise RuntimeError('Failed ' + label)
        code, text = command('negative-kernel', [kernel, negative])
        if code != 1 or '(kernel) declaration type mismatch' not in text or 'validation_control' not in text:
            raise RuntimeError('Negative did not reach intended stock kernel type rejection')
        for label, export, rejected in [('nanoda-positive', positive, False), ('nanoda-negative', negative, True)]:
            config = out / (label + '.json')
            config.write_text(json.dumps({'export_file_path': str(export),
                'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
                'unpermitted_axiom_hard_error': True, 'nat_extension': True, 'string_extension': True,
                'print_success_message': True, 'print_axioms': False, 'num_threads': 4}))
            code, text = command(label, [tools / 'nanoda_bin', config])
            if rejected:
                if code != 101 or 'assertion failed: self.def_eq(u, v)' not in text:
                    raise RuntimeError('Negative did not reach intended Nanoda type equality rejection')
            elif code != 0 or 'no errors' not in text:
                raise RuntimeError('Nanoda positive failed')
        if any(sha(root / name) != value for name, value in receipt['inputs'].items()):
            raise RuntimeError('Control input or stock binary changed')
        receipt['status'] = 'passed'
    except Exception as error:
        receipt.update(status='failed', error=f'{type(error).__name__}: {error}')
    finally:
        receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        save()
    print(json.dumps(receipt, indent=2))
    return 0 if receipt['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())

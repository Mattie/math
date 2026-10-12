"""Classify Nanoda issue 47 on the exact selected binaries, separate from the proof.

The deliberately invalid declaration bypasses Lean's compiler kernel check only
to construct a negative export. The stock replay must reject it. No candidate
source imports this fixture.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

SOURCE = '''import Lean
open Lean Elab Command

run_cmd liftTermElabM do
  let p : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit 0) (mkRawNatLit 0)
  let decl : Declaration := .defnDecl {
    name := `bad, levelParams := [], type := mkConst ``Nat, value := .proj `Sigma 0 p
    hints := .abbrev, safety := .safe }
  withOptions (debug.skipKernelTC.set · true) do addDecl decl
'''


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--tools', type=Path, required=True)
    parser.add_argument('--stock', type=Path, required=True)
    args = parser.parse_args()
    work = args.work_dir.resolve()
    work.mkdir()
    lean, exporter, nanoda = args.tools / 'lean/bin/lean', args.tools / 'lean/bin/lean4export', args.tools / 'nanoda_bin'
    receipt = {'status': 'running', 'scope': 'Nanoda issue 47 exact-pin regression classification; not theorem evidence',
               'issue': 'https://github.com/ammkrn/nanoda_lib/issues/47',
               'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'commands': []}

    def save():
        (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    def run(label, argv, output=None):
        log = output or work / (label + '.log')
        with log.open('wb') as stream:
            result = subprocess.run([str(a) for a in argv], cwd=work,
                env=dict(os.environ, LEAN_PATH=str(work), PATH=str(lean.parent) + ':/usr/bin:/bin'),
                stdout=stream, stderr=subprocess.STDOUT, timeout=180)
        receipt['commands'].append({'label': label, 'argv': [str(a) for a in argv],
                                    'exit': result.returncode, 'log': log.name, 'sha256': sha(log)})
        save()
        return result.returncode, log.read_text(errors='replace')

    try:
        source = work / 'Bad.lean'
        source.write_text(SOURCE)
        (work / 'Rejected.lean').write_text(SOURCE.replace('withOptions (debug.skipKernelTC.set · true) do addDecl decl', 'addDecl decl'))
        code, text = run('ordinary-lean-rejects', [lean, 'Rejected.lean'])
        if code == 0 or 'invalid projection' not in text:
            raise RuntimeError('Ordinary compiler did not reject the intended projection')
        code, _ = run('construct-negative-fixture', [lean, '-o', 'Bad.olean', 'Bad.lean'])
        if code != 0:
            raise RuntimeError('Negative fixture failed to compile with deliberate kernel bypass')
        export = work / 'bad.ndjson'
        code, _ = run('export-negative-fixture', [exporter, 'Bad', '--', 'bad'], export)
        if code != 0:
            raise RuntimeError('Negative fixture did not export')
        config = work / 'nanoda.json'
        config.write_text(json.dumps({'export_file_path': str(export), 'use_stdin': False,
            'nat_extension': True, 'string_extension': True,
            'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
            'unpermitted_axiom_hard_error': True, 'print_success_message': True, 'print_axioms': False}))
        nanoda_code, nanoda_text = run('nanoda', [nanoda, config])
        stock_code, stock_text = run('stock-lean', [args.stock, export])
        if stock_code == 0 or 'invalid projection' not in stock_text:
            raise RuntimeError('Stock replay did not reject invalid projection')
        if nanoda_code == 0 and 'no errors' in nanoda_text:
            classification = 'selected Nanoda pin accepts invalid projection; stock Lean rejects'
        elif nanoda_code != 0:
            classification = 'selected Nanoda pin rejected; inspect diagnostic before inferring intended rule'
        else:
            raise RuntimeError('Unrecognized Nanoda output')
        receipt.update(status='classified', classification=classification,
            binaries={str(p): sha(p) for p in [lean, exporter, nanoda, args.stock]},
            source_sha256=sha(source), export_sha256=sha(export))
    except Exception as error:
        receipt.update(status='failed', error=f'{type(error).__name__}: {error}')
    finally:
        receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        save()
    print(json.dumps(receipt, indent=2))
    return 0 if receipt['status'] == 'classified' else 1


if __name__ == '__main__':
    raise SystemExit(main())

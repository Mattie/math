#!/usr/bin/env python3
"""Replay the exact retained export with Nanoda and the supplemental Lean reader.

Provide binaries built from the documented pins. Acceptance/rejection controls
run first. Each run gets a separate directory and receipt under .work.
"""
from pathlib import Path
import argparse
import gzip
import json
import shutil
import subprocess
import tempfile
from check import ROOT, check_export, digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nanoda', required=True, type=Path)
    parser.add_argument('--lean-reader', required=True, type=Path)
    parser.add_argument('--export', type=Path)
    parser.add_argument('--controls-only', action='store_true')
    args = parser.parse_args()
    if not args.controls_only and not args.export:
        parser.error('--export is required unless --controls-only is set')
    nanoda, reader = args.nanoda.resolve(), args.lean_reader.resolve()
    (ROOT / '.work').mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='replay-', dir=ROOT / '.work'))
    receipt = {'status': 'running', 'scope': 'Controls only' if args.controls_only else 'Exact export body replay',
               'binary_sha256': {'nanoda': digest(nanoda), 'lean_reader': digest(reader)}, 'commands': []}

    def command(label, argv):
        """Capture an exit code and diagnostic output for a single checker run."""
        print(label, flush=True)
        result = subprocess.run([str(x) for x in argv], text=True, encoding='utf-8',
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (work / (label + '.log')).write_text(result.stdout, encoding='utf-8')
        receipt['commands'].append({'label': label, 'exit_code': result.returncode,
                                    'log_sha256': digest(work / (label + '.log'))})
        return result.returncode, result.stdout

    def nano(label, source):
        config = work / (label + '.json')
        config.write_text(json.dumps({'export_file_path': str(source), 'use_stdin': False,
            'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
            'unpermitted_axiom_hard_error': True, 'nat_extension': True,
            'string_extension': True, 'num_threads': 4, 'print_success_message': True}))
        return command(label, [nanoda, config])

    def require(condition, message):
        if not condition:
            raise RuntimeError(message + '; inspect logs in ' + str(work))

    try:
        positive, negative = ROOT / 'controls/positive.ndjson', ROOT / 'controls/ill-typed.ndjson'
        require(nano('nanoda-positive', positive)[0] == 0, 'Nanoda rejected the valid fixture')
        code, text = nano('nanoda-negative', negative)
        require(code != 0 and 'self.def_eq' in text, 'Nanoda did not reject at the expected type check')
        code, text = command('lean-positive', [reader, positive])
        require(code == 0 and 'Accepted ' in text, 'Lean rejected the valid fixture')
        code, text = command('lean-negative-parses', [reader, '--parse-only', negative])
        require(code == 0 and 'Parse successful.' in text, 'Lean negative fixture did not parse')
        code, text = command('lean-negative', [reader, negative])
        require(code != 0 and 'declaration type mismatch' in text and 'validation_control' in text,
                'Lean did not reject at the expected type check')
        receipt['controls'] = 'passed'
        if not args.controls_only:
            source = args.export.resolve()
            check_export(source)
            if source.suffix == '.gz':
                unpacked = work / 'solution-export.ndjson'
                with gzip.open(source, 'rb') as incoming, unpacked.open('wb') as outgoing:
                    shutil.copyfileobj(incoming, outgoing)
                source = unpacked
                check_export(source)
            receipt['export_sha256'] = digest(source)
            require(nano('nanoda-proof', source)[0] == 0, 'Nanoda rejected the proof export')
            code, text = command('lean-proof', [reader, source])
            require(code == 0 and 'Accepted 118382 declarations.' in text, 'Lean did not accept the expected closure')
        receipt['status'] = 'passed'
    except Exception as error:
        receipt['status'] = 'failed'
        receipt['error'] = str(error)
        raise
    finally:
        (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print('Receipt: ' + str(work / 'receipt.json'), flush=True)


if __name__ == '__main__':
    main()

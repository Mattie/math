"""Create public, path-free summaries of completed local control evidence."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    for source, name in [
        ('axiom-policy-receipt.json', 'axiom-policy'),
        ('axiom-controls/receipt.json', 'axiom-controls'),
        ('stock-controls/receipt.json', 'stock-controls'),
    ]:
        raw = (ROOT / 'evidence' / source).read_bytes()
        data = json.loads(raw)
        if data['status'] != 'passed':
            raise RuntimeError('Control did not pass: ' + source)
        if 'commands' in data:
            data['commands'] = [{k: v for k, v in command.items()
                                 if k in ('label', 'exit', 'log', 'sha256')}
                                for command in data['commands']]
        if 'binaries' in data:
            data['binaries'] = {Path(p).name: value for p, value in data['binaries'].items()}
        data['raw_receipt_sha256'] = hashlib.sha256(raw).hexdigest()
        data['evidence_note'] = 'Sanitized summary of fresh execution; raw logs retained privately and identified by digest.'
        destination = ROOT / 'results' / (name + '-2026-10-12.json')
        destination.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()

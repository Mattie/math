"""Summarize a completed local run without exposing operational paths."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = (args.evidence / 'receipt.json').read_bytes()
    receipt = json.loads(raw)
    index_raw = (args.evidence / 'evidence-index.json').read_bytes()
    index = json.loads(index_raw)
    if receipt['status'] != 'passed' or index['status'] != 'passed':
        raise RuntimeError('Only summarize an accepted final run')
    if index['files']['receipt.json']['sha256'] != hashlib.sha256(raw).hexdigest():
        raise RuntimeError('Receipt/index mismatch')
    fields = ('status', 'scope', 'evidence_kind', 'started_utc', 'finished_utc',
              'targets', 'source_manifest_sha256', 'runner_sha256', 'adapter_sha256',
              'inventory_driver_sha256', 'checks', 'pins', 'candidate', 'export', 'body_controls', 'boundary')
    summary = {key: receipt[key] for key in fields}
    summary['commands'] = [{key: entry[key] for key in ('label', 'exit_code', 'log', 'log_sha256')}
                           for entry in receipt['commands']]
    summary['binaries'] = {key: {'sha256': value['sha256']} for key, value in receipt['binaries'].items()}
    summary['dependencies'] = {key: receipt['dependencies'][key] for key in ('revisions', 'scope')}
    summary['raw_receipt_sha256'] = hashlib.sha256(raw).hexdigest()
    summary['raw_evidence_index_sha256'] = hashlib.sha256(index_raw).hexdigest()
    summary['evidence_note'] = 'Fresh local execution using identified inherited/upstream caches; no hosted or complete source rebuild claim. Raw evidence and full export retained privately.'
    summary['limitations'] = [
        'Nanoda selected pin accepts the malformed-projection diagnostic; Lean replay of identical bytes is mandatory.',
        'Export retention relationship to the Comparator temporary input assumes no concurrent modification.',
        'Source identity and cache identity do not authenticate cached objects as built from those sources.',
        'Standalone stock replay supplies neither semantic comparison nor an axiom allowlist; separate gates enforce those requirements.',
    ]
    args.output.write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()

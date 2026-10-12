#!/usr/bin/env python3
"""Exercise the actual axiom policy on compiled imported-proof fixtures.

Run with Lean 4.34.1 on PATH. Deliberate admission and extra-axiom fixtures live
only under .work and are never imported by the mathematical proof project.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from check import ROOT, digest


def main():
    lean = Path(shutil.which('lean') or 'lean').resolve()
    version = subprocess.check_output([str(lean), '--version'], cwd=ROOT, text=True).strip()
    if not version.startswith('Lean (version 4.34.1,'):
        raise RuntimeError('Expected Lean 4.34.1; got ' + version)
    (ROOT / '.work').mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='audit-controls-', dir=ROOT / '.work'))
    policy = ROOT / 'scripts/audit_axioms.py'
    targets = work / 'targets.json'
    targets.write_text('["validation_control"]\n')
    receipt = {'status': 'running', 'scope': 'Axiom-policy controls, not a new proof replay',
               'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
               'lean_version': version, 'lean_binary_sha256': digest(lean),
               'axiom_policy_sha256': digest(policy), 'cases': {}}

    def run(label, argv, cwd, env=None):
        """Retain the exact diagnostic used to classify each test result."""
        result = subprocess.run([str(a) for a in argv], cwd=cwd, env=env,
                                capture_output=True, text=True, encoding='utf-8')
        output = result.stdout + result.stderr
        log = work / (label + '.log')
        log.write_text(output, encoding='utf-8')
        return result.returncode, output, log

    def check(label, log, expected):
        code, output, policy_log = run(label + '-policy', [sys.executable, '-I', policy,
                                       '--log', log, '--targets', targets], ROOT)
        good = code == 0 if expected is None else code != 0 and expected in output
        if not good:
            raise RuntimeError('Unexpected policy outcome: ' + label)
        receipt['cases'][label] = {'status': 'passed', 'policy_exit_code': code,
                                  'expected_diagnostic': expected, 'input_log_sha256': digest(log),
                                  'policy_log_sha256': digest(policy_log)}
        print(label + ': passed', flush=True)

    try:
        fixtures = {
            'valid': ('theorem dependency_value : True := True.intro\n', None),
            'imported-admission': ('theorem dependency_value : True := by sorry\n', 'sorryAx'),
            'imported-extra-axiom': ('axiom forbidden_control : True\ntheorem dependency_value : True := forbidden_control\n', 'forbidden_control'),
        }
        for label, (source, rejected_axiom) in fixtures.items():
            case = work / label
            case.mkdir()
            (case / 'FixtureDependency.lean').write_text(source)
            (case / 'Audit.lean').write_text('import FixtureDependency\n'
                'theorem validation_control : True := dependency_value\n#print axioms validation_control\n')
            env = dict(os.environ, LEAN_PATH=str(case))
            flags = ['-DautoImplicit=false']
            if rejected_axiom != 'sorryAx':
                flags.append('-DwarningAsError=true')
            code, output, _ = run(label + '-dependency', [lean, *flags, '-o', 'FixtureDependency.olean',
                                                         'FixtureDependency.lean'], case, env)
            if code != 0 or (rejected_axiom == 'sorryAx' and 'declaration uses' not in output):
                raise RuntimeError('Dependency fixture did not compile as expected: ' + label)
            code, output, log = run(label + '-audit', [lean, '-DautoImplicit=false', '-DwarningAsError=true',
                                                     'Audit.lean'], case, env)
            if code != 0:
                raise RuntimeError('Imported fixture audit did not elaborate: ' + label)
            expected = None if rejected_axiom is None else 'Unexpected axioms for validation_control: ' + rejected_axiom
            check(label, log, expected)
            receipt['cases'][label]['importing_audit_exit_code'] = code
        malformed = {
            'missing-report': ('', 'Missing axiom report'),
            'truncated-report': ("'validation_control' depends on axioms: [propext\n", 'Malformed axiom report'),
            'conflicting-reports': ("'validation_control' depends on axioms: [sorryAx]\n"
                                    "'validation_control' depends on axioms: [propext, Classical.choice, Quot.sound]\n", 'Conflicting axiom reports'),
            'malformed-after-valid': ("'validation_control' depends on axioms: [propext]\n"
                                     "'validation_control' depends on axioms: [\n", 'Malformed axiom report'),
        }
        for label, (text, expected) in malformed.items():
            log = work / (label + '-input.log')
            log.write_text(text)
            check(label, log, expected)
        receipt['status'] = 'passed'
    except Exception as error:
        receipt['status'] = 'failed'
        receipt['error'] = str(error)
        raise
    finally:
        receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        (work / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print('Receipt: ' + str(work / 'receipt.json'), flush=True)


if __name__ == '__main__':
    main()

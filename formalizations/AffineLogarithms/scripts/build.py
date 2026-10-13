#!/usr/bin/env python3
"""Build the pinned proof project and axiom audits with Lean 4.34.1.

Run from any directory. Python 3.11+, Git, and elan's Lean/Lake executables
must be on PATH. Lake fetches locked upstream dependencies as needed.
"""
import sys

if __name__ == '__main__' and not sys.flags.isolated:
    raise SystemExit('Run this builder with Python isolated mode: python3 -I scripts/build.py')

from pathlib import Path
import argparse
import importlib.util
import json
import subprocess
import time

spec = importlib.util.spec_from_file_location('package_check', Path(__file__).with_name('check.py'))
package_check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(package_check)
ROOT, check_sources, digest = package_check.ROOT, package_check.check_sources, package_check.digest


def run(argv, log):
    """Stream one command to the console and build log, failing on nonzero exit."""
    print('+ ' + ' '.join(argv), flush=True)
    with subprocess.Popen(argv, cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, encoding='utf-8') as child:
        for line in child.stdout:
            print(line, end='', flush=True)
            log.write(line)
        if child.wait():
            raise RuntimeError('Command failed: ' + ' '.join(argv))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-cache-download', action='store_true',
                        help='Use already available upstream Mathlib caches.')
    parser.add_argument('--all-modules', action='store_true',
                        help='Explicitly build every bundled proof module, excluding the statement-only Challenge.')
    args = parser.parse_args()
    # Authenticate the Lake configuration, lock, toolchain and complete package
    # before even asking Lean for its version (elan selects a toolchain here).
    package_check.check_package()
    check_sources()
    target_map = json.loads((ROOT / 'evidence/target-map.json').read_text())
    targets = [entry['public_declaration'] for entry in target_map['public_declarations']] + target_map['standard_endpoints']
    work = ROOT / '.work'
    work.mkdir(exist_ok=True)
    receipt = {'status': 'running', 'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
               'source_manifest_sha256': digest(ROOT / 'evidence/source-sha256.json'),
               'target_map_sha256': digest(ROOT / 'evidence/target-map.json'),
               'scope': 'Source compilation and axiom guards; not independent kernel replay.'}
    try:
        version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
        if not version.startswith('Lean (version 4.34.1,'):
            raise RuntimeError('Expected the pinned Lean 4.34.1 toolchain; got ' + version)
        receipt['lean_version'] = version
        with (work / 'build.log').open('w', encoding='utf-8') as log:
            if not args.skip_cache_download:
                run(['lake', 'exe', 'cache', 'get'], log)
            if args.all_modules:
                sources = json.loads((ROOT / 'evidence/source-sha256.json').read_text())
                modules = sorted(name[:-5].replace('/', '.') for name in sources
                                 if name.endswith('.lean') and name != 'Challenge.lean')
                receipt['module_sweep'] = {'modules': modules, 'count': len(modules),
                                           'excluded_specification': 'Challenge.lean'}
                run(['lake', 'build', *('+' + module for module in modules)], log)
            run(['lake', 'build', '+Solution', '+PairedAffine.Audit', '+PairedAffine.AffineAudit'], log)
            # The specification-only Challenge intentionally contains placeholders.
            # Require warning-free elaboration of the actual solution and both audits.
            for module in ('StandardBridge', 'Solution', 'PairedAffine/Audit', 'PairedAffine/AffineAudit'):
                run(['lake', 'env', 'lean', '-DautoImplicit=false', '-DwarningAsError=true', module + '.lean'], log)
            audit = work / 'EndpointAudit.lean'
            audit.write_text('import Solution\n' + ''.join('#print axioms ' + name + '\n' for name in targets),
                             encoding='utf-8')
            run(['lake', 'env', 'lean', '-DautoImplicit=false', '-DwarningAsError=true', str(audit)], log)
        lock = json.loads((ROOT / 'lake-manifest.json').read_text())
        for package in lock['packages']:
            directory = ROOT / '.lake/packages' / package['name']
            revision = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            if revision != package['rev']:
                raise RuntimeError('Dependency revision mismatch: ' + package['name'])
            changed = subprocess.check_output(['git', '-C', str(directory), 'diff', '--name-only', 'HEAD'], text=True)
            if changed.strip():
                raise RuntimeError('Modified dependency source: ' + package['name'])
        package_check.check_package()
        check_sources()
        policy = ROOT / 'scripts/audit_axioms.py'
        checked = subprocess.run([sys.executable, '-I', str(policy), '--log', str(work / 'build.log'),
                                  '--targets', str(ROOT / 'evidence/target-map.json')],
                                 capture_output=True, text=True, encoding='utf-8')
        (work / 'axiom-policy.log').write_text(checked.stdout + checked.stderr, encoding='utf-8')
        if checked.returncode:
            raise RuntimeError('Axiom policy rejected the build; see .work/axiom-policy.log')
        receipt['axiom_policy_sha256'] = digest(policy)
        receipt['axiom_policy_log_sha256'] = digest(work / 'axiom-policy.log')
        receipt['public_axiom_reports_checked'] = len(target_map['public_declarations'])
        receipt['standard_axiom_reports_checked'] = len(target_map['standard_endpoints'])
        receipt['axiom_reports_checked'] = len(targets)
        receipt['status'] = 'passed'
        receipt['log_sha256'] = digest(work / 'build.log')
    except Exception as error:
        receipt['status'] = 'failed'
        receipt['error'] = str(error)
        raise
    finally:
        receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        (work / 'build-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()

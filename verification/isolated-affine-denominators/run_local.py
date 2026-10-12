"""Run the frozen local denominator package using identified inherited caches.

This is the ordinary local-source audit, not the clean hosted-source milestone.
New DenominatorAffine modules and wrappers start without compiled artifacts.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def local_module(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


verify = local_module('verify')
inventory_export = local_module('inventory_export')
legacy, sha, require = verify.legacy, verify.digest, verify.require


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--cache-receipt', type=Path, required=True)
    parser.add_argument('--tool-receipt', type=Path, required=True)
    parser.add_argument('--stock-root', type=Path, required=True)
    args = parser.parse_args()
    require(args.work_dir.is_absolute(), 'Use an absolute local verification scratch path')
    require(not args.work_dir.exists(), 'Use fresh local verification scratch')
    frozen, config = verify.check_inputs()
    run = legacy.Preflight(args.work_dir)
    run.receipt.update(scope='Six denominator affine targets: fresh new modules, identified inherited caches, full exported-body replay',
                       evidence_kind='fresh execution', targets=config['theorem_names'],
                       source_manifest_sha256=sha(verify.MANIFEST), phase='preparation',
                       runner_sha256=sha(Path(__file__)), adapter_sha256=sha(HERE / 'verify.py'),
                       inventory_driver_sha256=sha(HERE / 'inventory_export.py'))
    watcher = None
    try:
        earlier = json.loads(args.tool_receipt.read_text())
        require(earlier['status'] == 'passed', 'Earlier tool receipt is not successful')
        for item in earlier['binaries'].values():
            require(sha(Path(item['path'])) == item['sha256'], 'Tool identity mismatch')
        pins = json.loads((HERE / 'pins.json').read_text())
        require(all(pins[k] == v for k, v in earlier['pins'].items()), 'Tool pin mismatch')
        run.receipt.update(binaries=earlier['binaries'], pins=pins,
            reused_tool_receipt={'path': str(args.tool_receipt), 'sha256': sha(args.tool_receipt)})
        original_lean = Path(earlier['binaries']['lean']['path']).parents[1]
        run.lean = run.work / 'tools/lean'
        run.lean.mkdir(parents=True)
        # A new root keeps the boundary-control marker out of the archived tools.
        for child in original_lean.iterdir():
            if child.name != 'protected-marker':
                (run.lean / child.name).symlink_to(child, target_is_directory=child.is_dir())
        run.comparator = Path(earlier['binaries']['comparator']['path'])
        run.helper = Path(earlier['binaries']['probe']['path'])
        run.env.update(PATH=str(original_lean / 'bin') + ':/usr/bin:/bin', LEAN_NUM_THREADS='4')
        for key in ('COMPARATOR_LANDRUN', 'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_NANODA'):
            run.env[key] = earlier['binaries'][key]['path']
        run.receipt['checks']['tools'] = 'passed'
        run.receipt['phase'] = 'fresh-boundary-and-frontend-controls'
        for case in ('valid', 'mismatch', 'axiom'):
            run.fixture(case)
        legacy.imported_admission(run)
        run.receipt['phase'] = 'source-and-cache-preparation'
        cache = json.loads(args.cache_receipt.read_text())
        require(cache['status'] == 'passed' and cache['sources'] == frozen['inherited'], 'Inherited cache source inventory mismatch')
        old_project = Path(cache['project'])
        actual_source_names = {p.relative_to(old_project).as_posix()
            for library in ('OAI', 'Logarithm', 'AlgebraicLog', 'PairedAffine')
            for p in (old_project / library).rglob('*.lean')}
        actual_source_names.add('StandardBridge.lean')
        require(actual_source_names == set(frozen['inherited']), 'Inherited source inventory has missing or extra files')
        require(all(sha(old_project / n) == h for n, h in cache['sources'].items()), 'Inherited source changed')
        project = run.work / 'project'
        verify.stage_sources(project, frozen, package=True)
        (project / '.lake').mkdir()
        packages = Path(cache['packages_resolved'])
        (project / '.lake/packages').symlink_to(packages, target_is_directory=True)
        dependency_lock = json.loads((project / 'lake-manifest.json').read_text())
        revisions = {}
        for package in dependency_lock['packages']:
            code, head = run.command('dependency-' + package['name'], ['git', 'rev-parse', 'HEAD'], cwd=packages / package['name'])
            require(head.strip() == package['rev'], 'Dependency revision mismatch')
            _, changed = run.command('dependency-clean-' + package['name'], ['git', 'diff', '--name-only', 'HEAD'], cwd=packages / package['name'])
            require(not changed.strip(), 'Dependency tracked source changed')
            revisions[package['name']] = head.strip()
        for name, digest in cache['cache'].items():
            source, target = old_project / name, project / name
            require(sha(source) == digest, 'Inherited compiled object changed: ' + name)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            require(sha(target) == digest, 'Inherited compiled copy changed')
        require(not (project / '.lake/build/lib/lean/DenominatorAffine').exists(), 'New proof cache must be empty')
        protected = {p.relative_to(project).as_posix(): sha(p) for p in project.rglob('*')
                     if p.is_file() and '.lake' not in p.relative_to(project).parts}
        legacy.save_json(run.evidence / 'candidate-inputs.json', protected)
        shutil.copyfile(args.cache_receipt, run.evidence / 'inherited-cache-identity.json')
        shutil.copyfile(verify.MANIFEST, run.evidence / 'source-manifest.json')
        shutil.copyfile(HERE / 'config.json', run.evidence / 'config.json')
        run.receipt.update(dependencies={'revisions': revisions, 'packages': str(packages),
            'scope': 'Pinned tracked sources checked; existing upstream compiled cache reused'},
            candidate={'initial_denominator_compiled_modules': 0, 'inherited_source_count': len(cache['sources']),
                       'inherited_compiled_files': len(cache['cache'])})
        run.flush()
        shutil.copyfile(HERE / 'support/retain-export.py', run.work / 'retain-export.py')
        with (run.evidence / 'retention.log').open('w') as output:
            watcher = subprocess.Popen([sys.executable, run.work / 'retain-export.py'], stdout=output, stderr=subprocess.STDOUT)
        run.receipt['phase'] = 'fresh-denominator-build-comparison-and-kernels'
        code, output = run.command('six-target-comparison', legacy.proof_command(run, project),
                                  cwd=project, allow_failure=True, timeout=legacy.RUNTIME + 60)
        legacy.check_proof_output(code, output, config['theorem_names'])
        watcher.wait(timeout=60)
        require(watcher.returncode == 0, 'Actual Comparator export retention failed')
        retained = json.loads((run.evidence / 'retained-export.json').read_text())
        export = run.evidence / 'solution-export.ndjson'
        require(sha(export) == retained['sha256'], 'Retained export identity changed')
        require(retained['checker_config']['unpermitted_axiom_hard_error'] is True, 'Hard axiom rejection disabled')
        run.receipt['checks']['semantic-comparison-primary-kernels'] = 'passed'
        run.receipt['phase'] = 'retained-export-inventory'
        inventory = inventory_export.inspect(export, inventory_export.PUBLIC + config['theorem_names'])
        legacy.save_json(run.evidence / 'export-inventory.json', inventory)
        run.receipt['export'] = {'sha256': inventory['export_sha256'], 'bytes': inventory['bytes'],
                                 'public_targets': len(inventory_export.PUBLIC), 'comparison_targets': len(config['theorem_names'])}
        run.receipt['checks']['retained-export-inventory'] = 'passed'
        run.receipt['phase'] = 'same-byte-direct-replays'
        controls_path = args.stock_root / 'stock-controls/receipt.json'
        controls = json.loads(controls_path.read_text())
        require(controls['status'] == 'passed', 'Stock body controls did not pass')
        stock = args.stock_root / 'stock-reader/.lake/build/bin/kernel'
        require(sha(stock) == controls['inputs']['stock-reader/.lake/build/bin/kernel'], 'Stock reader changed')
        require(sha(Path(run.env['COMPARATOR_NANODA'])) == controls['binaries'][run.env['COMPARATOR_NANODA']], 'Nanoda controls used another binary')
        for entry in controls['commands']:
            require(sha(controls_path.parent / entry['log']) == entry['sha256'], 'Control evidence changed')
        run.receipt['body_controls'] = {'receipt_sha256': sha(controls_path), 'stock_sha256': sha(stock)}
        nanoda_config = run.evidence / 'nanoda-same-byte.json'
        legacy.save_json(nanoda_config, dict(retained['checker_config'], export_file_path=str(export),
                                            print_success_message=True, print_axioms=False))
        _, output = run.command('nanoda-same-byte', [run.env['COMPARATOR_NANODA'], nanoda_config], timeout=18000)
        require('no errors' in output, 'Nanoda acceptance diagnostic missing')
        require(sha(export) == inventory['export_sha256'], 'Export changed during Nanoda replay')
        run.receipt['checks']['nanoda-same-byte'] = 'passed'
        _, output = run.command('stock-lean-4.34.1-same-byte', [stock, export], timeout=18000)
        require('Accepted ' in output and ' declarations.' in output, 'Stock acceptance diagnostic missing')
        require(sha(export) == inventory['export_sha256'], 'Export changed during stock replay')
        run.receipt['checks']['stock-lean-same-byte'] = 'passed'
        require(all(sha(project / n) == h for n, h in protected.items()), 'Candidate source changed')
        verify.check_inputs()
        legacy.collect(run, required=False)
        run.collect(required=True)
        run.receipt['checks']['protected-inputs'] = 'passed'
        run.receipt.update(status='passed', phase='complete')
    except Exception as error:
        run.receipt.update(status='failed', error=f'{type(error).__name__}: {error}')
        print(run.receipt['error'], flush=True)
        try:
            legacy.collect(run)
        except Exception as extra:
            run.receipt['collection_error'] = str(extra)
    finally:
        if watcher is not None and watcher.poll() is None:
            watcher.terminate()
            watcher.wait(timeout=10)
        run.receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        run.flush()
    return 0 if run.receipt['status'] == 'passed' else 1


if __name__ == '__main__':
    if not sys.flags.isolated:
        raise SystemExit('Use python3 -I run_local.py')
    raise SystemExit(main())

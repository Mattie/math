"""Adapt the reviewed affine verifier to a separately frozen cubic overlay.

Preparation commands do not execute Lean or access the network. --run is the
fresh-source hosted route, requiring an explicit reviewed freeze first.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
OVERLAY = REPO / 'formalizations/AffineCubic'
LEGACY_PATH = REPO / 'verification/isolated-affine/verify.py'
LEGACY_SHA256 = '6f423aa99edb7d57ff9f0a8c42a7dbc3a55b5a1c0dae7922ffe046f83633d392'
MANIFEST = HERE / 'source-manifest.json'
WORKFLOW = REPO / '.github/workflows/isolated-irrationality.yml'
SPEC_FILES = ('Challenge.lean', 'Solution.lean', 'config.json', 'pins.json')


def digest(path):
    """Hash bytes without normalizing source or line endings."""
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def load_legacy():
    """Authenticate the adapter dependency before executing its Python code."""
    if LEGACY_PATH.is_symlink() or digest(LEGACY_PATH) != LEGACY_SHA256:
        raise RuntimeError('Reviewed affine runner changed before import')
    spec = importlib.util.spec_from_file_location('cubic_affine_legacy', LEGACY_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


legacy = load_legacy()
require = legacy.require


def inventory():
    """Validate old frozen sources and identify the independent new overlay."""
    pins, old_files, _ = legacy.check_inputs()
    require(json.loads((HERE / 'pins.json').read_text()) == pins, 'Dedicated pins differ')
    inherited = {n: sha for n, sha in old_files.items()
                 if n.endswith('.lean') and n not in ('Challenge.lean', 'Solution.lean')}
    root = OVERLAY / 'AffineCubic'
    require(root.is_dir() and not root.is_symlink(), 'Missing cubic source module tree')
    overlay = {p.relative_to(OVERLAY).as_posix(): digest(legacy.regular(OVERLAY, p.relative_to(OVERLAY).as_posix()))
               for p in root.rglob('*.lean')}
    require('AffineCubic/Pilot.lean' in overlay, 'Pilot source is not present')
    require(not set(inherited) & set(overlay), 'Overlay shadows inherited source')
    return {'inherited': inherited, 'overlay': overlay,
            'specification': {n: digest(legacy.regular(HERE, n)) for n in SPEC_FILES},
            'legacy_runner_sha256': LEGACY_SHA256}


def check_inputs():
    """Fail closed until reviewed source identities have been explicitly frozen."""
    require(MANIFEST.is_file(), 'Source freeze pending: review endpoints before --freeze')
    frozen = json.loads(MANIFEST.read_text())
    require(inventory() == frozen, 'Frozen cubic inputs changed; investigate before refreezing')
    config = json.loads((HERE / 'config.json').read_text())
    targets = ['AffineCubicVerification.' + suffix for suffix in
               ('eventual_lower_bound', 'irrational', 'irrationality_exponent_le_six', 'not_liouvilleWith')]
    require(config == {'challenge_module': 'Challenge', 'solution_module': 'Solution',
                       'theorem_names': targets, 'permitted_axioms': legacy.preflight.AXIOMS,
                       'enable_nanoda': True}, 'Unexpected target or axiom policy')
    return frozen, config


def stage_sources(destination, frozen, *, package=False):
    """Construct frozen candidate sources, never copying candidate build code/cache."""
    if package:
        pins = json.loads((HERE / 'pins.json').read_text())
        legacy.project(destination, legacy.SOURCE, pins['mathlib'],
            ['OAI', 'Logarithm', 'AlgebraicLog', 'PairedAffine', 'StandardBridge',
             'AffineCubic', 'Challenge', 'Solution'])
    else:
        destination.mkdir()
    files = {}
    for section, origin in [('inherited', legacy.SOURCE), ('overlay', OVERLAY)]:
        for name, sha in frozen[section].items():
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(legacy.regular(origin, name), target)
            require(digest(target) == sha, 'Source changed during copy: ' + name)
            files[name] = sha
    for name in ('Challenge.lean', 'Solution.lean', 'config.json'):
        shutil.copyfile(legacy.regular(HERE, name), destination / name)
        files[name] = frozen['specification'][name]
        require(digest(destination / name) == files[name], 'Specification changed during copy')
    for name in ('lake-manifest.json', 'lean-toolchain'):
        shutil.copyfile(legacy.SOURCE / name, destination / name)
    (destination / 'evidence').mkdir()
    legacy.save_json(destination / 'evidence/source-sha256.json', files)
    return files


def memory_snapshot(path=Path('/proc/meminfo')):
    """Record value-only Linux capacity observations, not a proof-fit guarantee."""
    wanted = {'MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree'}
    values = {}
    for line in path.read_text().splitlines():
        name, _, rest = line.partition(':')
        if name in wanted:
            fields = rest.split()
            require(len(fields) == 2 and fields[1] == 'kB', 'Unexpected memory diagnostic units')
            values[name + '_bytes'] = int(fields[0]) * 1024
    require(len(values) == len(wanted), 'Missing memory/swap diagnostics')
    return values


def run_hosted(work):
    """Use the reviewed fresh-source route with this target and independent challenge."""
    frozen, config = check_inputs()
    pins = json.loads((HERE / 'pins.json').read_text())
    legacy.preflight.PINS = HERE / 'pins.json'
    run = legacy.Preflight(legacy.fresh_work(work))
    run.receipt.update(scope='Fresh isolated cubic affine general theorem and pilot source; four exact wrappers',
        evidence_kind='fresh execution', targets=config['theorem_names'],
        runner_sha256=digest(Path(__file__)), source_manifest_sha256=digest(MANIFEST),
        soundness_version_assessment='verification/isolated-affine-cubic/CHECKERS.md, 2026-10-13',
        resources={'runtime_seconds': legacy.RUNTIME, 'memory_max': '12G',
                   'cpu_quota': '400%', 'lean_num_threads': 4},
        check_key_scope={'affine': 'All four AffineCubicVerification wrappers'},
        workflow_ref=os.environ.get('GITHUB_WORKFLOW_REF'))
    runner_identity = {p: digest(p) for p in (Path(__file__), MANIFEST, HERE / 'pins.json',
                                             LEGACY_PATH, HERE / 'CHECKERS.md',
                                             HERE / 'hosted-workflow.yml',
                                             WORKFLOW)}
    run.receipt['workflow_sha256'] = runner_identity[HERE / 'hosted-workflow.yml']
    run.receipt['dispatch_workflow_sha256'] = runner_identity[WORKFLOW]
    original_source, original_project, original_pins = legacy.SOURCE, legacy.project, legacy.PINS
    try:
        staged = run.work / 'frozen-sources'
        files = stage_sources(staged, frozen)
        legacy.SOURCE, legacy.PINS = staged, HERE / 'pins.json'

        def project(path, source, mathlib, libraries):
            if 'PairedAffine' in libraries:
                libraries = [*libraries, 'AffineCubic']
            original_project(path, source, mathlib, libraries)

        legacy.project = project
        run.env['LEAN_NUM_THREADS'] = '4'
        run.receipt['memory_capacity'] = {'before_setup': memory_snapshot(),
            'scope': 'Host memory/swap observations only; no guarantee that the clean source build fits.',
            'proof_memory_max': '12G'}
        legacy.shared.check_capacity(run, 'setup', legacy.shared.SETUP_GIB)
        run.receipt['phase'] = 'tools-and-controls'
        run.setup()
        for fixture in ('valid', 'mismatch', 'axiom'):
            run.fixture(fixture)
        legacy.imported_admission(run)
        run.receipt['phase'] = 'trusted-dependencies'
        packages, dependency_identity = legacy.prepare_dependencies(run, pins)
        path, protected = legacy.prepare_candidate(run, pins, files, packages)
        run.receipt['memory_capacity']['before_proof'] = memory_snapshot()
        legacy.shared.check_capacity(run, 'proof', legacy.shared.PROOF_GIB)
        run.receipt['phase'] = 'candidate-comparison-and-kernels'
        code, output = run.command('cubic-affine-comparator', legacy.proof_command(run, path),
                                   cwd=path, allow_failure=True, timeout=legacy.RUNTIME + 60)
        legacy.check_proof_output(code, output, config['theorem_names'])
        actual = {p.relative_to(path).as_posix(): digest(p) for p in path.rglob('*')
                  if p.is_file() and '.lake' not in p.relative_to(path).parts}
        require(actual == protected, 'Candidate input inventory changed')
        require(all(digest(legacy.regular(path, n)) == h for n, h in protected.items()), 'Candidate input replaced')
        require(legacy.tree_identity(packages) == dependency_identity, 'Dependencies changed')
        legacy.SOURCE = original_source
        check_inputs()
        require(all(digest(p) == sha for p, sha in runner_identity.items()), 'Verifier inputs changed')
        require(all(digest(Path(b['path'])) == b['sha256'] for b in run.receipt['binaries'].values()),
                'Checker binary changed')
        run.receipt['checks'].update(affine='passed', **{'protected-inputs': 'passed'})
        require(run.receipt['checks'] == dict.fromkeys(legacy.EXPECTED_CHECKS, 'passed'), 'Incomplete checks')
        legacy.collect(run, required=True)
        preparation = run.evidence / 'preparation'
        preparation.mkdir()
        for source in (Path(__file__), MANIFEST, HERE / 'CHECKERS.md',
                       HERE / 'hosted-workflow.yml', WORKFLOW):
            destination = preparation / source.name
            shutil.copyfile(source, destination)
            run.receipt['retained_files'][destination.relative_to(run.evidence).as_posix()] = digest(destination)
        run.receipt.update(status='passed', phase='complete')
    except Exception as error:
        run.receipt.update(status='failed', error=f'{type(error).__name__}: {error}')
        try:
            legacy.collect(run)
        except Exception as collection_error:
            run.receipt['collection_error'] = str(collection_error)
    finally:
        legacy.SOURCE, legacy.project, legacy.PINS = original_source, original_project, original_pins
        run.receipt['finished_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        run.flush()
    return 0 if run.receipt['status'] == 'passed' else 1


def main():
    """Freeze once, validate without execution, or perform an authorized source run."""
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--freeze', action='store_true')
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--work-dir', type=Path)
    args = parser.parse_args()
    if args.freeze:
        frozen = inventory()
        with MANIFEST.open('x', encoding='utf-8') as stream:
            json.dump(frozen, stream, indent=2)
            stream.write('\n')
        print('Source identity frozen; this is not proof acceptance.')
        return 0
    if args.check:
        check_inputs()
        print('Frozen preparation inputs match; no proof execution performed.')
        return 0
    require(args.work_dir is not None, '--run requires --work-dir')
    return run_hosted(args.work_dir)


if __name__ == '__main__':
    if not sys.flags.isolated:
        raise SystemExit('Use python3 -I verification/isolated-affine-cubic/verify.py')
    raise SystemExit(main())

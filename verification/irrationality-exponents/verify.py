"""Reproduce the four frozen statements with Comparator and independent Nanoda checking.

Only the requested working directory receives builds, downloads, caches and results.
The source checkout is read-only input. This is not a hostile-code sandbox.
"""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
AXIOMS = ['propext', 'Quot.sound', 'Classical.choice']
# This list matches the maintained comparator at the revision in pins.json.
PRIMITIVES = AXIOMS + ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind',
    'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod',
    'Nat.beq', 'Nat.ble', 'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft',
    'Nat.shiftRight', 'String.ofList', 'Char.ofNat', 'List', 'eagerReduce',
    'Nat', 'String', 'String.mk', 'Char', 'optParam', 'autoParam', 'semiOutParam', 'outParam']


def digest(path):
    """Hash an artifact without loading it into memory."""
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def save_json(path, value):
    """Replace a small receipt atomically so interruption cannot leave truncated JSON."""
    path = Path(path)
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')
    temporary.replace(path)


def validate_sources(repo, cases):
    """Check every frozen input before any source is built or downloaded."""
    for case in cases.values():
        for relative, expected in case['files'].items():
            path = repo / case['package'] / relative
            if not path.is_file() or digest(path) != expected:
                raise ValueError(f'Frozen source mismatch: {path}')


def inventory(path, target, lean_commit):
    """Inventory names and declarations while hashing the complete checked export."""
    names, axioms, unsafe, partial = {0: ''}, [], [], []
    count, found, meta = 0, False, None
    sha = hashlib.sha256()
    with path.open('rb') as stream:
        for line in stream:
            sha.update(line)
            # Expression/universe nodes have no declaration metadata. Nanoda parses
            # every node; avoid decoding them again for this independent inventory.
            if not any(key in line for key in (b'"in":', b'"meta":', b'"axiom":',
                       b'"def":', b'"thm":', b'"opaque":', b'"quot":', b'"inductive":')):
                continue
            item = json.loads(line)
            if 'meta' in item:
                meta = item['meta']
            if 'in' in item:
                data = item.get('str', item.get('num'))
                prefix = names[data['pre']]
                names[item['in']] = prefix + ('.' if prefix else '') + str(data.get('str', data.get('i')))
            declarations = []
            for kind in ('axiom', 'def', 'thm', 'opaque', 'quot'):
                if kind in item:
                    declarations.append(item[kind])
                    if kind == 'axiom':
                        axioms.append(names[item[kind]['name']])
            if 'inductive' in item:
                for kind in ('types', 'ctors', 'recs'):
                    declarations.extend(item['inductive'][kind])
            for declaration in declarations:
                count += 1
                name = names[declaration['name']]
                found |= name == target
                if declaration.get('isUnsafe') or declaration.get('safety') == 'unsafe':
                    unsafe.append(name)
                if declaration.get('safety') == 'partial':
                    partial.append(name)
    if not found or set(axioms) != set(AXIOMS) or unsafe or partial:
        raise ValueError(f'Export inventory failed: target={found}, axioms={axioms}, unsafe={unsafe}, partial={partial}')
    if not meta or meta['lean']['githash'] != lean_commit:
        raise ValueError('Export Lean revision differs from pin')
    return dict(sha256=sha.hexdigest(), bytes=path.stat().st_size, declarations=count,
                target=target, axioms=sorted(axioms), unsafe=unsafe, partial=partial, metadata=meta)


class Run:
    """Own one fresh run and its evidence; no previous result is used as acceptance."""
    def __init__(self, work, pins, selected):
        self.work, self.pins, self.selected = work, pins, selected
        (work / 'runs').mkdir(parents=True, exist_ok=True)
        stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ-')
        self.root = Path(tempfile.mkdtemp(prefix=stamp, dir=work / 'runs'))
        self.logs = self.root / 'logs'
        self.logs.mkdir()
        self.env = dict(os.environ)
        for key in list(self.env):
            if key.startswith(('LEAN_', 'LAKE_', 'ELAN_', 'CARGO_', 'RUSTUP_')):
                self.env.pop(key)
        self.env['PATH'] = '/usr/local/bin:/usr/bin:/bin'
        self.env['LEAN_NUM_THREADS'] = '4'
        for key, folder in [('CARGO_HOME', 'cargo'), ('RUSTUP_HOME', 'rustup'),
                            ('MATHLIB_CACHE_DIR', 'mathlib-cache'), ('ELAN_HOME', 'elan')]:
            self.env[key] = str(work / folder)
        self.receipt = dict(schema_version=1, status='running', selected_cases=selected,
            audited_revision=pins['audited_revision'], started_utc=dt.datetime.now(dt.timezone.utc).isoformat(),
            inputs={}, tools={}, cases={}, controls={}, commands=[],
            scope='Frozen source inputs; official dependency caches allowed; no hostile-code sandbox or full dependency rebuild.')
        self.receipt['cache_provenance'] = {
            'work_directory': str(work),
            'preexisting': {name: (work / name).exists() for name in
                ['tools', 'cargo', 'rustup', 'mathlib-cache']},
            'dependencies': 'Fresh checkout per run; official Mathlib artifacts may be reused from work_directory/mathlib-cache',
            'results': 'Fresh run directory; prior results never used for acceptance',
            'lean_num_threads': 4,
        }
        self.flush()

    def flush(self):
        """Persist current status; only finish() may mark it passed."""
        save_json(self.root / 'receipt.json', self.receipt)

    def command(self, args, label, cwd=None, env=None, output=None, reject=None):
        """Record a command and require success or a specific expected rejection."""
        print(f'[{label}]', flush=True)
        log = self.logs / f'{label}.log'
        actual_env = self.env | (env or {})
        command = [str(arg) for arg in args]
        started = dt.datetime.now(dt.timezone.utc).isoformat()
        with log.open('wb') as errors:
            if output is None:
                result = subprocess.run(command, cwd=cwd, env=actual_env, stdout=errors, stderr=subprocess.STDOUT)
            else:
                with Path(output).open('wb') as stream:
                    result = subprocess.run(command, cwd=cwd, env=actual_env, stdout=stream, stderr=errors)
        record = dict(label=label, argv=command, cwd=str(cwd or Path.cwd()), exit_code=result.returncode,
                      started_utc=started, finished_utc=dt.datetime.now(dt.timezone.utc).isoformat(),
                      log=str(log.relative_to(self.root)))
        self.receipt['commands'].append(record)
        self.flush()
        if reject:
            text = log.read_text(errors='replace')
            if result.returncode == 0 or result.returncode < 0 or not re.search(reject, text):
                raise RuntimeError(f'{label}: expected diagnostic rejection not observed; see {log}')
        elif result.returncode:
            raise RuntimeError(f'{label}: exit {result.returncode}; see {log}')
        return log

    def checkout(self, name, url, revision):
        """Use pinned source in our tool directory; never move a user's checkout."""
        path = self.work / 'tools' / name
        if not path.exists():
            self.command(['git', 'clone', '--no-checkout', url, path], f'clone-{name}')
        self.command(['git', 'checkout', '--detach', revision], f'pin-{name}', cwd=path)
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], env=self.env, text=True).strip()
        if actual != revision:
            raise ValueError(f'Unexpected {name} revision')
        changed = subprocess.check_output(['git', 'diff', '--name-only', revision],
            cwd=path, env=self.env, text=True).splitlines()
        allowed = {'lakefile.toml', 'lake-manifest.json'} if name == 'comparator' else set()
        if set(changed) - allowed:
            raise ValueError(f'Modified cached {name} sources: {changed}')
        untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'],
            cwd=path, env=self.env, text=True).splitlines()
        if set(untracked) - ({'AuditNative.lean'} if name == 'comparator' else set()):
            raise ValueError(f'Unexpected cached {name} sources: {untracked}')
        return path

    def tools(self):
        """Build pinned tools using only this work directory and system prerequisites."""
        tools = self.work / 'tools'
        tools.mkdir(exist_ok=True)
        version = self.pins['lean_version']
        lean = tools / f'lean-{version}-linux'
        archive = tools / f'lean-{version}-linux.zip'
        if not archive.exists() or digest(archive) != self.pins['lean_archive_sha256']:
            self.command(['curl', '-fL', '--retry', '3', '-o', str(archive) + '.part',
                f'https://github.com/leanprover/lean4/releases/download/v{version}/{archive.name}'], 'download-lean')
            if digest(Path(str(archive) + '.part')) != self.pins['lean_archive_sha256']:
                raise ValueError('Lean archive digest mismatch')
            Path(str(archive) + '.part').replace(archive)
        if not (lean / 'bin/lean').exists():
            self.command(['unzip', '-q', archive, '-d', tools], 'extract-lean')
        self.env['PATH'] = f'{lean}/bin:{self.env["CARGO_HOME"]}/bin:/usr/local/bin:/usr/bin:/bin'
        version_log = self.command(['lean', '--version'], 'lean-version')
        if self.pins['lean_commit'] not in version_log.read_text():
            raise ValueError('Unexpected Lean binary revision')
        rustup = Path(self.env['CARGO_HOME']) / 'bin/rustup'
        if not rustup.exists():
            installer = tools / 'rustup-init'
            self.command(['curl', '-fL', '--retry', '3', '-o', installer,
                'https://static.rust-lang.org/rustup/dist/x86_64-unknown-linux-gnu/rustup-init'], 'download-rustup')
            installer.chmod(0o755)
            self.command([installer, '-y', '--no-modify-path', '--profile', 'minimal',
                          '--default-toolchain', self.pins['rust']], 'install-rust')
        self.env['RUSTUP_TOOLCHAIN'] = self.pins['rust']
        self.command([rustup, 'toolchain', 'install', self.pins['rust'], '--profile', 'minimal'], 'pin-rust')
        self.command(['rustc', '--version'], 'rust-version')
        nano = self.checkout('nanoda', 'https://github.com/ammkrn/nanoda_lib', self.pins['nanoda'])
        self.command(['cargo', 'build', '--release', '--locked'], 'build-nanoda', cwd=nano)
        exporter = self.checkout('lean4export', 'https://github.com/leanprover/lean4export', self.pins['exporter'])
        self.command(['lake', 'build'], 'build-exporter', cwd=exporter)
        comp = self.checkout('comparator', 'https://github.com/leanprover/comparator', self.pins['comparator'])
        # Only local build configuration is extended. Comparator implementation stays pinned.
        lakefile = subprocess.check_output(['git', 'show', 'HEAD:lakefile.toml'], cwd=comp, env=self.env, text=True)
        lakefile = lakefile.replace('rev = "master"', f'rev = "{self.pins["exporter"]}"')
        (comp / 'lakefile.toml').write_text(lakefile + '\n[[lean_exe]]\nname = "audit-native"\nroot = "AuditNative"\n')
        shutil.copyfile(HERE / 'AuditNative.lean', comp / 'AuditNative.lean')
        packages = comp / '.lake/packages'
        packages.mkdir(parents=True, exist_ok=True)
        if not (packages / 'lean4export').exists():
            (packages / 'lean4export').symlink_to(exporter, target_is_directory=True)
        save_json(comp / 'lake-manifest.json', dict(version='1.2.0', packagesDir='.lake/packages',
            packages=[dict(url='https://github.com/leanprover/lean4export', type='git', subDir=None,
              scope='leanprover', rev=self.pins['exporter'], name='lean4export', manifestFile='lake-manifest.json',
              inputRev=self.pins['exporter'], inherited=False, configFile='lakefile.toml')],
            name='Comparator', lakeDir='.lake', fixedToolchain=False))
        self.command(['lake', 'build', 'audit-native'], 'build-comparator', cwd=comp)
        self.exporter = exporter / '.lake/build/bin/lean4export'
        self.nanoda = nano / 'target/release/nanoda_bin'
        self.comparator = comp / '.lake/build/bin/audit-native'
        for name, path in [('lean', lean / 'bin/lean'), ('exporter', self.exporter),
                           ('nanoda', self.nanoda), ('comparator', self.comparator)]:
            self.receipt['tools'][name] = dict(path=str(path), sha256=digest(path))
        self.receipt['tool_pins'] = {k: v for k, v in self.pins.items() if k != 'cases'}
        self.flush()

    def snapshot_configuration(self):
        """Freeze verified configuration before tool setup; later projects never read the checkout."""
        case = self.pins['cases'][self.selected[0]]
        snapshot = self.root / 'configuration'
        snapshot.mkdir()
        for file in ['lake-manifest.json', 'lean-toolchain']:
            shutil.copyfile(REPO / case['package'] / 'lean' / file, snapshot / file)
            if digest(snapshot / file) != case['files'][f'lean/{file}']:
                raise ValueError(f'Frozen configuration mismatch: {file}')
        self.configuration = snapshot
        self.expected_lock = json.loads((snapshot / 'lake-manifest.json').read_text())

    def project(self, path, libraries, dependencies=None):
        """Create an isolated project using the frozen Mathlib lock, without OAI in challenges."""
        path.mkdir(parents=True, exist_ok=True)
        case = self.pins['cases'][self.selected[0]]
        for file in ['lake-manifest.json', 'lean-toolchain']:
            shutil.copyfile(self.configuration / file, path / file)
            if digest(path / file) != case['files'][f'lean/{file}']:
                raise ValueError(f'Frozen configuration mismatch: {file}')
        (path / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage FrozenVerification where\n'
            '  fixedToolchain := true\n  leanOptions := #[⟨`autoImplicit, false⟩]\n'
            f'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{self.pins["mathlib"]}"\n'
            + ''.join(f'lean_lib {name}\n' for name in libraries), encoding='utf-8')
        if dependencies:
            (path / '.lake').mkdir(exist_ok=True)
            (path / '.lake/packages').symlink_to(dependencies, target_is_directory=True)
        return path

    def export(self, project, module, target, output, label):
        """Export the target and the complete pinned comparator primitive roots."""
        self.command(['lake', 'env', self.exporter, module, '--', target, *PRIMITIVES],
                     label, cwd=project, output=output)

    def compare(self, challenge, solution, theorem, label, reject=None):
        """Use maintained comparison logic without definition holes."""
        return self.command([self.comparator], label, env=dict(AUDIT_CHALLENGE=str(challenge),
            AUDIT_SOLUTION=str(solution), AUDIT_THEOREM=theorem), reject=reject)

    def check_proof(self, export, label, reject=None):
        """Replay the exact export with a strict foundational-axiom policy."""
        config = dict(export_file_path=str(export), use_stdin=False, permitted_axioms=AXIOMS,
            unpermitted_axiom_hard_error=True, unsafe_permit_all_axioms=False, num_threads=4,
            nat_extension=True, string_extension=True, print_success_message=True,
            print_axioms=True, pp_to_stdout=True)
        path = export.with_suffix('.nanoda.json')
        save_json(path, config)
        log = self.command([self.nanoda, path], label, reject=reject)
        # Exercise the exact success-report contract on the small positive control
        # before spending time on a full source build and its large exports.
        if not reject and not re.search(r'Checked \d+ declarations with no errors', log.read_text()):
            raise RuntimeError(f'{label}: missing clean Nanoda success report; see {log}')
        return log

    def controls(self):
        """Require diagnostic rejections rather than treating any crash as success."""
        root = self.root / 'controls'
        shutil.copytree(HERE / 'controls', root)
        env = dict(LEAN_PATH=str(root))
        modules = ['FixtureChallenge', 'FixturePositive', 'FixtureDefinitionMismatch',
                   'FixtureStatementMismatch', 'FixtureForbiddenAxiom']
        for module in modules:
            self.command(['lean', '-o', f'{module}.olean', f'{module}.lean'], f'control-build-{module}', cwd=root, env=env)
            self.command([self.exporter, module, '--', 'fixture', *PRIMITIVES], f'control-export-{module}',
                         cwd=root, env=env, output=root / f'{module}.ndjson')
        expected = {'FixturePositive': None, 'FixtureDefinitionMismatch': 'Const does not match',
                    'FixtureStatementMismatch': 'theorem statement do not match',
                    'FixtureForbiddenAxiom': 'Illegal axiom detected'}
        for module, rejection in expected.items():
            self.compare(root / 'FixtureChallenge.ndjson', root / f'{module}.ndjson', 'fixture',
                         f'control-compare-{module}', reject=rejection)
        self.check_proof(root / 'positive.ndjson', 'control-nanoda-positive')
        self.check_proof(root / 'ill-typed.ndjson', 'control-nanoda-ill-typed',
                         reject=r'assertion.*failed|type.*mismatch')
        self.check_proof(root / 'FixtureForbiddenAxiom.ndjson', 'control-nanoda-axiom',
                         reject=r'(?i)axiom.*(?:permitted|allowed)|(?:permitted|allowed).*axiom')
        self.receipt['controls'] = {name: 'passed' for name in [*expected, 'nanoda-positive', 'nanoda-ill-typed', 'nanoda-axiom']}
        self.flush()

    def cases(self):
        """Compile frozen solutions once and each independent specification separately."""
        cases = {key: self.pins['cases'][key] for key in self.selected}
        solution = self.root / 'solution'
        solution.mkdir()
        libraries = set()
        for key, case in cases.items():
            for relative, expected in case['files'].items():
                if not relative.endswith('.lean') or relative == 'lean/lakefile.lean':
                    continue
                target = relative.removeprefix('lean/') if relative.startswith('lean/') else 'CertifiedBridge.lean'
                path = solution / target
                path.parent.mkdir(parents=True, exist_ok=True)
                source = REPO / case['package'] / relative
                if path.exists() and digest(path) != expected:
                    raise ValueError(f'Conflicting shared source: {target}')
                shutil.copyfile(source, path)
                if digest(path) != expected:
                    raise ValueError(f'Source changed during snapshot: {source}')
                libraries.add(target.split('/')[0].removesuffix('.lean'))
            self.receipt['inputs'][key] = case
        self.project(solution, sorted(libraries))
        self.command(['lake', 'exe', 'cache', 'get'], 'fetch-mathlib-cache', cwd=solution)
        lock = json.loads((solution / 'lake-manifest.json').read_text())
        if lock['packages'] != self.expected_lock['packages']:
            raise ValueError('Lake changed the frozen dependency lock')
        dependencies = solution / '.lake/packages'
        for package in lock['packages']:
            actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=dependencies / package['name'], env=self.env, text=True).strip()
            if actual != package['rev']:
                raise ValueError(f'Dependency revision mismatch: {package["name"]}')
        self.receipt['dependencies'] = lock
        self.command(['lake', 'build', *[case['module'] for case in cases.values()]], 'build-solutions', cwd=solution)
        for key, case in cases.items():
            folder = self.root / key
            folder.mkdir()
            challenge = self.project(folder / 'challenge', ['Challenge'], dependencies)
            shutil.copyfile(HERE / f'challenges/{key}.lean', challenge / 'Challenge.lean')
            self.command(['lake', 'build', 'Challenge'], f'{key}-build-challenge', cwd=challenge)
            proof_export, spec_export = folder / 'solution.ndjson', folder / 'challenge.ndjson'
            self.export(solution, case['module'], case['theorem'], proof_export, f'{key}-export-solution')
            self.export(challenge, 'Challenge', case['theorem'], spec_export, f'{key}-export-challenge')
            before = digest(proof_export)
            log = self.check_proof(proof_export, f'{key}-nanoda')
            self.compare(spec_export, proof_export, case['theorem'], f'{key}-compare')
            info = inventory(proof_export, case['theorem'], self.pins['lean_commit'])
            if info['sha256'] != before:
                raise ValueError('Solution export changed during checking')
            match = re.search(r'Checked (\d+) declarations with no errors', log.read_text())
            if not match or int(match.group(1)) != info['declarations']:
                raise ValueError('Independent declaration inventory disagrees with Nanoda')
            self.receipt['cases'][key] = info | dict(status='passed', challenge_sha256=digest(spec_export))
            self.flush()

    def finish(self):
        """Success requires all selected cases and every rejection control."""
        if set(self.receipt['cases']) != set(self.selected) or len(self.receipt['controls']) != 7:
            raise RuntimeError('Cannot mark incomplete verification as passed')
        self.receipt['status'] = 'passed'
        self.receipt['finished_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
        self.flush()


def main():
    """Parse the portable interface and preserve a failed receipt on every run error."""
    pins = json.loads((HERE / 'pins.json').read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=['all', *pins['cases']], default='all')
    parser.add_argument('--work-dir', required=True, type=Path)
    args = parser.parse_args()
    work = args.work_dir.expanduser().resolve()
    if not args.work_dir.is_absolute() or work == REPO or REPO in work.parents:
        parser.error('--work-dir must be an absolute directory outside the checkout')
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        parser.error('This pinned toolchain supports x86_64 Linux/WSL')
    for tool in ['bash', 'git', 'curl', 'unzip', 'cc', 'make']:
        if not shutil.which(tool):
            parser.error(f'Missing prerequisite: {tool}')
    work.mkdir(parents=True, exist_ok=True)
    filesystem = subprocess.check_output(['stat', '-f', '-c', '%T', str(work)], text=True).strip()
    if filesystem in ('9p', 'drvfs', 'vfat', 'fuseblk'):
        parser.error('Use a native Linux filesystem for --work-dir')
    # Prevent simultaneous writes to shared tool checkouts within one work directory.
    import fcntl
    with (work / '.lock').open('w') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            parser.error('Another verification process owns this work directory')
        selected = list(pins['cases']) if args.case == 'all' else [args.case]
        run = Run(work, pins, selected)
        print(f'Evidence: {run.root}', flush=True)
        try:
            validate_sources(REPO, {key: pins['cases'][key] for key in selected})
            run.snapshot_configuration()
            run.receipt['workflow_sha256'] = {str(p.relative_to(HERE)): digest(p)
                for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
            run.tools()
            run.controls()
            run.cases()
            run.finish()
        except BaseException as error:
            run.receipt['status'] = 'failed'
            run.receipt['error'] = str(error) or type(error).__name__
            run.flush()
            print(f'FAILED: {error}\nEvidence: {run.root}', file=sys.stderr)
            return 1
        print(f'PASSED: {run.root / "receipt.json"}', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())

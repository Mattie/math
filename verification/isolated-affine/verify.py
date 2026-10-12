"""Prepare the frozen affine package for an explicitly authorized hosted source run.

Reuse the reviewed preflight and FC 6942 boundary/resource helpers. Importing this
module and running preparation tests never downloads tools or executes Lean.
"""
from __future__ import annotations

import sys

if __name__ == '__main__' and not sys.flags.isolated:
    raise SystemExit('Run this verifier with Python isolated mode: python3 -I verification/isolated-affine/verify.py')

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SOURCE = REPO / "formalizations/AffineLogarithms"
EXPECTED_CHECKS = {"tools", "isolation", "valid", "mismatch", "axiom",
                   "imported-admission", "dependencies", "affine", "protected-inputs"}
RUNTIME = 18000
BASELINE = {
    "verification/publication/prepare-independent-runner.sh": "3de51c75b00b595d30816bb643e61e7219ab9d611b39375762d0aa8855ed511c",
    "verification/isolated-6942/verify.py": "061475aa32588afce34d68e16e19763b5ec086602235e088f3f47874be183b47",
    "verification/isolated-preflight/preflight.py": "b6149c3a2265533769fdf3eade0c56b1bcd94c8ad3d128570ce1eca7eefbd1f8",
    "verification/isolated-preflight/boundary_probe.c": "1cf5105b89fa6207d4b5f8cc8d6c4b57370e91263abe82c81ed29c159fdd32ab",
    "formalizations/AffineLogarithms/evidence/source-sha256.json": "88516799eccd19825089e8e71ef84ebacb87d8a16174c0069b4cabe114089cb1",
    "formalizations/AffineLogarithms/lakefile.lean": "15bb452678fa3b3127edac380e487610012b8bfc307cd7925eb774dfc35229af",
    "formalizations/AffineLogarithms/lake-manifest.json": "75bef2b97ca07c8973031212031f4936198f4c2465459898cf5e6d75f3d5824d",
    "formalizations/AffineLogarithms/lean-toolchain": "d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b",
    "formalizations/AffineLogarithms/evidence/checker-receipt.json": "9647f2cde1d4f8e49f02b78d458f3155e80913bbc5278ae61e16c36ccf78aee6",
    "formalizations/AffineLogarithms/CHECKERS.md": "b62377391081d54799d2f48fdb7a826384b7eb52cab33b9678be150db39a2340",
}


def load_shared():
    """Authenticate both executable helpers before either module can run."""
    helpers = {
        'preflight': 'verification/isolated-preflight/preflight.py',
        'affine_shared_6942': 'verification/isolated-6942/verify.py',
    }
    for name in helpers.values():
        path = REPO / name
        if not path.is_file() or any(p.is_symlink() for p in (path, *path.parents)):
            raise RuntimeError('Unsafe helper path: ' + name)
        if hashlib.sha256(path.read_bytes()).hexdigest() != BASELINE[name]:
            raise RuntimeError('Reviewed helper changed before import: ' + name)
    loaded = {}
    for module_name, name in helpers.items():
        spec = importlib.util.spec_from_file_location(module_name, REPO / name)
        module = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = module
        spec.loader.exec_module(module)
        loaded[module_name] = module
    return loaded['preflight'], loaded['affine_shared_6942']


preflight, shared = load_shared()
# The dedicated affine process uses its own pins without changing shared files.
PINS = HERE / 'pins.json'
preflight.PINS = PINS
Preflight = preflight.Preflight
digest, require, regular = shared.digest, shared.require, shared.regular
save_json, tree_identity = shared.save_json, shared.tree_identity


def validate_sources(source: Path, files: dict) -> None:
    """Require the frozen inventory, excluding submitted Lake code and caches."""
    expected = {name for name in files if name.endswith(".lean")}
    actual = {p.relative_to(source).as_posix() for p in source.rglob("*.lean")
              if p.relative_to(source).parts[0] not in {".lake", ".work", "replay-reader"}
              and p != source / "lakefile.lean"}
    require(actual == expected, "Frozen Lean inventory has missing or extra files")
    for name, sha in files.items():
        require(digest(regular(source, name)) == sha, f"Frozen source mismatch: {name}")


def check_inputs() -> tuple[dict, dict, dict]:
    """Check source, locks, exact target configuration and historical tool identity."""
    for name, sha in BASELINE.items():
        require(digest(regular(REPO, name)) == sha, f"Reviewed input changed: {name}")
    files = json.loads((SOURCE / "evidence/source-sha256.json").read_text())
    require(len(files) == 969, "Unexpected frozen inventory size")
    validate_sources(SOURCE, files)
    pins = json.loads(PINS.read_text())
    earlier = json.loads((SOURCE / "evidence/checker-receipt.json").read_text())
    for key, value in earlier["pins"].items():
        require(pins[key] == value, f"Affine tool pin mismatch: {key}")
    require(pins["landrun"] == preflight.LANDRUN, "Landrun pin mismatch")
    config = json.loads((SOURCE / "config.json").read_text())
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution"
            and config["theorem_names"] == earlier["targets"] and len(set(earlier["targets"])) == 15
            and set(config["permitted_axioms"]) == set(preflight.AXIOMS)
            and config["enable_nanoda"] is True, "Unexpected affine target/policy")
    require((SOURCE / "lean-toolchain").read_text().strip() == f"leanprover/lean4:v{pins['lean_version']}",
            "Toolchain mismatch")
    lock = json.loads((SOURCE / "lake-manifest.json").read_text())
    require(next(p["rev"] for p in lock["packages"] if p["name"] == "mathlib") == pins["mathlib"],
            "Mathlib pin mismatch")
    return pins, files, config


def project(path: Path, source: Path, mathlib: str, libraries: list[str]) -> None:
    """Generate trusted Lake code; only copy the frozen lock and toolchain."""
    path.mkdir()
    for name in ("lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(regular(source, name), path / name)
    (path / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\npackage QuadraticPeriods where\n'
        '  fixedToolchain := true\n  leanOptions := #[⟨`autoImplicit, false⟩]\n'
        f'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{mathlib}"\n'
        + "".join(f"lean_lib {name}\n" for name in libraries), encoding="utf-8")


def prepare_dependencies(run: Preflight, pins: dict) -> tuple[Path, dict]:
    """Fetch official pinned upstream artifacts before introducing candidate code."""
    bootstrap = run.work / "dependencies"
    project(bootstrap, SOURCE, pins["mathlib"], ["Challenge"])
    shutil.copyfile(SOURCE / "Challenge.lean", bootstrap / "Challenge.lean")
    run.env["MATHLIB_CACHE_DIR"] = str(run.work / "mathlib-cache")
    lake = run.lean / "bin/lake"
    run.command("trusted-mathlib-cache", [lake, "exe", "cache", "get"], cwd=bootstrap, timeout=2400)
    run.command("trusted-mathlib-build", [lake, "build", "Mathlib"], cwd=bootstrap, timeout=2400)
    require(digest(bootstrap / "lake-manifest.json") == digest(SOURCE / "lake-manifest.json"),
            "Trusted setup changed frozen lock")
    packages = bootstrap / ".lake/packages"
    lock = json.loads((bootstrap / "lake-manifest.json").read_text())
    revisions = {}
    for dep in lock["packages"]:
        _, head = run.command(f"dependency-{dep['name']}", ["git", "rev-parse", "HEAD"], cwd=packages / dep["name"])
        require(head.strip() == dep["rev"], f"Dependency revision mismatch: {dep['name']}")
        _, diff = run.command(f"dependency-clean-{dep['name']}", ["git", "diff", "--name-only", "HEAD"],
                              cwd=packages / dep["name"])
        require(not diff.strip(), f"Dependency source changed: {dep['name']}")
        revisions[dep["name"]] = head.strip()
    identity = tree_identity(packages)
    save_json(run.evidence / "dependencies.json", identity)
    run.receipt["dependencies"] = {
        "revisions": revisions, "lock_sha256": digest(bootstrap / "lake-manifest.json"),
        "inventory_sha256": digest(run.evidence / "dependencies.json"),
        "cache": "Official Mathlib cache in trusted project; not a from-source dependency rebuild",
        "access": "Outside candidate writable .lake, symlink exposed read-only by Landrun",
    }
    run.receipt["checks"]["dependencies"] = "passed"
    run.flush()
    return packages, identity


def prepare_candidate(run: Preflight, pins: dict, files: dict, packages: Path) -> tuple[Path, dict]:
    """Copy all frozen candidate/spec bytes into new state, never compiled outputs."""
    path = run.work / "affine"
    project(path, SOURCE, pins["mathlib"],
            ["OAI", "Logarithm", "AlgebraicLog", "PairedAffine", "StandardBridge", "Challenge", "Solution"])
    (path / ".lake").mkdir()
    require(not packages.resolve().is_relative_to((path / ".lake").resolve()),
            "Dependencies must be outside writable candidate state")
    (path / ".lake/packages").symlink_to(packages, target_is_directory=True)
    for name, sha in files.items():
        require(name.endswith(".lean") or name == "config.json", "Unexpected frozen file type")
        destination = path / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(regular(SOURCE, name), destination)
        require(digest(destination) == sha, f"Copied source changed: {name}")
    protected = {p.relative_to(path).as_posix(): digest(p) for p in path.rglob("*")
                 if p.is_file() and ".lake" not in p.relative_to(path).parts}
    inputs = run.evidence / "inputs"
    inputs.mkdir()
    for name in ("Challenge.lean", "Solution.lean", "StandardBridge.lean", "config.json",
                 "lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(path / name, inputs / name)
    shutil.copyfile(SOURCE / "evidence/source-sha256.json", inputs / "source-sha256.json")
    shutil.copyfile(PINS, inputs / "pins.json")
    save_json(inputs / "candidate-files.json", protected)
    return path, protected


def imported_admission(run: Preflight) -> None:
    """Require sorryAx rejection from an imported module in the actual frontend."""
    path = run.work / "imported-admission"
    path.mkdir()
    (path / "lean-toolchain").write_text(f"leanprover/lean4:v{run.receipt['pins']['lean_version']}\n")
    (path / "lakefile.toml").write_text('name = "admission_control"\n'
        '[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Admitted"\n[[lean_lib]]\nname = "Solution"\n')
    (path / "Challenge.lean").write_text("theorem preflight : True := True.intro\n")
    (path / "Admitted.lean").write_text("theorem imported_admitted : True := by sorry\n")
    (path / "Solution.lean").write_text("import Admitted\ntheorem preflight : True := imported_admitted\n")
    save_json(path / "config.json", {"challenge_module": "Challenge", "solution_module": "Solution",
              "theorem_names": ["preflight"], "permitted_axioms": preflight.AXIOMS, "enable_nanoda": True})
    protected = {p.name: digest(p) for p in path.iterdir()}
    run.command("imported-admission-lake-update", [run.lean / "bin/lake", "update"], cwd=path)
    code, output = run.command("imported-admission-comparator",
        preflight.systemd_command(path, run.lean, run.comparator, run.env), cwd=path, allow_failure=True, timeout=360)
    preflight.check_comparator("axiom", code, output)
    require("Illegal axiom detected: 'sorryAx'" in output and "Building Solution" in output,
            "Imported admission did not reach intended actual-route rejection")
    require(all(digest(regular(path, name)) == sha for name, sha in protected.items()),
            "Admission control input changed")
    run.receipt["checks"]["imported-admission"] = "passed"
    run.flush()


def check_proof_output(code: int, output: str, targets: list[str]) -> None:
    """Require both kernels plus the exact target inventory in both exports."""
    preflight.check_comparator("valid", code, output)
    require("Building Challenge" in output and "Building Solution" in output, "Missing source build diagnostics")
    for module in ("Challenge", "Solution"):
        exports = [line for line in output.splitlines() if line.startswith("Exporting #[") and line.endswith(" from " + module)]
        require(len(exports) == 1, f"Missing/ambiguous {module} export")
        names = exports[0].split("#[", 1)[1].split("] from ", 1)[0].split(", ")
        require(all(name in names for name in targets), f"Missing {module} target in export")


def proof_command(run: Preflight, path: Path) -> list[str]:
    """Keep the tested restrictions, with a larger unvalidated fresh-build budget."""
    command = shared.proof_command(run, path)
    command[command.index(f"--property=RuntimeMaxSec={shared.RUNTIME}")] = f"--property=RuntimeMaxSec={RUNTIME}"
    command.insert(1, "--setenv=LEAN_NUM_THREADS=4")
    return command


def collect(run: Preflight, *, required: bool = False) -> None:
    """Retain exact inputs and diagnostics, including partial failed controls."""
    run.collect(required=required)
    fixture = run.work / "imported-admission"
    names = ("Challenge.lean", "Admitted.lean", "Solution.lean", "lakefile.toml", "lean-toolchain", "config.json")
    for name in names:
        src = fixture / name
        require(not required or src.is_file(), f"Missing admission evidence: {name}")
        if src.is_file():
            dest = run.evidence / "fixtures/imported-admission" / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dest)
    if required:
        require((run.evidence / "dependencies.json").is_file() and
                len(list((run.evidence / "inputs").glob("*"))) == 10, "Missing affine input evidence")
    for path in run.evidence.rglob("*"):
        if path.is_file() and path.name not in {"receipt.json", "receipt.tmp", "console.log"}:
            run.receipt["retained_files"][path.relative_to(run.evidence).as_posix()] = digest(path)


def fresh_work(path: Path) -> Path:
    """Permit only workflow bootstrap diagnostics in an otherwise fresh scratch dir."""
    work = shared.validate_work_dir(path)
    if work.exists():
        require(not work.is_symlink() and {p.name for p in work.iterdir()} <= {"evidence"}, "Work directory is not fresh")
        evidence = work / "evidence"
        if evidence.exists():
            require(not evidence.is_symlink() and all(p.is_file() and not p.is_symlink()
                    and p.name in {"started.txt", "capacity.log", "capacity-input.log", "console.log"} for p in evidence.iterdir()),
                    "Unexpected preexisting evidence")
    return work


def main() -> int:
    """Execute the complete hosted route, marking success only after all checks."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    run = Preflight(fresh_work(args.work_dir))
    run.receipt.update(scope="Fresh isolated affine candidate source; 15 targets; trusted official dependency cache", phase="input-validation",
        runner_sha256=digest(Path(__file__)), evidence_kind="fresh execution",
        workflow_ref=os.environ.get("GITHUB_WORKFLOW_REF"),
        soundness_version_assessment="Earlier bounded assessment inspected: formalizations/AffineLogarithms/CHECKERS.md, 2026-10-10 America/Chicago; no new upstream assessment")
    try:
        pins, files, config = check_inputs()
        identities = {name: digest(REPO / name) for name in BASELINE}
        identities.update({p.relative_to(REPO).as_posix(): digest(p) for p in
                           (Path(__file__), PINS, REPO / ".github/workflows/isolated-affine.yml",
                            REPO / ".github/workflows/isolated-irrationality.yml")})
        run.receipt.update(targets=config["theorem_names"], protected_inputs=identities,
                           candidate_compiled_state="Fresh; no candidate compiled artifacts copied")
        run.env["LEAN_NUM_THREADS"] = "4"
        shared.check_capacity(run, "setup", shared.SETUP_GIB)
        run.receipt["phase"] = "tool-setup"
        run.setup()
        run.receipt["phase"] = "boundary-and-controls"
        for fixture in ("valid", "mismatch", "axiom"):
            run.fixture(fixture)
        imported_admission(run)
        run.receipt["phase"] = "trusted-dependencies"
        packages, dependencies = prepare_dependencies(run, pins)
        run.receipt["phase"] = "candidate-preparation"
        path, protected = prepare_candidate(run, pins, files, packages)
        shared.check_capacity(run, "proof", shared.PROOF_GIB)
        run.receipt["resources"].update(runtime_seconds=RUNTIME, memory_max="12G", cpu_quota="400%", lean_num_threads=4)
        run.receipt["phase"] = "candidate-build-comparison-kernels"
        code, output = run.command("affine-comparator", proof_command(run, path),
                                   cwd=path, allow_failure=True, timeout=RUNTIME + 60)
        check_proof_output(code, output, config["theorem_names"])
        run.receipt["phase"] = "protected-inputs-and-evidence"
        actual = {p.relative_to(path).as_posix(): digest(p) for p in path.rglob("*")
                  if p.is_file() and ".lake" not in p.relative_to(path).parts}
        require(actual == protected, "Protected candidate inputs changed")
        require(all(digest(regular(path, name)) == sha for name, sha in protected.items()),
                "Protected candidate input replaced")
        require(tree_identity(packages) == dependencies, "Protected dependencies changed")
        check_inputs()
        require(all(digest(regular(REPO, name)) == sha for name, sha in identities.items()), "Protected runner inputs changed")
        run.receipt["checks"].update(affine="passed", **{"protected-inputs": "passed"})
        require(run.receipt["checks"] == dict.fromkeys(EXPECTED_CHECKS, "passed"), "Incomplete verification")
        collect(run, required=True)
        run.receipt["status"] = "passed"
        run.receipt["phase"] = "complete"
    except Exception as error:
        run.receipt.update(status="failed", error=f"{type(error).__name__}: {error}")
        print(run.receipt["error"], file=sys.stderr)
        try:
            collect(run)
        except Exception as collection_error:
            run.receipt["collection_error"] = str(collection_error)
    finally:
        run.receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        run.flush()
    return 0 if run.receipt["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

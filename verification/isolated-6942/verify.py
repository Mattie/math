"""Prepare trusted dependencies, then check only the frozen FC #6942 wrapper.

Execution is intended for a separately authorized manual hosted Linux run.
Importing this module or running its local tests does not build or download tools.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "isolated-preflight"))
from preflight import Preflight, AXIOMS, digest, require, check_comparator, systemd_command

CASE = "realnorm"
MODULE = "RealNorm.FormalConjectures"
THEOREM = "OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound"
PINS = HERE.parent / "irrationality-exponents/pins.json"
CHALLENGE = HERE.parent / "irrationality-exponents/challenges/realnorm.lean"
# These identify existing inputs; they neither replace nor update their manifests.
BASELINE = {
    "verification/irrationality-exponents/pins.json": "187d40141e389efc7c941e7392d2824f7aea8be9ea128af91050cb96ece3abca",
    "verification/irrationality-exponents/challenges/realnorm.lean": "c8447effa575f6047b60af0b683b00e325bd518ac4c97b739d9788b03e3fdcd4",
    "verification/isolated-preflight/preflight.py": "b6149c3a2265533769fdf3eade0c56b1bcd94c8ad3d128570ce1eca7eefbd1f8",
    "verification/isolated-preflight/boundary_probe.c": "1cf5105b89fa6207d4b5f8cc8d6c4b57370e91263abe82c81ed29c159fdd32ab",
}
RUNTIME = 7200


def save_json(path: Path, value) -> None:
    """Write new run metadata; callers only pass paths in the disposable work area."""
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def regular(root: Path, relative: str) -> Path:
    """Resolve a manifest input without accepting symlinks or path escapes."""
    path = root / relative
    require(not Path(relative).is_absolute() and ".." not in Path(relative).parts,
            f"Unsafe input path: {relative}")
    require(path.is_file() and not any(p.is_symlink() for p in (path, *path.parents)),
            f"Input must be a regular file: {relative}")
    require(path.resolve().is_relative_to(root.resolve()), f"Input escaped root: {relative}")
    return path


def validate_sources(root: Path, case: dict) -> None:
    """Require the complete frozen Lean inventory, including no extra source files."""
    expected = {name for name in case["files"] if name.endswith(".lean")}
    actual = {p.relative_to(root).as_posix() for p in (root / "lean").rglob("*.lean")}
    require(actual == expected, "Frozen Lean inventory has missing or extra files")
    for name, sha in case["files"].items():
        require(digest(regular(root, name)) == sha, f"Frozen source mismatch: {name}")


def check_inputs() -> tuple[dict, dict, Path]:
    """Validate existing pins and source bytes before any tool or dependency setup."""
    for name, sha in BASELINE.items():
        require(digest(regular(REPO, name)) == sha, f"Reviewed input changed: {name}")
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    case = pins["cases"][CASE]
    require((case["module"], case["theorem"]) == (MODULE, THEOREM), "Unexpected proof target")
    root = REPO / case["package"]
    validate_sources(root, case)
    return pins, case, root


def project(path: Path, source: Path, mathlib: str, libraries: list[str]) -> None:
    """Generate reviewed Lake configuration; never execute the submitted lakefile."""
    path.mkdir()
    for name in ("lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(regular(source, "lean/" + name), path / name)
    (path / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\npackage RealNormPort where\n'
        '  fixedToolchain := true\n  leanOptions := #[⟨`autoImplicit, false⟩]\n'
        f'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{mathlib}"\n'
        + "".join(f"lean_lib {name}\n" for name in libraries), encoding="utf-8")


def tree_identity(root: Path) -> dict:
    """Inventory dependency bytes and symlink targets without following symlinks.

Git administrative directories are excluded; pinned Git heads are recorded
separately. Source and compiled dependency files are included.
"""
    result = {}
    for folder, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(name for name in dirs if name != ".git")
        for name in sorted(set(dirs + files)):
            path = Path(folder) / name
            key = path.relative_to(root).as_posix()
            if path.is_symlink():
                result[key] = {"symlink": os.readlink(path)}
            elif path.is_file():
                result[key] = {"sha256": digest(path)}
    require(bool(result), "Empty dependency inventory")
    return result


def proof_command(run: Preflight, path: Path) -> list[str]:
    """Retain the tested invocation, with a larger time budget and memory/CPU caps."""
    args = systemd_command(path, run.lean, run.comparator, run.env)
    args[args.index("--property=RuntimeMaxSec=300")] = f"--property=RuntimeMaxSec={RUNTIME}"
    args[1:1] = ["--property=MemoryMax=12G", "--property=CPUQuota=400%"]
    return args


def prepare_dependencies(run: Preflight, pins: dict, case: dict, source: Path) -> tuple[Path, dict]:
    """Prepare only trusted upstream code before candidate files enter any project."""
    bootstrap = run.work / "dependencies"
    project(bootstrap, source, pins["mathlib"], ["Challenge"])
    shutil.copyfile(CHALLENGE, bootstrap / "Challenge.lean")
    run.env["MATHLIB_CACHE_DIR"] = str(run.work / "mathlib-cache")
    lake = run.lean / "bin/lake"
    run.command("trusted-mathlib-cache", [lake, "exe", "cache", "get"], cwd=bootstrap, timeout=2400)
    run.command("trusted-mathlib-build", [lake, "build", "Mathlib"], cwd=bootstrap, timeout=2400)
    require(digest(bootstrap / "lake-manifest.json") == case["files"]["lean/lake-manifest.json"],
            "Trusted setup changed the frozen dependency lock")
    packages = bootstrap / ".lake/packages"
    lock = json.loads((bootstrap / "lake-manifest.json").read_text())
    for dep in lock["packages"]:
        _, actual = run.command(f"dependency-{dep['name']}", ["git", "rev-parse", "HEAD"],
                                cwd=packages / dep["name"])
        require(actual.strip() == dep["rev"], f"Dependency revision mismatch: {dep['name']}")
        _, diff = run.command(f"dependency-clean-{dep['name']}", ["git", "diff", "--name-only", "HEAD"],
                              cwd=packages / dep["name"])
        require(not diff.strip(), f"Dependency source changed: {dep['name']}")
    identity = tree_identity(packages)
    save_json(run.evidence / "dependencies.json", identity)
    run.receipt["dependencies"] = {
        "lock_sha256": digest(bootstrap / "lake-manifest.json"),
        "inventory_sha256": digest(run.evidence / "dependencies.json"),
        "cache": "Official Mathlib cache fetched in a trusted project containing no candidate sources",
        "access": "Outside candidate .lake; exposed through a read-only symlink under Landrun",
    }
    run.receipt["checks"]["dependencies"] = "passed"
    run.flush()
    return packages, identity


def prepare_candidate(run: Preflight, pins: dict, case: dict, source: Path, packages: Path) -> tuple[Path, dict]:
    """Copy frozen source bytes after dependencies are ready, without compiling them."""
    path = run.work / "realnorm"
    project(path, source, pins["mathlib"], ["Challenge", "OAI", "Logarithm", "RealNorm"])
    (path / ".lake").mkdir()
    (path / ".lake/packages").symlink_to(packages, target_is_directory=True)
    require(not packages.resolve().is_relative_to((path / ".lake").resolve()),
            "Trusted dependencies must be outside candidate writable state")
    for name, sha in case["files"].items():
        if not name.endswith(".lean") or name == "lean/lakefile.lean":
            continue
        require(name.startswith("lean/"), "Unexpected source layout")
        destination = path / name.removeprefix("lean/")
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(regular(source, name), destination)
        require(digest(destination) == sha, f"Copied source changed: {name}")
    shutil.copyfile(CHALLENGE, path / "Challenge.lean")
    save_json(path / "config.json", {"challenge_module": "Challenge", "solution_module": MODULE,
              "theorem_names": [THEOREM], "permitted_axioms": AXIOMS, "enable_nanoda": True})
    protected = {p.relative_to(path).as_posix(): digest(p) for p in path.rglob("*")
                 if p.is_file() and ".lake" not in p.relative_to(path).parts}
    inputs = run.evidence / "inputs"
    inputs.mkdir()
    for name in ("Challenge.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain", "config.json"):
        shutil.copyfile(path / name, inputs / name)
    save_json(inputs / "frozen-case.json", case)
    save_json(inputs / "candidate-files.json", protected)
    return path, protected


def run_proof(run: Preflight, path: Path, protected: dict, packages: Path, dependencies: dict) -> None:
    """Let the stock frontend build/export the challenge before the candidate."""
    free = shutil.disk_usage(run.work).free
    run.receipt["resources"] = {"free_bytes_before_proof": free, "runtime_seconds": RUNTIME,
                                "memory_max": "12G", "cpu_quota": "400%"}
    require(free >= 5 * 1024**3, "Less than 5 GiB free before proof build")
    code, output = run.command("realnorm-comparator", proof_command(run, path),
                               cwd=path, allow_failure=True, timeout=RUNTIME + 60)
    check_comparator("valid", code, output)
    require(THEOREM in output and f"Building {MODULE}" in output, "Expected target missing from diagnostics")
    for name, sha in protected.items():
        require(digest(regular(path, name)) == sha, f"Protected candidate input changed: {name}")
    require(tree_identity(packages) == dependencies, "Protected dependencies changed during proof checking")
    check_inputs()
    run.receipt["checks"]["realnorm"] = "passed"
    run.flush()


def collect(run: Preflight, *, required: bool = False) -> None:
    """Retain small trusted inputs and receipts; never copy candidate build outputs."""
    run.collect(required=required)
    paths = [run.evidence / "dependencies.json"]
    paths.extend((run.evidence / "inputs").glob("*"))
    if required:
        require(len(paths) == 8 and all(p.is_file() for p in paths), "Missing proof input evidence")
    for path in paths:
        if path.is_file():
            run.receipt["retained_files"][path.relative_to(run.evidence).as_posix()] = digest(path)


def validate_work_dir(path: Path) -> Path:
    """Check the disposable directory boundary before creating any run evidence."""
    require(path.is_absolute(), "Use an absolute work directory")
    work = path.resolve()
    require(not work.is_relative_to(REPO.resolve()), "Work directory must be outside the repository")
    runner_temp = os.environ.get("RUNNER_TEMP", "")
    require(bool(runner_temp) and Path(runner_temp).is_absolute(),
            "RUNNER_TEMP must be an absolute directory")
    temp = Path(runner_temp).resolve()
    require(work != temp and work.is_relative_to(temp),
            "Work directory must be a subdirectory of RUNNER_TEMP")
    return work


def main() -> int:
    """Execute only after separate authorization; leave a failed receipt on errors."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    run = Preflight(validate_work_dir(args.work_dir))
    run.receipt["scope"] = "Isolated source verification of FC #6942 only; trusted upstream dependencies/cache"
    run.receipt["target"] = {"case": CASE, "module": MODULE, "theorem": THEOREM}
    run.receipt["preflight_reference"] = "https://github.com/Mattie/math/actions/runs/37975682035"
    run.receipt["runner_sha256"] = digest(Path(__file__))
    run.flush()
    try:
        pins, case, source = check_inputs()
        run.setup()
        for fixture in ("valid", "mismatch", "axiom"):
            run.fixture(fixture)
        run.collect(required=True)
        packages, dependencies = prepare_dependencies(run, pins, case, source)
        path, protected = prepare_candidate(run, pins, case, source, packages)
        run_proof(run, path, protected, packages, dependencies)
        require(set(run.receipt["checks"]) == {"tools", "isolation", "valid", "mismatch", "axiom",
                                              "dependencies", "realnorm"}, "Incomplete verification")
        collect(run, required=True)
        run.receipt["status"] = "passed"
    except Exception as error:
        run.receipt["status"] = "failed"
        run.receipt["error"] = f"{type(error).__name__}: {error}"
        print(run.receipt["error"], file=sys.stderr)
        collect(run)
    finally:
        run.receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        run.flush()
    return 0 if run.receipt["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

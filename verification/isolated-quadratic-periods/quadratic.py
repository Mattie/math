"""Run the published six-target package through the established hosted sandbox.

The existing preflight owns tool installation and real isolation controls. This
runner adds the quadratic package, an explicit complete-module build, and its
strict axiom audit. Earlier proof runs and published exports are not inputs to
the fresh proof check and are not modified or republished.
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
sys.path.insert(0, str(HERE.parent / "isolated-irrationality"))
from verify import (BASELINE, PINS, check_capacity, project, regular, save_json,
                    tree_identity, validate_work_dir)
from preflight import Preflight, AXIOMS, check_comparator, digest, require, systemd_command

PACKAGE = REPO / "preprints/The-irrationality-exponent-of-real-and-imaginary-quadratic-periods-is-2-October-9-2026"
SOURCE = PACKAGE / "lean"
MANIFEST_SHA256 = "ae7d619051118d539d98679954ce4d4a6e97a5740b2550295f5a9241237f31bb"
TARGETS = (
    "CompareChallenge.pi_sqrt_exponent_two",
    "CompareChallenge.pi_sqrt_eventual_bound",
    "CompareChallenge.quadratic_log_exponent_two",
    "CompareChallenge.quadratic_log_eventual_bound",
    "CompareChallenge.imaginary_quadratic_exponent_two",
    "CompareChallenge.imaginary_quadratic_eventual_bound",
)
LIBRARIES = ["OAI", "Logarithm", "Imaginary", "Periodic", "PeriodicGeometry", "PeriodicFamily",
             "Quadratic", "QuadraticReal3", "QuadraticImag5", "QuadraticAudit", "QuadraticFamilyAudit",
             "Combined", "StandardBridge", "Challenge", "Solution", "Audit"]
PROOF_SECONDS = 14400
SWEEP_SECONDS = 3600
CHECKER = PACKAGE / "scripts/check-axioms.py"
CONTROLS = REPO / "verification/publication/lean-controls.sh"


def check_configuration(config: dict) -> None:
    """Reject omitted endpoints, a different specification, or a weakened policy."""
    require(config.get("challenge_module") == "Challenge" and config.get("solution_module") == "Solution",
            "Unexpected comparison modules")
    require(config.get("theorem_names") == list(TARGETS), "Expected exactly the six published targets")
    require(config.get("enable_nanoda") is True and set(config.get("permitted_axioms", [])) == set(AXIOMS),
            "Unexpected kernel or axiom policy")
    require(set(config) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms", "enable_nanoda"},
            "Unexpected comparison configuration fields")


def proof_modules(sources: dict[str, str]) -> list[str]:
    """Select actual source modules; Lake library roots do not cover directory libraries."""
    return sorted(name[:-5].replace("/", ".") for name in sources
                  if name.endswith(".lean") and name not in {"lakefile.lean", "Challenge.lean"})


def check_inputs() -> tuple[dict, dict[str, str]]:
    """Validate the frozen package and reused hosted machinery before execution."""
    for name, sha in BASELINE.items():
        require(digest(regular(REPO, name)) == sha, f"Reviewed hosted input changed: {name}")
    manifest = regular(SOURCE, "source-manifest.json")
    require(digest(manifest) == MANIFEST_SHA256, "Unexpected published source manifest")
    rows = json.loads(manifest.read_text(encoding="utf-8"))
    sources = {row["path"]: row["sha256"] for row in rows}
    require(len(sources) == len(rows), "Duplicate source manifest entry")
    actual = {p.relative_to(SOURCE).as_posix() for p in SOURCE.rglob("*")
              if p.is_file() and ".lake" not in p.relative_to(SOURCE).parts
              and (p.suffix == ".lean" or p.name in {"lean-toolchain", "lake-manifest.json", "comparison.json"})}
    require(actual == set(sources), "Frozen source/config inventory has missing or extra files")
    for name, sha in sources.items():
        require(digest(regular(SOURCE, name)) == sha, f"Frozen source mismatch: {name}")
    require(len(proof_modules(sources)) == 1028, "Unexpected packaged proof-module count")
    check_configuration(json.loads((SOURCE / "comparison.json").read_text(encoding="utf-8")))
    return json.loads(PINS.read_text(encoding="utf-8")), sources


def prepare_dependencies(run: Preflight, pins: dict, sources: dict) -> tuple[Path, dict]:
    """Fetch trusted upstream artifacts before introducing any candidate source."""
    bootstrap = run.work / "dependencies"
    project(bootstrap, PACKAGE, pins["mathlib"], ["Challenge"])
    shutil.copyfile(SOURCE / "Challenge.lean", bootstrap / "Challenge.lean")
    run.env["MATHLIB_CACHE_DIR"] = str(run.work / "mathlib-cache")
    lake = run.lean / "bin/lake"
    run.command("trusted-mathlib-cache", [lake, "exe", "cache", "get"], cwd=bootstrap, timeout=2400)
    run.command("trusted-mathlib-build", [lake, "build", "Mathlib"], cwd=bootstrap, timeout=2400)
    require(digest(bootstrap / "lake-manifest.json") == sources["lake-manifest.json"],
            "Trusted setup changed the frozen dependency lock")
    packages = bootstrap / ".lake/packages"
    lock = json.loads((bootstrap / "lake-manifest.json").read_text(encoding="utf-8"))
    for dependency in lock["packages"]:
        name = dependency["name"]
        _, revision = run.command(f"dependency-{name}", ["git", "rev-parse", "HEAD"], cwd=packages / name)
        require(revision.strip() == dependency["rev"], f"Dependency revision mismatch: {name}")
        _, changed = run.command(f"dependency-clean-{name}", ["git", "diff", "--name-only", "HEAD"], cwd=packages / name)
        require(not changed.strip(), f"Dependency source changed: {name}")
    identity = tree_identity(packages)
    save_json(run.evidence / "dependencies.json", identity)
    run.receipt["dependencies"] = {
        "inventory_sha256": digest(run.evidence / "dependencies.json"),
        "lock_sha256": sources["lake-manifest.json"],
        "cache": "Official Mathlib cache, fetched before candidate sources are introduced",
        "access": "Outside candidate writable .lake; read-only through Landrun",
    }
    run.receipt["checks"]["dependencies"] = "passed"
    run.flush()
    return packages, identity


def prepare_candidate(run: Preflight, pins: dict, sources: dict, packages: Path) -> tuple[Path, dict]:
    """Copy frozen sources into empty build state using generated Lake configuration."""
    candidate = run.work / "quadratic-periods"
    project(candidate, PACKAGE, pins["mathlib"], LIBRARIES)
    (candidate / ".lake").mkdir()
    require(not packages.resolve().is_relative_to((candidate / ".lake").resolve()),
            "Trusted dependencies must stay outside candidate writable state")
    (candidate / ".lake/packages").symlink_to(packages, target_is_directory=True)
    for name, sha in sources.items():
        if not name.endswith(".lean") or name == "lakefile.lean":
            continue
        destination = candidate / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(regular(SOURCE, name), destination)
        require(digest(destination) == sha, f"Candidate copy changed: {name}")
    shutil.copyfile(SOURCE / "comparison.json", candidate / "config.json")
    require(set(p.name for p in (candidate / ".lake").iterdir()) == {"packages"}, "Candidate contains prior build state")
    protected = {p.relative_to(candidate).as_posix(): digest(p) for p in candidate.rglob("*")
                 if p.is_file() and ".lake" not in p.relative_to(candidate).parts}
    inputs = run.evidence / "inputs"
    inputs.mkdir()
    for name in ("Challenge.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain", "config.json", "Audit.lean"):
        shutil.copyfile(candidate / name, inputs / name)
    shutil.copyfile(SOURCE / "source-manifest.json", inputs / "source-manifest.json")
    save_json(inputs / "candidate-files.json", protected)
    run.receipt["candidate"] = {"initial_compiled_modules": 0, "targets": list(TARGETS),
                                 "source_manifest_sha256": MANIFEST_SHA256}
    run.flush()
    return candidate, protected


def comparison_command(run: Preflight, candidate: Path) -> list[str]:
    """Keep the established Comparator sandbox with a four-hour family budget."""
    args = systemd_command(candidate, run.lean, run.comparator, run.env)
    args[args.index("--property=RuntimeMaxSec=300")] = f"--property=RuntimeMaxSec={PROOF_SECONDS}"
    args[1:1] = ["--property=MemoryMax=12G", "--property=CPUQuota=400%"]
    return args


def build_command(run: Preflight, candidate: Path, arguments: list[str], seconds: int) -> list[str]:
    """Apply the same write boundary and socket denial to supplemental Lean loads."""
    service = ["systemd-run", "--user", "--wait", "--pipe", "--collect",
               "--property=RestrictAddressFamilies=~AF_UNIX", "--property=MemoryMax=12G",
               "--property=CPUQuota=400%", f"--property=RuntimeMaxSec={seconds}",
               "--setenv=LEAN_NUM_THREADS=4", f"--setenv=PATH={run.env['PATH']}",
               f"--working-directory={candidate}"]
    boundary = [run.env["COMPARATOR_LANDRUN"], "--best-effort", "--ro", "/", "--rw", "/dev",
                "--rwx", str(candidate / ".lake"), "--rox", str(run.lean), "--rox", "/usr",
                "--ro", "/lib,/lib64", "-ldd", "-add-exec", "--"]
    return service + boundary + [str(run.lean / "bin/lake"), *arguments]


def check_proof(run: Preflight, candidate: Path, sources: dict) -> None:
    """Compare all six targets, replay both kernels, then build every packaged module."""
    check_capacity(run, "proof", 10)
    run.receipt["resources"].update(runtime_seconds=PROOF_SECONDS, sweep_seconds=SWEEP_SECONDS,
                                    memory_max="12G", cpu_quota="400%")
    code, output = run.command("six-target-comparator", comparison_command(run, candidate),
                               cwd=candidate, allow_failure=True, timeout=PROOF_SECONDS + 60)
    check_comparator("valid", code, output)
    require("Building Solution" in output and all(name in output for name in TARGETS),
            "Expected candidate build or six targets missing from diagnostics")
    run.receipt["checks"]["comparison_and_kernels"] = "passed"
    run.flush()
    modules = proof_modules(sources)
    run.command("all-packaged-modules", build_command(run, candidate, ["build", *modules], SWEEP_SECONDS),
                cwd=candidate, timeout=SWEEP_SECONDS + 60)
    rows = []
    for name, sha in sorted(sources.items()):
        if not name.endswith(".lean") or name in {"lakefile.lean", "Challenge.lean"}:
            continue
        compiled = candidate / ".lake/build/lib/lean" / Path(name).with_suffix(".olean")
        regular(candidate, compiled.relative_to(candidate).as_posix())
        require(compiled.stat().st_size > 0, f"Packaged module has an empty object file: {name}")
        rows.append({"source": name, "source_sha256": sha, "olean_sha256": digest(compiled),
                     "olean_bytes": compiled.stat().st_size})
    save_json(run.evidence / "fresh-built-modules.json", rows)
    run.receipt["checks"]["all_packaged_modules_built"] = len(rows)
    _, audit = run.command("six-axiom-audit", build_command(run, candidate,
                           ["env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "Audit.lean"], 300),
                           cwd=candidate, timeout=360)
    log = run.evidence / "six-axioms.log"
    log.write_text(audit, encoding="utf-8")
    run.command("six-axiom-gate", [sys.executable, CHECKER, log, "--source", candidate / "Audit.lean"])
    run.receipt["checks"]["six_target_axiom_audit"] = "passed"
    run.flush()


def collect(run: Preflight, *, required: bool = False) -> None:
    """Retain new-run evidence while leaving prior receipts and exports untouched."""
    run.collect(required=required)
    names = ["dependencies.json", "fresh-built-modules.json", "six-axioms.log"]
    names += ["inputs/" + name for name in ("Challenge.lean", "lakefile.lean", "lake-manifest.json",
                                            "lean-toolchain", "config.json", "Audit.lean",
                                            "source-manifest.json", "candidate-files.json")]
    for name in names:
        path = run.evidence / name
        require(not required or path.is_file(), f"Required evidence missing: {name}")
        if path.is_file():
            run.receipt["retained_files"][name] = digest(path)


def main() -> int:
    """Execute the authorized hosted case; incomplete runs never receive a pass."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    run = Preflight(validate_work_dir(args.work_dir))
    run.receipt.update(scope="Fresh hosted build of all packaged quadratic-period modules and six-target isolated two-kernel check",
                       target={"case": "quadratic-periods", "module": "Solution", "theorems": list(TARGETS)},
                       runner_sha256=digest(Path(__file__)),
                       export_policy="No standalone export retained; existing published export remains a separate local-run artifact")
    run.flush()
    try:
        pins, sources = check_inputs()
        protected_tools = {path: digest(path) for path in (Path(__file__), CHECKER, CONTROLS,
                           HERE.parent / "isolated-irrationality/verify.py")}
        run.receipt["supporting_scripts"] = {path.relative_to(REPO).as_posix(): sha for path, sha in protected_tools.items()}
        check_capacity(run, "setup", 35)
        run.setup()
        for fixture in ("valid", "mismatch", "axiom"):
            run.fixture(fixture)
        run.collect(required=True)
        run.command("axiom-policy-controls", ["bash", CONTROLS, CHECKER])
        run.receipt["checks"]["axiom_policy_controls"] = "passed"
        packages, dependencies = prepare_dependencies(run, pins, sources)
        candidate, protected = prepare_candidate(run, pins, sources, packages)
        check_proof(run, candidate, sources)
        require(all(digest(regular(candidate, name)) == sha for name, sha in protected.items()), "Protected candidate input changed")
        require(tree_identity(packages) == dependencies, "Protected dependency bytes changed")
        require(all(digest(path) == sha for path, sha in protected_tools.items()), "Supporting script changed")
        check_inputs()
        run.receipt["checks"]["protected_inputs_and_dependencies"] = "unchanged"
        required = {name: "passed" for name in ("tools", "isolation", "valid", "mismatch", "axiom",
                    "axiom_policy_controls", "dependencies", "comparison_and_kernels", "six_target_axiom_audit")}
        required.update(all_packaged_modules_built=1028, protected_inputs_and_dependencies="unchanged")
        require(run.receipt["checks"] == required, "Incomplete hosted verification")
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

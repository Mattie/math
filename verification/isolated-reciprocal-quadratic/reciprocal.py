"""Check the frozen reciprocal-quadratic package in two fresh hosted sandboxes.

The established preflight supplies pinned tools and tested isolation controls.
Each comparison rebuilds its own candidate; a supplemental classification build
covers every packaged proof module. Stock Comparator exports stay in memory.
Preparation-only mode freezes inputs without fetching tools or checking proofs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PACKAGE_NAME = "Reciprocal-quadratic-integrals-are-rational-or-have-irrationality-exponent-2-October-10-2026"
REVIEWED_SUPPORT = {
    "verification/isolated-irrationality/verify.py": "7b4d86c1658b412e5ac2b305206d5d8fea466c92381e15fa9603a145468f0d5f",
    "verification/isolated-preflight/preflight.py": "b6149c3a2265533769fdf3eade0c56b1bcd94c8ad3d128570ce1eca7eefbd1f8",
    "verification/publication/lean-controls.sh": "f140df12410a0e398315d6911bc4299999e9cd44c0e9bbca02252d1e6538239e",
    f"preprints/{PACKAGE_NAME}/scripts/check-axioms.py": "be3f5c512718e02bbc3019079b72edb0f5f4c379c922ed0401c81374a27035ec",
}


def check_supporting_scripts() -> None:
    """Hash every executable helper before importing one, using only the stdlib."""
    for name, expected in REVIEWED_SUPPORT.items():
        path = REPO / name
        if not path.is_file() or any(p.is_symlink() for p in (path, *path.parents)):
            raise RuntimeError(f"Supporting script is not a regular file: {name}")
        with path.open("rb") as source:
            actual = hashlib.file_digest(source, "sha256").hexdigest()
        if actual != expected:
            raise RuntimeError(f"Reviewed supporting script changed: {name}")


check_supporting_scripts()
sys.path.insert(0, str(HERE.parent / "isolated-irrationality"))
from verify import (BASELINE, PINS, check_capacity, project, regular, save_json,
                    tree_identity, validate_work_dir)
from preflight import Preflight, AXIOMS, check_comparator, digest, require, systemd_command

PACKAGE = REPO / "preprints" / PACKAGE_NAME
SOURCE = PACKAGE / "lean"
CHECKER = PACKAGE / "scripts/check-axioms.py"
CONTROLS = REPO / "verification/publication/lean-controls.sh"
MANIFEST_SHA256 = "ce50a6ddd737466e7354f7ee72699f03a14bd89bf330a78d6244bcffa8a7641e"
FROZEN_INPUTS = {
    "source-manifest.json": MANIFEST_SHA256,
    "comparison-positive-integralcheck.json": "c7b372f716d72a803b6c38bfb113cce08869cfe6546a2019adac1385bab21340",
    "comparison-classification-check.json": "c8aabe829e69154f7a9262c125122fdfb301353890d3b30d529979471d012e5d",
    "lakefile.lean": "44f90b959c9293ffd74a1ea2b21ca58ba97c9ca4db51f5f62b0651b6b06bddde",
    "lake-manifest.json": "4ce08aeac1f673a63d24240ba9173297719d02ad9facfddcf696163cc9bd24d6",
    "lean-toolchain": "d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b",
}
GROUPS = {
    "positive": {
        "config": "comparison-positive-integralcheck.json",
        "challenge": "PositiveChallenge", "solution": "PositiveSolution", "audit": "PositiveAudit",
        "targets": (
            "PositiveIntegralCheck.positive_bound",
            "PositiveIntegralCheck.positive_exponent_two",
            "PositiveIntegralCheck.nonzero_discriminant_bound",
            "PositiveIntegralCheck.nonzero_discriminant_exponent_two",
        ),
    },
    "classification": {
        "config": "comparison-classification-check.json",
        "challenge": "ClassificationChallenge", "solution": "ClassificationSolution", "audit": "ClassificationAudit",
        "targets": (
            "ClassificationChallenge.repeated_root_evaluation",
            "ClassificationChallenge.rational_iff_discriminant_zero",
            "ClassificationChallenge.irrational_iff_discriminant_ne_zero",
        ),
    },
}
TARGETS = tuple(target for group in GROUPS.values() for target in group["targets"])
CHALLENGES = {group["challenge"] + ".lean" for group in GROUPS.values()}
LIBRARIES = ["Classification", "ClassificationAudit", "ClassificationChallenge", "ClassificationSolution",
             "Coefficients", "Combined", "Imaginary", "Logarithm", "Main", "Negative", "OAI",
             "PeriodicFamily", "PeriodicGeometry", "Positive", "PositiveAudit", "PositiveChallenge",
             "PositiveControls", "PositiveCrossRatio", "PositiveLogBridge", "PositiveMain",
             "PositiveNormCoefficients", "PositiveScaling", "PositiveSolution", "PositiveSquareclass",
             "Quadratic", "RepeatedRoot", "StandardBridge"]
PROOF_SECONDS = 7200
SWEEP_SECONDS = 3600
LIVE_EVIDENCE_FILES = {"console.log"}


def check_configuration(config: dict, group: str) -> None:
    """Require exactly the frozen targets, modules, two kernels, and three axioms."""
    require(group in GROUPS, "Unknown comparison group")
    spec = GROUPS[group]
    require(config.get("challenge_module") == spec["challenge"] and
            config.get("solution_module") == spec["solution"], "Unexpected comparison modules")
    require(config.get("theorem_names") == list(spec["targets"]), "Unexpected comparison targets")
    axioms = config.get("permitted_axioms", [])
    require(isinstance(axioms, list) and len(axioms) == 3 and set(axioms) == set(AXIOMS) and
            config.get("enable_nanoda") is True, "Unexpected kernel or axiom policy")
    require(set(config) == {"challenge_module", "solution_module", "theorem_names",
                            "permitted_axioms", "enable_nanoda"}, "Unexpected configuration fields")


def proof_modules(sources: dict[str, str]) -> list[str]:
    """Select all actual proof modules, excluding lakefile and both specifications."""
    return sorted(name[:-5].replace("/", ".") for name in sources
                  if name.endswith(".lean") and name not in CHALLENGES | {"lakefile.lean"})


def check_inputs() -> tuple[dict, dict[str, str]]:
    """Validate the published manifest, exact source inventory, and separate configs."""
    check_supporting_scripts()
    for name, sha in BASELINE.items():
        require(digest(regular(REPO, name)) == sha, f"Reviewed hosted input changed: {name}")
    for name, sha in FROZEN_INPUTS.items():
        require(digest(regular(SOURCE, name)) == sha, f"Frozen configuration changed: {name}")
    manifest = json.loads((SOURCE / "source-manifest.json").read_text(encoding="utf-8"))
    rows = manifest["files"]
    require(len(rows) == 986, "Unexpected frozen source count")
    require(all(row["path"].startswith("lean/") and row["path"].endswith(".lean") for row in rows),
            "Unexpected manifest source layout")
    sources = {row["path"].removeprefix("lean/"): row["sha256"] for row in rows}
    require(len(sources) == len(rows), "Duplicate source manifest entry")
    actual = {p.relative_to(SOURCE).as_posix() for p in SOURCE.rglob("*.lean")
              if ".lake" not in p.relative_to(SOURCE).parts and p.relative_to(SOURCE).as_posix() != "lakefile.lean"}
    require(actual == set(sources), "Frozen Lean inventory has missing or extra files")
    for row in rows:
        path = regular(SOURCE, row["path"].removeprefix("lean/"))
        require(digest(path) == row["sha256"] and path.stat().st_size == row["bytes"],
                f"Frozen source mismatch: {row['path']}")
    require(len(proof_modules(sources)) == 984, "Unexpected packaged proof-module count")
    for group, spec in GROUPS.items():
        check_configuration(json.loads((SOURCE / spec["config"]).read_text(encoding="utf-8")), group)
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    require(manifest["mathlib_revision"] == pins["mathlib"], "Unexpected Mathlib revision")
    return pins, sources


def prepare_dependencies(run: Preflight, pins: dict, sources: dict) -> tuple[Path, dict]:
    """Fetch trusted Mathlib before candidate files enter any generated project."""
    bootstrap = run.work / "dependencies"
    project(bootstrap, PACKAGE, pins["mathlib"], [spec["challenge"] for spec in GROUPS.values()])
    for name in sorted(CHALLENGES):
        shutil.copyfile(regular(SOURCE, name), bootstrap / name)
        require(digest(bootstrap / name) == sources[name], f"Bootstrap challenge changed: {name}")
    run.env["MATHLIB_CACHE_DIR"] = str(run.work / "mathlib-cache")
    lake = run.lean / "bin/lake"
    run.command("trusted-mathlib-cache", [lake, "exe", "cache", "get"], cwd=bootstrap, timeout=2400)
    run.command("trusted-mathlib-build", [lake, "build", "Mathlib"], cwd=bootstrap, timeout=2400)
    require(digest(bootstrap / "lake-manifest.json") == FROZEN_INPUTS["lake-manifest.json"],
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
        "lock_sha256": FROZEN_INPUTS["lake-manifest.json"],
        "cache": "Official Mathlib cache fetched before either candidate is introduced",
        "access": "Shared outside both writable candidate .lake directories; read-only through Landrun",
    }
    run.receipt["checks"]["dependencies"] = "passed"
    run.flush()
    return packages, identity


def prepare_candidate(run: Preflight, pins: dict, sources: dict, packages: Path, group: str) -> tuple[Path, dict]:
    """Create fresh build state and retain every frozen candidate input separately."""
    require(group in GROUPS, "Unknown comparison group")
    candidate = run.work / f"candidate-{group}"
    project(candidate, PACKAGE, pins["mathlib"], LIBRARIES)
    (candidate / ".lake").mkdir()
    require(packages.is_dir() and not packages.resolve().is_relative_to((candidate / ".lake").resolve()),
            "Trusted dependencies must stay outside candidate writable state")
    (candidate / ".lake/packages").symlink_to(packages, target_is_directory=True)
    for name, sha in sources.items():
        destination = candidate / name
        require(not destination.exists(), f"Duplicate candidate destination: {name}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(regular(SOURCE, name), destination)
        require(digest(destination) == sha, f"Candidate copy changed: {name}")
    shutil.copyfile(SOURCE / GROUPS[group]["config"], candidate / "config.json")
    require(set(p.name for p in (candidate / ".lake").iterdir()) == {"packages"}, "Candidate contains prior build state")
    protected = {p.relative_to(candidate).as_posix(): digest(p) for p in candidate.rglob("*")
                 if p.is_file() and ".lake" not in p.relative_to(candidate).parts}
    inputs = run.evidence / "inputs" / group
    inputs.mkdir(parents=True)
    for name in protected:
        destination = inputs / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(candidate / name, destination)
    shutil.copyfile(SOURCE / "source-manifest.json", inputs / "source-manifest.json")
    save_json(inputs / "candidate-files.json", protected)
    run.receipt.setdefault("candidates", {})[group] = {
        "directory": str(candidate), "initial_compiled_modules": 0, "targets": list(GROUPS[group]["targets"]),
        "source_manifest_sha256": MANIFEST_SHA256, "config_sha256": FROZEN_INPUTS[GROUPS[group]["config"]],
        "candidate_files_sha256": digest(inputs / "candidate-files.json"),
    }
    run.flush()
    return candidate, protected


def comparison_command(run: Preflight, candidate: Path) -> list[str]:
    """Use the tested Comparator boundary with a two-hour, 12 GiB, four-CPU cap."""
    args = systemd_command(candidate, run.lean, run.comparator, run.env)
    args[args.index("--property=RuntimeMaxSec=300")] = f"--property=RuntimeMaxSec={PROOF_SECONDS}"
    args[1:1] = ["--property=MemoryMax=12G", "--property=CPUQuota=400%", "--setenv=LEAN_NUM_THREADS=4"]
    return args


def build_command(run: Preflight, candidate: Path, arguments: list[str], seconds: int) -> list[str]:
    """Give supplemental Lean loads the same writable boundary and socket denial."""
    service = ["systemd-run", "--user", "--wait", "--pipe", "--collect",
               "--property=RestrictAddressFamilies=~AF_UNIX", "--property=MemoryMax=12G",
               "--property=CPUQuota=400%", f"--property=RuntimeMaxSec={seconds}",
               "--setenv=LEAN_NUM_THREADS=4", f"--setenv=PATH={run.env['PATH']}",
               f"--working-directory={candidate}"]
    boundary = [run.env["COMPARATOR_LANDRUN"], "--best-effort", "--ro", "/", "--rw", "/dev",
                "--rwx", str(candidate / ".lake"), "--rox", str(run.lean), "--rox", "/usr",
                "--ro", "/lib,/lib64", "-ldd", "-add-exec", "--"]
    return service + boundary + [str(run.lean / "bin/lake"), *arguments]


def check_comparison(run: Preflight, candidate: Path, group: str) -> None:
    """Require explicit Comparator and both-kernel acceptance for this target group."""
    spec = GROUPS[group]
    check_capacity(run, group, 10)
    try:
        code, output = run.command(f"{group}-comparator", comparison_command(run, candidate),
                                   cwd=candidate, allow_failure=True, timeout=PROOF_SECONDS + 60)
    finally:
        rows = []
        for path in sorted((candidate / ".lake/build/lib/lean").rglob("*.olean")):
            relative = path.relative_to(candidate).as_posix()
            regular(candidate, relative)
            rows.append({"path": relative, "sha256": digest(path), "bytes": path.stat().st_size})
        save_json(run.evidence / f"{group}-comparison-modules.json", rows)
    check_comparator("valid", code, output)
    require(f"Building {spec['solution']}" in output and all(name in output for name in spec["targets"]),
            f"Expected candidate build or {group} targets missing from diagnostics")
    run.receipt["checks"][f"{group}_comparison_and_kernels"] = "passed"
    run.flush()


def check_sweep_and_audits(run: Preflight, candidate: Path, sources: dict) -> None:
    """Build all 984 modules once, inventory their objects, and audit seven endpoints."""
    modules = proof_modules(sources)
    require(len(modules) == 984, "Incomplete supplemental module set")
    run.command("all-packaged-modules", build_command(run, candidate, ["build", *modules], SWEEP_SECONDS),
                cwd=candidate, timeout=SWEEP_SECONDS + 60)
    rows = []
    for name, sha in sorted(sources.items()):
        if name in CHALLENGES:
            continue
        compiled = regular(candidate, ".lake/build/lib/lean/" + str(Path(name).with_suffix(".olean")).replace("\\", "/"))
        require(compiled.stat().st_size > 0, f"Packaged module has an empty object file: {name}")
        rows.append({"source": name, "source_sha256": sha, "olean_sha256": digest(compiled),
                     "olean_bytes": compiled.stat().st_size})
    require(len(rows) == 984, "Incomplete fresh module inventory")
    save_json(run.evidence / "fresh-built-modules.json", rows)
    run.receipt["checks"]["all_packaged_modules_built"] = len(rows)
    run.flush()
    for group, spec in GROUPS.items():
        audit_source = spec["audit"] + ".lean"
        _, audit = run.command(f"{group}-axiom-audit", build_command(run, candidate,
                               ["env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", audit_source], 300),
                               cwd=candidate, timeout=360)
        log = run.evidence / f"{group}-axioms.log"
        log.write_text(audit, encoding="utf-8")
        run.command(f"{group}-axiom-gate", [sys.executable, CHECKER, log, "--source", candidate / audit_source])
        run.receipt["checks"][f"{group}_axiom_audit"] = "passed"
        run.flush()


def collect(run: Preflight, *, required: bool = False) -> None:
    """Keep all new-run evidence, including partial failures, without old exports."""
    run.collect(required=required)
    if required:
        for name in ("dependencies.json", "fresh-built-modules.json", "positive-axioms.log",
                     "classification-axioms.log", "supporting-scripts.json", "frozen-inputs.json",
                     "positive-comparison-modules.json", "classification-comparison-modules.json"):
            regular(run.evidence, name)
        require(json.loads((run.evidence / "supporting-scripts.json").read_text(encoding="utf-8")) ==
                run.receipt["supporting_scripts"], "Retained helper identities changed")
        require(json.loads((run.evidence / "frozen-inputs.json").read_text(encoding="utf-8")) ==
                FROZEN_INPUTS, "Retained frozen identities changed")
        for group in GROUPS:
            inputs = run.evidence / "inputs" / group
            protected = json.loads(regular(inputs, "candidate-files.json").read_text(encoding="utf-8"))
            require(digest(inputs / "candidate-files.json") == run.receipt["candidates"][group]["candidate_files_sha256"],
                    f"Retained {group} input inventory changed")
            for name, sha in protected.items():
                require(digest(regular(inputs, name)) == sha, f"Retained {group} input changed: {name}")
            require(digest(regular(inputs, "source-manifest.json")) == MANIFEST_SHA256, "Retained manifest changed")
        for name, sha in FROZEN_INPUTS.items():
            require(digest(regular(run.evidence / "frozen", name)) == sha, f"Retained frozen input changed: {name}")
    for path in run.evidence.rglob("*"):
        relative = path.relative_to(run.evidence).as_posix()
        if path.is_file() and relative not in {"receipt.json", "receipt.tmp"} | LIVE_EVIDENCE_FILES:
            run.receipt["retained_files"][relative] = digest(path)


def check_preservation(candidates: dict, packages: Path, dependencies: dict | None, protected_tools: dict) -> None:
    """Revalidate every protected source, helper, candidate input, and dependency."""
    for group, (candidate, protected) in candidates.items():
        actual = {p.relative_to(candidate).as_posix() for p in candidate.rglob("*")
                  if p.is_file() and ".lake" not in p.relative_to(candidate).parts}
        require(actual == set(protected), f"Protected {group} candidate inventory changed")
        require(all(digest(regular(candidate, name)) == sha for name, sha in protected.items()),
                f"Protected {group} candidate input changed")
        require((candidate / ".lake/packages").is_symlink() and
                (candidate / ".lake/packages").resolve() == packages.resolve(), "Dependency link changed")
    if dependencies is not None:
        require(tree_identity(packages) == dependencies, "Protected dependency bytes changed")
    else:
        require(not any(packages.iterdir()), "Preparation-only dependencies must remain empty")
    require(all(digest(regular(REPO, name)) == sha for name, sha in protected_tools.items()), "Supporting script changed")
    check_inputs()


def validate_initial_work(work: Path) -> None:
    """Allow only the workflow's initial diagnostics before creating a fresh run."""
    require(not work.is_symlink(), "Work directory must not be a symlink")
    if not work.exists():
        return
    require(work.is_dir() and {p.name for p in work.iterdir()} <= {"evidence"},
            "Work directory contains prior state")
    evidence = work / "evidence"
    if evidence.exists():
        require(evidence.is_dir() and not evidence.is_symlink(), "Evidence directory must be regular")
        allowed = {"started.txt", "capacity-input.log", "capacity.log", "console.log"}
        for path in evidence.iterdir():
            require(path.name in allowed and path.is_file() and not path.is_symlink(),
                    f"Work directory contains prior evidence: {path.name}")


def main() -> int:
    """Execute the hosted checks, or retain a clearly non-verifying preparation."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    work = validate_work_dir(args.work_dir)
    validate_initial_work(work)
    run = Preflight(work)
    run.receipt.update(
        scope="Fresh reciprocal-quadratic source builds; two separate comparisons covering seven targets and both kernels",
        targets=list(TARGETS), runner_sha256=digest(Path(__file__)),
        export_policy="Stock Comparator exports remain in memory; no downloadable export is retained or claimed",
        console_policy="Workflow console.log is uploaded as an unbound live stream; closed command logs carry hashes",
        preparation_only=args.prepare_only,
        resources={"comparison_seconds_each": PROOF_SECONDS, "sweep_seconds": SWEEP_SECONDS,
                   "memory_max": "12G", "cpu_quota": "400%"})
    candidates = {}
    packages = None
    dependencies = None
    protected_tools = {}
    run.flush()
    try:
        pins, sources = check_inputs()
        protected_tools = {name: digest(regular(REPO, name)) for name in
                           set(REVIEWED_SUPPORT) | set(BASELINE) | {Path(__file__).relative_to(REPO).as_posix()}}
        save_json(run.evidence / "supporting-scripts.json", protected_tools)
        save_json(run.evidence / "frozen-inputs.json", FROZEN_INPUTS)
        run.receipt["supporting_scripts"] = protected_tools
        frozen = run.evidence / "frozen"
        frozen.mkdir()
        for name in FROZEN_INPUTS:
            shutil.copyfile(SOURCE / name, frozen / name)
        if args.prepare_only:
            packages = run.work / "empty-dependencies"
            packages.mkdir()
        else:
            check_capacity(run, "setup", 35)
            run.setup()
            for fixture in ("valid", "mismatch", "axiom"):
                run.fixture(fixture)
            run.collect(required=True)
            run.command("axiom-policy-controls", ["bash", CONTROLS, CHECKER])
            run.receipt["checks"]["axiom_policy_controls"] = "passed"
            packages, dependencies = prepare_dependencies(run, pins, sources)
        for group in GROUPS:
            candidates[group] = prepare_candidate(run, pins, sources, packages, group)
        if args.prepare_only:
            check_preservation(candidates, packages, dependencies, protected_tools)
            run.receipt["checks"]["input_preparation"] = "complete"
            run.receipt["status"] = "preparation-only"
            run.receipt["scope"] = "Inputs prepared only; no tools fetched, proofs built, kernels run, or isolation verified"
            collect(run)
        else:
            for group, (candidate, _) in candidates.items():
                check_comparison(run, candidate, group)
            check_sweep_and_audits(run, candidates["classification"][0], sources)
            check_preservation(candidates, packages, dependencies, protected_tools)
            run.receipt["checks"]["protected_inputs_and_dependencies"] = "unchanged"
            required = {name: "passed" for name in ("tools", "isolation", "valid", "mismatch", "axiom",
                        "axiom_policy_controls", "dependencies", "positive_comparison_and_kernels",
                        "classification_comparison_and_kernels", "positive_axiom_audit", "classification_axiom_audit")}
            required.update(all_packaged_modules_built=984, protected_inputs_and_dependencies="unchanged")
            require(run.receipt["checks"] == required, "Incomplete hosted verification")
            collect(run, required=True)
            run.receipt["status"] = "passed"
    except Exception as error:
        run.receipt["status"] = "failed"
        run.receipt["error"] = f"{type(error).__name__}: {error}"
        print(run.receipt["error"], file=sys.stderr)
        if packages is not None and protected_tools:
            try:
                check_preservation(candidates, packages, dependencies, protected_tools)
                run.receipt["preservation_after_failure"] = "unchanged"
            except Exception as preservation_error:
                run.receipt["preservation_after_failure"] = f"{type(preservation_error).__name__}: {preservation_error}"
        try:
            collect(run)
        except Exception as collection_error:
            run.receipt["collection_error"] = f"{type(collection_error).__name__}: {collection_error}"
    finally:
        run.receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        run.flush()
    return 0 if run.receipt["status"] in {"passed", "preparation-only"} else 1


if __name__ == "__main__":
    raise SystemExit(main())

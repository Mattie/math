"""Prepare or run the isolated verifier for the two-case pi companion."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PACKAGE = REPO / "formalizations/PiTwoCaseBridge"
PAPER = REPO / "preprints/The-irrationality-exponent-of-pi-through-a-two-case-determinant-argument-October-11-2026"
LOCK = REPO / "formalizations/AffineLogarithms/lake-manifest.json"
FREEZE = HERE / "source-sha256.json"
RUNNER_INPUTS = (Path(__file__).resolve(), FREEZE,
                 REPO / "verification/isolated-6942/verify.py",
                 REPO / "verification/isolated-affine/verify.py",
                 REPO / "verification/isolated-preflight/preflight.py",
                 REPO / "verification/isolated-preflight/boundary_probe.c",
                 REPO / "verification/publication/prepare-independent-runner.sh",
                 REPO / ".github/workflows/isolated-irrationality.yml")
SPEC = ("Challenge.lean", "Solution.lean", "config.json", "pins.json")
TARGETS = ["PiTwoCaseBridge.main", "PiTwoCaseBridge.pi_irrationalityExponent_eq_two",
           "PiTwoCaseBridge.theorem_5_1"]
UPSTREAM = "https://github.com/openai/math.git"
NANODA_FIX = "8199c74c8166dc1fff1be3b4bd144cb725268628"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


shared = load("pi_isolated_shared", REPO / "verification/isolated-6942/verify.py")
affine = load("pi_isolated_affine", REPO / "verification/isolated-affine/verify.py")
preflight = sys.modules["preflight"]
require, digest = shared.require, shared.digest


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def inventory():
    recorded = read(PAPER / "evidence/manifest.json")["companion"]
    paths = {}
    for rel, expected in recorded["input_files"].items():
        source = (PAPER / rel).resolve(strict=True)
        name = source.relative_to(REPO).as_posix()
        require(source.is_relative_to(PACKAGE) or source == LOCK, "Unexpected proof input")
        require(digest(shared.regular(REPO, name)) == expected, f"Recorded input changed: {name}")
        paths[name] = expected
    module_paths = {p.relative_to(REPO).as_posix() for p in (PACKAGE / "PiTwoCaseBridge").rglob("*.lean")}
    require(module_paths == {p for p in paths if p.endswith(".lean")}, "Lean source inventory mismatch")
    require(len(module_paths) == 27 and len(paths) == 30, "Incomplete Lean input inventory")
    return {"proof": paths,
            "spec": {name: digest(shared.regular(HERE, name)) for name in SPEC}}


def check_inputs():
    frozen = inventory()
    require(read(FREEZE) == frozen, "Frozen candidate or trusted specification changed")
    pins = read(HERE / "pins.json")
    manifest = read(PAPER / "evidence/manifest.json")["companion"]
    for pin, field in (("openai", "upstream_openai_revision"),
                       ("pi_exponent_tree", "upstream_pi_exponent_tree"),
                       ("lean_commit", "lean_revision"), ("mathlib", "mathlib_revision")):
        require(pins[pin] == manifest[field], f"Unexpected pin: {pin}")
    require(read(HERE / "config.json") == {
        "challenge_module": "Challenge", "solution_module": "Solution",
        "theorem_names": TARGETS, "permitted_axioms": preflight.AXIOMS, "enable_nanoda": True,
    }, "Unexpected target or axiom policy")
    return pins, frozen


def upstream_project(path, pins):
    path.mkdir()
    shutil.copyfile(LOCK, path / "lake-manifest.json")
    shutil.copyfile(PACKAGE / "lean-toolchain", path / "lean-toolchain")
    (path / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\npackage QuadraticPeriods where\n"
        "  fixedToolchain := true\n  leanOptions := #[⟨`autoImplicit, false⟩]\n"
        f'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{pins["mathlib"]}"\n'
        "lean_lib OAI\n", encoding="utf-8", newline="\n")


def stage(path, frozen):
    """Stage byte-identical Lean source and generate the only executable Lake configuration."""
    path.mkdir()
    lock = read(LOCK)
    lock["name"] = "PiTwoCaseCheck"
    lock["packages"] = [{
        "type": "path", "scope": "", "name": "QuadraticPeriods",
        "manifestFile": "lake-manifest.json", "inherited": False,
        "dir": "../trusted", "configFile": "lakefile.lean",
    }, *[{**dep, "inherited": True} for dep in lock["packages"]]]
    for name in ("Challenge.lean", "Solution.lean", "config.json"):
        shutil.copyfile(HERE / name, path / name)
        require(digest(path / name) == frozen["spec"][name], f"Staged specification changed: {name}")
    for name, expected in frozen["proof"].items():
        if name.endswith(".lean"):
            source = shared.regular(REPO, name)
            target = path / source.relative_to(PACKAGE)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            require(digest(target) == expected, f"Staged proof input changed: {name}")
    (path / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\npackage PiTwoCaseCheck where\n"
        "  fixedToolchain := true\n  leanOptions := #[⟨`autoImplicit, false⟩]\n"
        'require QuadraticPeriods from "../trusted"\n'
        "lean_lib PiTwoCaseBridge\nlean_lib Challenge\nlean_lib Solution\n",
        encoding="utf-8", newline="\n")
    shared.save_json(path / "lake-manifest.json", lock)
    shutil.copyfile(PACKAGE / "lean-toolchain", path / "lean-toolchain")
    return shared.tree_identity(path)


def trusted_dependencies(run, pins):
    repo = run.work / "openai"
    run.command("upstream-init", ["git", "init", "-q", repo])
    run.command("upstream-fetch", ["git", "fetch", "--depth=1", UPSTREAM, pins["openai"]], cwd=repo,
                timeout=900)
    run.command("upstream-sparse", ["git", "sparse-checkout", "set", "lean/OAI"], cwd=repo)
    run.command("upstream-checkout", ["git", "checkout", "--detach", "FETCH_HEAD"], cwd=repo)
    _, commit = run.command("upstream-commit", ["git", "rev-parse", "HEAD"], cwd=repo)
    _, tree = run.command("upstream-tree", ["git", "rev-parse", "HEAD:lean/OAI/NumberTheory/PiExponent"],
                          cwd=repo)
    require(commit.strip() == pins["openai"] and tree.strip() == pins["pi_exponent_tree"],
            "Pinned OpenAI source mismatch")
    run.command("upstream-clean", ["git", "diff", "--exit-code", "HEAD", "--", "lean/OAI"], cwd=repo)
    root = run.work / "trusted"
    upstream_project(root, pins)
    shutil.copytree(repo / "lean/OAI", root / "OAI", symlinks=True)
    require(not any(p.is_symlink() for p in (root / "OAI").rglob("*")), "Unexpected upstream symlink")
    lake = run.lean / "bin/lake"
    run.env["MATHLIB_CACHE_DIR"] = str(run.work / "mathlib-cache")
    run.command("trusted-cache", [lake, "exe", "cache", "get"], cwd=root, timeout=3000)
    # Read only names from the hashed source. Nothing in the candidate has been built.
    files = sorted((PACKAGE / "PiTwoCaseBridge").glob("*.lean")) + [HERE / "Challenge.lean"]
    targets = sorted({match for p in files for match in
                      re.findall(r"^import (OAI\.[A-Za-z0-9_.]+)\s*$", p.read_text(encoding="utf-8"), re.M)})
    require(bool(targets), "No pinned inherited modules found")
    run.command("trusted-inherited-build", [lake, "build", *("+" + m for m in targets)],
                cwd=root, timeout=5400)
    require(digest(root / "lake-manifest.json") == digest(LOCK), "Trusted lock changed")
    packages = root / ".lake/packages"
    for dep in read(LOCK)["packages"]:
        _, revision = run.command("dependency-" + dep["name"], ["git", "rev-parse", "HEAD"],
                                  cwd=packages / dep["name"])
        require(revision.strip() == dep["rev"], f"Dependency revision changed: {dep['name']}")
        run.command("dependency-clean-" + dep["name"], ["git", "diff", "--exit-code", "HEAD"],
                    cwd=packages / dep["name"])
    identity = shared.tree_identity(root)
    shared.save_json(run.evidence / "trusted-dependencies.json", identity)
    run.receipt["checks"]["trusted-dependencies"] = "passed"
    run.flush()
    return root, identity


def run_hosted(work, pins, frozen):
    preflight.PINS = HERE / "pins.json"
    run = preflight.Preflight(affine.fresh_work(work))
    runner_identity = {path: digest(path) for path in RUNNER_INPUTS}
    run.receipt.update(scope="Fresh isolated two-case pi source verification",
                       targets=TARGETS, evidence_kind="fresh execution",
                       source_manifest_sha256=digest(FREEZE),
                       workflow_ref=os.environ.get('GITHUB_WORKFLOW_REF'),
                       runner_inputs={path.relative_to(REPO).as_posix(): sha
                                      for path, sha in runner_identity.items()})
    try:
        run.env["LEAN_NUM_THREADS"] = "4"
        shared.check_capacity(run, "setup", shared.SETUP_GIB)
        run.setup()
        run.command("nanoda-rec-field-fix", ["git", "merge-base", "--is-ancestor",
                    NANODA_FIX, pins["nanoda"]], cwd=run.work / "tools/nanoda")
        for fixture in ("valid", "mismatch", "axiom"):
            run.fixture(fixture)
        affine.imported_admission(run)
        trusted, identity = trusted_dependencies(run, pins)
        candidate = run.work / "candidate"
        protected = stage(candidate, frozen)
        (candidate / ".lake").mkdir()
        (candidate / ".lake/packages").symlink_to(trusted / ".lake/packages", target_is_directory=True)
        inputs = run.evidence / "inputs"
        inputs.mkdir()
        for name in ("Challenge.lean", "Solution.lean", "config.json", "lakefile.lean",
                     "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(candidate / name, inputs / name)
        shared.save_json(inputs / "candidate-inputs.json", protected)
        shutil.copyfile(FREEZE, inputs / FREEZE.name)
        shared.check_capacity(run, "proof", shared.PROOF_GIB)
        code, log = run.command("pi-two-case-comparator", affine.proof_command(run, candidate),
                                cwd=candidate, allow_failure=True, timeout=affine.RUNTIME + 60)
        affine.check_proof_output(code, log, TARGETS)
        require(all(digest(shared.regular(candidate, n)) == item["sha256"]
                    for n, item in protected.items()), "Protected candidate changed")
        require(shared.tree_identity(trusted) == identity, "Protected dependencies changed")
        require(check_inputs() == (pins, frozen), "Frozen inputs changed")
        require(all(digest(path) == sha for path, sha in runner_identity.items()),
                "Verifier inputs changed")
        run.collect(required=True)
        affine.collect(run)
        run.receipt["checks"].update(comparison="passed", protected_inputs="passed")
        run.receipt["status"] = "passed"
    except Exception as error:
        run.receipt.update(status="failed", error=f"{type(error).__name__}: {error}")
        print(run.receipt["error"], file=sys.stderr)
        affine.collect(run)
    finally:
        run.receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        run.flush()
    return 0 if run.receipt["status"] == "passed" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--stage", type=Path)
    modes.add_argument("--run", type=Path)
    args = parser.parse_args()
    pins, frozen = check_inputs()
    if args.run:
        return run_hosted(args.run, pins, frozen)
    if args.stage:
        stage(args.stage, frozen)
    print(f"Checked {len(frozen['proof'])} frozen inputs for {len(TARGETS)} comparison targets.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Prepare pinned tools and test the stock Comparator route on tiny fixtures only.

Designed for a manually authorized GitHub-hosted Ubuntu 24.04 run. All generated
files stay in a fresh RUNNER_TEMP directory. No mathematical proof is built.
Filesystem-probe design informed by lean-eval's sandbox_engaged_probe.py at
38361be884302c7edce1908c4aef8296eb2cb27e; this implementation additionally requires
successful Comparator/Lean/Nanoda completion and tests the systemd socket filter.
"""
from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PINS = REPO / "verification/irrationality-exponents/pins.json"
LANDRUN = "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
GO = "go1.25.12"
LABELS = {"allowed", "challenge", "config", "tool", "outside", "symlink", "unix_stream", "unix_dgram"}
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
ACCEPTANCE = ("Your solution is okay!", "Lean default kernel accepts the solution",
              "nanoda kernel accepts the solution")
REJECTIONS = {"mismatch": "theorem statement do not match", "axiom": "Illegal axiom detected"}


def digest(path: Path) -> str:
    """Hash a retained input/output without loading large tool archives in memory."""
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def check_boundary(result: dict, *, isolated: bool) -> None:
    """Only explicit permission/socket-policy errors count as denial."""
    require(set(result) == LABELS, "Missing or unexpected boundary result")
    require(all(type(value) is int for value in result.values()), "Invalid probe errno")
    for label, value in result.items():
        if not isolated or label == "allowed":
            require(value == 0, f"{label}: operation must succeed; errno={value}")
        elif label.startswith("unix_"):
            require(value in {errno.EPERM, errno.EACCES, errno.EAFNOSUPPORT},
                    f"{label}: socket policy not enforced; errno={value}")
        else:
            require(value in {errno.EPERM, errno.EACCES},
                    f"{label}: protected write not denied; errno={value}")


def check_comparator(case: str, code: int, output: str) -> None:
    """A crash, missing checker, or arbitrary nonzero exit is never a valid rejection."""
    if case == "valid":
        require(code == 0 and all(marker in output for marker in ACCEPTANCE),
                "Valid proof did not pass both kernels and Comparator")
    else:
        require(code > 0 and REJECTIONS[case] in output,
                f"{case}: expected Comparator rejection diagnostic missing")
        require("Your solution is okay!" not in output, "Conflicting acceptance and rejection")


def systemd_command(project: Path, lean: Path, comparator: Path, env: dict) -> list[str]:
    """Use the documented AF_UNIX guard; --pipe/--wait replace interactive --pty."""
    command = ["systemd-run", "--user", "--wait", "--pipe", "--collect",
               "--property=RestrictAddressFamilies=~AF_UNIX", "--property=RuntimeMaxSec=300",
               f"--working-directory={project}"]
    for key in ("PATH", "HOME", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA"):
        command.append(f"--setenv={key}={env[key]}")
    return command + [str(lean / "bin/lake"), "env", str(comparator), "config.json"]


class Preflight:
    def __init__(self, work: Path):
        self.work = work.resolve()
        self.evidence = self.work / "evidence"
        self.evidence.mkdir(parents=True, exist_ok=True)
        require(not (self.evidence / "receipt.json").exists(), "Use a fresh working directory")
        self.logs = self.evidence / "logs"
        self.logs.mkdir()
        self.env = os.environ.copy()
        self.receipt = {"status": "running", "scope": "tiny fixtures only; no mathematical proof",
                        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                        "commit": os.environ.get("GITHUB_SHA"), "run_id": os.environ.get("GITHUB_RUN_ID"),
                        "attempt": os.environ.get("GITHUB_RUN_ATTEMPT"), "commands": [], "checks": {}}
        self.flush()

    def flush(self):
        """Save a non-success receipt from the outset, including interrupted setup."""
        path = self.evidence / "receipt.json"
        temporary = path.with_suffix(".tmp")
        temporary.write_text(json.dumps(self.receipt, indent=2) + "\n", encoding="utf-8")
        temporary.replace(path)

    def command(self, label, args, *, cwd=None, allow_failure=False, timeout=1800):
        """Retain exact argv, combined diagnostics, exit status, and log identity."""
        args = [str(arg) for arg in args]
        log = self.logs / f"{len(self.receipt['commands']):02d}-{label}.log"
        entry = {"label": label, "argv": args, "cwd": str(cwd or self.work),
                 "log": str(log.relative_to(self.evidence)), "exit_code": None}
        self.receipt["commands"].append(entry)
        self.flush()
        print(f"Running {label}", flush=True)
        try:
            with log.open("w", encoding="utf-8") as output:
                result = subprocess.run(args, cwd=cwd or self.work, env=self.env,
                                        stdout=output, stderr=subprocess.STDOUT, timeout=timeout)
            entry["exit_code"] = result.returncode
        finally:
            if log.exists():
                entry["log_sha256"] = digest(log)
            self.flush()
        text = log.read_text(encoding="utf-8", errors="replace")
        require(allow_failure or result.returncode == 0, f"{label} failed; see {log.name}")
        return result.returncode, text

    def checkout(self, name, url, revision):
        folder = self.work / "tools" / name
        self.command(f"clone-{name}", ["git", "clone", "--no-checkout", url, folder])
        self.command(f"pin-{name}", ["git", "checkout", "--detach", revision], cwd=folder)
        _, actual = self.command(f"identity-{name}", ["git", "rev-parse", "HEAD"], cwd=folder)
        require(actual.strip() == revision, f"{name} revision mismatch")
        return folder

    def setup(self):
        require(platform.system() == "Linux" and platform.machine() == "x86_64", "Requires x86_64 Linux")
        require(os.geteuid() != 0, "Do not run as root")
        require(self.env.get("RUNNER_ENVIRONMENT") == "github-hosted" and
                self.env.get("ImageOS") == "ubuntu24", "Requires GitHub-hosted ubuntu-24.04")
        require(self.work.is_relative_to(Path(self.env["RUNNER_TEMP"]).resolve()), "Work must stay in RUNNER_TEMP")
        require(not self.work.is_relative_to(REPO), "Work must be outside the source checkout")
        self.command("host", ["uname", "-a"])
        self.command("identity", ["id"])
        self.command("systemd", ["systemctl", "--user", "show", "--property=Version"])
        self.receipt["host"] = {key: self.env.get(key) for key in
                                ("ImageOS", "ImageVersion", "RUNNER_ENVIRONMENT", "XDG_RUNTIME_DIR")}
        pins = json.loads(PINS.read_text(encoding="utf-8"))
        self.receipt["pins_file_sha256"] = digest(PINS)
        self.receipt["pins"] = {key: value for key, value in pins.items() if key != "cases"}
        self.receipt["landrun"] = LANDRUN
        self.receipt["inputs"] = {path.name: digest(path) for path in
                                   (HERE / "preflight.py", HERE / "boundary_probe.c")}
        tools = self.work / "tools"
        tools.mkdir()
        self.env.update(GOCACHE=str(self.work / "go-cache"), GOMODCACHE=str(self.work / "go-modules"),
                        GOTOOLCHAIN="local", CARGO_HOME=str(self.work / "cargo"),
                        RUSTUP_HOME=str(self.work / "rustup"))
        _, go = self.command("go-version", ["go", "version"])
        require(go.split()[2] == GO, "Unexpected Go version")
        archive = tools / "lean.zip"
        name = f"lean-{pins['lean_version']}-linux"
        self.command("download-lean", ["curl", "-fL", "--retry", "3", "-o", archive,
                     f"https://github.com/leanprover/lean4/releases/download/v{pins['lean_version']}/{name}.zip"])
        require(digest(archive) == pins["lean_archive_sha256"], "Lean archive hash mismatch")
        self.command("extract-lean", ["unzip", "-q", archive, "-d", tools])
        self.lean = tools / name
        self.env["PATH"] = str(self.lean / "bin") + os.pathsep + self.env["PATH"]
        _, lean_version = self.command("lean-version", [self.lean / "bin/lean", "--version"])
        require(pins["lean_commit"] in lean_version, "Lean revision mismatch")
        self.command("rust-version", ["rustup", "toolchain", "install", pins["rust"], "--profile", "minimal"])
        self.command("rust-identity", ["rustup", "run", pins["rust"], "rustc", "--version"])
        landrun = self.checkout("landrun", "https://github.com/Zouuup/landrun", LANDRUN)
        self.command("build-landrun", ["go", "build", "-mod=readonly", "-o", landrun / "landrun", "./cmd/landrun"], cwd=landrun)
        exporter = self.checkout("exporter", "https://github.com/leanprover/lean4export", pins["exporter"])
        comparator = self.checkout("comparator", "https://github.com/leanprover/comparator", pins["comparator"])
        for label, project, target in (("exporter", exporter, "lean4export"), ("comparator", comparator, "comparator")):
            # Only tool scratch checkouts change; proof/toolchain pins stay intact.
            (project / "lean-toolchain").write_text(f"leanprover/lean4:v{pins['lean_version']}\n", encoding="utf-8")
            self.command(f"build-{label}", [self.lean / "bin/lake", "build", target], cwd=project)
        manifest = json.loads((comparator / "lake-manifest.json").read_text())
        require(next(p['rev'] for p in manifest['packages'] if p['name'] == 'lean4export') == pins['exporter'],
                "Comparator exporter dependency drifted")
        _, dependency = self.command("comparator-exporter-identity", ["git", "rev-parse", "HEAD"],
                                     cwd=comparator / ".lake/packages/lean4export")
        require(dependency.strip() == pins["exporter"], "Built exporter dependency revision mismatch")
        nanoda = self.checkout("nanoda", "https://github.com/ammkrn/nanoda_lib", pins["nanoda"])
        self.command("build-nanoda", ["rustup", "run", pins["rust"], "cargo", "build", "--release", "--locked"], cwd=nanoda)
        self.comparator = comparator / ".lake/build/bin/comparator"
        self.env.update(COMPARATOR_LANDRUN=str(landrun / "landrun"),
                        COMPARATOR_LEAN4EXPORT=str(exporter / ".lake/build/bin/lean4export"),
                        COMPARATOR_NANODA=str(nanoda / "target/release/nanoda_bin"))
        self.helper = self.lean / "bin/preflight-boundary-probe"
        self.command("cc-version", ["cc", "--version"])
        self.command("build-boundary-helper", ["cc", "-std=c11", "-Wall", "-Wextra", "-Werror",
                     HERE / "boundary_probe.c", "-o", self.helper])
        binaries = {"lean": self.lean / "bin/lean", "lake": self.lean / "bin/lake",
                    "comparator": self.comparator, "probe": self.helper,
                    **{key: Path(self.env[key]) for key in
                       ("COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA")}}
        self.receipt["binaries"] = {key: {"path": str(path), "sha256": digest(path)} for key, path in binaries.items()}
        self.receipt["checks"]["tools"] = "passed"
        self.flush()

    def fixture(self, case):
        project = self.work / case
        project.mkdir()
        (project / ".lake").mkdir()
        (project / "lean-toolchain").write_text(f"leanprover/lean4:v{self.receipt['pins']['lean_version']}\n")
        (project / "lakefile.toml").write_text('name = "preflight"\n[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Solution"\n')
        (project / "Challenge.lean").write_text("theorem preflight : True := True.intro\n")
        config = {"challenge_module": "Challenge", "solution_module": "Solution",
                  "theorem_names": ["preflight"], "permitted_axioms": AXIOMS, "enable_nanoda": True}
        (project / "config.json").write_text(json.dumps(config, indent=2) + "\n")
        bodies = {"valid": "theorem preflight : True := True.intro\n",
                  "mismatch": "theorem preflight : 1 = 1 := rfl\n",
                  "axiom": "axiom preflight_forbidden : True\ntheorem preflight : True := preflight_forbidden\n"}
        prefix = ""
        protected = {}
        if case == "valid":
            allowed = project / ".lake/allowed.txt"
            outside = self.work / "outside-marker"
            tool = self.lean / "protected-marker"
            for file in (allowed, outside, tool):
                file.write_text("sentinel\n")
            (project / ".lake/escape").symlink_to(self.work, target_is_directory=True)
            paths = [allowed, project / "Challenge.lean", project / "config.json", tool, outside,
                     project / ".lake/escape/outside-marker"]
            originals = {path: path.read_bytes() for path in paths[:5]}
            _, baseline = self.command("unrestricted-boundary-baseline", [self.helper, *paths])
            check_boundary(json.loads(baseline), isolated=False)
            for path, contents in originals.items():
                path.write_bytes(contents)
            protected = {path: digest(path) for path in paths[1:5]}
            args = ", ".join(json.dumps(str(path)) for path in paths)
            prefix = ('import Lean\n#eval do\n'
                      f'  let result ← IO.Process.output {{ cmd := {json.dumps(str(self.helper))}, args := #[{args}] }}\n'
                      '  if result.exitCode != 0 then throw (IO.userError result.stderr)\n'
                      '  IO.FS.writeFile ".lake/boundary.json" result.stdout\n')
        (project / "Solution.lean").write_text(prefix + bodies[case], encoding="utf-8")
        # Controlled stdlib-only Lake configuration; no candidate imports/builds.
        self.command(f"{case}-lake-update", [self.lean / "bin/lake", "update"], cwd=project)
        code, output = self.command(f"{case}-comparator", systemd_command(project, self.lean, self.comparator, self.env),
                                    cwd=project, allow_failure=True, timeout=360)
        check_comparator(case, code, output)
        if case == "valid":
            require((project / ".lake/boundary.json").is_file(), "Boundary probe did not run")
            result = json.loads((project / ".lake/boundary.json").read_text())
            check_boundary(result, isolated=True)
            require((project / ".lake/allowed.txt").read_text() == "sentinel\n\n", "Permitted write did not persist")
            require(all(digest(path) == expected for path, expected in protected.items()), "Protected input changed")
            self.receipt["boundary"] = result
            self.receipt["checks"]["isolation"] = "passed"
        self.receipt["checks"][case] = "passed"
        self.flush()

    def collect(self, *, required=False):
        """Keep small generated inputs/outputs on failure without publishing build trees."""
        retained = {}
        for case in ("valid", "mismatch", "axiom"):
            source = self.work / case
            destination = self.evidence / "fixtures" / case
            for name in ("Challenge.lean", "Solution.lean", "lakefile.toml", "lean-toolchain", "config.json", ".lake/boundary.json"):
                file = source / name
                if required and (name != ".lake/boundary.json" or case == "valid"):
                    require(file.is_file(), f"Required evidence missing: {case}/{name}")
                if file.is_file():
                    destination.mkdir(parents=True, exist_ok=True)
                    saved = destination / file.name
                    shutil.copyfile(file, saved)
                    retained[str(saved.relative_to(self.evidence))] = digest(saved)
        self.receipt["retained_files"] = retained
        if required:
            for entry in self.receipt["commands"]:
                log = self.evidence / entry["log"]
                require(entry["exit_code"] is not None and log.is_file() and
                        digest(log) == entry["log_sha256"], "Command evidence missing or changed")
            for binary in self.receipt["binaries"].values():
                require(digest(Path(binary["path"])) == binary["sha256"], "Trusted tool changed during checks")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", required=True, type=Path)
    args = parser.parse_args()
    run = Preflight(args.work_dir)
    try:
        run.setup()
        for case in ("valid", "mismatch", "axiom"):
            run.fixture(case)
        require(set(run.receipt["checks"]) == {"tools", "isolation", "valid", "mismatch", "axiom"}, "Incomplete preflight")
        require(digest(PINS) == run.receipt["pins_file_sha256"], "Existing pins changed")
        run.collect(required=True)
        run.receipt["status"] = "passed"
    except Exception as exc:
        run.receipt["status"] = "failed"
        run.receipt["error"] = f"{type(exc).__name__}: {exc}"
        print(run.receipt["error"], file=sys.stderr)
        run.collect()
    finally:
        run.receipt["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        run.flush()
    return 0 if run.receipt["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

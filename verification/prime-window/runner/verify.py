"""Fresh, isolated Lean builds and a same-byte five-theorem comparison on Linux."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
KIT = HERE.parent
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
ROOTS = AXIOMS + """Quot Quot.mk Quot.lift Quot.ind Nat.add Nat.sub Nat.mul Nat.pow
Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam
semiOutParam outParam""".split()
PINS = {"lean": "bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38",
        "lake": "8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1",
        "leanexport": "c7c33370e238b31a7eb763c9c3f42f17677112d2c3e443a9155432480d791375",
        "leanchecker": "12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6",
        "nanoda_bin": "cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5"}


def sha(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(path):
    return json.loads(path.read_text())


def graph(src, root):
    """Visit only source modules in this side's tree. Lean resolves library imports."""
    ordered = []
    seen = set()

    def visit(name):
        path = src / (name.replace(".", "/") + ".lean")
        if name in seen or not path.is_file():
            return
        seen.add(name)
        for line in path.read_text(encoding="utf-8").splitlines():
            match = re.match(r"^\s*(?:(?:public|meta|private)\s+)*import\s+(.+)", line)
            if match:
                for dependency in match[1].split("--")[0].split("/-")[0].split():
                    if re.fullmatch(r"[\w.]+", dependency):
                        visit(dependency)
        ordered.append((name, path.relative_to(src)))
    visit(root)
    return ordered


class Run:
    def __init__(self, args):
        self.work = args.work.resolve()
        self.work.mkdir()
        self.logs = self.work / "evidence"
        self.logs.mkdir()
        self.tool = args.toolchain.resolve(strict=True)
        self.bwrap = args.bwrap.resolve(strict=True)
        self.env = {"PATH": f"{self.tool}/bin:/usr/bin:/bin", "HOME": str(self.work),
                    "LC_ALL": "C.UTF-8", "LEAN_NUM_THREADS": "2",
                    "COMPARATOR_BWRAP": str(self.bwrap)}
        self.bus_env = {"PATH": "/usr/bin:/bin", "XDG_RUNTIME_DIR": f"/run/user/{os.getuid()}",
                        "DBUS_SESSION_BUS_ADDRESS": f"unix:path=/run/user/{os.getuid()}/bus"}
        self.mounts = []
        self.paths = []
        self.report = {"status": "running", "tools": {}, "commands": [], "exports": {},
                       "revision": os.environ.get("GITHUB_SHA"), "uid": os.getuid()}
        for name, expected in PINS.items():
            actual = sha(self.tool / "bin" / name)
            require(actual == expected, f"Unexpected tool: {name}")
            self.report["tools"][name] = actual
        self.report["tools"]["bwrap"] = sha(self.bwrap)
        self.save()

    def save(self):
        (self.logs / "receipt.json").write_text(json.dumps(self.report, indent=2) + "\n")

    def call(self, label, cmd, *, reject=None, success=(), export=None):
        print(label, flush=True)
        log = self.logs / (label + ".log")
        start = time.monotonic()
        restricted = ["systemd-run", "--user", "--wait", "--pipe", "--collect", "--quiet",
                      "--property=RestrictAddressFamilies=~AF_UNIX", "--property=RuntimeMaxSec=5400",
                      f"--working-directory={self.work}", "/usr/bin/env", "-i",
                      *[f"{k}={v}" for k, v in self.env.items()], *cmd]
        with log.open("wb") as stream:
            if export:
                with export.open("xb") as out:
                    p = subprocess.run(restricted, stdout=out, stderr=stream, env=self.bus_env, cwd=self.work)
            else:
                p = subprocess.run(restricted, stdout=stream, stderr=subprocess.STDOUT, env=self.bus_env, cwd=self.work)
        self.report["commands"].append({"label": label, "exit": p.returncode, "expected_rejection": reject,
                                        "seconds": round(time.monotonic()-start, 2), "log_sha256": sha(log)})
        self.save()
        msg = log.read_text(errors="replace")
        if reject:
            require(p.returncode != 0 and re.search(reject, msg, re.I), f"Unexpected rejection result: {msg[-1500:]}")
        else:
            require(p.returncode == 0 and all(s in msg for s in success), f"{label}: {msg[-1500:]}")

    def box(self, src, build, *, writable, mathlib):
        cmd = [self.bwrap, "--die-with-parent", "--new-session", "--unshare-all", "--clearenv",
               "--ro-bind", "/usr", "/usr", "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]
        for name in ("bin", "lib", "lib64", "sbin"):
            path = Path("/") / name
            if path.is_symlink():
                cmd.extend(["--symlink", os.readlink(path), path])
            elif path.is_dir():
                cmd.extend(["--ro-bind", path, path])
        cmd += ["--ro-bind", self.tool, "/tool", "--ro-bind", src, "/src",
                "--bind" if writable else "--ro-bind", build, "/build"]
        paths = ["/build"]
        if mathlib:
            cmd += self.mounts
            paths += self.paths
        return cmd + ["--setenv", "PATH", "/tool/bin:/usr/bin:/bin", "--setenv", "HOME", "/tmp",
                      "--setenv", "LC_ALL", "C.UTF-8", "--setenv", "LEAN_NUM_THREADS", "2",
                      "--setenv", "LEAN_PATH", ":".join(paths), "--chdir", "/src", "--"]

    def build_export(self, src, root, names, mathlib):
        build = self.work / ("build-" + root)
        build.mkdir()
        for name, rel in graph(src, root):
            output = rel.with_suffix(".olean")
            (build / output.parent).mkdir(parents=True, exist_ok=True)
            options = []
            if name.startswith("Zeta2FourTrajectoryMatrices."):
                options = ["-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3"]
            elif root == "Solution" and not name.startswith("PrimeNumberTheoremAnd.") and name != "PrimeNumeratorPNT":
                options = ["-DautoImplicit=false"]
            self.call("build-" + root + "-" + name, self.box(src, build, writable=True, mathlib=mathlib)
                      + ["/tool/bin/lean", "-j2", *options, "-o", "/build/" + str(output), str(rel)])
        export = self.work / (root + ".ndjson")
        self.call("export-" + root, self.box(src, build, writable=False, mathlib=mathlib)
                  + ["/tool/bin/leanexport", root, "--", *names, *ROOTS], export=export)
        self.report["exports"][root] = {"sha256": sha(export), "bytes": export.stat().st_size}
        self.save()
        return export

    def compare(self, label, config, challenge, solution, reject=None):
        before = [sha(p) for p in (config, challenge, solution)]
        self.call(label, [self.tool / "bin/lake", "comparator", "--config", config,
                          "--challenge-from-export", challenge, "--solution-from-export", solution],
                  reject=reject, success=("nanoda kernel accepts the solution",
                                          "Lean default kernel accepts the solution", "Your solution is okay!"))
        require(before == [sha(p) for p in (config, challenge, solution)], "Comparator input changed")
        self.report["commands"][-1]["input_sha256"] = before
        self.save()

    def controls(self):
        src = HERE / "controls"
        (self.work / "empty").mkdir()
        self.call("namespace", self.box(src, self.work / "empty", writable=False, mathlib=False)
                  + ["/bin/sh", "-ec", 'test ! -e /home; test ! -e /root; test ! -e /etc; test "$(ls /sys 2>/dev/null || true)" = ""'])
        probe = """import errno, pathlib, socket
print("Checking writable scratch and read-only source", flush=True)
pathlib.Path('/build/probe').write_text('ok')
try:
    pathlib.Path('/src/FixtureChallenge.lean').open('ab')
except OSError as exc:
    assert exc.errno in (errno.EROFS, errno.EACCES, errno.EPERM)
else:
    raise RuntimeError('Source was writable')
for kind in (socket.SOCK_STREAM, socket.SOCK_DGRAM):
    try:
        socket.socket(socket.AF_UNIX, kind)
    except OSError as exc:
        assert exc.errno in (errno.EPERM, errno.EACCES, errno.EAFNOSUPPORT)
        print('AF_UNIX denied', kind, exc.errno)
    else:
        raise RuntimeError('Unix socket allowed')
print('Boundary controls passed')
"""
        self.call("boundary-controls", self.box(src, self.work / "empty", writable=True, mathlib=False)
                  + ["/usr/bin/python3", "-I", "-B", "-c", probe], success=("Boundary controls passed",))
        config = dict(read(KIT / "spec/config.json"), theorem_names=["fixture"])
        challenge = self.build_export(src, "FixtureChallenge", ["fixture"], False)
        for name, reject in (("FixturePositive", None), ("FixtureStatementMismatch", "statement.*match"),
                             ("FixtureDefinitionMismatch", "Const does not match.*auditValue"),
                             ("FixtureForbiddenAxiom", "axiom.*forbiddenAuditAssumption|forbiddenAuditAssumption.*permitted")):
            sol = self.build_export(src, name, ["fixture"], False)
            cfg = self.work / (name + ".json")
            cfg.write_text(json.dumps(dict(config, challenge_module="FixtureChallenge", solution_module=name)))
            self.compare("compare-" + name, cfg, challenge, sol, reject)
        for name, reject in (("positive", None), ("ill-typed", r"assertion failed: self\.def_eq")):
            build = self.work / ("nano-" + name)
            build.mkdir()
            cfg = dict(export_file_path=f"/src/{name}.ndjson", permitted_axioms=AXIOMS, num_threads=1,
                       unpermitted_axiom_hard_error=True, nat_extension=True, string_extension=True,
                       print_success_message=True, print_axioms=True, pp_to_stdout=True)
            (build / "config.json").write_text(json.dumps(cfg))
            self.call("nanoda-" + name, self.box(src, build, writable=False, mathlib=False)
                      + ["/tool/bin/nanoda_bin", "/build/config.json"], reject=reject,
                      success=("with no errors",))

    def proof(self, args):
        upstream = args.upstream.resolve(strict=True)
        pins = read(KIT / "inputs/pins.json")
        git = ["git", "-C", upstream]
        rev = subprocess.check_output([*git, "rev-parse", "HEAD"], text=True).strip()
        require(rev == pins["upstream"]["commit"], "Unexpected upstream revision")
        src = self.work / "solution"
        cmd = [sys.executable, "-I", "-B", KIT / "inputs/materialize.py", upstream, src]
        if args.pnt_cache:
            cmd += ["--pnt-cache", args.pnt_cache.resolve()]
        subprocess.run(cmd, check=True)
        rels = subprocess.check_output([*git, "ls-tree", "-r", "--name-only", rev,
                                        "Zeta2FourTrajectoryMatrices"], text=True).splitlines()
        for rel in rels:
            if rel.endswith(".lean") and not (src / rel).exists():
                target = src / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(subprocess.check_output([*git, "show", f"{rev}:{rel}"]))
        packages = args.packages.resolve(strict=True)
        manifest = KIT / "inputs/lake-manifest.json"
        require(sha(manifest) == "02c04e6e9f3e742e0c69312423caaa4470657cc319a3488a8c431bc3106a58d2",
                "Unexpected dependency manifest")
        self.report["dependency_revisions"] = {}
        for package in read(manifest)["packages"]:
            path = packages / package["name"]
            actual = subprocess.check_output(["git", "-C", path, "rev-parse", "HEAD"], text=True).strip()
            require(actual == package["rev"], f"Unexpected dependency revision: {path}")
            self.report["dependency_revisions"][package["name"]] = actual
            lib = path / ".lake/build/lib/lean"
            if lib.is_dir():
                dest = "/deps/" + package["name"]
                self.mounts.extend(["--ro-bind", lib, dest])
                self.paths.append(dest)
        spec = KIT / "spec"
        cfg = read(spec / "config.json")
        names = cfg["theorem_names"]
        require(len(set(names)) == len(names) == 5 and cfg["permitted_axioms"] == AXIOMS and
                cfg["external_kernels"] == {"nanoda": ["nanoda_bin"]}, "Unexpected comparison policy")
        ch_src = self.work / "challenge"
        ch_src.mkdir()
        shutil.copyfile(spec / "Challenge.lean", ch_src / "Challenge.lean")
        shutil.copyfile(spec / "Solution.lean", src / "Solution.lean")
        self.report.update(upstream=rev, manifest_sha256=sha(manifest), targets=names,
                           spec_sha256={p.name: sha(p) for p in spec.glob("*") if p.is_file()},
                           source_sha256=sha(KIT / "inputs/source-sha256.txt"))
        self.save()
        ch = self.build_export(ch_src, "Challenge", names, True)
        sol = self.build_export(src, "Solution", names, True)
        self.compare("compare-five-theorems", spec / "config.json", ch, sol)
        require(self.input_hashes == kit_hashes(), "Verification inputs changed during execution")
        self.report["inputs_post_sha256"] = self.input_hashes


def kit_hashes():
    files = [KIT / "inputs/SHA256SUMS", *sorted((KIT / "spec").glob("*.lean")),
             KIT / "spec/config.json", HERE / "verify.py", *sorted((HERE / "controls").glob("*"))]
    for line in files[0].read_text().splitlines():
        expected, rel = line.split("  ", 1)
        target = KIT / "inputs" / rel
        require(sha(target) == expected, f"Unexpected kit input {rel}")
        files.append(target)
    return {p.relative_to(KIT).as_posix(): sha(p) for p in files}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("work", "toolchain", "bwrap", "upstream", "packages", "pnt-cache"):
        parser.add_argument("--" + name, type=Path, required=name in ("work", "toolchain", "bwrap"))
    parser.add_argument("--controls-only", action="store_true")
    args = parser.parse_args()
    require(os.getuid() != 0, "Run as an ordinary user")
    run = Run(args)
    run.input_hashes = kit_hashes()
    run.report["inputs_pre_sha256"] = run.input_hashes
    run.save()
    try:
        run.controls()
        if not args.controls_only:
            require(args.upstream and args.packages, "Full run needs upstream and packages")
            run.proof(args)
    except BaseException:
        run.report["status"] = "failed"
        run.save()
        raise
    require(run.input_hashes == kit_hashes(), "Input hashes changed")
    run.report["inputs_post_sha256"] = run.input_hashes
    run.report["status"] = "controls passed" if args.controls_only else "passed"
    run.save()


if __name__ == "__main__":
    main()

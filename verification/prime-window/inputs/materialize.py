"""Reconstruct the exact Lean source overlay from independently pinned inputs."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--pnt-cache", type=Path)
    args = parser.parse_args()
    kit = Path(__file__).resolve().parent
    recipes = kit / "recipes"
    pin = json.loads((kit / "pins.json").read_text())["upstream"]["commit"]
    git = ["git", "-C", str(args.upstream)]
    if subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip() != pin:
        raise SystemExit("Expected the pinned trajectory checkout")
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        raise SystemExit("Choose an empty source output directory")
    for path in recipes.glob("*.lean"):
        shutil.copyfile(path, out / path.name)
    for name in ("numerator", "local", "chamber"):
        subprocess.run([sys.executable, recipes / f"prepare_kernel_{name}.py", args.upstream, out], check=True)
    with tempfile.TemporaryDirectory() as temporary:
        cache = args.pnt_cache if args.pnt_cache else Path(temporary)
        subprocess.run([sys.executable, kit / "prepare_pnt.py", out, "--cache", cache], check=True)
    rel = "Zeta2FourTrajectoryMatrices/ArithmeticRate/arith_rate.lean"
    source = subprocess.check_output(git + ["show", f"{pin}:{rel}"]).decode()
    old = "axiom prime_number_theorem :\n    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)"
    if source.count(old) != 1:
        raise SystemExit("Expected a unique pinned prime number theorem declaration")
    replacement = old.replace("axiom", "theorem", 1) + " :=\n  PrimeNumeratorPNT.prime_number_theorem"
    path = out / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(("import PrimeNumeratorPNT\n" + source.replace(old, replacement)).encode())
    expected = {}
    for line in (kit / "source-sha256.txt").read_text().splitlines():
        digest, name = line.split("  ", 1)
        expected[name] = digest
    actual = {f.relative_to(out).as_posix(): hashlib.sha256(f.read_bytes()).hexdigest()
              for f in out.rglob("*.lean")}
    if actual != expected:
        raise SystemExit("Generated source paths or hashes differ from the verified overlay")
    print(f"Verified {len(actual)} Lean source files.")


if __name__ == "__main__":
    main()

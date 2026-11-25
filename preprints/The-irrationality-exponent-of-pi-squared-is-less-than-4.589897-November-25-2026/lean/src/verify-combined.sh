#!/usr/bin/env bash
# Replay the π² proof in a new directory using the pinned upstream Lake project.
# Usage: bash verify-combined.sh UPSTREAM_CHECKOUT [NEW_OUTPUT_DIRECTORY]
set -euo pipefail
sources=$(cd -- "$(dirname -- "$0")" && pwd)
upstream=$(cd -- "${1:?Pass the upstream checkout}" && pwd)
if [[ $# -gt 1 ]]; then
  mkdir -- "$2"
  build=$(cd -- "$2" && pwd)
else
  build=$(mktemp -d)
fi
exec > >(tee "$build/transcript.log") 2>&1
printf 'Replay directory %s\n' "$build"
date -u
cd -- "$upstream"
pin=a0e8ac417cddc6ffa88e43cfd68d2b58ea339517
[[ $(git rev-parse HEAD) = "$pin" ]]
git diff --exit-code HEAD -- Zeta2FourTrajectoryMatrices lakefile.toml lake-manifest.json lean-toolchain
printf 'Upstream commit %s\n' "$pin"
unset LEAN_PATH LEAN_SRC_PATH
lake_bin=${LAKE_BIN:-lake}
lean_bin=$("$lake_bin" env which lean)
"$lean_bin" --version
[[ $("$lean_bin" --version) == *"4.35.0-rc4"*"c29b6dda4f7c20e3eeaa717c4e565663c5cfa364"* ]]
python3 - <<'PY'
import json, pathlib, subprocess
for package in json.loads(pathlib.Path("lake-manifest.json").read_text())["packages"]:
    checkout = pathlib.Path(".lake/packages") / package["name"]
    actual = subprocess.check_output(["git", "-C", checkout, "rev-parse", "HEAD"], text=True).strip()
    if actual != package["rev"]:
        raise SystemExit(f"{checkout}: expected {package['rev']}, found {actual}")
    subprocess.run(["git", "-C", checkout, "diff", "--exit-code", "HEAD", "--"], check=True)
    print(f"{package['name']} {actual}")
PY
"$lake_bin" exe cache get Mathlib
"$lake_bin" build +Zeta2FourTrajectoryMatrices.MainTheorem:olean
pkg_path=$("$lake_bin" env printenv LEAN_PATH)
pkg_path=$(python3 -c 'import os,sys; print(":".join(os.path.abspath(p) for p in sys.argv[1].split(":") if p))' "$pkg_path")

proof="$build/pnt"
overlay="$build/overlay"
private="$build/private"
mkdir -p -- "$overlay" "$private" "$proof"
export LEAN_PATH="$pkg_path"
bash "$sources/verify-pnt.sh" "$upstream" "$proof"
export LEAN_PATH="$overlay:$proof:$pkg_path"
cd -- "$overlay"
# Lean resolves a package by its first directory in LEAN_PATH. Give the overlay
# the complete upstream package, passing through each unchanged compiled module.
# Rebuild the changed module and both of its downstream imports from source.
python3 - "$upstream" "$overlay" <<'PY'
from pathlib import Path
import re, sys
upstream, overlay = map(Path, sys.argv[1:])
root = "Zeta2FourTrajectoryMatrices"
rate = Path(root, "ArithmeticRate", "arith_rate.lean")
blueprint = Path(root, "Blueprint", "blueprint.lean")
main = Path(root, "MainTheorem.lean")
modules = [rate, blueprint, main]
changed = set()
for source in modules:
    changed.add(".".join(source.with_suffix("").parts))
downstream = set()
for path in (upstream / root).rglob("*.lean"):
    imports = re.findall(r"^(?:public )?import\s+(\S+)", path.read_text(), re.M)
    if changed.intersection(imports):
        downstream.add(path.relative_to(upstream))
if downstream != {blueprint, main}:
    raise SystemExit(f"Unexpected downstream modules: {downstream}")
lib = upstream / ".lake/build/lib/lean"
for artifact in (lib / root).rglob("*"):
    if not artifact.is_file():
        continue
    rel = artifact.relative_to(lib)
    if any(str(rel).startswith(str(source.with_suffix("")) + ".") for source in modules):
        continue
    target = overlay / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.symlink_to(artifact)
old = "axiom prime_number_theorem :\n    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)"
new = old.replace("axiom ", "theorem ", 1) + " :=\n  PrimeNumeratorPNT.prime_number_theorem"
for source in modules:
    text = (upstream / source).read_text()
    if source == rate:
        if text.count(old) != 1:
            raise SystemExit("The pinned prime number theorem declaration has changed")
        text = "import PrimeNumeratorPNT\n" + text.replace(old, new)
    target = overlay / source
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)
PY
for module in Zeta2FourTrajectoryMatrices/{ArithmeticRate/arith_rate,Blueprint/blueprint,MainTheorem}; do
  echo "Building overlay $module"
  "$lean_bin" -j1 -DautoImplicit=false -o "$module.olean" "$module.lean"
done

cd -- "$private"
export LEAN_PATH="$private:$overlay:$proof:$pkg_path"
python3 "$sources/prepare_kernel_local.py" "$upstream" "$private"
cmp "$sources/KernelLocal.lean" "$private/KernelLocal.lean"
modules=(KernelDigits Chambers Bounds KernelChamber KernelFactor KernelLocal KernelBridge
         KernelNumerator KernelContent KernelEndToEnd KernelReduction Rate FiniteRate RateBridge
         WindowGeometry WindowAggregate WindowPNT WindowCriterion WindowPi WindowFinal)
for module in "${modules[@]}"; do
  if [[ $module != KernelLocal ]]; then cp -- "$sources/$module.lean" .; fi
  echo "Building private module $module"
  "$lean_bin" -j1 -DautoImplicit=false -o "$module.olean" "$module.lean" 2>&1 | tee "$module.log"
done
cat > AxiomAudit.lean <<'LEAN'
import WindowFinal
#print axioms PrimeNumerator.WindowFinal.irrationality_measure_pi_sq
#print axioms PrimeNumerator.WindowFinal.rational_upper_bound
#print axioms PrimeNumerator.WindowFinal.finite_good_ratios
LEAN
"$lean_bin" -j1 AxiomAudit.lean 2>&1 | tee AxiomAudit.log
python3 - <<'PY'
from pathlib import Path
import re
text = Path("AxiomAudit.log").read_text()
entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
expected = {"PrimeNumerator.WindowFinal.irrationality_measure_pi_sq",
            "PrimeNumerator.WindowFinal.rational_upper_bound",
            "PrimeNumerator.WindowFinal.finite_good_ratios"}
if {name for name, _ in entries} != expected or len(entries) != len(expected):
    raise SystemExit("Missing final axiom reports")
for name, raw in entries:
    actual = {s.strip() for s in raw.split(",")}
    if actual != {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit(f"{name}: unexpected axioms {actual}")
PY
sha256sum -- "${modules[@]/%/.lean}" "${modules[@]/%/.olean}"
date -u
echo 'All three final statements verified with propext, Classical.choice, and Quot.sound.'

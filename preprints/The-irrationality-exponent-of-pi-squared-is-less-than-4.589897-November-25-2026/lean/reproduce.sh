#!/usr/bin/env bash
# Usage: bash reproduce.sh [existing pinned Leibtag et al. checkout]
set -euo pipefail
kit=$(cd -- "$(dirname -- "$0")" && pwd)
if [[ $# -gt 1 ]]; then echo "Usage: bash reproduce.sh [upstream-checkout]" >&2; exit 2; fi
if [[ $# -eq 1 ]]; then checkout=$(cd -- "$1" && pwd); fi
cd "$kit"
sha256sum --check SHA256SUMS
work=$(mktemp -d "${TMPDIR:-/tmp}/pi2-window.XXXXXXXX")
echo "Build and verification output: $work"
pin=a0e8ac417cddc6ffa88e43cfd68d2b58ea339517
if [[ $# -eq 0 ]]; then
  checkout="$work/upstream"
  git init -q "$checkout"
  git -C "$checkout" fetch --depth=1 https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices.git "$pin"
  git -C "$checkout" checkout -q --detach "$pin"
fi
[[ $(git -C "$checkout" rev-parse HEAD) = "$pin" ]]
# Fetch the manifest-pinned dependencies on a new checkout.
(cd "$checkout" && "${LAKE_BIN:-lake}" exe cache get Mathlib)
mkdir -p "$work/sources"
cp "$kit"/src/* "$work/sources/"
python3 "$work/sources/prepare_kernel_numerator.py" "$checkout" "$work/sources"
python3 "$work/sources/prepare_kernel_local.py" "$checkout" "$work/sources"
python3 "$work/sources/prepare_kernel_chamber.py" "$checkout" "$work/sources"
bash "$work/sources/verify-combined.sh" "$checkout" "$work/verified"
# Compile the optional catalogue formulation against the same checked objects.
cd "$checkout"
lean_bin=$("${LAKE_BIN:-lake}" env which lean)
dep_path=$("${LAKE_BIN:-lake}" env printenv LEAN_PATH)
dep_path=$(python3 -c 'import os,sys; print(":".join(os.path.abspath(x) for x in sys.argv[1].split(":") if x))' "$dep_path")
export LEAN_PATH="$work/verified/private:$work/verified/overlay:$work/verified/pnt:$dep_path"
cd "$work/verified/private"
cp "$work/sources/WindowCatalogue.lean" .
"$lean_bin" -j1 -DwarningAsError=true -DautoImplicit=false -o WindowCatalogue.olean WindowCatalogue.lean | tee WindowCatalogue.log
python3 - <<'PY'
import pathlib, re
reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]+)\]", pathlib.Path("WindowCatalogue.log").read_text()))
for name in ("pi_sq_catalogue_bound", "pi_sq_catalogue_lt"):
    axioms = reports["PrimeNumerator.WindowCatalogue." + name]
    if {s.strip() for s in axioms.split(",")} != {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit("Unexpected catalogue axiom report: " + axioms)
print("Both catalogue statements verified.")
PY

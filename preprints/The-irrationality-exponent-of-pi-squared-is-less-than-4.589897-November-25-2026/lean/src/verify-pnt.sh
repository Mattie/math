#!/usr/bin/env bash
# Usage: bash verify-pnt.sh PINNED_UPSTREAM PNT_BUILD_DIR
set -euo pipefail
sources=$(cd -- "$(dirname -- "$0")" && pwd)
upstream=$(cd -- "${1:?Pass the pinned upstream checkout}" && pwd)
mkdir -p -- "${2:?Pass the PNT build directory}"
build=$(cd -- "$2" && pwd)
cd -- "$upstream"
[[ $(git rev-parse HEAD) = a0e8ac417cddc6ffa88e43cfd68d2b58ea339517 ]]
[[ $(git -C .lake/packages/mathlib rev-parse HEAD) = 1f414401f69059aa7eead47b53ee40bd38455eeb ]]
lake_bin=${LAKE_BIN:-lake}
lean_bin=$("$lake_bin" env which lean)
[[ $("$lean_bin" --version) = *4.35.0-rc4* ]]
library=$("$lake_bin" env printenv LEAN_PATH)
library=$(python3 -c 'import os,sys; print(os.pathsep.join(os.path.abspath(p) for p in sys.argv[1].split(os.pathsep) if p))' "$library")
export LEAN_PATH="$build:$library"
python3 "$sources/prepare_pnt.py" "$build" ${PNT_SOURCE_CACHE:+--cache "$PNT_SOURCE_CACHE"}
cd -- "$build"
modules=(
    PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support
    PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics
    PrimeNumberTheoremAnd/Sobolev
    PrimeNumberTheoremAnd/SmoothExistence
    PrimeNumberTheoremAnd/Fourier
    PrimeNumberTheoremAnd/Wiener
    PrimeNumeratorPNT
)
for module in "${modules[@]}"; do
    "$lean_bin" -j2 -o "$module.olean" "$module.lean" >"$module.log" 2>&1 || { cat "$module.log" >&2; exit 1; }
done
cat >PntAxiomAudit.lean <<'LEAN'
import PrimeNumeratorPNT

example : Filter.Tendsto (fun x : ℝ => Chebyshev.theta x / x) Filter.atTop (nhds 1) :=
  PrimeNumeratorPNT.prime_number_theorem

#print axioms PrimeNumeratorPNT.prime_number_theorem
LEAN
"$lean_bin" PntAxiomAudit.lean | tee PntAxiomAudit.log
grep -Fxq "'PrimeNumeratorPNT.prime_number_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" PntAxiomAudit.log
sha256sum -- "${modules[@]/%/.lean}" "${modules[@]/%/.olean}" >pnt-sha256.txt

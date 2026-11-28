#!/usr/bin/env bash
# Run in a Lean 4.34.1 environment with the pinned inherited OAI libraries
# and Mathlib on LEAN_PATH. Usage: build-overlay.sh OUTPUT_LIB_DIRECTORY
set -euo pipefail
if [[ $# -ne 1 ]]; then
  printf 'Usage: %s OUTPUT_LIB_DIRECTORY\n' "$0" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")" && pwd)
mkdir -p -- "$1"
out=$(cd "$1" && pwd)
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"

compile() {
  local source_root=$1
  shift
  cd "$source_root"
  for module; do
    local file=${module//.//}
    mkdir -p "$out/$(dirname "$file")"
    lean -DautoImplicit=false -DwarningAsError=true \
      -o "$out/$file.olean" -i "$out/$file.ilean" "$file.lean"
  done
}

modules=(
  Reduction Colength CRT GradedLifts Triangular Packets FiniteInterpolation
  RationalWeights Margin Certificate Determinant WeightedArcs SectionArcBridge
  CurveGeometryCore CurveGeometryModel CurveGeometry CurveGeometryAdmissible
  CurveGeometryLift CurveGeometryArcs SectionPolynomials ProjectionUnit MonomialDegree
  SectionInitials Main FiniteExample LogExample Audit
)
for i in "${!modules[@]}"; do modules[$i]="PiTwoCaseBridge.${modules[$i]}"; done
compile "$root" "${modules[@]}"

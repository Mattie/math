#!/usr/bin/env bash
set -euo pipefail
# Rebuild the quadratic extension and audit without changing the dependency project.
package=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
build="$package/.verification"
mkdir -p "$build"
case "$(cd -- "$package/lean" && lean --version)" in
  'Lean (version 4.34.1,'*) ;;
  *) printf '%s\n' 'Use Lean 4.34.1 (the lean/lean-toolchain pin).' >&2; exit 1 ;;
esac
if [[ -z "${LEAN_DEPENDENCY_ROOT:-}" ]]; then
  LEAN_DEPENDENCY_ROOT=$(python3 "$package/scripts/fetch-dependency.py" "$build/dependency")
  export LEAN_DEPENDENCY_ROOT
  python3 "$package/scripts/check-sources.py" "$LEAN_DEPENDENCY_ROOT"
  # This project has no default Lake targets. Build actual imported modules.
  target_list=$(python3 "$package/scripts/dependency-targets.py")
  mapfile -t dependency_targets <<< "$target_list"
  (cd "$LEAN_DEPENDENCY_ROOT"; lake exe cache get; lake build "${dependency_targets[@]}")
fi
dependency=$(cd -- "$LEAN_DEPENDENCY_ROOT" && pwd)
python3 "$package/scripts/check-sources.py" "$dependency"
dependency_path=$(cd "$dependency"; lake env printenv LEAN_PATH)
export LEAN_PATH="$build/lib:$dependency_path"
mkdir -p "$build/lib/AlgebraicLog"
cd "$package/lean"
{
  lean --version
  for module in AnalyticData ParameterShape DimensionBudget AdmissibleParameters DeterminantData LiteralAnalyticSummand AnalyticAggregate CurveWeights ApproximationGeometry IntegerClearing QuadraticNorm MatrixArithmetic ArithmeticBounds GlobalMatrixInterpolation SelectedArithmetic ConjugateBound ConjugateDeterminant ConjugateAggregate EmbeddingBudget ContradictionNumerics DeterminantContradiction FieldRealization ExponentConsequence Main Examples AxiomAudit; do
    lean -DautoImplicit=false -o "$build/lib/AlgebraicLog/$module.olean" \
      -i "$build/lib/AlgebraicLog/$module.ilean" "AlgebraicLog/$module.lean"
  done
} 2>&1 | tee "$build/build.log"
python3 "$package/scripts/check-axioms.py" "$build/build.log" --source "AlgebraicLog/AxiomAudit.lean"
python3 "$package/scripts/check-sources.py" "$dependency"
printf '%s\n' 'Quadratic extension and audit rebuilt; dependency sources verified.'

#!/usr/bin/env bash
set -euo pipefail
# Rebuild the five new modules without changing the dependency project.
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
  # The pinned project has no default targets; build the actual inherited imports.
  target_list=$(python3 "$package/scripts/dependency-targets.py")
  mapfile -t dependency_targets <<< "$target_list"
  (cd "$LEAN_DEPENDENCY_ROOT"; lake exe cache get; lake build "${dependency_targets[@]}")
fi
dependency=$(cd -- "$LEAN_DEPENDENCY_ROOT" && pwd)
python3 "$package/scripts/check-sources.py" "$dependency"
dependency_path=$(cd "$dependency"; lake env printenv LEAN_PATH)
export LEAN_PATH="$build/lib:$dependency_path"
mkdir -p "$build/lib/Degree"
cd "$package/lean"
{
  lean --version
  for module in PolynomialPowers SectionDegrees AllPowers LogarithmBridge Audit; do
    lean -DautoImplicit=false -o "$build/lib/Degree/$module.olean" \
      -i "$build/lib/Degree/$module.ilean" "Degree/$module.lean"
  done
} 2>&1 | tee "$build/build.log"
python3 "$package/scripts/check-axioms.py" "$build/build.log" --source "Degree/Audit.lean"
python3 "$package/scripts/check-sources.py" "$dependency"
printf '%s\n' 'Five new modules rebuilt; dependency sources verified.'

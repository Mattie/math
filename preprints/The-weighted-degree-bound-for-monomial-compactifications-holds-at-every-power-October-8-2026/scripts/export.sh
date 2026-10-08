#!/usr/bin/env bash
set -euo pipefail
# Export the selected proof dependency closure after a native rebuild.
: "${LEAN_DEPENDENCY_ROOT:?Set this to the built pinned Lean dependency project}"
: "${LEAN4EXPORT:?Set this to lean4export built from the pinned revision in VERIFY.md}"
package=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
dependency=$(cd -- "$LEAN_DEPENDENCY_ROOT" && pwd)
python3 "$package/scripts/check-sources.py" "$dependency"
test -f "$package/.verification/lib/Degree/Audit.olean"
dependency_path=$(cd "$dependency"; lake env printenv LEAN_PATH)
export LEAN_PATH="$package/.verification/lib:$dependency_path"
mkdir -p "$package/.verification/export"
cd "$package/lean"
"$LEAN4EXPORT" Degree.Audit -- \
  Degree.supportBound_of_pow Degree.monomial_all_supportBound \
  Degree.logarithm_all_supportBound Degree.admissible_all_supportBound \
  Degree.Audit.projective_line_example > "$package/.verification/export/degree-main.ndjson"
python3 "$package/scripts/check-export.py" "$package/.verification/export/degree-main.ndjson"

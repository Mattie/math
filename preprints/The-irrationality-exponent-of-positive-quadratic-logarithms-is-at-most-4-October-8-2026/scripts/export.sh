#!/usr/bin/env bash
set -euo pipefail
# Export the selected proof dependency closure after a native rebuild.
: "${LEAN_DEPENDENCY_ROOT:?Set this to the built pinned Lean dependency project}"
: "${LEAN4EXPORT:?Set this to lean4export built from the pinned revision in VERIFY.md}"
package=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
dependency=$(cd -- "$LEAN_DEPENDENCY_ROOT" && pwd)
python3 "$package/scripts/check-sources.py" "$dependency"
test -f "$package/.verification/lib/AlgebraicLog/AxiomAudit.olean"
dependency_path=$(cd "$dependency"; lake env printenv LEAN_PATH)
export LEAN_PATH="$package/.verification/lib:$dependency_path"
mkdir -p "$package/.verification/export"
cd "$package/lean"
"$LEAN4EXPORT" AlgebraicLog.AxiomAudit -- \
  OAI.AlgebraicLog.quadratic_log_explicit_bound \
  OAI.AlgebraicLog.quadratic_log_irrational \
  OAI.AlgebraicLog.quadratic_log_irrationalityExponent_le_four \
  OAI.AlgebraicLog.Examples.first_sample_bound \
  OAI.AlgebraicLog.Examples.second_sample_bound > "$package/.verification/export/algebraic-main.ndjson"
python3 "$package/scripts/check-export.py" "$package/.verification/export/algebraic-main.ndjson"

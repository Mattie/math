#!/usr/bin/env bash
# Compile the vendored closure against the locked Mathlib dependency.
set -euo pipefail
package=$(cd "$(dirname "$0")/.." && pwd)
python3 "$package/scripts/check-package.py"
cd "$package/lean"
# Install dependencies at their lockfile revisions; fetch matching Mathlib objects.
lake exe cache get
lake build ClassificationAudit PositiveAudit PositiveChallenge ClassificationChallenge
mkdir -p "$package/build"
lake env lean -DautoImplicit=false -DwarningAsError=true ClassificationAudit.lean | tee "$package/build/classification-axioms.log"
lake env lean -DautoImplicit=false -DwarningAsError=true PositiveAudit.lean | tee "$package/build/positive-axioms.log"
python3 "$package/scripts/check-axioms.py" "$package/build/classification-axioms.log" --source ClassificationAudit.lean
python3 "$package/scripts/check-axioms.py" "$package/build/positive-axioms.log" --source PositiveAudit.lean

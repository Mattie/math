#!/usr/bin/env bash
# Exercise the actual axiom-output gate using Lean, including an imported hole.
set -euo pipefail
checker=$(realpath "${1:?Give the package check-axioms.py path}")
lean_bin="$(lean --print-prefix)/bin/lean"
temporary=$(mktemp -d)
trap 'rm -rf -- "$temporary"' EXIT
cd "$temporary"
"$lean_bin" -DwarningAsError=true --stdin > positive.log <<'LEAN'
theorem cleanControl : True := True.intro
#print axioms cleanControl
LEAN
python3 "$checker" positive.log --expect cleanControl
"$lean_bin" -DwarningAsError=true --stdin > axiom.log <<'LEAN'
axiom extraControl : False
theorem axiomControl : False := extraControl
#print axioms axiomControl
LEAN
if python3 "$checker" axiom.log --expect axiomControl > axiom-result.log 2>&1; then
  echo 'Forbidden axiom was accepted.' >&2; exit 1
fi
grep -F 'Unpermitted axioms for axiomControl: extraControl' axiom-result.log
cat > Sorried.lean <<'LEAN'
theorem cachedHole : False := by sorry
LEAN
"$lean_bin" -o Sorried.olean Sorried.lean
LEAN_PATH="$temporary" "$lean_bin" -DwarningAsError=true --stdin > sorry.log <<'LEAN'
import Sorried
theorem importedHoleControl : False := cachedHole
#print axioms importedHoleControl
LEAN
if python3 "$checker" sorry.log --expect importedHoleControl > sorry-result.log 2>&1; then
  echo 'Imported sorry was accepted.' >&2; exit 1
fi
grep -F 'Unpermitted axioms for importedHoleControl: sorryAx' sorry-result.log
echo 'Lean acceptance, forbidden-axiom, and imported-sorry controls passed.'

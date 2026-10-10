#!/usr/bin/env bash
# Build the public endpoints and enforce their transitive axiom policy.
set -euo pipefail
cd "$(dirname "$0")"
python3 ../scripts/check-publication.py
lake build PeriodicFamily.Main Quadratic.RationalFamilies Combined Solution Audit
mkdir -p ../.verification
lake env lean -DautoImplicit=false -DwarningAsError=true Audit.lean > ../.verification/axioms.log 2>&1
python3 ../scripts/check-axioms.py ../.verification/axioms.log --source Audit.lean
printf '%s\n' 'Explicit family targets built; six required axiom closures passed.'

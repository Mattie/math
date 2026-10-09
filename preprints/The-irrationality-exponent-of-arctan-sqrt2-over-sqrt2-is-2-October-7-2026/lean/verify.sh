#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
sha256sum --check sources.sha256
sha256sum --check formal-conjectures-sources.sha256
lake exe cache get
lake build Imaginary.EndpointAudit
lake build Imaginary.FormalConjectures
# Check the wrapper strictly without replaying dependency style warnings.
lake env lean -DwarningAsError=true Imaginary/FormalConjectures.lean
mkdir -p ../.verification
lake env lean Imaginary/EndpointAudit.lean 2>&1 | tee ../.verification/endpoint-axioms.log
python3 ../scripts/check-axioms.py ../.verification/endpoint-axioms.log --source Imaginary/EndpointAudit.lean
lake env lean -DwarningAsError=true --stdin 2>&1 <<'LEAN' | tee ../.verification/catalogue-axioms.log
import Imaginary.FormalConjectures
#print axioms OAI.Imaginary.normalized_arctan_sqrt_two_irrationality_and_bound
LEAN
python3 ../scripts/check-axioms.py ../.verification/catalogue-axioms.log --expect OAI.Imaginary.normalized_arctan_sqrt_two_irrationality_and_bound

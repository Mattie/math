#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
sha256sum --check sources.sha256
sha256sum --check formal-conjectures-sources.sha256
lake exe cache get
lake build Arctangent.EndpointAudit
lake build Arctangent.FormalConjectures
# Check the wrapper strictly without replaying dependency style warnings.
lake env lean -DwarningAsError=true Arctangent/FormalConjectures.lean
mkdir -p ../.verification
lake env lean Arctangent/EndpointAudit.lean 2>&1 | tee ../.verification/endpoint-axioms.log
python3 ../scripts/check-axioms.py ../.verification/endpoint-axioms.log --source Arctangent/EndpointAudit.lean
lake env lean -DwarningAsError=true --stdin 2>&1 <<'LEAN' | tee ../.verification/catalogue-axioms.log
import Arctangent.FormalConjectures
#print axioms OAI.Arctangent.rational_arctan_irrationality_and_bound
LEAN
python3 ../scripts/check-axioms.py ../.verification/catalogue-axioms.log --expect OAI.Arctangent.rational_arctan_irrationality_and_bound

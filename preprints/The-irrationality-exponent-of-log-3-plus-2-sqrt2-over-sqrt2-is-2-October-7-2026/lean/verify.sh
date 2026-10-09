#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
sha256sum --check sources.sha256
sha256sum --check formal-conjectures-sources.sha256
lake exe cache get
lake build RealNorm.EndpointAudit
lake build RealNorm.FormalConjectures
# Check the wrapper strictly without replaying dependency style warnings.
lake env lean -DwarningAsError=true RealNorm/FormalConjectures.lean
mkdir -p ../.verification
lake env lean RealNorm/EndpointAudit.lean 2>&1 | tee ../.verification/endpoint-axioms.log
python3 ../scripts/check-axioms.py ../.verification/endpoint-axioms.log --source RealNorm/EndpointAudit.lean
lake env lean -DwarningAsError=true --stdin 2>&1 <<'LEAN' | tee ../.verification/catalogue-axioms.log
import RealNorm.FormalConjectures
#print axioms OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound
LEAN
python3 ../scripts/check-axioms.py ../.verification/catalogue-axioms.log --expect OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound

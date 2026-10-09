#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake exe cache get
lake build Logarithm.AxiomAudit Logarithm.EndpointAudit
mkdir -p ../.verification
lake env lean Logarithm/AxiomAudit.lean 2>&1 | tee ../.verification/axioms.log
lake env lean Logarithm/EndpointAudit.lean 2>&1 | tee ../.verification/endpoints.log
python3 ../scripts/check-axioms.py ../.verification/axioms.log --source Logarithm/AxiomAudit.lean
python3 ../scripts/check-axioms.py ../.verification/endpoints.log --source Logarithm/EndpointAudit.lean

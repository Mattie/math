#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
sha256sum --check sources.sha256
sha256sum --check formal-conjectures-sources.sha256
lake exe cache get
lake build RealNorm.EndpointAudit
lake --wfail build RealNorm.FormalConjectures
lake env lean -DwarningAsError=true --stdin <<'LEAN'
import RealNorm.FormalConjectures
#print axioms OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound
LEAN

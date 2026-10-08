#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
sha256sum --check sources.sha256
sha256sum --check formal-conjectures-sources.sha256
lake exe cache get
lake build Arctangent.EndpointAudit
lake --wfail build Arctangent.FormalConjectures
lake env lean -DwarningAsError=true --stdin <<'LEAN'
import Arctangent.FormalConjectures
#print axioms OAI.Arctangent.rational_arctan_irrationality_and_bound
LEAN

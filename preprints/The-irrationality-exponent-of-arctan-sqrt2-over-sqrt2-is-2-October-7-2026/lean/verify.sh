#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
sha256sum --check sources.sha256
sha256sum --check formal-conjectures-sources.sha256
lake exe cache get
lake build Imaginary.EndpointAudit
lake --wfail build Imaginary.FormalConjectures
lake env lean -DwarningAsError=true --stdin <<'LEAN'
import Imaginary.FormalConjectures
#print axioms OAI.Imaginary.normalized_arctan_sqrt_two_irrationality_and_bound
LEAN

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
lake exe cache get
lake build Logarithm.AxiomAudit Logarithm.EndpointAudit
lake env lean Logarithm/AxiomAudit.lean
lake env lean Logarithm/EndpointAudit.lean

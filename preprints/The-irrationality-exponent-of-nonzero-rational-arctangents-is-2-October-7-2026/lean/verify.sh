#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lean --version
sha256sum --check sources.sha256
lake exe cache get
lake build Arctangent.EndpointAudit
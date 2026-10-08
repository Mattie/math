#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
: "${NANODA:?Set NANODA to the pinned nanoda_bin binary}"
printf '%s  %s\n' a726e9e6f9ff30e1844b9c79abe14d225a3dad8f77c07cebb528f81399b4f0fc release-assets/imaginary-main.ndjson.gz | sha256sum --check
gzip -dc release-assets/imaginary-main.ndjson.gz | "$NANODA" evidence/nanoda/replay-config.json

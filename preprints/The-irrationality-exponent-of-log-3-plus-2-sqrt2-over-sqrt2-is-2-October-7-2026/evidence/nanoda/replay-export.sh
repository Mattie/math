#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${NANODA:?Set NANODA to the pinned nanoda_bin binary}"
printf '%s  %s\n' ba956b96b984af6ca2ed76875df1dcefc841eb5dbe5017d010f2abc3c0cc1207 ../../release-assets/realnorm-main.ndjson.gz | sha256sum --check
gzip -dc ../../release-assets/realnorm-main.ndjson.gz | "$NANODA" replay-config.json

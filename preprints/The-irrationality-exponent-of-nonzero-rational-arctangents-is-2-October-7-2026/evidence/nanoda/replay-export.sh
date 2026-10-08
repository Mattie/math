#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
: "${NANODA:?Set NANODA to the pinned nanoda_bin}"
input=${1:-"$here/../../release-assets/arctangent-main.ndjson.gz"}
printf '%s  %s\n' 695453c9039fd6b88c066d7893e4c1b9d9de7c9ad51e873c5e374dab895a87dd "$input" | sha256sum --check
gzip -dc "$input" | "$NANODA" "$here/replay-config.json"

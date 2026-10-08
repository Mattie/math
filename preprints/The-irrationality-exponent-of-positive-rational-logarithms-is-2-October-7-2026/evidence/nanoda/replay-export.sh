#!/usr/bin/env bash
# Replay the exact retained proof export with the pinned Nanoda checker.
set -euo pipefail
script_dir=$(cd "$(dirname "$0")" && pwd)
: "${NANODA:?Set NANODA to the pinned nanoda_bin binary}"
# Publication relocation: accept a caller-relative path, or use the release asset.
export_file="$script_dir/../../release-assets/logarithm-main.ndjson.gz"
if [ "$#" -gt 0 ]; then export_file="$1"; fi
gzip -dc "$export_file" | "$NANODA" "$script_dir/replay-config.json"

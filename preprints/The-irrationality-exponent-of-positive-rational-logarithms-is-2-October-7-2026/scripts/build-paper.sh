#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
tectonic --keep-logs --outdir "$repo/build" "$repo/build/main.tex"
cp "$repo/build/main.pdf" "$repo/paper.pdf"

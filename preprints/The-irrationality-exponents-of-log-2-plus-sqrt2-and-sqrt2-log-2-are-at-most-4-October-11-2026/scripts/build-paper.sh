#!/usr/bin/env bash
# Requires Tectonic 0.15.0; a first build may download its TeX resource bundle.
set -euo pipefail
package=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$package/.work"
export SOURCE_DATE_EPOCH=1791676800
tectonic --keep-logs --outdir "$package/.work" "$package/build/main.tex"
cp "$package/.work/main.pdf" "$package/paper.pdf"

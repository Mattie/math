#!/usr/bin/env bash
set -euo pipefail
# Tectonic builds the standalone source; no external bibliography is required.
package=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
tool=${TECTONIC:-tectonic}
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
"$tool" --keep-logs --outdir "$tmp" "$package/build/main.tex"
if grep -Eq 'Overfull|Missing character|^!' "$tmp/main.log"; then
  printf '%s\n' 'Inspect the TeX diagnostics before distributing the PDF.' >&2
  exit 1
fi
cp "$tmp/main.pdf" "$package/paper.pdf"

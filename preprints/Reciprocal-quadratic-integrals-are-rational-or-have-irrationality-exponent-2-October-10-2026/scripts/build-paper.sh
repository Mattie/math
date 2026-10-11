#!/usr/bin/env bash
# Requires Python 3, Pandoc and Tectonic on PATH.
set -euo pipefail
package=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$package/build"
python3 "$package/scripts/prepare-manuscript.py"
pandoc "$package/build/typeset.md" --from=markdown+tex_math_single_backslash --standalone \
  --to=latex --template="$package/build-template.tex" -o "$package/build/main.tex"
tectonic --keep-logs --outdir "$package/build" "$package/build/main.tex"
cp "$package/build/main.pdf" "$package/paper.pdf"

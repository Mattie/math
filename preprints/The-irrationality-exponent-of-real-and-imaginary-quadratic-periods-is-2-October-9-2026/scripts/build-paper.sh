#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
python3 "$repo/scripts/prepare-manuscript.py" "$tmp/manuscript.md"
pandoc "$tmp/manuscript.md" --from=markdown+tex_math_single_backslash --standalone \
  --to=latex --template="$repo/build/template.tex" \
  -V documentclass=article -V fontsize=11pt -V geometry:margin=1.08in \
  -V colorlinks=true -V linkcolor=blue -V urlcolor=blue \
  --metadata title="The irrationality exponent of real and imaginary quadratic periods is 2" \
  --metadata author="Ryan Matthew Casper" --metadata date="October 9, 2026" \
  -o "$repo/build/main.tex"
tectonic --keep-logs --outdir "$tmp" "$repo/build/main.tex"
cp "$tmp/main.pdf" "$repo/paper.pdf"

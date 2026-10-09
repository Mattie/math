#!/usr/bin/env bash
set -euo pipefail
package=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
python3 "$package/scripts/prepare-manuscript.py" "$tmp/manuscript.md"
pandoc "$tmp/manuscript.md" --from=markdown+raw_tex --standalone --to=latex \
  --template="$package/build/template.tex" -o "$package/build/main.tex"
tectonic --keep-logs --outdir "$tmp" "$package/build/main.tex"
mkdir -p "$package/.verification"
cp "$tmp/main.log" "$package/.verification/paper.log"
if grep -Eq 'Overfull|Missing character|^!' "$tmp/main.log"; then
  printf '%s\n' 'Resolve TeX layout or glyph diagnostics before distributing the PDF.' >&2
  exit 1
fi
cp "$tmp/main.pdf" "$package/paper.pdf"

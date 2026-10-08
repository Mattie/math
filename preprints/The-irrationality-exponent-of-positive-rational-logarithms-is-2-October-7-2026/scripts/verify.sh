#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
python3 "$repo/scripts/check-publication.py"
cd "$repo/lean"
bash verify.sh
lake env lean ../review/blind-statement/CertifiedBridge.lean

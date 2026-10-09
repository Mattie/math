#!/usr/bin/env bash
# Run outside the checkout; never reuse an earlier successful result.
set -euo pipefail
exec python3 "$(dirname "$0")/verify.py" "$@"

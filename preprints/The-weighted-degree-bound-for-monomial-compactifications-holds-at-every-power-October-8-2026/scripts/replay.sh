#!/usr/bin/env bash
set -euo pipefail
# Check an existing export with a caller-supplied pinned checker executable.
package=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
route=${1:?Use nanoda or lean340 as the first argument}
input=${2:?Give the uncompressed export path as the second argument}
input=$(realpath -- "$input")
python3 "$package/scripts/check-export.py" "$input"
mkdir -p "$package/.verification/replay"
case "$route" in
  nanoda)
    : "${NANODA_BIN:?Set this to Nanoda built from the pinned revision in VERIFY.md}"
    python3 - "$package" "$input" <<'PY'
from pathlib import Path
import json, sys
package, artifact = Path(sys.argv[1]), sys.argv[2]
meta = json.loads((package / 'evidence/checker-metadata.json').read_text())
config = {'export_file_path': artifact, 'use_stdin': False,
          'permitted_axioms': meta['permitted_axioms'],
          'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False,
          'num_threads': 4, 'nat_extension': True, 'string_extension': True,
          'print_success_message': True, 'print_axioms': True,
          'pp_to_stdout': True, 'pp_declars': meta['endpoints'],
          'pp_options': {'proofs': False}}
(package / '.verification/replay/nanoda-config.json').write_text(json.dumps(config, indent=2))
PY
    "$NANODA_BIN" "$package/.verification/replay/nanoda-config.json"
    ;;
  lean340)
    : "${LEAN340_READER:?Set this to the retained reader built using Lean 4.34.0}"
    "$LEAN340_READER" "$input"
    ;;
  *) printf '%s\n' 'Unknown replay route.' >&2; exit 1 ;;
esac

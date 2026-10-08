#!/usr/bin/env bash
# Expected result: Nanoda rejects the deliberately forbidden axiom.
# The negative source stays outside the certified Logarithm tree.
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to the pinned lean4export binary}"
: "${NANODA:?Set NANODA to the pinned nanoda_bin binary}"
control_dir=${1:-$(mktemp -d)}
mkdir -p "$control_dir"
control_dir=$(cd "$control_dir" && pwd)
cat > "$control_dir/Bad.lean" <<'LEAN'
namespace IndependentControls
axiom deliberatelyForbidden : False
theorem negativeControl : False := deliberatelyForbidden
end IndependentControls
LEAN
lake env lean --root="$control_dir" "$control_dir/Bad.lean" -o "$control_dir/Bad.olean"
LEAN_PATH="$control_dir${LEAN_PATH:+:$LEAN_PATH}" "$LEAN4EXPORT" Bad -- \
  IndependentControls.negativeControl > "$control_dir/bad.ndjson"
python3 - "$control_dir" <<'PY'
import json, pathlib, sys
directory = pathlib.Path(sys.argv[1])
config = {'export_file_path': str(directory / 'bad.ndjson'), 'use_stdin': False,
    'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
    'unpermitted_axiom_hard_error': True, 'unsafe_permit_all_axioms': False,
    'num_threads': 4, 'nat_extension': True, 'string_extension': True,
    'print_success_message': True, 'print_axioms': False}
(directory / 'config.json').write_text(json.dumps(config, indent=2) + '\n')
PY
set +e
"$NANODA" "$control_dir/config.json" > "$control_dir/check.log" 2>&1
status=$?
set -e
cat "$control_dir/check.log"
test "$status" -ne 0
grep -F 'export file declares unpermitted axiom "IndependentControls.deliberatelyForbidden"' "$control_dir/check.log"
printf 'Negative control rejected as expected (exit %s).\n' "$status"

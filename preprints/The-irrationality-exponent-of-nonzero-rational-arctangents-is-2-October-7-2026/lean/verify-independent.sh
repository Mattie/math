#!/usr/bin/env bash
# Set LEAN4EXPORT and NANODA to binaries built from the pins in README.md.
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to the pinned lean4export binary}"
: "${NANODA:?Set NANODA to the pinned nanoda_bin binary}"
verification_dir=${1:-$(mktemp -d)}
mkdir -p "$verification_dir"
verification_dir=$(cd "$verification_dir" && pwd)
lake build Arctangent.Main
lake env "$LEAN4EXPORT" Arctangent.Main -- \
  OAI.Arctangent.arctan_half_irrationalityExponent_eq_two \
  OAI.Arctangent.arctan_half_explicit_bound \
  OAI.Arctangent.rational_arctan_irrationalityExponent_eq_two \
  OAI.Arctangent.rational_arctan_integer_eventualLowerBound \
  OAI.Arctangent.rational_arctan_explicit_bound \
  > "$verification_dir/arctangent-main.ndjson"
python3 - "$verification_dir" <<'PY'
import json, pathlib, sys
directory = pathlib.Path(sys.argv[1])
config = {
    'export_file_path': str(directory / 'arctangent-main.ndjson'),
    'use_stdin': False,
    'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
    'unpermitted_axiom_hard_error': True,
    'unsafe_permit_all_axioms': False,
    'num_threads': 4,
    'nat_extension': True,
    'string_extension': True,
    'print_success_message': True,
    'print_axioms': True,
    'pp_to_stdout': True,
    'pp_declars': ['OAI.Arctangent.arctan_half_irrationalityExponent_eq_two',
        'OAI.Arctangent.arctan_half_explicit_bound',
        'OAI.Arctangent.rational_arctan_irrationalityExponent_eq_two',
        'OAI.Arctangent.rational_arctan_integer_eventualLowerBound',
        'OAI.Arctangent.rational_arctan_explicit_bound'],
    'pp_options': {'proofs': False},
}
(directory / 'config.json').write_text(json.dumps(config, indent=2) + '\n')
PY
"$NANODA" "$verification_dir/config.json"
printf 'Independent verification evidence retained at: %s\n' "$verification_dir"

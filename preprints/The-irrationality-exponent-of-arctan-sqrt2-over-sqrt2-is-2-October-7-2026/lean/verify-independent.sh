#!/usr/bin/env bash
# Set LEAN4EXPORT and NANODA to binaries built from the pins in README.md.
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to the pinned lean4export binary}"
: "${NANODA:?Set NANODA to the pinned nanoda_bin binary}"
verification_dir=${1:-$(mktemp -d)}
mkdir -p "$verification_dir"
verification_dir=$(cd "$verification_dir" && pwd)
lake build Imaginary.Main
lake env "$LEAN4EXPORT" Imaginary.Main -- \
  OAI.Imaginary.period_irrationalityExponent_eq_two \
  OAI.Imaginary.normalized_arctan_sqrt_two_eventualLowerBound \
  OAI.Imaginary.normalized_arctan_sqrt_two_irrationalityExponent_eq_two \
  OAI.Imaginary.normalized_arctan_sqrt_two_integer_eventualLowerBound \
  OAI.Imaginary.normalized_arctan_sqrt_two_explicit_bound \
  > "$verification_dir/imaginary-main.ndjson"
python3 - "$verification_dir" <<'PY'
import json, pathlib, sys
directory = pathlib.Path(sys.argv[1])
config = {
    'export_file_path': str(directory / 'imaginary-main.ndjson'),
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
    'pp_declars': ['OAI.Imaginary.period_irrationalityExponent_eq_two',
        'OAI.Imaginary.normalized_arctan_sqrt_two_eventualLowerBound',
        'OAI.Imaginary.normalized_arctan_sqrt_two_irrationalityExponent_eq_two',
        'OAI.Imaginary.normalized_arctan_sqrt_two_integer_eventualLowerBound',
        'OAI.Imaginary.normalized_arctan_sqrt_two_explicit_bound'],
    'pp_options': {'proofs': False},
}
(directory / 'config.json').write_text(json.dumps(config, indent=2) + '\n')
PY
"$NANODA" "$verification_dir/config.json"
printf 'Independent verification evidence retained at: %s\n' "$verification_dir"

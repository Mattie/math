"""Verify this proof module and the inherited OAI sources it imports."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
inherited = root / '../../preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/lean'
manifest = json.loads((root / 'inherited-sources.json').read_text())
actual = {p.relative_to(inherited).as_posix() for p in (inherited / 'OAI').rglob('*.lean')}
assert actual == set(manifest), 'Inherited source inventory differs'
for name, expected in manifest.items():
    assert hashlib.sha256((inherited / name).read_bytes()).hexdigest() == expected, name
expected = '9a6604aebf7eb7ed284f89b2841cffcac8dc45493b7b6958b6578877987467ad'
assert hashlib.sha256((root / 'SmallDivisors/Main.lean').read_bytes()).hexdigest() == expected
print(f'Checked the Cookson module and {len(manifest)} inherited source files.')

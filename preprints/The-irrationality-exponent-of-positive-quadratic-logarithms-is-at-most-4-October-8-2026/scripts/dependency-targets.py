"""List explicit Lake targets for the extension's direct inherited imports.

The pinned dependency project has no default build targets. Building these
modules also builds their transitive imports, without modifying its configuration.
"""
from pathlib import Path
import re

package = Path(__file__).resolve().parents[1]
targets = set()
for source in (package / 'lean/AlgebraicLog').glob('*.lean'):
    for line in source.read_text(encoding='utf-8').splitlines():
        if line.startswith('import '):
            for module in line.split('--', 1)[0].split()[1:]:
                if module.startswith(('OAI.', 'Logarithm.')):
                    if not re.fullmatch(r'[A-Za-z0-9_.]+', module):
                        raise SystemExit('Invalid dependency module name.')
                    targets.add('+' + module)
if not targets:
    raise SystemExit('No inherited dependency imports found.')
print('\n'.join(sorted(targets)))

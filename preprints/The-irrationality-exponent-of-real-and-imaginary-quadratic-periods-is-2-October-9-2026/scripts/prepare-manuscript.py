"""Prepare the editable manuscript for Pandoc without changing mathematical prose."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
text = (root / 'build/manuscript.md').read_text(encoding='utf-8')
# PDF metadata supplies title, author, and date. Keep all text from the first section.
match = re.search(r'^## ', text, flags=re.M)
if match:
    text = text[match.start():]
text = re.sub(r'^## ', '# ', text, flags=re.M)
text = re.sub(r'^### ', '## ', text, flags=re.M)
text = text.replace('](../lean/', '](lean/')
Path(sys.argv[1]).write_text(text, encoding='utf-8')

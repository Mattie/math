"""Prepare the public manuscript for the bundled typesetting template."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
text = (root/'manuscript.md').read_text(encoding='utf-8')
body = '## Abstract' + text.split('## Abstract',1)[1]
body = body.replace('## References','\\begingroup\n\\raggedright\n\n## References')
body = body.replace('**Theorem 1.**','\\Needspace{8\\baselineskip}\n\n**Theorem 1.**')
(root/'build').mkdir(exist_ok=True)
(root/'build/typeset.md').write_text(body+'\n\\endgroup\n',encoding='utf-8',newline='\n')

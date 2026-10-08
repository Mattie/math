"""Prepare the editable Markdown for the article PDF without changing mathematics."""
from pathlib import Path
import re, sys
root=Path(__file__).resolve().parents[1]
text=(root/'build/manuscript.md').read_text(encoding='utf-8')
text=text.split('7 October 2026',1)[1].lstrip()
text=text.replace('](../lean/','](lean/')
text=text.replace('](../../The-','](../The-')
text=text.replace('## References', '## References\n\n\\begingroup\\raggedright') + '\n\\endgroup\n'
text=re.sub(r'^## ', '# ', text, flags=re.M)
text=re.sub(r'^### ', '## ', text, flags=re.M)
# Long module names are clearer as a source list than narrow table columns.
lines=[]
for line in text.splitlines():
    if line.startswith('| Step |') or line.startswith('| --- |'): continue
    if line.startswith('| ') and line.endswith(' |'):
        a,b=line.strip('| ').split(' | ',1)
        lines.append('- '+a+': '+b)
    else: lines.append(line)
Path(sys.argv[1]).write_text('\n'.join(lines)+'\n',encoding='utf-8')

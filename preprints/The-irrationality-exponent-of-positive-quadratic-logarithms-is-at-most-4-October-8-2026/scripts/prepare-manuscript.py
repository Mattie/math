"""Prepare the PDF body from the editable manuscript without changing formulas."""
from pathlib import Path
import re, sys
package = Path(__file__).resolve().parents[1]
text = (package / 'build/manuscript.md').read_text(encoding='utf-8')
text = text.split('October 8, 2026', 1)[1].lstrip()
text = text.replace('](../VERIFY.md)', '](VERIFY.md)')
displayed_math = re.findall(r'\$\$(.*?)\$\$', text, re.S)
# Long declaration names read better as source lists than narrow table cells.
lines = []
for line in text.splitlines():
    if line.startswith('|') and line.endswith('|') and line.count('|') >= 3:
        cells = [c.strip() for c in line.strip('|').split('|')]
        if cells[0] in {'Ingredient', 'Obligation'}:
            continue
        if all(re.fullmatch(r'[-: ]+', c) for c in cells):
            continue
        lines.append('- ' + ': '.join(cells))
    else:
        lines.append(line)
text = '\n'.join(lines).replace('## ', '# ')
if re.findall(r'\$\$(.*?)\$\$', text, re.S) != displayed_math:
    raise SystemExit('Table conversion changed displayed mathematics.')
text = text.replace('π', r'$\pi$')
text = text.replace(r'\texttt{PiExponent.PersistentWeightComparison.comparisonConstant }m\,\sigma.',
                    r'\operatorname{comparisonConstant}(m,\sigma).')
text = text.replace('E=\\frac\\nu F+\n', '\\begin{aligned}\nE={}&\\frac\\nu F+\n')
text = text.replace('+2\\Lambda\\sum_i\\frac1{w_i}\n', '\\\\\n&+2\\Lambda\\sum_i\\frac1{w_i}\n')
text = text.replace('\\log(KR+2)}{w_*}.\n$$\nBy our choices',
                    '\\log(KR+2)}{w_*}.\n\\end{aligned}\n$$\nBy our choices')
# Let long module identifiers break at punctuation in the PDF.
def code(match):
    value = match.group(1).replace('ℚ', 'Q')
    if ' ' in value:
        return r'\texttt{' + value.replace('_', r'\_') + '}'
    return r'\path{' + value + '}'
text = re.sub(r'`([^`]+)`', code, text)
text = text.replace('following table', 'following list').replace('the table above', 'the source list above')
Path(sys.argv[1]).write_text(text + '\n', encoding='utf-8')

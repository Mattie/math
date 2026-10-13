"""Compile the local manuscript with Tectonic and retain PDF provenance.

Pass --tectonic to select an existing executable. The script installs nothing;
Tectonic may retrieve its normal TeX support files when they are not cached.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def main():
    """Build the source and copy its verified output to the paper entrypoint."""
    parser = argparse.ArgumentParser()
    parser.add_argument('--tectonic', default='tectonic')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    version = subprocess.check_output([args.tectonic, '--version'], text=True).strip()
    subprocess.run([args.tectonic, '--keep-logs', 'main.tex'], cwd=root/'build', check=True)
    shutil.copyfile(root/'build/main.pdf', root/'paper.pdf')
    record = {'engine':version, 'source_sha256':hashlib.sha256((root/'build/main.tex').read_bytes()).hexdigest(),
              'pdf_sha256':hashlib.sha256((root/'paper.pdf').read_bytes()).hexdigest(),
              'scope':'PDF compilation and byte identity; visual review is recorded separately.'}
    (root/'build/receipt.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(record))


if __name__ == '__main__':
    main()

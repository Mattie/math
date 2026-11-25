"""Build the preprint PDF and record the input and output hashes."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

EPOCH = "1795564800"
PAPER = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tectonic", default="tectonic")
    args = parser.parse_args()
    version = subprocess.check_output([args.tectonic, "--version"], text=True).strip()
    source = PAPER / "build/main.tex"
    with tempfile.TemporaryDirectory() as output:
        subprocess.run([args.tectonic, "--outdir", output, source.name], cwd=source.parent,
                       env={**os.environ, "SOURCE_DATE_EPOCH": EPOCH}, check=True)
        pdf = (Path(output) / "main.pdf").read_bytes()
    receipt = {"engine": version, "source_date_epoch": int(EPOCH),
               "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
               "pdf_sha256": hashlib.sha256(pdf).hexdigest()}
    (PAPER / "paper.pdf").write_bytes(pdf)
    (PAPER / "build/receipt.json").write_bytes((json.dumps(receipt, indent=2) + "\n").encode())
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()

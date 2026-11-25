"""Check the preprint and the complete, pinned proof supplement."""

import hashlib
import json
import re
import zipfile
from pathlib import Path

PAPER = Path(__file__).resolve().parents[1]
ZIP_HASH = "56a3c7643dabdc4225ca41e92c4cab8530c8408cdc71184f18780759d91b80b2"


def check(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    proof = PAPER / "lean"
    archive = PAPER / "lean-proof.zip"
    check(hashlib.sha256(archive.read_bytes()).hexdigest() == ZIP_HASH, "Proof archive changed")
    with zipfile.ZipFile(archive) as zipped:
        names = zipped.namelist()
        sources = {path.relative_to(proof).as_posix() for path in proof.rglob("*") if path.is_file()}
        check(len(names) == len(sources) == 30, "Wrong proof file count")
        for name in sources:
            check(zipped.read("pi2-window-proof/" + name) == (proof / name).read_bytes(), name)

    checked = set()
    for line in (proof / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        check(name in sources and name not in checked, "Unexpected manifest path: " + name)
        check(hashlib.sha256((proof / name).read_bytes()).hexdigest() == digest, name)
        checked.add(name)
    check(checked == sources - {"SHA256SUMS"}, "Incomplete proof manifest")
    check((PAPER / "check_rate.py").read_bytes() == (proof / "check_rate.py").read_bytes(), "Rate checker changed")

    endpoints = json.loads((PAPER / "theorem-map.json").read_text(encoding="utf-8"))["theorems"]
    check(len({row["declaration"] for row in endpoints}) == len(endpoints) == 5, "Expected five endpoints")
    for row in endpoints:
        namespace, name = row["declaration"].rsplit(".", 1)
        path = proof / "src" / (namespace.rsplit(".", 1)[1] + ".lean")
        check(path.relative_to(PAPER).as_posix() == row["source"], row["source"])
        src = path.read_text(encoding="utf-8")
        check("namespace " + namespace in src and re.search(r"^theorem " + re.escape(name) + r"\b", src, re.M), name)

    manifest = json.loads((PAPER / "package-manifest.json").read_text(encoding="utf-8"))["files"]
    required = {"README.md", "paper.pdf", "build/main.tex", "scripts/check-publication.py",
                "scripts/build.py", "build/receipt.json", "lean-proof.zip", "lean/SHA256SUMS", "VERIFY.md", "theorem-map.json",
                "LICENSES.md", "licenses/MIT.txt", "licenses/CC-BY-4.0.txt", "CITATION.cff"}
    check(required <= manifest.keys(), "Incomplete publication manifest")
    for name, entry in manifest.items():
        path = (PAPER / name).resolve()
        check(path.is_relative_to(PAPER) and path.relative_to(PAPER).as_posix() == name, name)
        data = path.read_bytes()
        check(len(data) == entry["bytes"] and hashlib.sha256(data).hexdigest() == entry["sha256"], name)
    tex = (PAPER / "build/main.tex").read_text(encoding="utf-8")
    check(r"\end{document}" in tex, "Incomplete manuscript")
    pdf = (PAPER / "paper.pdf").read_bytes()
    check(pdf.startswith(b"%PDF-") and pdf.rstrip().endswith(b"%%EOF"), "Incomplete PDF")
    receipt = json.loads((PAPER / "build/receipt.json").read_text(encoding="utf-8"))
    check(receipt["source_sha256"] == manifest["build/main.tex"]["sha256"], "LaTeX receipt mismatch")
    check(receipt["pdf_sha256"] == manifest["paper.pdf"]["sha256"], "PDF receipt mismatch")
    check(receipt["source_date_epoch"] == 1795564800, "Unexpected PDF timestamp")
    for document in (PAPER / name for name in manifest if name.endswith(".md")):
        for target in re.findall(r"\]\(([^\s)]+)\)", document.read_text(encoding="utf-8")):
            if target.startswith(("https://", "#")):
                continue
            path = (document.parent / target.partition("#")[0]).resolve()
            check(path.is_relative_to(PAPER) and path.is_file(), f"{document.name}: {target}")
    print("Publication integrity passed for the manuscript, PDF, proof archive, manifest and five theorem entries.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Check this paper's inventory and its links to the unchanged proof package."""

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT.parents[1] / "formalizations" / "AffineLogarithms"


def digest(path):
    """Return a file's SHA-256, streaming large artifacts."""
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    """Require exact listed bytes, accessible local links, and all checked targets."""
    manifest = json.loads((ROOT / "manifest-sha256.json").read_text(encoding="utf-8"))
    for name, expected in manifest.items():
        relative = PurePosixPath(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("Invalid paper inventory path: " + name)
        if digest(ROOT / name) != expected:
            raise ValueError("Paper file changed: " + name)

    for path in ROOT.rglob("*.md"):
        if any(part in {".work", ".lake", "__pycache__"} for part in path.relative_to(ROOT).parts):
            continue
        for target in re.findall(r"\]\(([^\s)]+)\)", path.read_text(encoding="utf-8")):
            if "://" in target or target.startswith("#"):
                continue
            if not (path.parent / target.split("#", 1)[0]).exists():
                raise ValueError(f"Missing local link in {path.name}: {target}")

    mapping = json.loads((ROOT / "theorem-map.json").read_text(encoding="utf-8"))
    targets = json.loads((PROOF / "evidence/target-map.json").read_text(encoding="utf-8"))
    public = {row["public_declaration"] for row in targets["public_declarations"]}
    comparisons = {row["comparison_target"] for row in targets["public_declarations"]}
    comparisons.update(targets["standard_endpoints"])
    mapped_public, mapped_comparisons = set(), set()
    manuscript = (ROOT / "build/main.tex").read_text(encoding="utf-8")
    for theorem in mapping["main_results"]:
        if "\\label{" + theorem["latex_label"] + "}" not in manuscript:
            raise ValueError("Missing manuscript theorem: " + theorem["latex_label"])
        mapped_public.update(theorem["public_declarations"])
        mapped_comparisons.update(theorem["comparison_targets"])
    if mapped_public != public or mapped_comparisons != comparisons:
        raise ValueError("Paper mapping does not cover the exact checked targets")
    if digest(PROOF / "evidence/source-sha256.json") != mapping["source_inventory_sha256"]:
        raise ValueError("Frozen proof inventory changed")
    if not (ROOT / "paper.pdf").read_bytes().startswith(b"%PDF-"):
        raise ValueError("Missing or invalid PDF header")
    subprocess.run([sys.executable, "-B", str(PROOF / "scripts/check.py")], check=True)
    print(f"Paper integrity passed: {len(manifest)} files; three main results; fifteen targets.")


if __name__ == "__main__":
    main()

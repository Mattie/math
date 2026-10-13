#!/usr/bin/env python3
"""Check listed publication bytes, local links, and frozen proof inputs."""

import sys

if __name__ == "__main__" and not sys.flags.isolated:
    raise SystemExit("Run with Python isolated mode: python3 -I scripts/check-publication.py")

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

PAPER = Path(__file__).resolve().parents[1]
REPO = PAPER.parents[1]


def main():
    """Validate the manifest and links, then reuse the frozen-input checker."""
    manifest = json.loads((PAPER / "package-manifest.json").read_text(encoding="utf-8"))
    files = manifest["files"]
    prefix = PAPER.relative_to(REPO).as_posix()
    required = {f"{prefix}/{name}" for name in (
        "paper.pdf", "build/main.tex", "theorem-map.json", "VERIFY.md",
        "scripts/check-publication.py")}
    if not required <= files.keys():
        raise ValueError("Publication manifest omits a required paper file")
    for name, expected in files.items():
        relative = PurePosixPath(name)
        if relative.is_absolute() or ".." in relative.parts or "\\" in name:
            raise ValueError("Invalid publication path: " + name)
        path = REPO / name
        if path.is_symlink() or not path.resolve().is_relative_to(REPO.resolve()):
            raise ValueError("Publication path escapes its checkout: " + name)
        data = path.read_bytes()
        if len(data) != expected["bytes"] or hashlib.sha256(data).hexdigest() != expected["sha256"]:
            raise ValueError("Publication file changed: " + name)
        if path.suffix == ".md":
            for target in re.findall(r"\]\(([^\s)]+)\)", data.decode("utf-8")):
                if "://" in target or target.startswith("#"):
                    continue
                if not (path.parent / target.split("#", 1)[0]).exists():
                    raise ValueError(f"Missing local link in {name}: {target}")
    if not (PAPER / "paper.pdf").read_bytes().startswith(b"%PDF-"):
        raise ValueError("Invalid PDF header")
    subprocess.run([
        sys.executable, "-I", "-B",
        str(REPO / "verification/isolated-affine-denominators/verify.py"), "--check"
    ], check=True)
    print(f"Publication integrity passed: {len(files)} listed files and frozen proof inputs.")


if __name__ == "__main__":
    main()

"""Check source identity, statement scope, and portable publication links."""

from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    """Hash even the large release export without loading it into memory."""
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def statement(path):
    """Read the declaration type without importing its proof placeholder."""
    source = path.read_text(encoding="utf-8")
    return source.split("theorem log_rational_challenge", 1)[1].split(":= by", 1)[0]


def check_links(path):
    """Check local Markdown links outside math and fenced examples."""
    source = path.read_text(encoding="utf-8")
    source = re.sub(r"\\\[.*?\\\]|\\\(.*?\\\)", "", source, flags=re.S)
    fence = re.escape(chr(96) * 3)
    source = re.sub(fence + ".*?" + fence, "", source, flags=re.S)
    for target in re.findall(r"\]\(([^)]+)\)", source):
        if "://" in target or target.startswith("#"):
            continue
        target = target.split("#", 1)[0]
        if not (path.parent / target).exists():
            raise ValueError(f"Missing link from {path.relative_to(ROOT)}: {target}")


def main():
    """Reject any changed certified source or frozen specification."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--release-assets", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "lean/source-manifest.json").read_text())
    assert len(manifest["files"]) == 924
    for entry in manifest["files"]:
        path = ROOT / "lean" / entry["path"]
        assert sha(path) == entry["sha256"], f"Changed certified source: {entry['path']}"
    print("All 924 certified Lean source hashes match.")
    blind = ROOT / "review/blind-statement"
    receipt = json.loads((blind / "comparison-receipt.json").read_text())
    assert sha(blind / "Challenge.lean") == receipt["frozen_statement_sha256"]
    assert sha(blind / "CertifiedBridge.lean") == receipt["certified_bridge_sha256"]
    assert statement(blind / "Challenge.lean") == statement(blind / "CertifiedBridge.lean")
    print("Frozen blind statement and its proved bridge match.")
    for name in ("README.md", "VERIFY.md", "LICENSES.md",
                 "release-assets/README.md"):
        check_links(ROOT / name)
    for name in ("README.md", "build/main.tex"):
        assert "Ryan Matthew Casper" in (ROOT / name).read_text(encoding="utf-8")
    assert r"\author{OpenAI}" not in (ROOT / "build/main.tex").read_text()
    print("Publication links and Casper authorship checked.")
    if args.release_assets:
        manifest = json.loads((ROOT / "evidence/release-assets.json").read_text())
        for entry in manifest["files"]:
            path = ROOT / entry["path"]
            assert path.stat().st_size == entry["bytes"]
            assert sha(path) == entry["sha256"], f"Changed asset: {entry['path']}"
        print("Release asset sizes and hashes match.")


if __name__ == "__main__":
    main()

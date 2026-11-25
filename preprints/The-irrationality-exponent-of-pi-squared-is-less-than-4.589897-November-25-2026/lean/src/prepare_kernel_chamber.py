"""Reconstruct KernelChamber.lean from its template and pinned chi_min' proof.

Usage: python prepare_kernel_chamber.py UPSTREAM_CHECKOUT BUILD_DIRECTORY
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path)
    parser.add_argument("build_dir", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / "kernel_provenance.json").read_text(encoding="utf-8"))
    item = manifest["chamber_input"]
    blob = f"{manifest['commit']}:{item['path']}"
    source = subprocess.check_output(["git", "-C", str(args.upstream), "show", blob])
    if hashlib.sha256(source).hexdigest() != item["sha256"]:
        raise SystemExit(f"Unexpected upstream bytes for {item['path']}")
    first, last = item["source_lines"]
    proof = "\n".join(source.decode("utf-8").splitlines()[first - 1:last])
    proof = proof.replace("theorem chi_min'", "theorem chi_min").replace("hp0", "hp")
    template = (here / "KernelChamber.lean.in").read_text(encoding="utf-8")
    marker = "-- INSERT upstream chi_min' with renamed binders"
    if template.count(marker) != 1:
        raise SystemExit("Expected one chi_min' marker in the template")
    result = template.replace(marker, proof).encode("utf-8")
    if hashlib.sha256(result).hexdigest() != manifest["outputs"]["KernelChamber.lean"]["lf_sha256"]:
        raise SystemExit("Reconstructed KernelChamber.lean failed its SHA-256 check")
    args.build_dir.mkdir(parents=True, exist_ok=True)
    target = args.build_dir / "KernelChamber.lean"
    if target.exists() and target.read_bytes().replace(b"\r\n", b"\n") != result:
        raise SystemExit(f"Refusing to replace a different file at {target}")
    target.write_bytes(result)


if __name__ == "__main__":
    main()

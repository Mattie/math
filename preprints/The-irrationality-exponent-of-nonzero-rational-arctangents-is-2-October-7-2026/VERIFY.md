# Reproducing the checks

The Lean project in lean/ pins Lean 4.34.1 and Mathlib commit
d13f23b723b8a846827a245b89c10fc7d3f11612. Its unchanged manifest covers
14 Arctangent, 55 Logarithm, and 869 inherited OpenAI modules.

From this preprint directory:

```sh
python3 scripts/check-publication.py
cd lean
bash verify.sh
```

The second command group requires Bash, elan/Lean, Git, and network access to
fetch pinned dependencies. Use a native Linux filesystem for large WSL builds.
It verifies the frozen and supplementary source hashes, builds the project and
`Arctangent.FormalConjectures`, and runs their axiom audits. The supplementary
module proves the exact catalogue statement; it is not part of the retained export.

For independent exported-proof checking, also install Rust and Python 3:

```sh
cd lean  # from the preprint directory
bash setup-independent-tools.sh /absolute/path/to/tools
# Set LEAN4EXPORT and NANODA to the binaries printed by that script.
bash verify-independent.sh /absolute/path/to/new-evidence
bash verify-negative-control.sh
bash verify-second-lean.sh ../release-assets/arctangent-main.ndjson.gz
```

The last command reconstructs the official Lean 4.34.0 checker and tests a
positive and ill-typed negative fixture before full replay. It needs curl,
unzip, a C/C++ build toolchain, and /usr/bin/time. To replay the retained export
with Nanoda, from the preprint directory:

```sh
NANODA=/absolute/path/to/nanoda_bin bash evidence/nanoda/replay-export.sh
```

The compressed export is an external release asset, not a Git source file.
Place it in release-assets/; its hashes are in [evidence/release-assets.json](evidence/release-assets.json).
The [verification summary](lean/VERIFICATION.md) records the completed checks and states their limitations.

Rebuild the PDF with Pandoc 3.6.4 and Tectonic 0.15.0:

```sh
bash scripts/build-paper.sh
```

This converts build/manuscript.md to build/main.tex and paper.pdf, using the
same 11pt article, Latin Modern font, and 1.08-inch margins as the preceding preprint.

## Verification and distribution update

Verification scripts enforce the three-axiom allowlist on fresh output and reject
missing reports. Frozen dependency style warnings remain visible; catalogue
wrappers are compiled separately with warnings treated as errors. Publication
checks exclude generated dependency/build directories. Historical receipts and
all proof sources retain their original identities.

The [repository verification guide](https://github.com/Mattie/math/blob/main/verification/publication/README.md)
records the six-package build run, resource observations, and the distinction
between publication checks and full Lean builds. The build run's live status,
not a publication-only green check, determines whether reproduction succeeded.

The retained export is listed in the [distribution inventory](https://github.com/Mattie/math/blob/main/verification/publication/release-assets.json).
The [release location](https://github.com/Mattie/math/releases/tag/proof-exports-2026-10-08)
is planned; publication awaits the repair PR's merge and successful verification.
After publication, use the existing replay commands with the downloaded export.
Publishing a retained export does not claim a new kernel-check run.

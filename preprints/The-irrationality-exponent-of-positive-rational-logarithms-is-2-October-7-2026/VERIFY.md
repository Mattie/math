# Reproducing the checks

The Lean project is in lean/, pinned to Lean 4.34.1 and Mathlib commit
d13f23b723b8a846827a245b89c10fc7d3f11612. The source manifest covers all
55 extension modules and 869 unchanged original modules.

From this preprint directory, run the quick integrity checks:

    python3 scripts/check-publication.py

With elan/Lean, Git, Python 3, and Bash installed, rebuild and audit:

    bash scripts/verify.sh

That command checks the source manifest and frozen blind statement, runs the
Lean build and axiom audits, and checks the proved statement bridge. The
intentional specification placeholder is not imported into either proof. Use a native Linux filesystem for large builds under WSL.

The retained checks comprise Lean 4.34.1, Nanoda 0.4.19, and a separate
official Lean 4.34.0 kernel replay. Their results, exact hashes,
negative controls, and limitations are in [lean/VERIFICATION.md](lean/VERIFICATION.md).
The large export is kept locally in release-assets/ and should be attached
to a GitHub release. Its digest is recorded in evidence/release-assets.json.

After downloading the export and reconstructing the pinned Nanoda binary:

    cd lean
    bash setup-independent-tools.sh /absolute/path/to/tools
    # Set LEAN4EXPORT and NANODA to the paths printed by that script.
    bash verify-independent.sh /absolute/path/to/new-evidence
    bash verify-negative-control.sh
    bash verify-second-lean.sh ../release-assets/logarithm-main.ndjson.gz

The first independent command creates and checks a fresh export. The last
replays the retained export with the different Lean kernel. To replay the
retained export with Nanoda, from this preprint directory use:

    NANODA=/absolute/path/to/nanoda_bin bash evidence/nanoda/replay-export.sh

An optional first argument selects a different compressed export path.

To rebuild the paper, install Tectonic and run:

    bash scripts/build-paper.sh

This creates paper.pdf from build/main.tex, its section sources, and
build/references.bib. The TeX layout follows the upstream preprint's 11pt
article style, Latin Modern font, and 1.08-inch margins.

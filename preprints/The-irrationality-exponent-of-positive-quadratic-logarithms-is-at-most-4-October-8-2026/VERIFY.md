# Verification and reproduction

## Recorded proof checks

The 25 mathematical modules and accompanying audit use Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. Their identities are in [checker metadata](evidence/checker-metadata.json). Recorded endpoint axiom checks list only `propext`, `Classical.choice`, and `Quot.sound`.

The selected proof closure contains the literal bound, irrationality, conventional exponent consequence, and both examples. Nanoda checked 118,145 declarations with exit 0. Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, replayed 118,142 declarations into an empty kernel environment; Lean regenerates the three quotient primitives omitted by the reader. Both routes accepted a positive control and rejected an ill-typed proof during type checking.

The shared exporter is lean4export `076e8e57707e813375e8f9da8bf989799ace9680`; Nanoda is `3a2407216ee84a75f9e1aead6803d0578be06ae7`. The export identity is in the metadata. These are recorded checks of unchanged sources, not new replay runs made during packaging. The second Lean implementation is related to the original; Nanoda provides implementation diversity, while both share an exporter. The [reader](lean/reference-reader) and [its provenance](evidence/second-lean-reader.json) are retained. The packaged reader corrects only a comment and its invalid-argument usage message; the provenance preserves the historical replay source and binary identities separately from the packaged source hash. The recorded full replay predates these corrections.

## Automated mathematical reviews

A fresh-context blind reviewer inspected the extension, rebuilt all 25 modules, and assigned the final theorems to independently authored, separately compiled Mathlib-only propositions. A separate proof-failure investigation found no demonstrated defect; its assumed failure was a commissioned exercise, not an observed rejection. A third reviewer examined inherited local length, weighted Bezout, rigidity, degree normalization, ampleness, jet restriction, and polynomial support arguments. Ten focused inherited source checks and nonvacuity/boundary examples passed.

No confirmed defect was found in the reviewed scope. The 848-module inherited interpolation import closure was not exhaustively audited. Remaining boundaries include local intersection/Hilbert theory, tangent and slice algebra, finite Taylor targets, curve contact/product formulas, normalization, divisor/Euler theory, numerical ampleness foundations, Rees recovery, Cech/Ext and Serre machinery, global homogeneous representation, and affine/formal-log filtration. These are coverage limits, not identified counterexamples.

No independent human specialist review, sandboxed cross-environment comparator run, or exhaustive priority determination is claimed. Native builds reused inherited compiled objects after source hash checks. Formal proof checking does not by itself establish the intended interpretation of every inherited definition.

## Reproduce the package

Use Bash, Python 3.11 or later, Git, and Lean 4.34.1 with Lake. Run:

```bash
cd lean
bash verify.sh
```

With no `LEAN_DEPENDENCY_ROOT`, this fetches the pinned public rational-logarithm project, checks its 924 sources and configuration files, retrieves the Mathlib cache, and explicitly builds the inherited modules imported by the extension, together with their dependencies. The pinned project has no default Lake targets, so a bare `lake build` is insufficient. To reuse an already built matching project:

```bash
LEAN_DEPENDENCY_ROOT=/path/to/pinned-project/lean bash verify.sh
```

All output is under ignored `.verification/`. The [dependency pin](evidence/dependency-pin.json) records the public revision and source location. The preparation receipt distinguishes the paths actually tested for this package from documented reproduction paths.

The [publication review](evidence/publication-review.json) records the explicit-target correction and its validation. A complete network bootstrap followed by a fresh rebuild of every inherited source has not been performed. The replay reader's `.lake/` cache is also excluded from Git.

To regenerate the export, set `LEAN_DEPENDENCY_ROOT` and `LEAN4EXPORT` to the pinned built project and exporter, then run `bash scripts/export.sh` from the package root. The script requires the native overlay build and checks the regenerated export's identity. To replay an export:

```bash
NANODA_BIN=/path/to/nanoda_bin bash scripts/replay.sh nanoda /path/to/algebraic-main.ndjson
LEAN340_READER=/path/to/kernel bash scripts/replay.sh lean340 /path/to/algebraic-main.ndjson
```

Build the retained reader with Lean 4.34.0 using `lake build kernel` inside `lean/reference-reader/`. Caller-supplied binaries must come from the stated revisions; these scripts do not authenticate arbitrary binaries.

## Manuscript and package checks

With Pandoc 3.6.4 and Tectonic 0.17.0 available, `bash scripts/build-paper.sh` regenerates the LaTeX source and PDF from `build/manuscript.md`. Run `python3 scripts/check-publication.py` to check required files, source identities, local links, and accidental private text. See [preparation results](evidence/preparation.json) for the actual packaging checks. No public release or upload is implied by this directory.

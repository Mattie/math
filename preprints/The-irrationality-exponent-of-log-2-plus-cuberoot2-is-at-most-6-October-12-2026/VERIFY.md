# Verification

The mathematical sources are in the [AffineCubic overlay](../../formalizations/AffineCubic/). The [theorem map](theorem-map.json) identifies the main bound and its standard consequences. The proof uses Lean 4.34.1 and Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Hosted proof checking

[Run 38434422471](https://github.com/Mattie/math/actions/runs/38434422471), attempt 1, checked commit `1ee3266da6bd7f6ecafd063caab2cfe7a6defbd2`. It built the frozen candidate sources in the tested isolation boundary. Comparator matched the four independently specified [challenge statements](../../verification/isolated-affine-cubic/Challenge.lean), and Nanoda and Lean's default kernel accepted the solution. The statements cover the eventual approximation lower bound, irrationality, irrationality exponent at most six, and the corresponding Mathlib `LiouvilleWith` consequence.

All nine required checks passed, including the valid control, statement mismatch, forbidden axiom, imported admission, dependencies, and protected-input checks. The permitted axioms are `propext`, `Quot.sound`, and `Classical.choice`. The [dated result](../../verification/isolated-affine-cubic/results/hosted-verification-2026-10-13.md) and [machine-readable audit](../../verification/isolated-affine-cubic/results/hosted-audit-2026-10-13.json) identify the source, checker binaries, resource limits, boundary probes, and exact acceptance evidence.

The run trusts the identified official dependency cache; it is not a from-source rebuild of every dependency. The [checker assessment](../../verification/isolated-affine-cubic/CHECKERS.md) documents the selected Nanoda baseline and other checking limits. The hosted source route retains no standalone proof export and does not claim replay of the separate historical local export.

## Retained evidence

The complete [hosted evidence ZIP](../../verification/isolated-affine-cubic/evidence/hosted-2026-10-13.zip) is now retained in Git, independently of the Actions artifact's January 11, 2027 expiry. It is the unmodified 6,447,231-byte archive downloaded and audited after the run, with SHA-256:

```text
4a3eaf9ebaf3ea0d247274dd38a737744f312fb2a83aa49e558f88383b8ff83c
```

It contains the receipt, checker diagnostics, retained inputs, and all 101 indexed evidence files, including 58 command logs. The publication checker verifies the ZIP's exact hash, complete indexed membership, and every member's size and hash. This checks retained evidence integrity; it does not execute the proof again. Instructions for a fresh hosted run are in the [verification package](../../verification/isolated-affine-cubic/README.md).

## Manuscript correspondence

The published source and seven-page PDF are the reviewed October 13 manuscript. The final editorial and acknowledgement changes preserved the mathematical statements, displayed mathematical blocks, and frozen Lean sources. Independent model reviews covered the written argument and its correspondence to the formalization; these are not human peer review. Private review packets are not part of this publication.

The [build receipt](build/receipt.json) records the exact manuscript and PDF hashes. The [publication manifest](package-manifest.json) binds the distributed paper, companion files, checking inputs, and retained hosted archive. Run `python -I scripts/check-publication.py` from this directory to check their integrity without rebuilding the proof.

The [publication review record](build/publication-review.json) retains the initial publication inspection and downloads. Its publication-date update identifies the rebuilt source and PDF after changing only the title-page date to October 13, 2026; all seven pages were inspected again.

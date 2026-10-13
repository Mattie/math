# Affine cubic source overlay

The [Pilot module](AffineCubic/Pilot.lean) proves four concrete consequences for
`log 2 + real cuberoot 2`, including irrationality exponent at most six.
[Endpoint.lean](AffineCubic/Endpoint.lean) supplies the general cubic affine theorem.

This is an overlay on the frozen [affine sources](../AffineLogarithms/), using
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The [original source freeze](evidence/source-freeze.json) identifies unchanged
proof bytes; [overlay.json](overlay.json) lists module order and endpoints.

The separate [hosted verifier](../../verification/isolated-affine-cubic/README.md)
generates trusted build configuration, assembles these sources with their
inherited dependency closure, and checks the literal intended statements.
The [paper and editable manuscript](../../preprints/The-irrationality-exponent-of-log-2-plus-cuberoot2-is-at-most-6-October-12-2026/README.md)
explain the argument and connect its statements to these declarations.

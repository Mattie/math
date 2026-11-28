# Lean companion to the two-case π argument

[Main.lean](PiTwoCaseBridge/Main.lean) contains the strict degree margin
theorem and its use in the original two-case determinant argument.
`PiTwoCaseBridge.theorem_5_1` proves simultaneous logarithmic interpolation
at every positive real cutoff with one source bound of the form `κT + B`,
where `0 < κ < 1`. The inputs are the positive rational weights, finitely
many distinct centers, and the strict branch-contact curve inequality.
`theorem_5_1_eventual` gives the equal-cutoff consequence. `PiTwoCaseBridge.main`
includes the explicit eventual bound for integer denominators and the
exact value of the irrationality exponent.

The replacement proof uses global sections of the exceptional twist, their
values on weighted arcs, and finite polynomial reduction. It first proves
the finite step with a finite-dimensional quotient as a hypothesis, then
derives that hypothesis using Nullstellensatz. The examples check two
distinct centers, including the actual logarithmic chart and real cutoffs.
The degree proof evaluates each section on monomial curves and bounds its pole
at infinity. The finite bridge uses that degree bound on the same polynomials
whose weighted initial forms are read along the lifted arcs.

Build the overlay in an environment with Lean 4.34.1 and the compiled
[AffineLogarithms](../AffineLogarithms/) Lean library on `LEAN_PATH`.
Use the Mathlib revision pinned in that package's
[lake-manifest.json](../AffineLogarithms/lake-manifest.json). For example,
from the inherited package with its dependencies and imported modules built:

```bash
lake env bash ../PiTwoCaseBridge/build-overlay.sh /path/to/bridge-build/lib
```

For a fresh checkout, follow the [pinned source and replay instructions](../../verification/isolated-pi-two-case/REPLAY.md).

The script builds the overlay with warnings as errors and elaborates
[Audit.lean](PiTwoCaseBridge/Audit.lean), which prints the endpoint types
and transitive axiom lists.

The geometry modules adapt the PiExponent geometry from OpenAI's
[`fd4aeeb2`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/PiExponent)
sources under the [Apache 2.0 license](../AffineLogarithms/OAI/LICENSE).
The determinant and original curve inequality also come from that development.

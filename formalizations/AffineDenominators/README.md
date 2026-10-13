# Affine logarithms with fixed denominators

This source overlay removes the algebraic-integrality hypotheses from the degree-four paired affine theorem. It proves the literal eventual rational lower bound, irrationality, and exponent upper bound four for

$$\log(3/2)+\sqrt2.$$

Read the [paper](../../preprints/The-irrationality-exponent-of-log-3-over-2-plus-sqrt2-is-at-most-4-October-12-2026/paper.pdf), [general endpoint](DenominatorAffine/Endpoint.lean), or [pilot declarations](DenominatorAffine/Pilot.lean).

The ten new modules import the unchanged [AffineLogarithms package](../AffineLogarithms/). They use Lean 4.34.1 and Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. The [source inventory](evidence/proof-source-sha256.json) identifies the mathematical files separately from documentation and operational records.

All new modules and seven audited endpoints have compiled. Six-target statement comparison and complete same-byte Nanoda and separately built stock Lean 4.34.1 replay passed locally. The [six-target verifier](../../verification/isolated-affine-denominators/) separately specifies the general endpoint and five pilot statements, records the confirmed Nanoda limitation and inherited-cache scope, and identifies the checked artifacts. Fresh hosted source verification and the [downloaded-evidence audit](../../verification/isolated-affine-denominators/results/hosted-audit-2026-10-12.json) also passed.

The public general theorem is `OAI.DenominatorAffine.Endpoint.paired_eventualLowerBound`. Its hypotheses describe the field degree, a positive distinguished base unequal to one, a nonzero real target, and two selected compatible embeddings with slopes bounded by two. It has no integrality hypotheses and chooses fixed denominators before constructing approximation parameters.

The five pilot declarations, all in `OAI.DenominatorAffine`, are:

- `log_three_halves_add_sqrt_two_eventualLowerBound`
- `log_three_halves_add_sqrt_two_explicit_bound`
- `log_three_halves_add_sqrt_two_irrational`
- `log_three_halves_add_sqrt_two_irrationalityExponent_le_four`
- `log_three_halves_add_sqrt_two_standard_exponent_le_four`

The last theorem uses Mathlib's `LiouvilleWith`, with a separate irrationality conclusion. The literal bound quantifies over every integer numerator and every sufficiently large natural denominator, without coprimality.

Reconstruction uses the inherited pinned source package plus this overlay; it does not require copying inherited files into a second proof package. The verifier generates its own minimal Lake configuration and records dependency-cache scope. Development builds that reuse compiled inherited modules are distinct from a fresh candidate-source reconstruction.

The formalized scope does not include the optional arbitrary-real-quadratic-field family or the rational slope-rescaling corollary. It makes no claim of a new best published bound. [Provenance and license scope](PROVENANCE.md) distinguish new source, inherited mathematics, and checking tools.

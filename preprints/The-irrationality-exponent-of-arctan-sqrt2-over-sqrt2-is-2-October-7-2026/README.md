# The irrationality exponent of arctan(sqrt(2))/sqrt(2) is 2

Ryan Matthew Casper · October 7, 2026

This preprint proves that the normalized value arctan(√2)/√2 has rational irrationality exponent 2. The generic formal theorem treats non-torsion normalized periods in Q(√−2); it does not establish the corresponding result for all imaginary quadratic fields or for the unnormalized arctangent.

- [Paper](paper.pdf) and [editable manuscript](build/manuscript.md)
- [Lean proof](lean/Imaginary/Main.lean), [catalogue statement](lean/Imaginary/FormalConjectures.lean), [verification summary](lean/VERIFICATION.md), and [reproduction](VERIFY.md)
- Explanations: [PhD](explainers/ELIPHD.md), [master's](explainers/ELIMS.md), [bachelor's](explainers/ELIBS.md), and [high school](explainers/ELIHS.md)
- [Licenses and attribution](LICENSES.md), [NOTICE](NOTICE), and [citation metadata](CITATION.cff)

The proof was checked with Lean 4.34.1, Nanoda, and a separate stock Lean 4.34.0 replay. The two export checks cover the same 117,922 declarations, with only `propext`, `Classical.choice`, and `Quot.sound`. These checks are not external human peer review.

The work builds on OpenAI's released weighted interpolation library, Mathlib, and Casper's preceding logarithm and Gaussian-arctangent adaptations. OpenAI coding agents contributed substantially to the mathematical adaptation, formalization, checking, and exposition under Casper's direction. The paper includes the full disclosure and makes no priority claim.

[Verification status and retained-export downloads](VERIFY.md#verification-and-distribution-update).

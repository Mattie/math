# The irrationality exponent of real and imaginary quadratic periods is 2

Ryan Matthew Casper · October 9, 2026

[Paper](paper.pdf) · [Editable manuscript](build/manuscript.md) · [Explanations](explainers/README.md) · [Verification](VERIFY.md) · [Theorem map](evidence/theorem-map.md) · [License scope](LICENSES.md)

The conventional irrationality exponent is exactly two for each of three precise families: π/√r for positive rational r; log(A+B√d)/√d for squarefree natural d>1 and rational A,B with A²−dB²=1 and A+B√d>0, A+B√d≠1; and every nonzero real x satisfying exp(i√d x)=A+B i√d for positive natural d and rational A,B. The last statement includes torsion values and all real branches. It is not a theorem about arbitrary algebraic scaling.

The proofs also give a literal bound: for each ν>2 there exists Q≥2 such that every integer p and natural q≥Q satisfy q^(−ν)≤|x−p/q|. There is no coprimality condition.

The package contains the frozen proof libraries, exact dependency pins, and six public specification/solution declarations. A fresh verification run rebuilt all 1,028 packaged proof modules from an initially empty candidate build directory. The maintained comparator accepted the six standard statements and referenced definitions; Nanoda and Lean kernel replay both accepted the fresh export. Lean and Mathlib binaries remain trusted dependencies. The [verification record](VERIFY.md) gives the scope, controls, retained evidence, and reproduction instructions. The checker exports are retained locally and have no public download.

OpenAI coding agents contributed substantially to mathematical development, formalization, verification, review, and writing under Casper's direction. OpenAI's released weighted interpolation and determinant method and library, together with Mathlib, are substantial foundations. This disclosure does not assert OpenAI authorship, sponsorship, endorsement, human peer review, or an exhaustive priority claim.

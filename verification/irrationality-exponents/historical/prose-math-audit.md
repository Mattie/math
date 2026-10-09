# Sampled mathematical correspondence audit

Public rendering of the retained audit: only the workstation path was omitted.
Original file SHA-256: `e134c0fa810afa1c7b83f4d34361ebcceded0b5a5ee21df9037c353dab589d2f`. The original remains unchanged.

Audited 8 October 2026, read-only, against the reviewed checkout at `3f4e514444214e562eababb4eecc5b6ffb818002`.

## Result and scope

No concrete mathematical mismatch was found in the sampled high-risk steps below. This is a source-level correspondence review, not a new compilation, full transitive semantic audit, or independent reconstruction of the inherited algebraic geometry. In particular, no publication-readiness certification follows from this pass.

Paths below are relative to `preprints/` in that checkout. Package abbreviations:

- A: `The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026`
- B: `The-irrationality-exponent-of-nonzero-rational-arctangents-is-2-October-7-2026`
- C: `The-irrationality-exponent-of-arctan-sqrt2-over-sqrt2-is-2-October-7-2026`
- D: `The-irrationality-exponent-of-log-3-plus-2-sqrt2-over-sqrt2-is-2-October-7-2026`

## Substantiated correspondences

| Risk sampled | Prose and source evidence | Finding |
|---|---|---|
| Different selected minors at the real embeddings | D `build/manuscript.md:97`; D `lean/RealNorm/ScaledArithmetic.lean:53`, `:78`, `:107`, `:121`; D `lean/RealNorm/DeterminantContradiction.lean:55` | One order-valued `clearedMinor` and one `selection` occur in both embedding identities. The contradiction selects once, proves the flipped determinant nonzero, and applies both analytic estimates to that same selection. |
| Invalid claim that each real embedding has modulus at least one | D prose `:39`, `:141`, `:146`; `ScaledArithmetic.lean:121`, `:199`; `DeterminantContradiction.lean:67` | The actual lower bound concerns the average of the two logarithms. Both signs use the same positive clearing factors. The code does not replace the product norm bound by a lower bound on each embedding. The normalized denominator is the actual row count times positive height. |
| Irrational algebraic scaling mistaken for rational scaling | C prose `:37`, `:51`; C `lean/Imaginary/Endpoint.lean:9`, `:32`, `:51`, `:82`; C `lean/Imaginary/Main.lean:14` | The actual generic angle is `2 * Real.arctan (Real.sqrt 2) / Real.sqrt 2`; its exponential and non-torsion conditions are discharged. The final target is obtained by division by natural 2. No invariance under multiplication by sqrt(2) is invoked. |
| Wrong real-quadratic target or assumed exponential identities | D `lean/RealNorm/Endpoint.lean:6`, `:8`, `:19`, `:25`, `:36`, `:61`, `:76` | `normalizedLog` is exactly `Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2`. Both sign identities and injective powers are established before constructing `sqrtTwoPeriod`; they are not public endpoint hypotheses. |
| Missing quadratic rotation cost | C prose `:254`; D prose `:256`; C `lean/Imaginary/DeterminantData.lean:91`; D `lean/RealNorm/DeterminantData.lean:91`; D `DeterminantContradiction.lean:74`, `:80`, `:99` | The additional `log 2 / wstar` is paid explicitly: the strengthened arithmetic bound subtracts that amount from its error allowance; the analytic bound adds it. The contradiction uses exactly these complementary quantities. Parameters are constructed with `lcmConstant + Real.log 2`. |
| Treating a mere lower bound on weights as an attained minimum | A `lean/Logarithm/AdmissibleParameters.lean:60`, `:62`, `:135`; D `lean/RealNorm/DeterminantData.lean:103` | The data includes `wstar_attained`, constructed by a finite-minimum lemma. This supplies the crucial inequality `1 / wstar <= sum (1 / weight)` used by the reserve. |
| Circular parameter selection or interpolation supplied as hypothesis | A `lean/Logarithm/AdmissibleParameters.lean:66`, `:87`, `:123`, `:130`, `:134`; A `lean/Logarithm/Interpolation.lean:13`, `:24`; D `lean/RealNorm/GlobalMatrixInterpolation.lean:67`; D `DeterminantContradiction.lean:85` | Source ordering fixes dimension, margin and finitely many approximants before choosing the cofinal height. The contradiction asks the cofinal interpolation theorem for a height after its own eventual analytic threshold. It does not assume the desired nonzero determinant in the final theorem. This checks the interface/quantifier order, not every inherited geometric definition. |
| Non-torsion excludes rational arctangent endpoints ±1 | B `lean/Arctangent/Main.lean:44`, `:47`, `:50`, `:54` | Both exceptional inputs are explicitly split off and use the inherited pi bound divided by 4, with negation for -1. Only the remaining rational cases use the non-torsion period construction. |
| Supremum convention hides rationality or unboundedness | A `build/sections/introduction.tex`; A `lean/Logarithm/ExponentConsequence.lean:8`, `:28`; A `lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean:57`, `:77`, `:92` | Irrationality follows from the unreduced-denominator lower bound using exact multiples of a rational representation. The exponent proof separately establishes membership of 2 and an upper bound for every admissible exponent before applying `csSup_le` and `le_csSup`. It does not exploit an empty or unbounded real supremum. |

## Independent arithmetic checks on the exposition

The parameter inequalities are mutually compatible as described. With rational b in `(1/2, 1-1/nu)`, theta = 1-s and A = 1-bs, `nu(A-theta) > 1-theta` reduces to `nu(1-b)>1`. Also `A^2 < theta` holds for sufficiently small positive s because `2b-1>0`. Therefore `(A/theta, 1/A)` is nonempty; choosing C there leaves a nonempty interval `(A, min(1/C, C*theta))` for B and ensures `C*theta<1` since theta<A. Substituting `v0 = 2K theta^m w0` and `w0=B^(-m)` into the collision limit gives exactly `c eta^2 (B/A)^m / (2(m+1))`. No lost factor two was found at that substitution.

The real determinant bound includes the base-denominator cost `K log D / w0`, while the analytic budget includes `rho K / w0`. The manuscript's dimension budget combines these as `(rho + log D) K / w0`, matching the formal error decomposition. The extra sqrt(2) slope is bounded conservatively by 2 and its logarithmic cost is budgeted separately as described above.

## Remaining review boundary

The sampled checks support the current normalizations, same-minor arithmetic, parameter reserves, exceptional cases and exponent bridge. They do not replace a detailed review of the inherited weighted curve comparison, differential frame, ordinary blowup/Serre-vanishing construction, and analytic collision estimates. Those components carry substantial mathematical content and are shared by the four results. A defect in their statement-to-definition correspondence could affect all four even if each extension above is assembled correctly.

The next substantive mathematical review should assign an algebraic geometer the degree-bounded interpolation argument and an approximation theorist the determinant/collision argument, with the exact compiled theorem statements and supporting definitions available. Avoid labeling this sample a completed lemma-by-lemma manuscript certification.

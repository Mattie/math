# Questions worth revisiting

These are research questions, not conjectured theorems with supporting proofs. See the [findings](findings.md) for the rate gap and the [certificates](certificates.md) for sufficient inputs.

## 1. Can a construction share denominators before combining forms?

Independent approximations usually pay a product-of-denominators cost. A simultaneous Padé or integral construction might allow several logarithmic or arctangent terms to share arithmetic structure from the start.

The useful first deliverable would be an exact integral or recurrence producing integer forms in the intended single constant, together with justified height and error rates after all clearing costs. For the motivating π application, a rate ratio below $3/2$ would justify further investigation. Strong individual approximations are not enough without a proof that the combination retains their advantage.

## 2. Is there additional divisibility with a provable exponential rate?

Large gcds in a finite sample can suggest arithmetic structure. The challenge is to turn that observation into a uniform divisor theorem and quantify its savings in the same normalization as the analytic estimates.

For the inspected Bai family, reaching the $12/5$ target would require an additional saving rate of at least about $1.24315$. That is a substantial requirement. An isolated large gcd or a parameter scan with better early terms would not establish it.

## 3. Can recurrences certify independence uniformly?

The bounded-window certificate needs two nonproportional coefficient pairs in every fixed-length window. A recurrence may permit an exact determinant identity, sign argument, or invariant that establishes this for all indices.

If such independence is awkward, the second certificate offers another route: prove two-sided coefficient growth and use irrationality to handle coincidences. Either approach could be useful for constants whose analytic rates are already favorable. Sampling determinants cannot replace the uniform proof.

## 4. Can effective local exclusion replace a separated-tuple argument?

The effectivity obstacle would change if one could exclude a single sufficiently large exceptional denominator, or bound the location of the last cluster of exceptions. An explicit auxiliary degree for a tuple already assumed to exist does not supply this.

A promising result would state a computable threshold directly in terms of the target constant and exponent, and explain why no exception can occur beyond it. The current investigation did not find such a result for the π target.

## 5. Where would the certificate lemmas be immediately useful?

Before formalizing them, look for a concrete family that supplies all hypotheses with numerical data. Quadratic irrational recurrences provide simple examples; the √2 instance checks that the formulas can be instantiated, although its bound is deliberately weak and has no novelty claim.

A useful formal library contribution would connect an actual approximation construction to an actual downstream numerical estimate. The generic lemmas alone do not produce a new π result. They may still reduce duplicated work when an effective family for another constant is available.

## What would change the present assessment?

Revisit the numerical π application when a candidate provides either a certified denominator threshold or a family with favorable rates, explicit constants, and a proved noncoincidence mechanism. Until then, retaining these notes is more useful than expanding a formal development around a missing hypothesis.

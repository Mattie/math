# Effective approximation: certificates and open questions

Ryan Matthew Casper · October 9, 2026

These research notes collect useful consequences of an investigation into explicit rational approximation bounds. The motivating question was whether a numerical bound for approximating π could give certified error estimates for the Flint Hills and Cookson Hills series.

**We did not obtain the required numerical constant for π.** The useful output is a pair of explicit certificate lemmas, a quantitative assessment of several candidate constructions, and a more precise description of the mathematical input still needed.

## Contents

- [Certificate lemmas](certificates.md): two ways to turn a family of integer linear forms into a global irrationality bound, with proofs and a worked √2 example.
- [Findings and limitations](findings.md): the distinction between finiteness and an effective threshold, candidate rates, and the limits of finite experiments.
- [Questions worth revisiting](questions.md): concrete directions and the evidence that would make them promising.

The certificate lemmas are ordinary mathematical arguments. They are not Lean-checked results, and no novelty or priority claim is made for them. The second lemma adapts a selection mechanism from Hata. The literature assessment records sources inspected on October 8, 2026; it is not an exhaustive survey or a statement about all later work.

## Why the constant matters

A useful target is a supplied rational number $0<c\le1$ satisfying

$$
\left|\pi-\frac pq\right|\ge c q^{-12/5}
\qquad(p\in\mathbb Z,\ q\in\mathbb Z_{\ge1}).
$$

Such a bound is an input to explicit small-divisor tail estimates. More generally, an effective approximation exponent strictly below $5/2$ is useful for these series. An exponent-two theorem with an unspecified exceptional range does not by itself provide the numerical input.

These notes do not include a formal tail-bound library or claim an unconditional numerical evaluation of either series. Their reusable mathematical content is the certificate interface, which applies to real numbers other than π as well.

## Authorship and AI use

The author initiated and directed this investigation. OpenAI coding agents contributed substantially to the literature search, mathematical derivations, computational diagnostics, and preparation of these notes. The investigation builds on the cited published work, including OpenAI's manuscript and released library. Mathematical arguments and source assessments here remain open to independent review.

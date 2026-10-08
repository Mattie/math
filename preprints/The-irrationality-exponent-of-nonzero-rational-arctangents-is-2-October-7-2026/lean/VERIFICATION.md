# Arctangent proof verification

Date: 7 October 2026. Verification timestamps use UTC.

## Accepted formal statements

The checked endpoint file is `Arctangent/Main.lean`. Its five export targets are:

- `OAI.Arctangent.arctan_half_irrationalityExponent_eq_two`
- `OAI.Arctangent.arctan_half_explicit_bound`
- `OAI.Arctangent.rational_arctan_irrationalityExponent_eq_two`
- `OAI.Arctangent.rational_arctan_integer_eventualLowerBound`
- `OAI.Arctangent.rational_arctan_explicit_bound`

They prove the exponent-two theorem for `Real.arctan (1/2)` and for `Real.arctan (r : ℝ)` for every rational `r ≠ 0`. The family hypothesis is exactly `r ≠ 0`.

The fully expanded family bound is:

```lean
∀ (r : ℚ), r ≠ 0 → ∀ (nu : ℝ), 2 < nu →
  ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
    (q : ℝ) ^ (-nu) ≤ |Real.arctan (r : ℝ) - (p : ℝ) / (q : ℝ)|
```

The half-arctangent bound has the same type with the target replaced by `Real.arctan (1 / 2)` and no rational-input hypothesis. Fractions need not be reduced.

`irrationalityExponent x` is `sSup (ApproximationExponents x)`, where the exponent set uses infinitely many distinct reduced rational numbers with denominator at least 2 and strictly positive error below the negative real power of the denominator. The proof derives irrationality from the unreduced eventual bound, establishes membership of 2 by Dirichlet approximation, and excludes every larger exponent. It does not exploit an unbounded-supremum convention.

## Lean source and axiom audit

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, compiled all 14 new modules in dependency order with `autoImplicit=false`, including `Arctangent.EndpointAudit`.

All 31 audited endpoint and intermediate declarations report exactly `propext`, `Classical.choice`, and `Quot.sound`. The audits include Gaussian clearing, rotated errors, the actual interpolation matrix, analytic expansion, parameter existence, the determinant contradiction, root-of-unity classification, angle specialization, scaling transport, and the final statements.

Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. OpenAI's original source is pinned to `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The frozen core contains 14 new Arctangent modules, 55 unchanged Logarithm modules, and 869 unchanged OpenAI modules. All 938 module hashes match the sources used by the checked native environment. The inherited files also match the previous audited bundle byte for byte. The new source scan found no `sorry`, `admit`, axiom declaration, `unsafe`, `extern`, or `implemented_by`. See `source-manifest.json` and `sources.sha256`.

`source-manifest.json` SHA-256:

`535f967f1357e1be4524c1a8dc97942898a101508924aeb19a34f7b26a7157bf`

## Export and independent checkers

The final frozen-source export contains 1,281,816,054 bytes. Its SHA-256 is:

`f02fa59112a93d2d82077fe5d39ac171e914b31dcaf1fa93e8b301b76594702c`

The exact export is retained as `release-assets/arctangent-main.ndjson.gz` in the preprint directory. Its SHA-256 is `695453c9039fd6b88c066d7893e4c1b9d9de7c9ad51e873c5e374dab895a87dd`. The script `evidence/nanoda/replay-export.sh` streams it to the pinned Nanoda checker without relying on the original native path.

The export includes the dependency closure of all five targets. Exporter format is 3.1.0. The source is unmodified lean4export at commit `076e8e57707e813375e8f9da8bf989799ace9680`, compiled with Lean 4.34.1. Binary SHA-256:

`8c5d64ba68f4d3a68b3bcb7e1c5f188e35ae573b29470b8d4530a62324c9ddd1`

Nanoda is version 0.4.19, source commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`, built unmodified with Rust 1.99.0 and `cargo build --release --locked`. Binary SHA-256:

`a58f6590e9561bd296b7b187d75515fb3e6920defcaeac3582417579210e062d`

Its strict configuration permits only the three foundational axioms, sets `unpermitted_axiom_hard_error=true` and `unsafe_permit_all_axioms=false`, and enables the ordinary Nat and String kernel extensions. Four threads check the declarations. Suppressing proof text in the pretty printer does not suppress checking proof bodies.

**Final Nanoda status: accepted.** The final run checked 118,572 declarations with no errors, exit 0. It ran from 2026-10-08 00:44:23 to 00:45:52 UTC, with measured wall time 88.66 seconds and peak resident memory 1,678,324 KiB. The portable checker configuration is retained in `evidence/nanoda/replay-config.json`. This receipt covers the final export hash above.

**Second stock Lean status: accepted.** Stock Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, replayed exactly the final export in a fresh trust-level-zero kernel environment. It reported 118,569 accepted declarations plus the three regenerated quotient primitives, accounting for all 118,572 exported declarations. The run lasted 685.00 seconds, from 2026-10-08T00:44:44Z to 2026-10-08T00:56:09Z, with peak resident memory 2,317,932 KiB and exit 0. The unmodified official checker comes from Lean Kernel Arena commit `b83254de5146ef34147ab82a48edbe1856b0edcc`, with the pinned lean4export parser. Its binary SHA-256 is `f18020ea3525ee1058788decc2169480cc9ed371a990f4081170c82c186053f9`. A concise replay receipt is in `evidence/stock-lean-replay.json`.

## Fresh negative controls

The strict Nanoda checker rejected the intentionally extra axiom `ArctangentControls.deliberatelyForbidden`, exit 1. That separate control is outside the proof source tree.

The stock Lean checker accepted a positive fixture with two declarations. It parsed the ill-typed negative fixture successfully, then rejected the same fixture during normal kernel replay with `(kernel) declaration type mismatch`, exit 1. Thus the normal invocation checks theorem bodies rather than stopping at successful parsing.

The portable scripts reproduce these positive and negative controls. Raw execution logs and development records are not part of this publication package.

## What is and is not established

The formalization rotates rational approximants by `Complex.I`, preserving their norms and ordinary denominator weights. Its matrix retains the factors `alpha^(j*h)`. Gaussian clearing retains the row savings and incurs the explicit cost `K*log(D)/w0`; the parameter proof absorbs this cost and the complex radius cost. The angle is specified by `exp(I*xi)=alpha`, so no incorrect principal-logarithm identity is assumed for its powers.

The dedicated half-arctangent path uses `U=3+4i`, `D=5`. The general path proves non-torsion for rational inputs outside `0,±1`, handles `±1` through the certified pi bound, and excludes zero. Division by 2 and 4 is proved at the quantified approximation-bound level with exponent slack. No algebraic-scaling invariance is invoked.

The verification concerns the displayed formal statements and definitions relative to the three foundational axioms. Independent exported-proof checking and stock-kernel replay reduce reliance on a single checker implementation; they do not constitute an independent mathematical discovery, exhaustive priority search, or external human peer review.

## Catalogue statement module

[Arctangent/FormalConjectures.lean](Arctangent/FormalConjectures.lean) proves
`OAI.Arctangent.rational_arctan_irrationality_and_bound`, the exact conjunction
used by the proposed Formal Conjectures entry. It imports `Arctangent.Main`.
The supplementary module has its own hash in `formal-conjectures-sources.sha256`;
the frozen core manifests above are unchanged.

The module compiled on Lean 4.34.1 with `autoImplicit=false` and warnings treated
as errors, using native dependencies whose sources match the frozen manifests.
Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
See the [receipt](../evidence/formal-conjectures-verification.json) and
[axiom output](../evidence/formal-conjectures-axioms.log). Run `bash verify.sh`
to build and audit it with the rest of the source package. This additional
module is not included in the retained export or its earlier independent replay.

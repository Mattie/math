# Normalized quadratic arctangent verification

Date: 7 October 2026, America/Chicago. Checker timestamps use UTC.

## Exact accepted Lean statements

`Imaginary/Main.lean` proves

```lean
OAI.PiExponent.irrationalityExponent
  (Real.arctan (Real.sqrt 2) / Real.sqrt 2) = 2
```

The fully expanded approximation theorem has no arithmetic, interpolation, determinant, or analytic premise:

```lean
∀ (nu : ℝ), 2 < nu →
  ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
    (q : ℝ) ^ (-nu) ≤
      |Real.arctan (Real.sqrt 2) / Real.sqrt 2 - (p : ℝ) / (q : ℝ)|
```

Fractions need not be reduced. Irrationality follows by applying this bound to hypothetical exact fractions with unbounded denominators. The irrationality exponent is the supremum of exponents admitting infinitely many distinct reduced rational approximants with denominator at least 2 and strictly positive error below the negative power of that denominator. The proof supplies exponent 2 by Dirichlet approximation and excludes every larger exponent, so it does not exploit a convention for an unbounded supremum.

The five exported targets are:

- `OAI.Imaginary.period_irrationalityExponent_eq_two`
- `OAI.Imaginary.normalized_arctan_sqrt_two_eventualLowerBound`
- `OAI.Imaginary.normalized_arctan_sqrt_two_irrationalityExponent_eq_two`
- `OAI.Imaginary.normalized_arctan_sqrt_two_integer_eventualLowerBound`
- `OAI.Imaginary.normalized_arctan_sqrt_two_explicit_bound`

The generic first theorem accepts `PeriodData`: a nonzero real angle, a positive integer denominator, an integer element of `Zsqrtd (-2)`, the specified complex exponential identity, and injectivity of the nonnegative powers of the resulting quotient. These are arithmetic input conditions. The exact endpoint constructs all of them, using `U=-1+2i√2`, `D=3`, and the angle `2 arctan(√2)/√2`. Rational division by 2 is proved with exponent slack.

## Source build and audit

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, compiled all 15 new modules in one coherent dependency-order run with `autoImplicit=false`. `Imaginary.EndpointAudit` audits 27 intermediate and endpoint declarations. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. The source audit can be reproduced with `bash verify.sh`.

Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. The original OpenAI library is pinned to `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The frozen core contains 15 Imaginary, 55 Logarithm, and 869 OAI modules. All 939 source files match the sources used in the compiled environment; the 924 inherited files also match the preceding frozen package byte for byte. The new-source scan found no `sorry`, `admit`, axiom declaration, `unsafe`, `extern`, or `implemented_by`.

Source-manifest SHA-256: `611f176c1dc96160ce1c966c7bbbea2b9554c5fc5a16ca265ff6065035ef49fc`.

The build uses a populated native Mathlib/library cache with verified source equality. A new network bootstrap of the whole bundle was not run. `verify.sh` provides that reproducible path; the actual final audit and independent exported-proof checks are separately recorded.

## Independent check status

The textual export contains 1,273,418,143 bytes, with SHA-256:

`1aeffb0545974663a19694c8810d0bb8eb9110dc77f0aa9bf76d39a404f7c0dd`

The compressed export is a separately distributed release asset; its sizes and hashes are in [release-assets.json](../evidence/release-assets.json). The [Nanoda replay script](../evidence/nanoda/replay-export.sh) streams it through the pinned checker. The [export audit](../evidence/export-audit.json) records exactly the three foundational axioms and no unsafe or partial declarations.

Its dependency closure contains all five listed endpoints. Exporter format is 3.1.0, from unmodified lean4export commit `076e8e57707e813375e8f9da8bf989799ace9680`, built with Lean 4.34.1. Exporter binary SHA-256: `8c5d64ba68f4d3a68b3bcb7e1c5f188e35ae573b29470b8d4530a62324c9ddd1`.

Nanoda 0.4.19 is pinned to commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`, built unmodified with Rust 1.99.0 using `cargo build --release --locked`. Its binary SHA-256 is `a58f6590e9561bd296b7b187d75515fb3e6920defcaeac3582417579210e062d`. The configuration permits only the three foundational axioms, rejects all others, and enables the ordinary Nat and String kernel extensions. Pretty-printing suppresses proof text, not proof checking.

**Nanoda final export check: accepted.** It checked 117,922 declarations with no errors, exit 0, from 2026-10-08T01:33:23Z to 01:35:13Z. Measured wall time was 110.05 seconds; peak resident memory was 1,667,500 KiB. It printed the five exact endpoints and the three foundational axioms.

The second checker is official stock Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, using unmodified Lean Kernel Arena checker commit `b83254de5146ef34147ab82a48edbe1856b0edcc`. It replays the exact textual export in a fresh trust-level-zero environment. Checker binary SHA-256: `f18020ea3525ee1058788decc2169480cc9ed371a990f4081170c82c186053f9`. The reproduction script fetches the pinned unmodified checker source.

**Stock Lean final export replay: accepted.** It accepted 117,919 replayed declarations plus three regenerated quotient primitives, covering all 117,922 exported declarations. The run lasted 672.62 seconds, from 2026-10-08T01:33:31Z to 01:44:43Z, with peak resident memory 2,312,856 KiB and exit 0. The concise [replay receipt](../evidence/stock-lean-replay.json) records the accepted count and negative control. Both checkers consumed the exact export hash above.

## Fresh controls and scope

The same Nanoda binary rejected an intentionally extra axiom `ImaginaryControls.deliberatelyForbidden`, exit 1. The same stock Lean binary accepted the positive fixture, parsed the ill-typed negative fixture, and rejected the latter during normal proof replay with `(kernel) declaration type mismatch`, exit 1. Both controls were rerun for this package; fixtures are outside the proof source tree.

The new determinant argument retains the matrix factors `alpha^(j*h)` and the row denominator savings. Clearing into `Z[√−2]` uses its positive integral norm; conjugate complex embeddings have equal modulus. The rotation has length `√2`, so the analytic estimate incurs a fixed `log 2 / wstar` cost. The parameter proof explicitly pays it from an increased lcm budget and an attained minimum weight, while retaining the `K log(D)/w0` and complex-radius costs.

The result covers the exact normalized target and non-torsion periods in `Q(√−2)`. It does not certify every imaginary quadratic field, the unnormalized `arctan√2`, or torsion periods such as `π/√d`. No algebraic-scaling invariance or principal-logarithm identity for powers is assumed.

Formal verification is relative to the three stated foundational axioms. Independent proof checking is not external human peer review or an exhaustive priority search. Ryan Matthew Casper is the author; OpenAI coding agents contributed substantially to the adaptation, proof development, checking, and exposition. The mathematical framework and inherited library are attributed to OpenAI/math and Mathlib.

## Catalogue statement module

[Imaginary/FormalConjectures.lean](Imaginary/FormalConjectures.lean) proves
`OAI.Imaginary.normalized_arctan_sqrt_two_irrationality_and_bound` for the
normalized value arctan(sqrt(2))/sqrt(2). Its hash is recorded separately in
`formal-conjectures-sources.sha256`; the frozen core manifests are unchanged.

The module compiled on Lean 4.34.1 with `autoImplicit=false` and warnings treated
as errors, using native dependencies whose sources match the frozen manifests.
Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
See the [receipt](../evidence/formal-conjectures-verification.json) and
[axiom output](../evidence/formal-conjectures-axioms.log). Run `bash verify.sh`
to build and audit it with the rest of the source package. This supplementary
module is not included in the retained export or its earlier independent replay.

# Normalized real quadratic logarithm verification

Date: 7 October 2026, America/Chicago. Checker timestamps use UTC.

## Exact endpoint

`RealNorm/Main.lean` proves

```lean
OAI.PiExponent.irrationalityExponent
  (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) = 2
```

The expanded approximation statement has no arithmetic, interpolation, determinant, or analytic premise:

```lean
∀ (nu : ℝ), 2 < nu →
  ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
    (q : ℝ) ^ (-nu) ≤
      |Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 - (p : ℝ) / (q : ℝ)|
```

Fractions need not be reduced. The threshold is uniform in numerator and denominator; no computable threshold is claimed. The formal generic input describes compatible norm-one periods in Q(√2), with explicit identities at both embeddings and injective nonnegative powers. The endpoint verifies those inputs for the unit 3 + 2√2. The theorem does not cover all real quadratic fields or assert algebraic-scaling invariance for irrationality exponents.

## Frozen source and Lean build

All 14 new RealNorm modules compiled in one coherent Lean 4.34.1 build. `RealNorm.EndpointAudit` audits 29 intermediate and endpoint declarations, each with only `propext`, `Classical.choice`, and `Quot.sound`. No new-source `sorry`, `admit`, axiom declaration, `unsafe`, `extern`, or `implemented_by` is present.

The frozen source contains 14 RealNorm, 55 Logarithm, and 869 OpenAI modules: 938 total. `source-manifest.json` and `sources.sha256` identify the exact source bytes. The source-manifest SHA-256 is `8222fe1962cebaec1490e2e7b30b9d928e46c6ff316202492f0e738d78b10c9b`.

Lean is pinned to 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`; OpenAI/math to `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The final source build used a populated native cache with source equality checks. Publication preparation does not claim a fresh network bootstrap or rerun of the complete proof. [Reproduction instructions](../VERIFY.md) provide those paths.

## Export checks

The export has 1,272,939,363 bytes and SHA-256 `cc979a7171672356f72344b7c1771b3344fb19a0601ce5fdff050da60ffbff56`. Its compressed identity is in [the asset manifest](../evidence/release-assets.json). Both retained-export replay scripts verify that identity. Fresh source re-export is not assumed byte-identical.

**Nanoda accepted all 117,830 declarations, exit 0.** It printed the five endpoint declarations and the three foundational axioms. Its [receipt and configuration](../evidence/nanoda/verification.json) record the exact exporter and checker pins, binary hashes, and permitted axioms. The checker rejects all other axioms and enables the standard Nat and String extensions. Pretty-printing suppresses proof text, not proof checking. A fresh forbidden-axiom control was rejected, exit 1.

**Stock Lean 4.34.0 replay accepted 117,827 declarations plus three regenerated quotient primitives, exit 0.** This covers the same 117,830 exported declarations. The run lasted 687.86 seconds, from 2026-10-08T03:10:50Z to 03:22:18Z, with peak resident memory 2,313,564 KiB. The [replay receipt](../evidence/stock-lean-replay.json) records these results and the exact export identity.

The portable script uses the official unmodified Lean Kernel Arena checker at commit `b83254de5146ef34147ab82a48edbe1856b0edcc`, with Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. It audits the export, accepts a positive fixture, parses then rejects an ill-typed proof, and replays proof bodies at trust level zero. The [export audit](../evidence/export-audit.json) found exactly the three foundational axioms and no unsafe or partial declarations.

## Scope and attribution

The proof constructs one cleared order-valued matrix and evaluates its same selected minor at both real embeddings. The norm lower bound is combined with analytic upper bounds for both signs; averaging pays the degree-two arithmetic cost without losing the row savings. The analytic slope cost is explicitly included in the parameter budget.

Formal checking is relative to the stated foundational axioms. It is not external human peer review or a priority determination. Ryan Matthew Casper is the author; OpenAI coding agents contributed substantially under his direction. OpenAI's interpolation framework and library, Mathlib, and the preceding logarithm and quadratic-period adaptations are substantial foundations.

## Catalogue statement module

[RealNorm/FormalConjectures.lean](RealNorm/FormalConjectures.lean) proves
`OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound`, combining
irrationality of log(3 + 2√2)/√2 with its eventual approximation bound using
standard Mathlib definitions. Its hash is recorded separately in
`formal-conjectures-sources.sha256`; the frozen core manifests are unchanged.

The module compiled on Lean 4.34.1 with `autoImplicit=false` and warnings treated
as errors, using native dependencies whose sources match all 938 frozen modules.
Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
See the [receipt](../evidence/formal-conjectures-verification.json),
[build record](../evidence/formal-conjectures-build.log), and
[axiom output](../evidence/formal-conjectures-axioms.log). Run `bash verify.sh`
to build and audit it with the rest of the source package. This supplementary
module is not included in the retained export or its earlier independent replay.

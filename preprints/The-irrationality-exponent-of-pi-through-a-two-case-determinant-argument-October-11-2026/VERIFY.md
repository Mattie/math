# Verification of the November 27 package

## Manuscript and build

The current package identifies the revised TeX, its 18-page PDF, the build and inspection records, and the Lean sources used for the proof. [Artifact manifest](evidence/manifest.json)

Tectonic 0.17.0 rebuilt the paper on Windows. The rendered pages were inspected, including the revised abstract, Section 5, and the attribution and formalization discussion. The inspection also checked PDF destinations, metadata, and attachments. [Build receipt](evidence/build.json) · [PDF inspection](evidence/pdf-inspection.json)

## What the Lean companion proves

- `PiTwoCaseBridge.theorem_5_1` gives simultaneous logarithmic interpolation at every positive real cutoff `T` in source degree at most `κT+B` with `0<κ<1`. Its proof uses the source degree bound from monomial curves, global generators, weighted arcs, and finite polynomial reduction.
- `PiTwoCaseBridge.pi_irrationalityExponent_eq_two` uses that theorem to obtain the interpolation for OpenAI's two-case determinant argument. The exported body reaches `pi_eventual_lower_bound`, `admissible_strictInterpolation`, and `theorem_5_1`. It also reaches the equal-cutoff inference in the determinant adapter and the inherited analytic aggregate.
- `PiTwoCaseBridge.main` is the replay root. It gives the eventual nonstrict lower bound for every integer numerator and sufficiently large integer denominator, and the supremum statement for `μ(π)=2`. The strict inequality in the paper follows by applying the bound at an exponent strictly between `2` and the one requested.

[Lean entry point](../../formalizations/PiTwoCaseBridge/PiTwoCaseBridge/Main.lean) · [Paper-to-Lean map](SOURCE-MAP.md)

## Recorded proof checks

On November 26, stock Lean 4.34.1 and Nanoda accepted the same 1,255,233,780-byte export of `PiTwoCaseBridge.main`. Its SHA-256 was `9c8013cd869e49790892ca6224624cafed2a7b9df6a6461b3c463716d0133b31`. The stock reader omits three quotient entries supplied by the kernel. Both checkers exited successfully.

| Checker | Revision | Declarations accepted |
| --- | --- | ---: |
| Stock Lean 4.34.1 | `5045d0056413266e57c625dcd7c365b10e377c52` | 117,238 |
| Nanoda | `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` | 117,241 |

The clean companion build reused the pinned Mathlib and inherited OpenAI objects. The transitive axiom audit of both endpoints and Theorem 5.1 reported `propext`, `Classical.choice`, and `Quot.sound`. This paper revision reuses those proof checks. The companion sources and inputs listed in the manifest match the recorded input hashes. The full export and raw checker logs are retained separately.

The [source ZIP](build/PiTwoCaseBridge-2026-11-26.zip) is also embedded on page 18. The [fresh-checkout replay instructions](../../verification/isolated-pi-two-case/REPLAY.md) describe how to reconstruct the export. The November 26 export and raw logs are retained separately.

## Build and audit from source

Build the companion in the pinned Lean and Mathlib environment with the inherited OpenAI modules available on `LEAN_PATH`. The overlay build elaborates `Audit.lean`, which prints the endpoint types and transitive axioms. For export, add the built overlay to `LEAN_PATH` and run the `lean4export` executable at revision `05d43a2bc773b40ecfdebb32294192a5ef756951`.

~~~sh
lean4export PiTwoCaseBridge.Main -- PiTwoCaseBridge.main > closure.ndjson
~~~

[Companion build instructions](../../formalizations/PiTwoCaseBridge/README.md) · [Audit.lean](../../formalizations/PiTwoCaseBridge/PiTwoCaseBridge/Audit.lean) · [Pinned exporter](https://github.com/leanprover/lean4export/tree/05d43a2bc773b40ecfdebb32294192a5ef756951)

## Fresh local replay

The separate [fresh-checkout replay](evidence/fresh-replay.json) rebuilt the required OpenAI modules and all 27 companion modules from source, using the pinned Mathlib cache. Both newly built checkers accepted the same new export of PiTwoCaseBridge.main. The export matches the November 26 export byte for byte. The hosted isolation check is tracked separately.

## Isolated source verification

The [manual GitHub verifier](../../verification/isolated-pi-two-case/README.md) stages the frozen companion and checks three declarations against independently stated claims. Its local staging and challenge checks passed. GitHub execution and evidence review remain pending.

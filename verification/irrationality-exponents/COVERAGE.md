# Catalogue-wrapper coverage

This package supplies a reproducible independent-verification route for four
final approximation statements. Its 8 October results are retained evidence,
not a new checker run performed while preparing PR #10.

## Normalized logarithm and FC #6942

The solution declaration is
`OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound` in
[`RealNorm/FormalConjectures.lean`](../../preprints/The-irrationality-exponent-of-log-3-plus-2-sqrt2-over-sqrt2-is-2-October-7-2026/lean/RealNorm/FormalConjectures.lean).
The independent [Mathlib-only challenge](challenges/realnorm.lean) states the
same proposition as [FC #6942](https://github.com/google-deepmind/formal-conjectures/pull/6942):

- `log(3 + 2 sqrt(2)) / sqrt(2)` is irrational.
- For every real `nu > 2`, there is one integer threshold `Q >= 2` such that
  the lower bound `q^(-nu) <= |log(3 + 2 sqrt(2)) / sqrt(2) - p/q|`
  holds for every pair of integers `p, q` with `q >= Q`.

There is no coprimality restriction; unreduced fractions are included. The
challenge uses standard Mathlib definitions and does not import solution modules.
Its `sorry` is an intentional specification placeholder. Comparator compares
its compiled proposition and supporting definition closure against the solution;
Nanoda checks the solution export, not the placeholder challenge.

The [recorded portable run](validation/2026-10-08.json) names that exact wrapper.
Its [Comparator log](validation/realnorm-compare.log) reports acceptance of the
statement, definition closure, and axiom policy. Its
[Nanoda log](validation/realnorm-nanoda.log) reports 117,787 declarations checked
without errors. The permitted axioms were `propext`, `Classical.choice`, and
`Quot.sound`. The receipt records seven successful acceptance/rejection controls.
This addresses independent verification of the submitted wrapper; it is not
independent human mathematical review or a proof of novelty.

## Keep the artifacts distinct

| Artifact | Scope |
| --- | --- |
| `realnorm-main.ndjson.gz` | Retained core export with its original historical identity; omits the supplementary catalogue wrapper. |
| `realnorm-catalogue-20261008T144533Z.ndjson.gz` | Separate transport of the portable validation run's solution export, including the exact wrapper above. |
| [Historical audit](historical/README.md) | Earlier local checking route with different export identities; not the portable validation run. |
| [Six-package CI](https://github.com/Mattie/math/actions/runs/37872740986) | Lean source builds, fresh axiom audits, and publication checks at `a1fdf2f`; not an independent Nanoda replay. |

The portable wrapper export has uncompressed SHA-256
`8c1e66f96e5e982442dcebceda1b1298d97079664bee14a40377080ac4fc12fe`
and size 1,271,711,610 bytes. Its separate
[distribution inventory](../publication/wrapper-release-assets.json) records
its transport identity. The six old distribution entries remain unchanged.
The planned release is `proof-exports-2026-10-08`; no download is claimed available
until it is published and downloaded bytes are verified. After publication:

```sh
python3 verification/publication/check-release-assets.py /path/to/downloads \
  --inventory verification/publication/wrapper-release-assets.json
```

The full run directory and receipt were located during integration. The receipt's
SHA-256 matches `659dac4658e834bbdac93faa832b04ae330f58b8917c8ce11db78e2959c7a2d6`.
The solution export and challenge export were checked against the compact record.
The full working directory is not committed or represented as a public download;
the [portable command](README.md) creates a fresh complete evidence directory.

## Reuse boundaries

All 3,755 pinned inputs (942 for RealNorm) and all 17 retained checker logs
were checked against the PR checkout and recorded identities. The current runner
includes the later configuration-snapshot guard described in
[the validation notes](validation/README.md). Its nine focused tests were rerun;
the old full-run runtime hash and receipt remain unchanged. The full independent
check was not repeated for that guard or this integration.

The [integration identity record](integration-2026-10-09.json) distinguishes
byte-identical copied files from one public rendering of a prose audit that omits
a workstation path. Original local evidence remains unchanged. Tool pins,
challenge sources, checker sources, validation JSON, and checker logs are copied
byte for byte. `check-wrapper-evidence.py` verifies those published identities
and their correspondence to current pinned proof inputs; it does not establish
fresh checker acceptance. Official dependency caches and the absence of a
hostile-code sandbox remain explicit limits of the recorded run.

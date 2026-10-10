# Verification

The proofs use Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Two earlier isolated runs built the candidate sources and compared seven endpoints with independently written specifications. Nanoda and Lean's default kernel accepted both exports. Both exported closures contained only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

| Endpoints | Proof source | Sanitized historical receipt |
| --- | --- | --- |
| Positive-discriminant and nonzero-discriminant bounds and exponent statements (four) | [PositiveSolution.lean](lean/PositiveSolution.lean) | [positive-integralcheck.json](evidence/positive-integralcheck.json) |
| Repeated-root evaluation; rationality and irrationality equivalences (three) | [ClassificationSolution.lean](lean/ClassificationSolution.lean) | [classification-check.json](evidence/classification-check.json) |

The independent specifications are [PositiveChallenge.lean](lean/PositiveChallenge.lean) and [ClassificationChallenge.lean](lean/ClassificationChallenge.lean). Their intentional proof placeholders belong only to the comparator inputs; candidate proofs do not import them. The comparison configurations are retained beside them. The exponent statements use ordinary Mathlib `Irrational` and `LiouvilleWith`; the bounds quantify over every integer numerator and every sufficiently large natural denominator.

The combined dichotomy and example controls passed local compilation and axiom audits, but were not additional comparator targets. The [classification audit](lean/ClassificationAudit.lean) and [positive-discriminant audit](lean/PositiveAudit.lean) remain available to rebuild.

## Evidence scope

The two JSON summaries preserve the original receipt hashes, target lists, export identities, candidate-source hashes, verdicts and limitations. The original receipts and detailed private run evidence remain unchanged. These summaries are reports of those runs, not new kernel executions or cryptographically signed attestations.

Both historical runs reused pinned compiled dependencies; neither rebuilt all inherited sources. The proof exports are locally retained and are not distributed here. No public download or exact-export replay route for these integral exports is claimed. The upstream quadratic-period package has its own public evidence, which does not replace the integral checks.

The [source manifest](lean/source-manifest.json) binds every bundled Lean source. The package checker verifies these hashes, local import closure, and the candidate sources against both receipt summaries. The portable build script supplies a source-build route using locked public dependencies. A full clean bootstrap and fresh dual-kernel replay of this newly arranged package have not been performed.

A [fresh cached build](evidence/package-build.json) compiled all 20 integral proof, specification, control and audit modules from this package. Both audits also passed with warnings treated as errors, and the axiom gate checked 28 declarations against the three permitted axioms. The other sources retained existing style warnings and the independent specifications retained their intentional placeholders. The exact Lake configuration and lockfile loaded successfully with the existing pinned dependency cache. This check did not rebuild the 942 inherited modules or execute the full portable build from a clean checkout.

Independent model reviews assessed the original mathematical text, statement correspondence and retained evidence. Subsequent abstract, prose and reference edits preserved the mathematical statements and proof bytes. Automated checks and model review are distinct from human mathematical peer review.

The latest [abstract sentence revision](evidence/abstract-sentence.json) replaces one explanatory sentence with the author's selected wording. The current [PDF inspection](evidence/pdf-check.json) covers all six pages. Earlier editorial and paper-build receipts identify their earlier artifact versions.

The [repository integration](evidence/repository-integration.json) adds 24 unchanged upstream modules to retain the complete 869-module upstream inventory and adopts the repository's shared axiom checker. The integral sources and paper are unchanged. Earlier build receipts describe the preceding package inventory; no additional proof rebuild or replay is claimed.

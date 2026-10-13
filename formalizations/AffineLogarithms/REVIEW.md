# Review before PR preparation

Two fresh GPT-6 Astra reviewers found no confirmed defect within the scopes below.
These are model reviews, not human peer review or a claim of novelty. The original
assessments remain unchanged in the local research record; their hashes and the
reviewed input identities are recorded in [review.json](evidence/pre-pr/review.json).

The specification reviewer wrote an independent target description before reading
the challenge, solution wrappers, or concrete conclusions. The mathematical
reviewer first assessed a separately authored proof memo without seeing source or
checker results, saved that judgment, and then inspected the decisive source
interfaces and proof bodies. Neither saw the other's findings. Context separation
was instructional, not enforced by filesystem permissions.

The resulting [proof memo](ARGUMENT.md) differs from the reviewed text only in
Markdown math delimiters. It states the parameter margins, interpolation
hypotheses, common-minor construction, integral clearing, four-to-two norm count,
analytic multiplier cost, both contradiction branches, and concrete instances.

## What the reviews establish

| Review | Work performed | Scope limit |
| --- | --- | --- |
| Mathematical argument | Prose-first deduction review, followed by source correspondence for the decisive affine and inherited interfaces | No exhaustive reconstruction of inherited geometry, analysis, or asymptotic counting; no checker execution |
| Specification | Quantifiers, literal expressions, exponent conventions, all 969 frozen input hashes, and all 27 target theorem bodies in the retained export | Inventory is not proof-body type checking |
| Evidence stage | Original receipt/log identities, structured axiom inventory, pinned Mathlib definition, and fresh execution of the actual axiom policy on the retained build log | Historical execution is assessed through retained evidence; full kernel checks were reused |

The specification review's initial gap about the standard Mathlib definition was
closed by reading the pinned `LiouvilleWith` definition and its smaller-exponent
approximation lemma. The mathematical review found no missing endpoint hypothesis.
It requested better navigation for the deep inherited inputs; the map below supplies
that navigation without claiming a new bibliographic or priority assessment.

## Inherited mathematical inputs

| Input used by the memo | Source entry points |
| --- | --- |
| Numerical interpolation data and eventual surjectivity | [GeometryData](Logarithm/GeometryData.lean), [Interpolation](Logarithm/Interpolation.lean) |
| Ampleness and curve-model route | [GeometryAmple](Logarithm/GeometryAmple.lean), [CurveModel](Logarithm/CurveModel.lean) |
| Formal packet to truncated matrix | [ScaledMatrix](Logarithm/ScaledMatrix.lean) |
| Analytic collision and branch-compatible local identity | [ScaledCollision](Logarithm/ScaledCollision.lean), [ScaledPeriodAnalytic](Logarithm/ScaledPeriodAnalytic.lean) |
| Parameter construction and determinant contradiction | [AdmissibleParameters](AlgebraicLog/AdmissibleParameters.lean), [DeterminantContradiction](AlgebraicLog/DeterminantContradiction.lean) |

[PROVENANCE.md](PROVENANCE.md) identifies the inherited projects and exact pins.
The memo is a source-relative mathematical account; a conventional bibliographic
history of those deep inputs remains outside this preparation pass.

## Added checks

The [new build](evidence/pre-pr/build-receipt.json) passes all twelve public axiom
reports under the maintained policy. [Seven policy controls](evidence/pre-pr/axiom-controls/receipt.json)
accept an imported valid proof and reject an imported admission, an extra axiom,
and missing, truncated, conflicting, or malformed diagnostic reports.

The [maintained Comparator controls](evidence/pre-pr/comparator-controls/receipt.json)
also accept the imported valid proof and reject imported `sorryAx` and the extra
axiom. These are fresh small controls, not a new full solution replay.
[CHECKERS.md](CHECKERS.md) records the version-specific weaknesses, mitigations,
shared dependencies, and remaining boundaries.

All 969 frozen source/specification inputs and the accepted export remain unchanged.
The original archive is retained; revision two adds prose, controls, and evidence.
Novelty remains deferred. A network-only bootstrap, Windows build test, and public
download test remain unperformed and are disclosed in [VERIFY.md](VERIFY.md).

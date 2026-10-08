# All-power weighted degree bounds for monomial compactifications

**Ryan Matthew Casper · October 8, 2026**

[Read the paper](paper.pdf). The [editable manuscript](build/manuscript.md) and
[LaTeX source](build/main.tex) accompany the five new [Lean modules](lean/Degree).

The [companion explanations](explainers/README.md) cover the same result for
[PhD](explainers/ELIPHD.md), [master's](explainers/ELIMS.md),
[bachelor's](explainers/ELIBS.md), and [senior-calculus](explainers/ELIHS.md) readers.

For a finite monomial compactification containing the constant and coordinate
monomials, a section of the $n$-th hyperplane-bundle power has weighted polynomial
coefficients bounded by $nR$ for every $n\geq0$. Taking tensor powers upgrades the
inherited eventual degree bound; the degree-zero case uses the actual
constant-coordinate section. The result holds in every bundle frame on the fixed
affine chart, over every field.

This separate reference note strengthens an intermediate lemma shared by our
rational-logarithm, rational-arctangent, and two normalized quadratic-period
papers. Their proofs and endpoint statements remain valid without revision.
The note does not remove the interpolation threshold, compute effective
irrationality constants, or establish another irrationality endpoint. The
underlying tensor-power principle is standard.

The new sources were compiled with Lean 4.34.1. A selected proof export was
accepted by Nanoda and replayed by Lean 4.34.0. An independent automated
adversarial review checked the mathematical statement and Lean specification,
freshly compiled the five modules, and audited the recorded replay evidence.
See [verification and reproduction](VERIFY.md) for scope and exact identities.

The Lean overlay fetches a pinned public rational-logarithm package rather than
duplicating its 924 source files. Checker artifacts are described in
[the release-asset manifest](evidence/release-assets.json); the compressed export
is prepared separately from the Git source tree.

## AI use and attribution

The author initiated and directed the investigation of simplifying the degree-bound step in the earlier interpolation arguments. OpenAI coding agents contributed substantially to developing this reference note, producing its Lean formalization, and conducting an independent automated adversarial review. The construction builds on OpenAI's released manuscript and π library, the rational-logarithm extension, and Mathlib. Automated checking and model review are distinct from independent human mathematical review.


See [citation metadata](CITATION.cff), [license scope](LICENSES.md), and [notices](NOTICE).

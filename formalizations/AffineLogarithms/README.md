# Three affine logarithm bounds at four

The accompanying [preprint](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/README.md)
is titled **The irrationality exponents of log(2) + √2 and √2 log(2) are at most 4**.
It presents all three results below; this directory is its shared proof package.

This standalone Lean source package proves $\mu(x)\le4$ and irrationality for

| Number $x$ | Public declarations |
| --- | --- |
| $\log2+\sqrt2$ | [AffineExamples.lean](PairedAffine/AffineExamples.lean), prefix `log_two_add_sqrt_two` |
| $\sqrt2\log2$ | [AffineExamples.lean](PairedAffine/AffineExamples.lean), prefix `sqrt_two_mul_log_two` |
| $\log(3+2\sqrt2)/\sqrt2+\sqrt3$ | [Main.lean](PairedAffine/Main.lean), prefix `shifted_period` |

All names begin with `OAI.PairedAffine.`. Each prefix has four endpoints:
`eventualLowerBound`, `explicit_bound`, `irrational`, and
`irrationalityExponent_le_four`. The [complete theorem map](evidence/target-map.json)
also identifies three wrappers using Mathlib's standard approximation definitions.

For every displayed $x$, the explicit conclusion is

$$
\forall\nu>4\;\exists Q\in\mathbb N,\ Q\ge2,\quad
\forall p\in\mathbb Z\;\forall q\in\mathbb N,\quad
q\ge Q\Longrightarrow q^{-\nu}\le|x-p/q|.
$$

The threshold is chosen before both $p$ and $q$. The fractions need not be
reduced. These results give an upper bound of four, not equality or a
numerical threshold. [Solution.lean](Solution.lean) exposes the expressions
and quantifiers independently of the concrete target aliases.

## Build and check

Requirements: Python 3.11+, Git, and Lean's `elan` toolchain manager with
`lean` and `lake` on PATH. The toolchain and every Lake dependency are pinned.
The proof sources from OpenAI and the rational-logarithm extension are included;
Mathlib and its dependencies are fetched from the lockfile.

From the extracted package directory:

```sh
python3 -I scripts/check.py
python3 -I scripts/build.py
```

On Windows, use `python` in place of `python3`. The build fetches the Mathlib
cache, compiles the actual solution and two audit modules, checks all twelve
public axiom reports and the three standard endpoints, and writes
`.work/build-receipt.json` and `.work/build.log`.
Allow substantial time for the inherited proof library on the first build.
See [VERIFY.md](VERIFY.md) for precise verification scope and replay commands.
The [proof memo](ARGUMENT.md) explains the mathematical deduction, and the
[review summary](REVIEW.md) records the independent reviews and added controls.
The maintained [workflow checklist](WORKFLOW.md) records completed local and hosted verification, the retained-evidence audit,
and remaining publication steps.

## Included evidence

The unchanged solution closure passed Rust Nanoda and Lean 4.34.1, with fifteen
statement comparisons by the maintained Comparator. A separately built Lean
4.34.0 reader accepted the same export. Only `propext`, `Classical.choice`, and
`Quot.sound` occur as axioms. [Verification summary](evidence/verification-summary.json).

`Challenge.lean` contains intentional specification placeholders. It imports
only Mathlib and is never imported by the solution. The checked solution export
contains no challenge placeholders.

The source archive and a separate compressed copy of the exact checked export
are prepared locally in `release-assets/`. They have not been uploaded or
published. The export's uncompressed SHA-256 is
`5f242493d0a285caaf5db6d0fa20eda5bd773f51fbd2c843544ac3b442abe5aa`.

## Provenance and interpretation

The argument uses a degree-four field norm with two compatible embeddings
providing analytic estimates for the same determinant. Its general hypotheses
are in [Endpoint.lean](PairedAffine/Endpoint.lean); the concrete specializations
discharge them in [Concrete.lean](PairedAffine/Concrete.lean) and
[AffineExamples.lean](PairedAffine/AffineExamples.lean).

Luchin–Salikhov's 2018 Theorem 1 gives an exponent bound of 7.98101 for the first
two examples without a factor-of-two loss. Four improves that particular
benchmark. We have not established mathematical priority through an exhaustive
literature review. See [PRIOR-ART.md](PRIOR-ART.md).

Prepared by Ryan Matthew Casper with substantive AI assistance in research,
formalization, checking, review, and documentation. Automated and model review
do not constitute human peer review. OpenAI's inherited mathematical library,
Mathlib, Lean, and the independent checker projects are credited in
[PROVENANCE.md](PROVENANCE.md). License scopes are in [LICENSES.md](LICENSES.md).

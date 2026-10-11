# The irrationality exponents of log(2) + √2 and √2 log(2) are at most 4

Ryan Matthew Casper · October 11, 2026

We prove irrationality and an irrationality-exponent upper bound of four for
log(2) + √2 and √2 log(2). The paper also proves the same bound for
log(3 + 2√2)/√2 + √3. All three results come from one determinant argument over
a degree-four field, using analytic estimates at two embeddings and a norm
comparison involving all four.

Read the [paper](paper.pdf), [editable LaTeX manuscript](build/main.tex),
[formalization](../../formalizations/AffineLogarithms/README.md), or
[verification record](VERIFY.md). These are upper bounds; we do not establish
that any of the three exponents equals four or claim mathematical priority.

## Reproduction

This preprint shares the [frozen proof package](../../formalizations/AffineLogarithms/)
already in this repository. It does not duplicate or modify those Lean sources.
Keep the repository layout when downloading the source.

With Python 3.11+ installed, run from this directory:

```sh
python3 scripts/check-publication.py
```

With Tectonic 0.15.0 on PATH, rebuild the PDF with:

```sh
bash scripts/build-paper.sh
```

The first typesetting run may download Tectonic's TeX resource bundle. A later
compiler or resource bundle may produce different PDF bytes. The script fixes
the source date; the recorded build identifies the exact manuscript and output.
Proof building and proof replay are separate operations described in the
[proof reproduction instructions](../../formalizations/AffineLogarithms/VERIFY.md).

The [theorem map](theorem-map.json) connects the paper to the checked declarations.
See the [license scope](LICENSES.md), [citation metadata](CITATION.cff), and
[workflow checklist](../../formalizations/AffineLogarithms/WORKFLOW.md).

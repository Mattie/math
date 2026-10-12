# The irrationality exponent of log(3/2) + sqrt(2) is at most four

[Read the paper](paper.pdf) · [Manuscript source](build/main.tex) · [Formalization](../../formalizations/AffineDenominators/) · [Verification](VERIFY.md)

For every real $\nu>4$, there is a natural $Q\ge2$ such that

$$q^{-\nu}\le\left|\log(3/2)+\sqrt2-\frac pq\right|$$

for every integer $p$ and natural $q\ge Q$. The target is irrational and its irrationality exponent is at most four. This is an upper bound, not an exact value.

The argument extends the preceding paired affine determinant construction to fixed nonintegral algebraic data. It preserves the selected matrix and pays the extra denominator cost before increasing the matrix height. The paper states the inherited geometric and analytic inputs and proves the new clearing and cost estimates.

The Lean pilot and general denominator-aware endpoint have compiled. Independent mathematical, specification, and blind manuscript reviews found no remaining mathematical or statement defect; manuscript/source correspondence was checked. Six-target statement comparison and same-byte Nanoda and stock Lean replay passed locally. The fresh hosted build remains pending; see [verification status](VERIFY.md) for evidence and the confirmed Nanoda limitation. No new best-bound or priority claim is made.

The [preceding affine paper](../The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/paper.pdf) supplies the inherited estimates. The [claim map](theorem-map.json) identifies the new declarations. Authorship and AI assistance are disclosed in the manuscript; [licenses](LICENSES.md) retain the inherited scopes.

Rebuild the PDF with Tectonic 0.17.0:

```powershell
./scripts/build-paper.ps1 -Tectonic tectonic
```

The first build may download Tectonic's TeX resources. The source also opens in the Codex LaTeX editor with a PDF preview. A successful build is separate from mathematical and reader-facing review.

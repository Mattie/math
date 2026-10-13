# The irrationality exponent of log 2 + cube root of 2 is at most six

[Read the paper](paper.pdf) · [LaTeX source](build/main.tex) · [Lean proof](../../formalizations/AffineCubic/) · [Verification](VERIFY.md)

For every real $\nu>6$, the paper proves an eventual lower bound

$$q^{-\nu}\le\left|\log2+\sqrt[3]{2}-\frac pq\right|$$

for all integer numerators and sufficiently large natural denominators. Consequently the target is irrational and has irrationality exponent at most six.

The proof extends the inherited integral affine determinant method to a cubic field with one compatible embedding. It retains one selected minor across all embeddings and pays the complete cost `3 E + 2 U + V` before increasing the matrix height. The numerical bound is not asserted to be optimal or novel.

The [theorem map](theorem-map.json) connects the statements to Lean declarations. [Hosted verification](VERIFY.md) passed exact comparison of four statements and fresh candidate checking through Nanoda and Lean. The [audited evidence archive](../../verification/isolated-affine-cubic/evidence/hosted-2026-10-13.zip) is retained in this repository. The seven-page PDF has been compiled and visually reviewed.

To rebuild the PDF with Tectonic, run `python scripts/build.py --tectonic PATH_TO_TECTONIC`. Tectonic 0.17.0 was used for the retained PDF. A compatible TeX installation can also compile `build/main.tex`. [License and attribution](LICENSES.md).

To check the publication inventory, frozen proof inputs, and retained evidence archive without running the proof, use `python -I scripts/check-publication.py` from this directory.

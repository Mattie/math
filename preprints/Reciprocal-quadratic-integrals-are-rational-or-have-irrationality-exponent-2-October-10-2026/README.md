# Reciprocal quadratic integrals are rational or have irrationality exponent 2

Ryan Matthew Casper · October 10, 2026

For a quadratic polynomial with rational coefficients and a nonzero leading coefficient, integrated over an interval of positive length with rational endpoints and no pole, the reciprocal integral is rational exactly when the discriminant vanishes. Otherwise its irrationality exponent is 2.

Read the [paper](paper.pdf), [editable manuscript](manuscript.md), or [verification record](VERIFY.md). This is a prepared local publication package; it has not been uploaded.

## Reproduction

The [Lean project](lean/lakefile.lean) contains the complete non-Mathlib source closure, with dependencies fixed by [the lockfile](lean/lake-manifest.json) and [toolchain](lean/lean-toolchain). Install that Lean version through Elan, Python 3 and Git, then run:

```sh
python3 scripts/check-package.py
bash scripts/build-lean.sh
```

The build downloads locked dependencies and their matching Mathlib cache, then compiles the vendored proof sources. It is separate from replaying the historical proof exports. Compilation needs substantial memory and time because the inherited proof contains hundreds of modules.

To rebuild the PDF, put Pandoc 3.6.4 and Tectonic 0.17.0 on PATH and run `bash scripts/build-paper.sh`. A later typesetting version may produce different PDF bytes.

The source manifest records the unchanged inherited sources from [the published quadratic-period package](https://github.com/Mattie/math/tree/a93fdbe5e5aef90a9d38d805848abb07a173bfb1/preprints/The-irrationality-exponent-of-real-and-imaginary-quadratic-periods-is-2-October-9-2026). See [license scope](LICENSES.md) and [citation metadata](CITATION.cff). The manuscript discloses the use of AI in the work.

# Flint Hills and Cookson Hills

Lean proofs of convergence of the two positive-integer series

$$\sum_{n=1}^{\infty}\frac{1}{n^3\sin^2 n},\qquad
\sum_{n=1}^{\infty}\frac{1}{n^3\cos^2 n}.$$

OpenAI's released library already formally proves Flint Hills convergence. This contribution adds the short Cookson comparison, cosine nonvanishing at positive integers, and declarations matching the FormalConjectures series statements. It is a formalization contribution, not a new informal convergence result.

The new argument uses $\sin(2n)=2\sin n\cos n$ and $\sin^2 n\le1$ to bound a Cookson term by 32 times the corresponding even-indexed Flint term. The even-index map is injective, so summability follows by comparison.

## Proof entry points

See [SmallDivisors/Main.lean](SmallDivisors/Main.lean):

- `SmallDivisors.flint_hills_series_converges`
- `SmallDivisors.cookson_hills_series_converges`
- `SmallDivisors.cookson_term_le_flint_even`

Both series use `n + 1` over natural indices. The file also proves sine and cosine are nonzero at every positive integer, so no singular term is hidden by totalized division.

## Reproduce

Clone this entire repository. The Lake project reuses the unchanged `OAI` sources already included with the [rational-logarithm preprint](../../preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/README.md), rather than vendoring another copy. Their 869 hashes are pinned in `inherited-sources.json`.

From this directory, with the pinned Lean 4.34.1 toolchain available:

```sh
python3 check.py
lake exe cache get
lake --wfail build SmallDivisors.Main
```

The dependency is Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. The inherited library is from [OpenAI/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean). See [verification scope](VERIFY.md) and the [build receipt](evidence/lean-build.log). CI checks source integrity; a full proof rebuild is a separate operation.

## Attribution

Author: Ryan Matthew Casper. OpenAI coding agents contributed substantially to preparing the Cookson formalization, reviewing its statements, and running automated checks. OpenAI supplies the pi theorem, the spacing argument, and the formal Flint Hills result; Mathlib supplies the analysis library. No new Flint proof or priority claim is made.

Source is licensed under Apache 2.0; see [LICENSE](LICENSE).

# Affine cubic hosted verification

This package checks the eventual lower bound, irrationality, irrationality
exponent at most six, and non-LiouvilleWith consequences for
`Real.log 2 + (2 : Real) ^ (1 / 3 : Real)`.

[Challenge.lean](Challenge.lean) states the mathematics independently in trusted
Mathlib definitions. [Solution.lean](Solution.lean) wraps the exact public
endpoints in [AffineCubic](../../formalizations/AffineCubic/AffineCubic/Pilot.lean).
The [source manifest](source-manifest.json) binds all inherited and new proof
sources and the specification. Frozen proof files have not been changed.

Run the preparation checks from the repository root:

```sh
python3 -m unittest discover -s verification/isolated-affine-cubic -p 'test_*.py'
python3 -I verification/isolated-affine-cubic/verify.py --check
```

For authorized hosted execution, dispatch **Isolated irrationality verification**
on the intended immutable commit's branch with `case=affine-cubic`. Its selected
route builds fresh candidate source under the tested isolation boundary and
requires acceptance by Comparator, Lean's default kernel, and Nanoda.
[CHECKERS.md](CHECKERS.md) describes dependency trust, selected versions, controls,
resource limits, and the distinction from historical local replay.

The job retains an evidence archive for 90 days, including failure diagnostics.
A dated result record will identify the exact workflow commit, run and attempt,
archive identity, evidence audit, and outcome. Preparation alone is not a passed
hosted check. The standalone [template](hosted-workflow.yml) is retained for
comparison; the registered [dispatcher](../../.github/workflows/isolated-irrationality.yml)
is the workflow used for this run.

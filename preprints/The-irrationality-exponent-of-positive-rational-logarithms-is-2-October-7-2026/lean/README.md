# Logarithms of positive rationals: Lean formalization

The completed theorem is `OAI.Logarithm.rational_log_irrationalityExponent_eq_two` in `Logarithm/Main.lean`:

```lean
theorem rational_log_irrationalityExponent_eq_two
    (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1) :
    PiExponent.irrationalityExponent (Real.log (a : ℝ)) = 2
```

The same file proves the individual cases `Real.log 2` and `Real.log 3`. Its `rational_log_explicit_bound` states the uniform Diophantine inequality directly: for every real ν > 2 there is an integer Q ≥ 2 such that, for all integers p and q with q ≥ Q,

`q ^ (-ν) ≤ |Real.log (a : ℝ) - p / q|`.

These statements concern individual real logarithms, not their quotient. Positivity of the rational base and exclusion of 1 are the only assumptions on the base. The endpoint does not assume irrationality, interpolation, ampleness, an analytic bound, or a Diophantine conclusion.

## Proof contents

The new geometric theorem `eventually_weighted_logarithmic_interpolation` in `Logarithm/Interpolation.lean` proves eventual interpolation with its polynomial weighted degree bound at arbitrary distinct nonzero complex Y centers. It uses the numerical hypotheses explicitly recorded in `GeometryData`. Transverse centers need not be injective. The curve theorem uses the released comparison constant and only the ambient volume inequality; no sharper unproved comparison constant is substituted.

The actual logarithm argument uses Y centers `(a : ℂ)^j` and transverse centers `j*p_i/q_i`. The scaled matrix includes `(a : ℂ)^(j*h)`. Its arithmetic estimate includes the additional denominator cost `K*log(a.den)/w0`. The analytic estimate uses radius `rho*K`, with `rho = 100*max(1,|log(a)|)`. Both costs are included in the proved parameter selection. Actual global matrix surjectivity, arithmetic and analytic determinant bounds, the contradiction, and the final exponent consequence are connected in the source.

The exponent definition is the supremum of positive ν for which infinitely many reduced rational approximations satisfy `0 < |x-r| < r.den^(-ν)`. The endpoint proves that this set is bounded above by 2 and contains 2; the value does not arise from an unbounded-set convention for real `sSup`. The uniform lower bound also proves the target irrational by excluding exact rational representations with arbitrarily large unreduced denominators.

## Verification and reproduction

The toolchain is Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`, with transitive pins in `lake-manifest.json`. The unchanged 869-file PiExponent development is included under `OAI/NumberTheory/PiExponent`; it is from commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. SHA-256 comparison against the original workspace copy found zero differences.

`Logarithm/AxiomAudit.lean` checks the main geometric, arithmetic, and analytic theorems. `Logarithm/EndpointAudit.lean` checks and prints the final theorem statements. All 42 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The certified source contains no `sorry`, `admit`, or new axiom declaration. A deliberately forbidden axiom is used only in a separate independent-checker negative control, outside this source tree.

With the pinned Lean toolchain available, run `bash verify.sh` from this directory. The first run fetches mathlib and its cached artifacts, then builds and audits the extension. Sources and a verification summary are retained here; reproduction does not require the original working directories.

The proof export also passed Nanoda 0.4.19 and the official Lean 4.34.0
kernel. See [VERIFICATION.md](VERIFICATION.md) for the results and limits,
and [VERIFY.md](../VERIFY.md) for commands to repeat the checks and their
negative controls. The scripts fetch the pinned checker sources and tools;
no original workstation paths or saved build logs are required.

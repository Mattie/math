# Statement-to-declaration map

Each row has both a literal eventual bound and a conventional exponent-two statement in [Solution.lean](../lean/Solution.lean). Exact hypotheses are in the [independent specification](../lean/Challenge.lean); names below are in namespace `CompareChallenge`.

| Family | Exponent declaration | Bound declaration | Frozen family source |
| --- | --- | --- | --- |
| Positive rational r; π/√r | `pi_sqrt_exponent_two` | `pi_sqrt_eventual_bound` | [PeriodicFamily.Main](../lean/PeriodicFamily/Main.lean) |
| Squarefree natural d>1; rational A,B; A²−dB²=1; α=A+B√d>0 and α≠1; log(α)/√d | `quadratic_log_exponent_two` | `quadratic_log_eventual_bound` | [Quadratic.RationalFamilies](../lean/Quadratic/RationalFamilies.lean) |
| Natural d>0; real x≠0; rational A,B; exp(i√d x)=A+B i√d, including torsion and every branch | `imaginary_quadratic_exponent_two` | `imaginary_quadratic_eventual_bound` | [Combined](../lean/Combined.lean) |

For all three, the standard formulation is `Irrational x ∧ ∀ ν : ℝ, 2 < ν → ¬ LiouvilleWith ν x`. The pinned Mathlib has no `irrationalityExponent` definition. The inherited `OAI.PiExponent.irrationalityExponent` is a custom invariant; the public endpoint uses standard predicates instead. [StandardBridge](../lean/StandardBridge.lean) derives this conventional formulation from the literal eventual bound.

The bound chooses Q≥2 after ν>2 and before p,q: `∀ p : ℤ, ∀ q : ℕ, Q ≤ q → 1 / (q : ℝ)^ν ≤ |x - p/q|`. Exact equality is not excepted and coprimality is not required. Irrationality and Dirichlet approximation supply the conventional lower exponent bound. These statements impose no claim about general algebraic multiples.

All six declarations are covered by the [fresh six-target comparison and two-kernel replay](fresh-verification.json). The [earlier broader run](historical-checking.json) is preserved separately. The scoped files and unchanged bridge/Combined retain their recorded source and provenance identities.
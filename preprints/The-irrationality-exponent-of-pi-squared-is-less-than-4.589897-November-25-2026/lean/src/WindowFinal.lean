import WindowPNT
import WindowCriterion
import WindowPi

/-!
# The irrationality exponent of π² is less than 4.589897

[Leibtag et al.](https://arxiv.org/abs/2610.27799v1) obtained an upper bound of
4.62675 for ζ(2). We divide both coefficients of their integer linear forms by
an additional common divisor coming from six translated prime intervals.
`WindowPNT.translatedProduct_rate` bounds its growth, and
`WindowCriterion.zeta2_bound` uses that saving to improve the exponent for ζ(2).
The identity π² = 6ζ(2) transfers the bound to π².

`rational_upper_bound` gives the exact fraction. Its strict comparison with
4.589897 yields `irrationality_measure_pi_sq` and the finiteness statement
`finite_good_ratios`, which applies to all reduced rational approximations.
-/

namespace PrimeNumerator.WindowFinal

open Zeta2Blueprint

noncomputable abbrev bound : ℝ := 821200073639400000000 / 178914706731744129841

theorem bound_lt : bound < (4.589897 : ℝ) := by norm_num [bound]

/-- Every exponent above `bound` admits only finitely many exceptionally close
reduced rational approximations to π². -/
theorem pi_sq_bound : IrrMeasureLE (Real.pi ^ 2) bound :=
  WindowPi.pi_sq_bound (by norm_num [bound])
    (WindowCriterion.zeta2_bound WindowPNT.translatedProduct_rate)

/-- The infimum defining μ(π²) is at most the exact rational bound. -/
theorem rational_upper_bound :
    irrationalityMeasure (Real.pi ^ 2) ≤ (bound : EReal) :=
  iInf_le_of_le bound (iInf_le_of_le pi_sq_bound le_rfl)

/-- The irrationality measure of π² is strictly smaller than 4.589897. -/
theorem irrationality_measure_pi_sq :
    irrationalityMeasure (Real.pi ^ 2) < ((4.589897 : ℝ) : EReal) :=
  WindowPi.measure_lt pi_sq_bound bound_lt

/-- Only finitely many reduced rationals beat the displayed power of their
positive denominator. There are no restrictions on which denominators occur. -/
theorem finite_good_ratios :
    {q : ℚ | |Real.pi ^ 2 - (q : ℝ)| < (q.den : ℝ) ^ (-(4.589897 : ℝ))}.Finite :=
  WindowPi.finite_lt pi_sq_bound bound_lt

#print axioms irrationality_measure_pi_sq
#print axioms rational_upper_bound
#print axioms finite_good_ratios

end PrimeNumerator.WindowFinal

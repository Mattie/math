import PeriodicFamily.Main
import PeriodicGeometry.Nonvacuity

noncomputable section

set_option pp.universes true
set_option pp.explicit true

#print OAI.PeriodicFamily.rational_scaled_pi_explicit_bound
#print OAI.PeriodicFamily.rational_scaled_pi_integer_explicit_bound
#print OAI.PeriodicFamily.rational_scaled_pi_irrationalityExponent_eq_two
#print OAI.PeriodicFamily.nat_scaled_pi_irrationalityExponent_eq_two
#print OAI.PeriodicFamily.PeriodData
#print OAI.PeriodicFamily.Integral
#print OAI.PeriodicFamily.slopeBound
#print OAI.PeriodicFamily.slopeCost

#print axioms OAI.PeriodicFamily.Integral.intCast_real_norm
#print axioms OAI.PeriodicFamily.Arithmetic.quadratic_norm_one_le
#print axioms OAI.PeriodicFamily.ScaledArithmetic.entry_truncatedLog_cleared_quadratic
#print axioms OAI.PeriodicFamily.ScaledApproximationErrors.actual_error_exp
#print axioms OAI.PeriodicFamily.GlobalMatrixInterpolation.cofinal_actualMatrix
#print axioms OAI.PeriodicFamily.DeterminantContradiction.period_eventualLowerBound
#print axioms OAI.PeriodicFamily.rationalRadicand_sqrt
#print axioms OAI.PeriodicFamily.exp_rationalAngle
#print axioms OAI.PeriodicFamily.rational_scaled_pi_explicit_bound
#print axioms OAI.PeriodicFamily.rational_scaled_pi_irrationalityExponent_eq_two

example (r : ℚ) (hr : 0 < r) (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt (r : ℝ) - (p : ℝ) / q| :=
  OAI.PeriodicFamily.rational_scaled_pi_explicit_bound r hr nu hnu

example (r : ℚ) (hr : 0 < r) (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt (r : ℝ) - (p : ℝ) / (q : ℝ)| :=
  OAI.PeriodicFamily.rational_scaled_pi_integer_explicit_bound r hr nu hnu

example (r : ℚ) (hr : 0 < r) :
    OAI.PiExponent.irrationalityExponent (Real.pi / Real.sqrt (r : ℝ)) = 2 :=
  OAI.PeriodicFamily.rational_scaled_pi_irrationalityExponent_eq_two r hr

example : OAI.PeriodicFamily.PeriodData 5 :=
  OAI.PeriodicFamily.natPeriod 5 (by norm_num)

example : OAI.PeriodicFamily.PeriodData
    (OAI.PeriodicFamily.rationalRadicand (3 / 7 : ℚ)) :=
  OAI.PeriodicFamily.rationalPeriod (3 / 7 : ℚ) (by norm_num)

example : OAI.PeriodicFamily.PeriodData
    (OAI.PeriodicFamily.rationalRadicand (97 / 5 : ℚ)) :=
  OAI.PeriodicFamily.rationalPeriod (97 / 5 : ℚ) (by norm_num)

example : OAI.PiExponent.PeriodicGeometryData :=
  OAI.PiExponent.PeriodicNonvacuity.sample

end

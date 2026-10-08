import Arctangent.DeterminantData

namespace OAI.Arctangent

theorem exists_period_parameters (base : PeriodData)
    (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |base.angle - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (Logarithm.AdmissibleParameters base.angle nu Lambda c
      base.radius (Real.log base.den)) :=
  Logarithm.exists_admissible_parameters base.angle nu Lambda c base.radius
    (Real.log base.den) hnu hLambda hc base.angle_ne_zero
    base.radius_large base.radius_covers_target (Real.log_natCast_nonneg _) hbad

end OAI.Arctangent

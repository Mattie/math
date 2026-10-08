import Logarithm.ApproximationGeometry

namespace OAI.Logarithm

noncomputable def logRadius (a : ℚ) : ℝ := 100 * max 1 |Real.log (a : ℝ)|
noncomputable def logDenominator (a : ℚ) : ℝ := Real.log (a.den : ℝ)

theorem real_log_rat_ne_zero (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Real.log (a : ℝ) ≠ 0 := by
  intro h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haR1 : (a : ℝ) ≠ 1 := by exact_mod_cast ha1
  have he := Real.exp_log haR
  rw [h, Real.exp_zero] at he
  exact haR1 he.symm

theorem logRadius_large (a : ℚ) : 100 ≤ logRadius a := by
  unfold logRadius
  nlinarith [le_max_left (1 : ℝ) |Real.log (a : ℝ)|]

theorem logRadius_covers_target (a : ℚ) : 100 * |Real.log (a : ℝ)| ≤ logRadius a := by
  unfold logRadius
  nlinarith [le_max_right (1 : ℝ) |Real.log (a : ℝ)|]

theorem logDenominator_nonneg (a : ℚ) : 0 ≤ logDenominator a := by
  apply Real.log_nonneg
  exact_mod_cast a.pos

/-- The actual logarithm, radius, denominator cost, and approximation sequence
instantiate the generic parameter construction for every positive rational base. -/
theorem exists_logarithm_parameters
    (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1)
    (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.log (a : ℝ) - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (AdmissibleParameters (Real.log (a : ℝ)) nu Lambda c
      (logRadius a) (logDenominator a)) :=
  exists_admissible_parameters (Real.log (a : ℝ)) nu Lambda c (logRadius a)
    (logDenominator a) hnu hLambda hc (real_log_rat_ne_zero a ha ha1)
    (logRadius_large a) (logRadius_covers_target a) (logDenominator_nonneg a) hbad

end OAI.Logarithm

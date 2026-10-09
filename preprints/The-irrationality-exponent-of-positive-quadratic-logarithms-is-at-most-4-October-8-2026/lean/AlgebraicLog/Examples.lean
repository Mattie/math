import AlgebraicLog.Main

namespace OAI.AlgebraicLog.Examples
open Polynomial

noncomputable def sample (t : ℚ) : ℝ := (1 + (t : ℝ) * Real.sqrt 2) / 2

theorem sample_irrational (t : ℚ) (ht : t ≠ 0) : Irrational (sample t) := by
  have hm := irrational_sqrt_two.ratCast_mul ht
  have ha := hm.ratCast_add (1 : ℚ)
  have hd := ha.div_ratCast (by norm_num : (2 : ℚ) ≠ 0)
  simpa only [Rat.cast_one, Rat.cast_ofNat, sample] using hd

theorem sample_algebraic_degree (t : ℚ) (ht : t ≠ 0) :
    IsAlgebraic ℚ (sample t) ∧ (minpoly ℚ (sample t)).natDegree = 2 := by
  let p : Polynomial ℚ := X ^ 2 - (X + C ((2 * t ^ 2 - 1) / 4))
  have hm : p.Monic := by
    apply monic_X_pow_sub
    rw [degree_X_add_C]
    norm_num
  have he : p.aeval (sample t) = 0 := by
    simp only [p, map_sub, map_pow, map_add, aeval_X, aeval_C, eq_ratCast]
    dsimp [sample]
    push_cast
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hst := congrArg (fun x : ℝ => (t : ℝ) ^ 2 * x) hs
    nlinarith
  have hi : IsIntegral ℚ (sample t) := ⟨p, hm, he⟩
  have hdeg : p.degree = 2 := by
    dsimp [p]
    rw [degree_sub_eq_left_of_degree_lt]
    · simp
    · rw [degree_X_add_C]
      norm_num
  have hupper : (minpoly ℚ (sample t)).natDegree ≤ 2 := by
    apply natDegree_le_of_degree_le
    exact (minpoly.min ℚ (sample t) hm he).trans hdeg.le
  have hlower : 2 ≤ (minpoly ℚ (sample t)).natDegree := by
    apply (minpoly.two_le_natDegree_iff hi).mpr
    rintro ⟨q, hq⟩
    exact (sample_irrational t ht).ne_rat q hq.symm
  exact ⟨hi.isAlgebraic, Nat.le_antisymm hupper hlower⟩

theorem first_sample_positive : 0 < (1 + Real.sqrt 2) / 2 := by positivity

theorem second_sample_positive : 0 < (1 + 3 * Real.sqrt 2) / 2 := by positivity

theorem first_sample_degree :
    IsAlgebraic ℚ ((1 + Real.sqrt 2) / 2) ∧
      (minpoly ℚ ((1 + Real.sqrt 2) / 2)).natDegree = 2 := by
  simpa [sample] using sample_algebraic_degree 1 (by norm_num)

theorem second_sample_degree :
    IsAlgebraic ℚ ((1 + 3 * Real.sqrt 2) / 2) ∧
      (minpoly ℚ ((1 + 3 * Real.sqrt 2) / 2)).natDegree = 2 := by
  simpa [sample] using sample_algebraic_degree 3 (by norm_num)

/-- Nonintegral base with negative conjugate of modulus below one. -/
theorem first_sample_bound :
    PiExponent.irrationalityExponent (Real.log ((1 + Real.sqrt 2) / 2)) ≤ 4 := by
  apply quadratic_log_irrationalityExponent_le_four _ first_sample_positive _
    first_sample_degree.1 first_sample_degree.2
  have hi : Irrational ((1 + Real.sqrt 2) / 2) := by
    simpa [sample] using sample_irrational 1 (by norm_num)
  simpa using hi.ne_rat 1

/-- Nonintegral base with negative conjugate of modulus above one; the
nonzero conjugate-growth cost is handled by the same theorem. -/
theorem second_sample_bound :
    PiExponent.irrationalityExponent (Real.log ((1 + 3 * Real.sqrt 2) / 2)) ≤ 4 := by
  apply quadratic_log_irrationalityExponent_le_four _ second_sample_positive _
    second_sample_degree.1 second_sample_degree.2
  have hi : Irrational ((1 + 3 * Real.sqrt 2) / 2) := by
    simpa [sample] using sample_irrational 3 (by norm_num)
  simpa using hi.ne_rat 1

theorem first_sample_conjugate_check :
    -1 < (1 - Real.sqrt 2) / 2 ∧ (1 - Real.sqrt 2) / 2 < 0 ∧
      ((1 + Real.sqrt 2) / 2) * ((1 - Real.sqrt 2) / 2) = -(1 / 4 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem second_sample_conjugate_check :
    (1 - 3 * Real.sqrt 2) / 2 < -1 ∧
      ((1 + 3 * Real.sqrt 2) / 2) * ((1 - 3 * Real.sqrt 2) / 2) = -(17 / 4 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

end OAI.AlgebraicLog.Examples

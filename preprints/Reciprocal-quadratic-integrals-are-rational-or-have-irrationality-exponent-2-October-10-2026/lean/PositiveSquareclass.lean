import Mathlib

namespace PositiveIntegrals

/-- A positive rational square root is a positive rational multiple of a
square root of a positive squarefree natural number. -/
theorem positive_rat_squareclass (r : ℚ) (hr : 0 < r) :
    ∃ c : ℚ, ∃ d : ℕ, 0 < c ∧ Squarefree d ∧ 0 < d ∧
      Real.sqrt (r : ℝ) = (c : ℝ) * Real.sqrt (d : ℝ) := by
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have habs : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg hn.le
  have hnabs : 0 < r.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  obtain ⟨d, e, hd, he, hde, hsf⟩ :=
    Nat.sq_mul_squarefree_of_pos (Nat.mul_pos hnabs r.pos)
  refine ⟨(e : ℚ) / r.den, d, by positivity, hsf, hd, ?_⟩
  have hrat : (r.num.natAbs : ℚ) / r.den = r := by
    rw [show (r.num.natAbs : ℚ) = (r.num : ℚ) by rw [← Int.cast_natCast, habs]]
    exact r.num_div_den
  have hreal : (r.num.natAbs : ℝ) / r.den = (r : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) hrat
  have heq : (e : ℝ) ^ 2 * d = (r.num.natAbs : ℝ) * r.den := by exact_mod_cast hde
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hsquare : ((e : ℝ) / r.den * Real.sqrt (d : ℝ)) ^ 2 = (r : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), div_pow, ← hreal]
    field_simp
    nlinarith [heq]
  push_cast
  have hnonneg : 0 ≤ (e : ℝ) / r.den * Real.sqrt (d : ℝ) := by positivity
  nlinarith [Real.sq_sqrt (show 0 ≤ (r : ℝ) by exact_mod_cast hr.le),
    Real.sqrt_nonneg (r : ℝ)]

end PositiveIntegrals

#print axioms PositiveIntegrals.positive_rat_squareclass
#check PositiveIntegrals.positive_rat_squareclass

import OAI.NumberTheory.PiExponent.Approximation.Exponent

namespace OAI.LogarithmExtension

open PiExponent

/-- The unreduced-denominator lower bound excludes every exact rational value. -/
theorem irrational_of_eventualLowerBound {x : ℝ}
    (h : EventualLowerBound x) : Irrational x := by
  rintro ⟨r, hr⟩
  obtain ⟨Q, hQ, hb⟩ := h 3 (by norm_num)
  have hQpos : 0 < Q := by omega
  have hden : 1 ≤ r.den := r.pos
  have hq : Q ≤ Q * r.den := by nlinarith
  have hqpos : 0 < Q * r.den := Nat.mul_pos hQpos r.pos
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQpos
  have hdR : (r.den : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt r.pos
  have heq : (((Q : ℤ) * r.num : ℤ) : ℝ) / ((Q * r.den : ℕ) : ℝ) = (r : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    field_simp [hQR, hdR]
  have hlower := hb ((Q : ℤ) * r.num) (Q * r.den) hq
  rw [heq, hr, sub_self, abs_zero] at hlower
  exact (not_lt_of_ge hlower)
    (Real.rpow_pos_of_pos (by exact_mod_cast hqpos) (-3))

/-- This generic consequence introduces no separate irrationality hypothesis. -/
theorem exponent_eq_two_of_eventualLowerBound {x : ℝ}
    (h : EventualLowerBound x) : irrationalityExponent x = 2 :=
  irrationalityExponent_eq_two_of_eventualLowerBound
    (irrational_of_eventualLowerBound h) h

end OAI.LogarithmExtension

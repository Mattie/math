import Quadratic.PeriodData

namespace OAI.Quadratic
noncomputable section

def realContext (d : ℕ) (hn : ∀ n : ℤ, n * n ≠ (d : ℤ)) : Context where
  radicand := d
  generator := (Real.sqrt d : ℂ)
  generator_sq := by exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d)
  no_int_square := hn
  bound := max 1 (Real.sqrt d)
  one_le_bound := le_max_left _ _
  norm_generator_le := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d)] using
      le_max_right (1 : ℝ) (Real.sqrt d)

def imaginaryContext (d : ℕ) (hd : 0 < d) : Context where
  radicand := -(d : ℤ)
  generator := Complex.I * (Real.sqrt d : ℂ)
  generator_sq := by
    have hs : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d)
    calc
      _ = (Complex.I * Complex.I) * ((Real.sqrt d : ℂ) * (Real.sqrt d : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I, hs]; push_cast; ring
  no_int_square := by
    intro n hn
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg n]
  bound := max 1 (Real.sqrt d)
  one_le_bound := le_max_left _ _
  norm_generator_le := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg d)] using
      le_max_right (1 : ℝ) (Real.sqrt d)

end
end OAI.Quadratic

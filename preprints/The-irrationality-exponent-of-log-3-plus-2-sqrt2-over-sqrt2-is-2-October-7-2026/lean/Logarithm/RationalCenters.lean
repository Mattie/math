import Mathlib

namespace OAI.Logarithm

/-- The centers used for a positive rational logarithm satisfy the new geometric
hypotheses, including rational bases strictly between zero and one. -/
theorem rational_power_centers_nonzero (a : ℚ) (ha : 0 < a) (K : ℕ) :
    ∀ j : Fin K, (a : ℂ) ^ j.val ≠ 0 := by
  intro j
  apply pow_ne_zero
  exact_mod_cast ha.ne'

theorem rational_power_centers_injective (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1)
    (K : ℕ) : Function.Injective (fun j : Fin K => (a : ℂ) ^ j.val) := by
  intro j k h
  dsimp only at h
  have hq : a ^ j.val = a ^ k.val := by exact_mod_cast h
  exact Fin.ext (pow_right_injective₀ ha ha1 hq)

theorem exp_log_rational_center (a : ℚ) (ha : 0 < a) (j : ℕ) :
    Complex.exp ((j : ℂ) * (Real.log (a : ℝ) : ℂ)) = (a : ℂ) ^ j := by
  rw [Complex.exp_nat_mul]
  congr 1
  rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast ha)]
  norm_cast

end OAI.Logarithm

import Quadratic.ScaledArithmetic
import Logarithm.ScaledApproximationErrors

namespace OAI.Quadratic.ScaledApproximationErrors
variable {f : Context}
open PiExponent

theorem actual_error_exp {m : ℕ} (base : (PeriodData f)) (xi : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |xi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (ScaledArithmetic.realCenters base.slope p q i - base.slope * (xi : ℂ))‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu + Real.log f.bound) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have he : (j : ℂ) * (ScaledArithmetic.realCenters base.slope p q i - base.slope * (xi : ℂ)) =
      base.slope * ((j : ℂ) * (Logarithm.ScaledArithmetic.rationalCenters p q i - (xi : ℂ))) := by
    unfold ScaledArithmetic.realCenters Logarithm.ScaledArithmetic.rationalCenters
    ring
  rw [he, norm_mul]
  have hr : ‖base.slope‖ ≤ f.bound := by
    rw [PeriodData.slope, norm_rotation]
    exact f.norm_generator_le
  have ha := Logarithm.ScaledApproximationErrors.actual_error_exp xi p q j K nu hK hj hnu hq happrox i
  calc
    _ ≤ f.bound * Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) :=
      mul_le_mul hr ha (norm_nonneg _) f.bound_pos.le
    _ = _ := by
      rw [show (Real.log (2 * (K : ℝ)) + nu + Real.log f.bound) - nu * (⌈Real.log (q i)⌉₊ : ℝ) =
        Real.log f.bound + ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) by ring,
        Real.exp_add, Real.exp_log f.bound_pos]

end OAI.Quadratic.ScaledApproximationErrors

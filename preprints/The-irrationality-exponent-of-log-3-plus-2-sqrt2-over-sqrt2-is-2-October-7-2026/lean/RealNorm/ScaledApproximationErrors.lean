import RealNorm.ScaledArithmetic
import Logarithm.ScaledApproximationErrors

namespace OAI.RealNorm.ScaledApproximationErrors
open PiExponent

theorem actual_error_exp {m : ℕ} (base : PeriodData) (xi : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |xi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (ScaledArithmetic.realCenters base.slope p q i - base.slope * (xi : ℂ))‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu + Real.log 2) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have he : (j : ℂ) * (ScaledArithmetic.realCenters base.slope p q i - base.slope * (xi : ℂ)) =
      base.slope * ((j : ℂ) * (Logarithm.ScaledArithmetic.rationalCenters p q i - (xi : ℂ))) := by
    unfold ScaledArithmetic.realCenters Logarithm.ScaledArithmetic.rationalCenters
    ring
  rw [he, norm_mul]
  have hr : ‖base.slope‖ ≤ 2 := by
    rw [PeriodData.slope, norm_rotation]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have ha := Logarithm.ScaledApproximationErrors.actual_error_exp xi p q j K nu hK hj hnu hq happrox i
  calc
    _ ≤ 2 * Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) :=
      mul_le_mul hr ha (norm_nonneg _) (by norm_num)
    _ = _ := by
      rw [show (Real.log (2 * (K : ℝ)) + nu + Real.log 2) - nu * (⌈Real.log (q i)⌉₊ : ℝ) =
        Real.log 2 + ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end OAI.RealNorm.ScaledApproximationErrors

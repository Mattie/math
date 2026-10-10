import QuadraticImag5.ScaledArithmetic
import Logarithm.ScaledApproximationErrors

namespace OAI.QuadraticImag5.ScaledApproximationErrors
open PiExponent

theorem actual_error_exp {m : ℕ} (xi : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |xi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (ScaledArithmetic.imaginaryCenters p q i - rotation * (xi : ℂ))‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu + Real.log 3) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have he : (j : ℂ) * (ScaledArithmetic.imaginaryCenters p q i - rotation * (xi : ℂ)) =
      rotation * ((j : ℂ) * (Logarithm.ScaledArithmetic.rationalCenters p q i - (xi : ℂ))) := by
    unfold ScaledArithmetic.imaginaryCenters Logarithm.ScaledArithmetic.rationalCenters
    ring
  rw [he, norm_mul]
  have hr : ‖rotation‖ ≤ 3 := by
    simp only [rotation, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 5)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have ha := Logarithm.ScaledApproximationErrors.actual_error_exp xi p q j K nu hK hj hnu hq happrox i
  calc
    _ ≤ 3 * Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) :=
      mul_le_mul hr ha (norm_nonneg _) (by norm_num)
    _ = _ := by
      rw [show (Real.log (2 * (K : ℝ)) + nu + Real.log 3) - nu * (⌈Real.log (q i)⌉₊ : ℝ) =
        Real.log 3 + ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

end OAI.QuadraticImag5.ScaledApproximationErrors

import Arctangent.ScaledArithmetic
import Logarithm.ScaledApproximationErrors

namespace OAI.Arctangent.ScaledApproximationErrors
open PiExponent

theorem actual_error_exp {m : ℕ} (xi : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |xi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (ScaledArithmetic.imaginaryCenters p q i - Complex.I * (xi : ℂ))‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have he : (j : ℂ) * (ScaledArithmetic.imaginaryCenters p q i - Complex.I * (xi : ℂ)) =
      Complex.I * ((j : ℂ) * (Logarithm.ScaledArithmetic.rationalCenters p q i - (xi : ℂ))) := by
    unfold ScaledArithmetic.imaginaryCenters Logarithm.ScaledArithmetic.rationalCenters
    ring
  rw [he, norm_mul, Complex.norm_I, one_mul]
  exact Logarithm.ScaledApproximationErrors.actual_error_exp xi p q j K nu hK hj hnu hq happrox i

end OAI.Arctangent.ScaledApproximationErrors

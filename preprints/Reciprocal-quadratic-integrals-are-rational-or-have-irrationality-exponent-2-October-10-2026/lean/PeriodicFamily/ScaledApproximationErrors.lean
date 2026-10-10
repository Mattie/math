import PeriodicFamily.ScaledArithmetic
import Logarithm.ScaledApproximationErrors

namespace OAI.PeriodicFamily.ScaledApproximationErrors
variable {rad : ℕ} [Fact (0 < rad)]
open PiExponent

theorem actual_error_exp {m : ℕ} (xi : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |xi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (ScaledArithmetic.imaginaryCenters (rad := rad) p q i - rotation rad * (xi : ℂ))‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu + slopeCost rad) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have he : (j : ℂ) * (ScaledArithmetic.imaginaryCenters (rad := rad) p q i - rotation rad * (xi : ℂ)) =
      rotation rad * ((j : ℂ) * (Logarithm.ScaledArithmetic.rationalCenters p q i - (xi : ℂ))) := by
    unfold ScaledArithmetic.imaginaryCenters Logarithm.ScaledArithmetic.rationalCenters
    ring
  rw [he, norm_mul]
  have ha := Logarithm.ScaledApproximationErrors.actual_error_exp xi p q j K nu hK hj hnu hq happrox i
  calc
    _ ≤ slopeBound rad * Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) :=
      mul_le_mul (norm_rotation_le rad) ha (norm_nonneg _) (slopeBound_pos rad).le
    _ = _ := by
      rw [show (Real.log (2 * (K : ℝ)) + nu + slopeCost rad) - nu * (⌈Real.log (q i)⌉₊ : ℝ) =
        slopeCost rad + ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) by ring,
        Real.exp_add, slopeCost, Real.exp_log (slopeBound_pos rad)]

end OAI.PeriodicFamily.ScaledApproximationErrors

import Logarithm.ScaledArithmetic
import OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters

namespace OAI
noncomputable section
namespace Logarithm.ScaledApproximationErrors
open PiExponent

theorem actual_error_exp {m : ℕ} (xi : ℝ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (nu : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hnu : 0 ≤ nu)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |xi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ i, ‖(j : ℂ) * (ScaledArithmetic.rationalCenters p q i - (xi : ℂ))‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + nu) - nu * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have he : ScaledArithmetic.rationalCenters p q i - (xi : ℂ) =
      (((p i : ℝ) / q i - xi : ℝ) : ℂ) := by
    simp only [ScaledArithmetic.rationalCenters, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
  have hn : ‖(j : ℂ) * (ScaledArithmetic.rationalCenters p q i - (xi : ℂ))‖ =
      (j : ℝ) * |xi - (p i : ℝ) / q i| := by
    rw [he, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hjR : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hqpow : 0 ≤ (q i : ℝ) ^ (-nu) := Real.rpow_nonneg (by positivity) _
  have hle : ‖(j : ℂ) * (ScaledArithmetic.rationalCenters p q i - (xi : ℂ))‖ ≤
      2 * K * (q i : ℝ) ^ (-nu) := by
    rw [hn]
    nlinarith [happrox i, abs_nonneg (xi - (p i : ℝ) / q i)]
  calc
    _ ≤ 2 * K * (q i : ℝ) ^ (-nu) := hle
    _ ≤ 2 * K * (Real.exp nu * Real.exp (-nu * (⌈Real.log (q i)⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log nu hnu (hq i)) (by positivity)
    _ = _ := by
      have hKpos : (0 : ℝ) < 2 * K := by exact_mod_cast (by omega : 0 < 2 * K)
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
      ring

end Logarithm.ScaledApproximationErrors
end
end OAI

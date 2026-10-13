import Logarithm.AdmissibleParameters
import Logarithm.ScaledArithmetic

namespace OAI.AlgebraicLog
open PiExponent
open scoped BigOperators

/-- Numerical and approximation inputs to the analytic argument. The geometric
shape uses `nu/2`, but the approximation exponent is `nu` throughout. No endpoint
or determinant bound is included as a field. -/
structure AnalyticData (ξ nu rho : ℝ) where
  base : Parameters (nu / 2)
  F0 : ℝ
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  p : ℕ → ℤ
  q : ℕ → ℕ
  x : ℕ → ℝ
  wstar : ℝ
  rho_large : 100 ≤ rho
  rho_covers_target : 100 * |ξ| ≤ rho
  F0_pos : 0 < F0
  K_pos : 1 ≤ K
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  x_log : ∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)
  approximations : ∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
    |ξ - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu)
  x_one_le : ∀ i, 1 ≤ x i
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i : Fin m, wstar ≤ x (i.val + 1)

namespace AnalyticData
variable {ξ nu rho : ℝ} (d : AnalyticData ξ nu rho)

noncomputable def translationError : ℝ :=
  nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
    (Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar

noncomputable def holomorphicError : ℝ :=
  rho * (d.K : ℝ) / (d.w0 : ℝ) + Real.log 2 / (d.v0 : ℝ) +
    (Real.log (200 * (d.K : ℝ)) + Real.log (rho / 100)) / d.wstar

noncomputable def analyticError : ℝ := d.translationError + d.holomorphicError
end AnalyticData

theorem exp_log_real_center (a : ℝ) (ha : 0 < a) (j : ℕ) :
    Complex.exp ((j : ℂ) * (Real.log a : ℂ)) = (a : ℂ) ^ j := by
  rw [Complex.exp_nat_mul]
  congr 1
  rw [← Complex.ofReal_exp, Real.exp_log ha]

end OAI.AlgebraicLog

import AlgebraicLog.ParameterShape
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters

namespace OAI.AlgebraicLog
open PiExponent

/-- Fixed clearing and conjugate costs can be absorbed before choosing the
successive approximation weights. The collision target is arbitrary. -/
theorem exists_dimension_budget
    {nu : ℝ} (P : Parameters (nu / 2))
    (a b u v epsilon target : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV P.theta P.B P.C m +
        (u * (dimensionK P.C m : ℝ) + v) / dimensionW P.B m < epsilon ∧
      target < P.eta ^ 2 * ((P.B : ℝ) / P.A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have hscale : 0 < 1 + u + v := by positivity
  obtain ⟨m, hm, hdim, hcollision⟩ := exists_dimension_margin
    P.theta P.A P.B P.C P.eta a b (epsilon / (1 + u + v)) target
    P.theta_pos P.B_pos P.one_lt_C P.CB_lt_one
    P.one_lt_C_theta_div_B P.one_lt_B_div_A P.eta_pos ha hb
    (div_pos hepsilon hscale)
  refine ⟨m, hm, ?_, hcollision⟩
  have hK : (1 : ℝ) ≤ dimensionK P.C m := by
    exact_mod_cast dimensionK_one_le P.C P.one_lt_C.le m
  have hW := dimensionW_pos P.B P.B_pos m
  have hV := dimensionV_pos P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hnonneg : 0 ≤ (a * (m : ℝ) + b) / dimensionV P.theta P.B P.C m :=
    div_nonneg (by positivity) hV.le
  have hquot : 0 ≤ (dimensionK P.C m : ℝ) / dimensionW P.B m :=
    div_nonneg (by positivity) hW.le
  have hvK : v ≤ v * (dimensionK P.C m : ℝ) := by nlinarith
  have hlast : (u * (dimensionK P.C m : ℝ) + v) / dimensionW P.B m ≤
      (u + v) * ((dimensionK P.C m : ℝ) / dimensionW P.B m) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hW).2
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hdim hscale
  have heq : (1 + u + v) * (epsilon / (1 + u + v)) = epsilon := by
    field_simp
  rw [heq] at hscaled
  simp only [mul_div_assoc] at hscaled
  nlinarith [mul_nonneg (show 0 ≤ u + v by positivity) hnonneg,
    mul_nonneg (show 0 ≤ u + v by positivity) hquot]

/-- The quadratic proof needs twice the arithmetic cost, one conjugate cost,
and the analytic cost. All fixed constants are chosen before the dimension. -/
theorem exists_quadratic_dimension_budget
    {nu : ℝ} (P : Parameters (nu / 2))
    (Lambda F rho delta kappa epsilon c : ℝ)
    (hLambda : 0 < Lambda) (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 < epsilon) (hc : 0 < c) :
    ∃ m : ℕ, 1 ≤ m ∧
      (2 * Lambda * F * (m : ℝ) + 3 * Real.log 2) /
          dimensionV P.theta P.B P.C m +
        ((rho + 2 * delta + kappa) * (dimensionK P.C m : ℝ) +
          Real.log (3 / 2 : ℝ)) / dimensionW P.B m < epsilon / 3 ∧
      3 < c * (P.eta ^ 2 * ((P.B : ℝ) / P.A) ^ m / (2 * ((m : ℝ) + 1))) := by
  obtain ⟨m, hm, hmargin, hcollision⟩ := exists_dimension_budget P
    (2 * Lambda * F) (3 * Real.log 2) (rho + 2 * delta + kappa)
    (Real.log (3 / 2 : ℝ)) (epsilon / 3) (3 / c)
    (by positivity) (by positivity) (by positivity)
    (Real.log_nonneg (by norm_num)) (by positivity)
  refine ⟨m, hm, hmargin, ?_⟩
  have h := (div_lt_iff₀ hc).mp hcollision
  nlinarith

end OAI.AlgebraicLog

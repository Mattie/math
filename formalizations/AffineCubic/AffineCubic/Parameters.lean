import AlgebraicLog.AdmissibleParameters

/-! Cubic arithmetic budgets with the inherited approximation and geometry data. -/

namespace OAI.AffineCubic
open PiExponent AlgebraicLog

set_option maxHeartbeats 800000 in
theorem exists_parameters
    (ξ nu Lambda c rho kappa R : ℝ) (hnu : 6 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hξ : ξ ≠ 0) (hrho : 100 ≤ rho) (hrhoξ : 100 * |ξ| ≤ rho) (hkappa : 0 ≤ kappa) (hR : 0 ≤ R)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |ξ - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ d : AdmissibleParameters ξ nu Lambda c rho 0 kappa R,
      3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) - 3 * (1 - d.base.theta) ∧
      3 + (3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError) <
        c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
          (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  classical
  obtain ⟨P₃, hgap₃⟩ := ParameterShape.exists_degree_shape nu 3 (by norm_num) (by linarith)
  have hnu0 : 0 < nu := by linarith
  have htheta1 := P₃.theta_lt_one
  have hsave : 0 < (P₃.A : ℝ) * (1 - P₃.eta) - P₃.theta := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hnu0.le h
    linarith
  let P : Parameters (nu / 2) := {
    P₃ with
    approximation_gap := by
      have h := P₃.approximation_gap
      have ht := P₃.theta_lt_A
      nlinarith
    gap_pos := by
      have h := P₃.gap_pos
      nlinarith [mul_pos hnu0 hsave]
  }
  have hgap : 0 < nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - 3 * (1 - P.theta) := hgap₃
  let g : ℝ := nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - 3 * (1 - P.theta)
  have hg : 0 < g := hgap
  let epsilon : ℝ := min (g / 2) (1 / 2)
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hepsg : epsilon < g := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepshalf : epsilon ≤ 1 / 2 := min_le_right _ _
  have heps3 : 0 < epsilon / 3 := by positivity
  obtain ⟨F0, hF0, hFtheta, hFmargin⟩ :=
    exists_initial_scale nu P.theta epsilon P.theta_pos hepsilon
  obtain ⟨m, hm, hdim, hcollisionRaw⟩ := exists_dimension_budget
    P (3 * Lambda * F0) (4 * Real.log 2) (rho + 2 * kappa)
    (2 * Real.log (3 / 2 : ℝ)) (epsilon / 3) (4 / c)
    (by positivity) (by positivity) (by linarith)
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) heps3
  have hcollision : 4 < c *
      (P.eta ^ 2 * ((P.B : ℝ) / P.A) ^ m / (2 * ((m : ℝ) + 1))) := by
    have := (div_lt_iff₀ hc).mp hcollisionRaw
    nlinarith
  let K : ℕ := dimensionK P.C m
  let w0 : ℚ := (P.B ^ m)⁻¹
  let v0 : ℚ := 2 * (K : ℚ) * P.theta ^ m * w0
  have hK : 1 ≤ K := dimensionK_one_le P.C P.one_lt_C.le m
  have hw0eq : (w0 : ℝ) = dimensionW P.B m := by simp [w0, dimensionW]
  have hv0eq : (v0 : ℝ) = dimensionV P.theta P.B P.C m := by
    simp [v0, dimensionV, K, hw0eq]
  have hw0 : 0 < (w0 : ℝ) := by
    rw [hw0eq]
    exact dimensionW_pos P.B P.B_pos m
  have hv0 : 0 < (v0 : ℝ) := by
    rw [hv0eq]
    exact dimensionV_pos P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume : (K : ℝ) * ((w0 : ℝ) / v0) * (P.theta : ℝ) ^ m = 1 / 2 := by
    rw [hw0eq, hv0eq]
    exact dimension_volume P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume1 : (K : ℝ) * (P.theta : ℝ) ^ m < 1 :=
    dimension_volume_lt_one P.theta P.C P.theta_pos P.C_pos.le P.C_theta_lt_one m hm
  have hcollision' : 4 < c *
      (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (P.A : ℝ) ^ m)) := by
    rw [hv0eq]
    change 4 < c * (P.eta ^ 2 * (dimensionK (P.C : ℝ) m : ℝ) *
      (P.theta : ℝ) ^ m / (((m : ℝ) + 1) *
        dimensionV (P.theta : ℝ) P.B P.C m * (P.A : ℝ) ^ m))
    rw [dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    exact hcollision
  obtain ⟨sigma, hsigma, hsigmaVol, hsigmaK, hsigmaTheta⟩ :=
    exists_small_rational_sigma m (1 / 2)
      ((K : ℝ) * (P.theta : ℝ) ^ m) P.theta (by norm_num) hvolume1 P.theta_lt_one
  have hnupos : 0 < nu := by linarith
  have hrho100 : 1 ≤ rho / 100 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).mpr (by linarith)
  have hKr : (0 : ℝ) ≤ K := by positivity
  have hconj : 0 ≤ Real.log (2 * ((K : ℝ) * R + 2)) :=
    Real.log_nonneg (by nlinarith [mul_nonneg hKr hR])
  have hS : 0 ≤ weightErrorCoefficient nu P.theta K + 2 * P.theta +
      Real.log (rho / 100) + 2 * Real.log (2 * ((K : ℝ) * R + 2)) := by
    have hbase := weightErrorCoefficient_nonneg nu P.theta K hnupos P.theta_pos hK
    have hr := Real.log_nonneg hrho100
    have ht := P.theta_pos
    linarith
  obtain ⟨X, hX, hXmargin⟩ := exists_uniform_weight_error_margin m (3 * Lambda)
    (weightErrorCoefficient nu P.theta K + 2 * P.theta + Real.log (rho / 100) +
      2 * Real.log (2 * ((K : ℝ) * R + 2))) (epsilon / 3) (by positivity) hS heps3
  obtain ⟨p, q, x, hx0, hxlog, happ, hx1, hgrowth⟩ :=
    OAI.Logarithm.exists_normalized_successive_approximations ξ nu X
      (PiExponentApprox.weightSeparationFactor m
        (interpolationSeparationConstant m sigma) w0 v0 P.theta) hnupos hξ hbad
  obtain ⟨wstar, hwstarX, hwstarLower, hwstarAttained⟩ :=
    exists_minimum_weight m hm (fun i : Fin m => x (i.val + 1)) X
      (fun i => (happ i.val).2.2.2.2)
  have hwstar : 0 < wstar := lt_of_lt_of_le zero_lt_one (le_trans hX hwstarX.le)
  have hweight := hXmargin wstar (fun i : Fin m => x (i.val + 1))
    hwstarX hwstarLower
  have hdim' :
      (3 * Lambda * F0 * (m : ℝ) + 4 * Real.log 2) / (v0 : ℝ) +
        ((rho + 2 * kappa) * (K : ℝ) + 2 * Real.log (3 / 2 : ℝ)) / (w0 : ℝ) < epsilon / 3 := by
    rw [hv0eq, hw0eq]
    exact hdim
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog32 : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hsum : 0 ≤ ∑ i : Fin m, 1 / x (i.val + 1) :=
    Finset.sum_nonneg (fun i _ => div_nonneg (by norm_num) (by linarith [hx1 (i.val + 1)]))
  let d : AdmissibleParameters ξ nu Lambda c rho 0 kappa R := {
    base := P
    epsilon := epsilon
    F0 := F0
    m := m
    K := K
    w0 := w0
    v0 := v0
    sigma := sigma
    p := p
    q := q
    x := x
    wstar := wstar
    rho_large := hrho
    rho_covers_target := hrhoξ
    delta_nonneg := le_refl 0
    kappa_nonneg := hkappa
    R_nonneg := hR
    epsilon_pos := hepsilon
    epsilon_lt_gap := by
      have ht := P.theta_lt_one
      dsimp [g] at hepsg
      linarith only [ht, hepsg]
    epsilon_le_half := hepshalf
    F0_pos := hF0
    F0_large := hFtheta
    initial_margin := hFmargin
    m_pos := hm
    K_eq := rfl
    K_pos := hK
    w0_eq := hw0eq
    v0_eq := hv0eq
    w0_pos := hw0
    v0_pos := hv0
    volume_eq := hvolume
    volume_lt_one := hvolume1
    dimension_margin := by
      have hfirst :
          (2 * Lambda * F0 * (m : ℝ) + 3 * Real.log 2) / (v0 : ℝ) ≤
          (3 * Lambda * F0 * (m : ℝ) + 4 * Real.log 2) / (v0 : ℝ) := by
        apply div_le_div_of_nonneg_right _ hv0.le
        nlinarith only [hlog2, mul_nonneg (mul_nonneg hLambda.le hF0.le) (show (0 : ℝ) ≤ m by positivity)]
      have hsecond :
          ((rho + 2 * 0 + kappa) * (K : ℝ) + Real.log (3 / 2 : ℝ)) / (w0 : ℝ) ≤
          ((rho + 2 * kappa) * (K : ℝ) + 2 * Real.log (3 / 2 : ℝ)) / (w0 : ℝ) := by
        apply div_le_div_of_nonneg_right _ hw0.le
        nlinarith only [hlog32, mul_nonneg hkappa hKr]
      linarith only [hfirst, hsecond, hdim']
    collision_margin := by linarith only [hcollision']
    sigma_pos := hsigma
    sigma_volume := by
      rw [hvolume]
      exact hsigmaVol
    sigma_centers := hsigmaK
    sigma_theta := hsigmaTheta
    x_zero := hx0
    x_log := hxlog
    approximations := fun n => ⟨(happ n).1, (happ n).2.1, (happ n).2.2.1⟩
    x_one_le := hx1
    weight_growth := fun i hi _ => hgrowth i hi
    wstar_pos := hwstar
    wstar_lower := hwstarLower
    wstar_attained := hwstarAttained
    weight_margin := by
      have hfirst : 2 * Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) ≤
          3 * Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) := by nlinarith only [mul_nonneg hLambda.le hsum]
      have hsecond :
          (weightErrorCoefficient nu P.theta K + P.theta + Real.log (rho / 100) +
            Real.log (2 * ((K : ℝ) * R + 2))) / wstar ≤
          (weightErrorCoefficient nu P.theta K + 2 * P.theta + Real.log (rho / 100) +
            2 * Real.log (2 * ((K : ℝ) * R + 2))) / wstar := by
        apply div_le_div_of_nonneg_right _ hwstar.le
        linarith only [P.theta_pos, hconj]
      linarith only [hfirst, hsecond, hweight]
  }
  have herror : 3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError < epsilon := by
    have heq : 3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError =
        nu / F0 +
        ((3 * Lambda * F0 * (m : ℝ) + 4 * Real.log 2) / (v0 : ℝ) +
          ((rho + 2 * kappa) * (K : ℝ) + 2 * Real.log (3 / 2 : ℝ)) / (w0 : ℝ)) +
        (3 * Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) +
          (weightErrorCoefficient nu P.theta K + 2 * P.theta + Real.log (rho / 100) +
            2 * Real.log (2 * ((K : ℝ) * R + 2))) / wstar) := by
      dsimp [AlgebraicLog.AdmissibleParameters.arithmeticError, AlgebraicLog.AdmissibleParameters.conjugateError,
        AlgebraicLog.AdmissibleParameters.analyticError, AlgebraicLog.AdmissibleParameters.translationError,
        AlgebraicLog.AdmissibleParameters.holomorphicError, d, weightErrorCoefficient]
      ring
    rw [heq]
    linarith only [hFmargin, hdim', hweight]
  refine ⟨d, ?_, ?_⟩
  · exact herror.trans hepsg
  · change 3 + (3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError) <
      c * (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (P.A : ℝ) ^ m))
    linarith only [herror, hepshalf, hcollision']

end OAI.AffineCubic

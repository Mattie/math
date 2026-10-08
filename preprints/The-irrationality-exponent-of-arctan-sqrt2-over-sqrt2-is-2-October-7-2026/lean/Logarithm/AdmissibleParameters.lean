import OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters
import Logarithm.SuccessiveApproximations

namespace OAI
namespace Logarithm
open PiExponent

structure AdmissibleParameters (ξ nu Lambda c rho delta : ℝ) where
  base : Parameters nu
  epsilon : ℝ
  F0 : ℝ
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  sigma : ℚ
  p : ℕ → ℤ
  q : ℕ → ℕ
  x : ℕ → ℝ
  wstar : ℝ
  rho_large : 100 ≤ rho
  rho_covers_target : 100 * |ξ| ≤ rho
  delta_nonneg : 0 ≤ delta
  epsilon_pos : 0 < epsilon
  epsilon_lt_gap : epsilon <
    nu * ((base.A : ℝ) * (1 - base.eta) - base.theta) - (1 - base.theta)
  epsilon_le_half : epsilon ≤ 1 / 2
  F0_pos : 0 < F0
  F0_large : 2 / (base.theta : ℝ) < F0
  initial_margin : nu / F0 < epsilon / 3
  m_pos : 1 ≤ m
  K_eq : K = dimensionK (base.C : ℝ) m
  K_pos : 1 ≤ K
  w0_eq : (w0 : ℝ) = dimensionW (base.B : ℝ) m
  v0_eq : (v0 : ℝ) = dimensionV (base.theta : ℝ) base.B base.C m
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  volume_eq : (K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m = 1 / 2
  volume_lt_one : (K : ℝ) * (base.theta : ℝ) ^ m < 1
  dimension_margin :
    (Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / (v0 : ℝ) +
      (rho + delta) * (K : ℝ) / (w0 : ℝ) < epsilon / 3
  collision_margin : 2 < c *
    (base.eta ^ 2 * (K : ℝ) * (base.theta : ℝ) ^ m /
      (((m : ℝ) + 1) * (v0 : ℝ) * (base.A : ℝ) ^ m))
  sigma_pos : 0 < (sigma : ℝ)
  sigma_volume : (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
    ((K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m) < 1
  sigma_centers : (1 + 3 * (sigma : ℝ)) ^ m *
    ((K : ℝ) * (base.theta : ℝ) ^ m) < 1
  sigma_theta : (1 + (sigma : ℝ)) * (base.theta : ℝ) < 1
  x_zero : x 0 = 1
  x_log : ∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)
  approximations : ∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
    |ξ - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu)
  x_one_le : ∀ i, 1 ≤ x i
  weight_growth : PiExponentApprox.SeparatedWeightGrowth m
    (PiExponentApprox.weightSeparationFactor m (interpolationSeparationConstant m sigma)
      w0 v0 base.theta) x
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i : Fin m, wstar ≤ x (i.val + 1)
  wstar_attained : ∃ i : Fin m, wstar = x (i.val + 1)
  weight_margin : Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) +
    (weightErrorCoefficient nu base.theta K + Real.log (rho / 100)) / wstar < epsilon / 3

theorem exists_admissible_parameters
    (ξ nu Lambda c rho delta : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hξ : ξ ≠ 0) (hrho : 100 ≤ rho) (hrhoξ : 100 * |ξ| ≤ rho) (hdelta : 0 ≤ delta)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |ξ - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (AdmissibleParameters ξ nu Lambda c rho delta) := by
  classical
  obtain ⟨P⟩ := exists_parameters nu hnu
  let g : ℝ := nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - (1 - P.theta)
  have hg : 0 < g := P.gap_pos
  let epsilon : ℝ := min (g / 2) (1 / 2)
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hepsg : epsilon < g := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepshalf : epsilon ≤ 1 / 2 := min_le_right _ _
  have heps3 : 0 < epsilon / 3 := by positivity
  obtain ⟨F0, hF0, hFtheta, hFmargin⟩ :=
    exists_initial_scale nu P.theta epsilon P.theta_pos hepsilon
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 0 ≤ rho + delta := by linarith
  have hM1 : 0 < 1 + rho + delta := by linarith
  have htol : 0 < (epsilon / 3) / (1 + rho + delta) := div_pos heps3 hM1
  obtain ⟨m, hm, hdim, hcollision⟩ := exists_dimension_margin
    P.theta P.A P.B P.C P.eta (Lambda * F0) (2 * Real.log 2)
    ((epsilon / 3) / (1 + rho + delta)) (2 / c) P.theta_pos P.B_pos P.one_lt_C
    P.CB_lt_one P.one_lt_C_theta_div_B P.one_lt_B_div_A P.eta_pos
    (mul_pos hLambda hF0).le (by positivity) htol
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
  have hcollision' : 2 < c *
      (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (P.A : ℝ) ^ m)) := by
    rw [hv0eq]
    change 2 < c * (P.eta ^ 2 * (dimensionK (P.C : ℝ) m : ℝ) *
      (P.theta : ℝ) ^ m / (((m : ℝ) + 1) *
        dimensionV (P.theta : ℝ) P.B P.C m * (P.A : ℝ) ^ m))
    rw [dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    have hh := (div_lt_iff₀ hc).mp hcollision
    nlinarith
  obtain ⟨sigma, hsigma, hsigmaVol, hsigmaK, hsigmaTheta⟩ :=
    exists_small_rational_sigma m (1 / 2)
      ((K : ℝ) * (P.theta : ℝ) ^ m) P.theta (by norm_num) hvolume1 P.theta_lt_one
  have hnupos : 0 < nu := by linarith
  have hrho100 : 1 ≤ rho / 100 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).mpr (by linarith)
  have hS : 0 ≤ weightErrorCoefficient nu P.theta K + Real.log (rho / 100) :=
    add_nonneg (weightErrorCoefficient_nonneg nu P.theta K hnupos P.theta_pos hK)
      (Real.log_nonneg hrho100)
  obtain ⟨X, hX, hXmargin⟩ := exists_uniform_weight_error_margin m Lambda
    (weightErrorCoefficient nu P.theta K + Real.log (rho / 100)) (epsilon / 3) hLambda hS heps3
  obtain ⟨p, q, x, hx0, hxlog, happ, hx1, hgrowth⟩ :=
    exists_normalized_successive_approximations ξ nu X
      (PiExponentApprox.weightSeparationFactor m
        (interpolationSeparationConstant m sigma) w0 v0 P.theta) hnupos hξ hbad
  obtain ⟨wstar, hwstarX, hwstarLower, hwstarAttained⟩ :=
    exists_minimum_weight m hm (fun i : Fin m => x (i.val + 1)) X
      (fun i => (happ i.val).2.2.2.2)
  have hwstar : 0 < wstar := lt_of_lt_of_le zero_lt_one (le_trans hX hwstarX.le)
  refine ⟨{
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
    delta_nonneg := hdelta
    epsilon_pos := hepsilon
    epsilon_lt_gap := hepsg
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
    dimension_margin := ?_
    collision_margin := hcollision'
    sigma_pos := hsigma
    sigma_volume := ?_
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
    weight_margin := hXmargin wstar (fun i : Fin m => x (i.val + 1))
      hwstarX hwstarLower
  }⟩
  · rw [hv0eq, hw0eq]
    have hscaled := mul_lt_mul_of_pos_left hdim hM1
    have heq : (1 + rho + delta) * ((epsilon / 3) / (1 + rho + delta)) = epsilon / 3 := by
      field_simp [ne_of_gt hM1]
    rw [heq] at hscaled
    have hnonneg : 0 ≤ (Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / dimensionV P.theta P.B P.C m :=
      div_nonneg (by positivity) (by rw [← hv0eq]; exact hv0.le)
    have hquot : 0 ≤ (K : ℝ) / dimensionW P.B m :=
      div_nonneg (by positivity) (by rw [← hw0eq]; exact hw0.le)
    change (1 + rho + delta) *
      ((Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / dimensionV P.theta P.B P.C m +
        100 * (K : ℝ) / dimensionW P.B m) < epsilon / 3 at hscaled
    simp only [mul_div_assoc] at hscaled ⊢
    nlinarith [mul_nonneg hM hnonneg, mul_nonneg hM hquot]
  · rw [hvolume]
    exact hsigmaVol

namespace AdmissibleParameters

variable {ξ nu Lambda c rho delta : ℝ} (d : AdmissibleParameters ξ nu Lambda c rho delta)

noncomputable def rationalWeight : ℕ → ℚ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (d.q n)) : ℚ)

theorem cast_rationalWeight (i : ℕ) : (d.rationalWeight i : ℝ) = d.x i := by
  cases i with
  | zero => simpa [rationalWeight] using d.x_zero.symm
  | succ n => simpa [rationalWeight] using (d.x_log n).symm

theorem rationalWeight_pos (i : ℕ) : 0 < d.rationalWeight i := by
  have h : (0 : ℝ) < (d.rationalWeight i : ℝ) := by
    rw [d.cast_rationalWeight]
    exact zero_lt_one.trans_le (d.x_one_le i)
  exact_mod_cast h

theorem multiplicity_constant_bound (k : ℕ) (hk : k ≤ d.m) :
    2 * (k.factorial : ℝ) * (((d.m : ℝ) + 2) / (d.sigma : ℝ)) ^ k ≤
      interpolationSeparationConstant d.m d.sigma := by
  exact PiExponentApprox.multiplicity_constant_le_enlarged d.m k d.sigma d.sigma_pos hk

theorem rectangular_multiplicity_constant_bound (k : ℕ) (hk : k ≤ d.m) :
    (k : ℝ) ^ k * (((d.m : ℝ) + 2) / (d.sigma : ℝ)) ^ k ≤
      interpolationSeparationConstant d.m d.sigma := by
  exact PiExponentApprox.rectangular_multiplicity_constant_le_enlarged
    d.m k d.sigma d.sigma_pos hk

theorem separated_weight_products
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (d.m + 1)) (hB : B ⊆ Finset.range (d.m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    interpolationSeparationConstant d.m d.sigma *
      (∏ j ∈ B, PiExponentApprox.geometricJetWeight d.v0 d.base.theta d.x j) <
      ∏ j ∈ A, PiExponentApprox.geometricDegreeWeight d.w0 d.x j := by
  exact PiExponentApprox.geometric_weight_products_separated d.m
    (interpolationSeparationConstant d.m d.sigma) d.w0 d.v0 d.base.theta d.x
    (interpolationSeparationConstant_pos d.m d.sigma d.sigma_pos)
    d.w0_pos d.v0_pos d.base.theta_pos d.x_zero d.x_one_le d.weight_growth
    A B hcard hA hB i hi hiA hiB hbelow

theorem total_error_lt_gap :
    nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        (rho + delta) * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        (weightErrorCoefficient nu d.base.theta d.K + Real.log (rho / 100)) / d.wstar) <
      nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
        (1 - d.base.theta) := by
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_lt_gap
  linarith

theorem collision_exceeds_one_add_error :
    1 + (nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        (rho + delta) * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        (weightErrorCoefficient nu d.base.theta d.K + Real.log (rho / 100)) / d.wstar)) <
      c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
        (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_le_half
  have h5 := d.collision_margin
  linarith

noncomputable def arithmeticError : ℝ :=
  Lambda * d.F0 * (d.m : ℝ) / (d.v0 : ℝ) +
    Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) + (d.base.theta : ℝ) / d.wstar + delta * (d.K : ℝ) / (d.w0 : ℝ)

noncomputable def translationError : ℝ :=
  nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
    (Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar

noncomputable def holomorphicError : ℝ :=
  rho * (d.K : ℝ) / (d.w0 : ℝ) + Real.log 2 / (d.v0 : ℝ) +
    (Real.log (200 * (d.K : ℝ)) + Real.log (rho / 100)) / d.wstar

noncomputable def analyticError : ℝ := d.translationError + d.holomorphicError

theorem error_sum_eq : d.arithmeticError + d.analyticError =
    nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        (rho + delta) * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        (weightErrorCoefficient nu d.base.theta d.K + Real.log (rho / 100)) / d.wstar) := by
  unfold arithmeticError analyticError translationError holomorphicError weightErrorCoefficient
  ring

theorem error_sum_lt_gap : d.arithmeticError + d.analyticError <
    nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
      (1 - d.base.theta) := by
  rw [d.error_sum_eq]
  exact d.total_error_lt_gap

theorem collision_exceeds_error_sum : 1 + d.arithmeticError + d.analyticError <
    c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  rw [add_assoc, d.error_sum_eq]
  exact d.collision_exceeds_one_add_error

end AdmissibleParameters

end Logarithm

end OAI

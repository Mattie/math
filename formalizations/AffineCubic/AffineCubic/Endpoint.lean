import PairedAffine.Analytic
import PairedAffine.AnalyticCoarse
import PairedAffine.Geometry
import AffineCubic.Norm
import AffineCubic.Numerics
import AffineCubic.Consequence
import AffineCubic.Parameters
import AlgebraicLog.Main

namespace OAI.AffineCubic.Endpoint

open scoped BigOperators Topology NumberField
open Filter PiExponent Logarithm AlgebraicLog.DeterminantData PairedAffine

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- One compatible embedding provides the analytic saving, while all
remaining embeddings are bounded coarsely for that same selected minor. -/
theorem no_fixed_data
    (a u v : F) (ha : IsIntegral ℤ a) (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (hdegree : Module.finrank ℚ F = 3) (σ₀ : F →ₐ[ℚ] ℂ)
    (base : ℝ) (hbase : 0 < base) (hbase1 : base ≠ 1)
    (hbaseImage : σ₀ a = (base : ℂ))
    (good : Finset (F →ₐ[ℚ] ℂ)) (hgood : good.card = 1)
    (proxy : ℝ) {rho kappa R : ℝ} (hkappa : 0 ≤ kappa) (hR : 0 ≤ R)
    (hbaseBound : ∀ σ : F →ₐ[ℚ] ℂ, Real.log (max 1 ‖σ a‖) ≤ kappa)
    (hcentreBound : ∀ σ : F →ₐ[ℚ] ℂ,
      ‖σ u‖ * (|Real.log proxy| + 1 + ‖σ v‖) ≤ R)
    (hcompatible : ∀ σ ∈ good,
      Complex.exp (σ u * ((Real.log proxy : ℂ) - σ v)) = σ a)
    (hscale : ∀ σ ∈ good, ‖σ u‖ ≤ 1)
    (hradius : ∀ σ ∈ good, 100 * ‖σ u * ((Real.log proxy : ℂ) - σ v)‖ ≤ rho)
    {nu : ℝ} (hnu : 6 < nu)
    (d : AlgebraicLog.AdmissibleParameters (Real.log proxy) nu
      Arithmetic.lcmConstant collisionConstant rho 0 kappa R)
    (hbudget : 3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError <
      nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) - 3 * (1 - d.base.theta))
    (hcollision : 3 + (3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError) <
      collisionLimit d.toAnalyticData) : False := by
  classical
  let e := d.toAnalyticData
  let centres : (F →ₐ[ℚ] ℂ) → Fin d.m → ℂ := fun σ i =>
    σ u * ((finiteNumerators e i : ℂ) / (finiteDenominators e i : ℂ) - σ v)
  have hnu0 : 0 ≤ nu := by linarith
  have hE : AlgebraicLog.SelectedArithmetic.arithmeticError e 1 = d.arithmeticError := by
    unfold AlgebraicLog.SelectedArithmetic.arithmeticError
      AlgebraicLog.AdmissibleParameters.arithmeticError
    simp only [logWeights_eq]
    dsimp [e, AlgebraicLog.AdmissibleParameters.toAnalyticData]
    norm_num only [Nat.cast_one, Real.log_one]
    ring
  have hU : AlgebraicLog.ConjugateAggregate.conjugateCost e kappa R =
      d.conjugateError := by
    unfold AlgebraicLog.ConjugateAggregate.conjugateCost
      AlgebraicLog.AdmissibleParameters.conjugateError
    dsimp [e, AlgebraicLog.AdmissibleParameters.toAnalyticData]
    ring
  have hA : e.analyticError = d.analyticError := rfl
  let error := fun H => AlgebraicLog.LiteralAnalytic.analyticRemainder e H +
    2 * AlgebraicLog.ConjugateAggregate.conjugateRemainder e H
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (AlgebraicLog.LiteralAnalytic.tendsto_analyticRemainder e).add
        ((AlgebraicLog.ConjugateAggregate.tendsto_conjugateRemainder e).const_mul 2)
  have hsum : Tendsto (fun H : ℝ =>
      3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError + error H)
      atTop (𝓝 (3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
          3 * (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using hbudget))
  have hdiff : Tendsto (fun H : ℝ => collisionRate e H -
      (3 + 3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError + error H))
      atTop (𝓝 (collisionLimit e -
        (3 + 3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError + 0))) :=
    (AlgebraicLog.DeterminantContradiction.tendsto_collisionRate e).sub
      (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop, 0 < collisionRate e H -
      (3 + 3 * d.arithmeticError + 2 * d.conjugateError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := hcollision
    linarith
  have hcontradiction : ∀ᶠ H : ℝ in atTop,
      Function.Surjective (matrix e H (σ₀ a) (centres σ₀)).mulVecLin → False := by
    filter_upwards [hsmall, hlarge, eventually_gt_atTop (0 : ℝ)] with H hsmall hlarge hH
    intro hsurj
    obtain ⟨selection, _, hdet⟩ :=
      InterpolationMatrix.exists_full_row_minor_of_surjective
        (matrix e H (σ₀ a) (centres σ₀)) hsurj
    have hdet0 : (minor e H selection (σ₀ a) (centres σ₀)).det ≠ 0 := hdet
    have hne (σ : F →ₐ[ℚ] ℂ) : (minor e H selection (σ a) (centres σ)).det ≠ 0 :=
      PairedAffine.Arithmetic.selected_minor_ne_zero_all e a u v ha hu hv
        H selection σ₀ hdet0 σ
    let bound : ℝ := d.analyticError + AlgebraicLog.LiteralAnalytic.analyticRemainder e H +
      max (-collisionRate e H)
        (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean e H))
    have hgoodBound : ∀ σ ∈ good,
        Real.log ‖(minor e H selection (σ a) (centres σ)).det‖ /
          ((actualRowCount e H : ℝ) * H) ≤ bound := by
      intro σ hσ
      have herr := Analytic.errorBound_of_affine e (σ u) (σ v)
        (σ u * ((Real.log proxy : ℂ) - σ v)) 0 hnu0 rfl
        (by simpa using hscale σ hσ)
      have hb := Analytic.minor_analytic_bound e (centres σ) (σ a)
        (σ u * ((Real.log proxy : ℂ) - σ v)) 0
        (hcompatible σ hσ) (hradius σ hσ) (by norm_num) hnu0
        herr hH selection (hne σ)
      rw [hA] at hb
      simpa only [zero_div, add_zero] using hb
    have hbadBound : ∀ σ ∉ good,
        Real.log ‖(minor e H selection (σ a) (centres σ)).det‖ /
          ((actualRowCount e H : ℝ) * H) ≤
            AlgebraicLog.ConjugateAggregate.conjugateCost e kappa R +
              AlgebraicLog.ConjugateAggregate.conjugateRemainder e H := by
      intro σ _
      apply AnalyticCoarse.minor_log_bound e hH hkappa hR (σ a) (centres σ)
        (hbaseBound σ) _ selection (hne σ)
      intro i
      exact (AnalyticCoarse.affine_centres_norm_le e hnu0 (σ u) (σ v) i).trans
        (hcentreBound σ)
    have hnorm := AffineCubic.cubic_selected_normalized_bound e hdegree a u v ha hu hv
      H hH selection σ₀ hdet0 good hgood
      bound
      (AlgebraicLog.ConjugateAggregate.conjugateCost e kappa R +
        AlgebraicLog.ConjugateAggregate.conjugateRemainder e H)
      hgoodBound hbadBound
    rw [hE] at hnorm
    rw [hU] at hnorm
    have hlower : -3 * (1 - actualMean e H) -
        (3 * d.arithmeticError + 2 * d.conjugateError +
          2 * AlgebraicLog.ConjugateAggregate.conjugateRemainder e H) ≤ bound := by
      linarith
    have hb := actualMean_bounds e H hH
    apply AffineCubic.cubic_determinant_bounds_inconsistent nu d.base.theta
      ((d.base.A : ℝ) * (1 - d.base.eta)) (actualMean e H)
      (3 * d.arithmeticError + 2 * d.conjugateError +
        2 * AlgebraicLog.ConjugateAggregate.conjugateRemainder e H)
      d.analyticError (AlgebraicLog.LiteralAnalytic.analyticRemainder e H)
      (collisionRate e H) bound (by linarith) hb.1 hb.2
    · dsimp [error] at hsmall
      linarith
    · dsimp [error] at hlarge
      linarith
    · exact hlower
    · rfl
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hcontradiction
  obtain ⟨H, hLH, hsurj⟩ := Geometry.cofinal_matrix d base hbase hbase1 (centres σ₀) L
  rw [← hbaseImage] at hsurj
  exact hL H hLH hsurj

/-- A cubic integral affine configuration with one compatible
embedding of scale at most one has rational-approximation exponent at most six. All assumptions
describe field elements, embeddings, or exact exponential identities. -/
theorem cubic_eventualLowerBound
    (a u v : F) (ha : IsIntegral ℤ a) (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (hdegree : Module.finrank ℚ F = 3) (σ₀ : F →ₐ[ℚ] ℂ)
    (base : ℝ) (hbase : 0 < base) (hbase1 : base ≠ 1)
    (hbaseImage : σ₀ a = (base : ℂ))
    (x : ℝ) (hx : x ≠ 0)
    (good : Finset (F →ₐ[ℚ] ℂ)) (hgood : good.card = 1)
    (hcompatible : ∀ σ ∈ good, Complex.exp (σ u * ((x : ℂ) - σ v)) = σ a)
    (hscale : ∀ σ ∈ good, ‖σ u‖ ≤ 1) : AffineCubic.EventualLowerBoundSix x := by
  classical
  let proxy := Real.exp x
  have hproxy : Real.log proxy = x := Real.log_exp x
  let kappa := AlgebraicLog.EmbeddingBudget.embeddingCost a
  let R : ℝ := ∑ σ : F →ₐ[ℚ] ℂ, ‖σ u‖ * (|x| + 1 + ‖σ v‖)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => by positivity)
  have hcentre : ∀ σ : F →ₐ[ℚ] ℂ, ‖σ u‖ * (|x| + 1 + ‖σ v‖) ≤ R := by
    intro σ
    exact Finset.single_le_sum (f := fun τ : F →ₐ[ℚ] ℂ =>
      ‖τ u‖ * (|x| + 1 + ‖τ v‖)) (fun _ _ => by positivity) (Finset.mem_univ σ)
  let radiusSum : ℝ := ∑ σ : F →ₐ[ℚ] ℂ, ‖σ u * ((x : ℂ) - σ v)‖
  let rho : ℝ := 100 * max 1 (max |x| radiusSum)
  have hrho : 100 ≤ rho := by
    dsimp [rho]
    nlinarith [le_max_left (1 : ℝ) (max |x| radiusSum)]
  have hrhox : 100 * |x| ≤ rho := by
    have hh := (le_max_left |x| radiusSum).trans (le_max_right 1 (max |x| radiusSum))
    dsimp [rho]
    nlinarith
  have hradius : ∀ σ : F →ₐ[ℚ] ℂ, 100 * ‖σ u * ((x : ℂ) - σ v)‖ ≤ rho := by
    intro σ
    have hs : ‖σ u * ((x : ℂ) - σ v)‖ ≤ radiusSum :=
      Finset.single_le_sum (f := fun τ : F →ₐ[ℚ] ℂ => ‖τ u * ((x : ℂ) - τ v)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
    have hh := hs.trans ((le_max_right |x| radiusSum).trans
      (le_max_right 1 (max |x| radiusSum)))
    dsimp [rho]
    nlinarith
  apply AffineCubic.eventualLowerBoundSix_of_not_unbounded
  intro nu hnu hbad
  obtain ⟨d, hbudget, hcollision⟩ := AffineCubic.exists_parameters (Real.log proxy) nu
    Arithmetic.lcmConstant collisionConstant rho kappa R hnu
    Arithmetic.lcmConstant_pos collisionConstant_pos (by simpa only [hproxy] using hx)
    hrho (by simpa only [hproxy] using hrhox)
    (AlgebraicLog.EmbeddingBudget.embeddingCost_nonneg a) (by positivity)
    (by simpa only [hproxy] using hbad)
  apply no_fixed_data a u v ha hu hv hdegree σ₀ base hbase hbase1 hbaseImage
    good hgood proxy (AlgebraicLog.EmbeddingBudget.embeddingCost_nonneg a) hR
    (AlgebraicLog.EmbeddingBudget.log_norm_le_embeddingCost a)
    (fun σ => by simpa only [hproxy] using hcentre σ)
    (fun σ hσ => by simpa only [hproxy] using hcompatible σ hσ) hscale
    (fun σ _ => by simpa only [hproxy] using hradius σ) hnu d hbudget
  simpa only [collisionLimit, AlgebraicLog.AdmissibleParameters.toAnalyticData] using hcollision

end
end OAI.AffineCubic.Endpoint

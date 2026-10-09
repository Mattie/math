import AlgebraicLog.GlobalMatrixInterpolation
import AlgebraicLog.SelectedArithmetic
import AlgebraicLog.ConjugateAggregate
import AlgebraicLog.EmbeddingBudget
import AlgebraicLog.ContradictionNumerics

namespace OAI.AlgebraicLog.DeterminantContradiction
noncomputable section
open Filter PiExponent DeterminantData
open scoped Topology BigOperators

local instance {F : Type*} [Field F] [NumberField F] : DecidableEq (F →ₐ[ℚ] ℂ) :=
  Classical.decEq _

theorem tendsto_collisionRate {base nu rho : ℝ} (d : FixedData base nu rho) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hA : 0 < d.base.A := by exact_mod_cast d.base.A_pos
  have hh := MatrixCounting.tendsto_collisionRatio d.K d.v0 d.base.theta d.base.A
    (finiteDenominators d) hv ht hA (finiteDenominators_two_le d)
    collisionConstant d.base.eta
  have he : collisionConstant * d.base.eta ^ 2 * (d.K : ℝ) *
      (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m) =
        collisionLimit d := by unfold collisionLimit; ring
  rw [he] at hh
  exact hh

/-- The norm, conjugate, analytic and interpolation inequalities contradict
one another for the same selected minor. No determinant conclusion is assumed
in the parameter package. -/
theorem no_fixed_data {F : Type*} [Field F] [NumberField F]
    (a : F) (hdegree : Module.finrank ℚ F = 2) (σ₀ : F →ₐ[ℚ] ℂ)
    (base : ℝ) (hbase : 0 < base) (hbase1 : base ≠ 1) (hbaseImage : σ₀ a = (base : ℂ))
    (D : ℕ) (hD : 0 < D) (ha : IsIntegral ℤ ((D : F) * a))
    {nu rho : ℝ} (hnu : 4 < nu)
    (d : AdmissibleParameters (Real.log base) nu Arithmetic.lcmConstant collisionConstant rho
      (Real.log D) (EmbeddingBudget.embeddingCost a) (|Real.log base| + 1)) : False := by
  classical
  let e := d.toAnalyticData
  have hnu0 : 0 ≤ nu := by linarith
  have hE : SelectedArithmetic.arithmeticError e D = d.arithmeticError := by
    unfold SelectedArithmetic.arithmeticError AdmissibleParameters.arithmeticError
    simp only [logWeights_eq]
    dsimp [e, AdmissibleParameters.toAnalyticData]
    ring
  have hU : ConjugateAggregate.conjugateCost e (EmbeddingBudget.embeddingCost a)
      (|Real.log base| + 1) = d.conjugateError := by
    unfold ConjugateAggregate.conjugateCost AdmissibleParameters.conjugateError
    dsimp [e, AdmissibleParameters.toAnalyticData]
    ring
  have hA : e.analyticError = d.analyticError := rfl
  let error := fun H => LiteralAnalytic.analyticRemainder e H + ConjugateAggregate.conjugateRemainder e H
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [add_zero] using
      (LiteralAnalytic.tendsto_analyticRemainder e).add (ConjugateAggregate.tendsto_conjugateRemainder e)
  have hsum : Tendsto (fun H : ℝ =>
      2 * d.arithmeticError + d.conjugateError + d.analyticError + error H)
      atTop (𝓝 (2 * d.arithmeticError + d.conjugateError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      2 * d.arithmeticError + d.conjugateError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) - 2 * (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using d.error_sum_lt_gap))
  have hdiff : Tendsto (fun H : ℝ => collisionRate e H -
      (2 + 2 * d.arithmeticError + d.conjugateError + d.analyticError + error H))
      atTop (𝓝 (collisionLimit e -
        (2 + 2 * d.arithmeticError + d.conjugateError + d.analyticError + 0))) :=
    (tendsto_collisionRate e).sub (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop, 0 < collisionRate e H -
      (2 + 2 * d.arithmeticError + d.conjugateError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := d.collision_exceeds_error_sum
    change 2 + 2 * d.arithmeticError + d.conjugateError + d.analyticError < collisionLimit e at hh
    linarith
  have hcontradiction : ∀ᶠ H : ℝ in atTop,
      Function.Surjective (actualMatrix e H).mulVecLin → False := by
    filter_upwards [hsmall, hlarge, eventually_gt_atTop (0 : ℝ)] with H hsmall hlarge hH
    intro hsurj
    obtain ⟨selection, _, hdet⟩ :=
      InterpolationMatrix.exists_full_row_minor_of_surjective (actualMatrix e H) hsurj
    have hdet' : (actualMinor e H selection).det ≠ 0 := hdet
    have himage : complexMinor e H selection (σ₀ a) = actualMinor e H selection := by
      rw [hbaseImage, complexMinor_at_base]
    have hdet0 : (complexMinor e H selection (σ₀ a)).det ≠ 0 := by rwa [himage]
    have hM : (0 : ℝ) < actualRowCount e H := by
      exact_mod_cast LiteralAnalytic.actualRowCount_pos e hH
    have hconj : (∑ σ ∈ Finset.univ.erase σ₀,
        Real.log ‖(complexMinor e H selection (σ a)).det‖) ≤
        (actualRowCount e H : ℝ) * H *
          (ConjugateAggregate.conjugateCost e (EmbeddingBudget.embeddingCost a) (|Real.log base| + 1) +
            ConjugateAggregate.conjugateRemainder e H) := by
      apply EmbeddingBudget.quadratic_other_sum_le hdegree σ₀
      intro σ _
      have hn := SelectedArithmetic.complexMinor_det_ne_zero_all e a D hD ha H selection σ₀ hdet0 σ
      have hb := ConjugateAggregate.complexMinor_log_bound e hnu0 hH
        (EmbeddingBudget.embeddingCost_nonneg a) (le_refl (|Real.log base| + 1)) (σ a)
        (EmbeddingBudget.log_norm_le_embeddingCost a σ) selection hn
      exact (div_le_iff₀ (mul_pos hM hH)).mp hb |>.trans_eq (by ring)
    have hlower := SelectedArithmetic.normalized_selected_lower e a D hD ha hdegree H hH
      selection σ₀ hdet0 _ _ hconj
    rw [himage, hE, hU] at hlower
    have hb := actualMean_bounds e H hH
    have hupper := LiteralAnalytic.actual_minor_analytic_bound e hbase hnu0 hH selection hdet'
    rw [hA] at hupper
    apply quadratic_determinant_bounds_inconsistent nu d.base.theta
      ((d.base.A : ℝ) * (1 - d.base.eta)) (actualMean e H)
      (2 * d.arithmeticError + d.conjugateError + ConjugateAggregate.conjugateRemainder e H)
      d.analyticError (LiteralAnalytic.analyticRemainder e H) (collisionRate e H)
      (Real.log ‖(actualMinor e H selection).det‖ / ((actualRowCount e H : ℝ) * H))
      (by linarith) hb.1 hb.2
    · dsimp [error] at hsmall
      linarith
    · dsimp [error] at hlarge
      linarith
    · linarith
    · exact hupper
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hcontradiction
  obtain ⟨H, hLH, hsurj⟩ := GlobalMatrixInterpolation.cofinal_actualMatrix d hbase hbase1 L
  exact hL H hLH hsurj

end
end OAI.AlgebraicLog.DeterminantContradiction

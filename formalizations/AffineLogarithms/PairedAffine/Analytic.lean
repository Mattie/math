import PairedAffine.Data
import AlgebraicLog.AnalyticAggregate

namespace OAI.PairedAffine.Analytic

open scoped BigOperators Topology
open Filter PiExponent Logarithm AlgebraicLog.DeterminantData
open AlgebraicLog.LiteralAnalytic

noncomputable section

/-- The distinguished approximation can be multiplied by a fixed algebraic
constant without changing its denominator exponent. -/
def ErrorBound {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (omega : ℂ) (extra : ℝ) : Prop :=
  ∀ (j : Fin d.K) (i : Fin d.m),
    ‖(j.val : ℂ) * (centres i - omega)‖ ≤
      Real.exp ((Real.log (2 * (d.K : ℝ)) + nu + extra) - nu * fixedWeights d i)

theorem errorBound_of_comparison {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (omega : ℂ) (extra : ℝ) (hnu : 0 ≤ nu)
    (hcomparison : ∀ i,
      ‖centres i - omega‖ ≤ Real.exp extra *
        ‖ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          (Real.log proxy : ℂ)‖) :
    ErrorBound d centres omega extra := by
  intro j i
  have heps := ScaledApproximationErrors.actual_error_exp (Real.log proxy)
    (finiteNumerators d) (finiteDenominators d) j.val d.K nu d.K_pos j.isLt.le hnu
    (fun k => le_trans (by decide : 1 ≤ 2) (finiteDenominators_two_le d k))
    (fun k => (d.approximations k.val).2.2)
  calc
    _ = ‖(j.val : ℂ)‖ * ‖centres i - omega‖ := norm_mul _ _
    _ ≤ ‖(j.val : ℂ)‖ * (Real.exp extra *
        ‖ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          (Real.log proxy : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (hcomparison i) (norm_nonneg _)
    _ = Real.exp extra *
        ‖(j.val : ℂ) *
          (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
            (Real.log proxy : ℂ))‖ := by rw [norm_mul]; ring
    _ ≤ Real.exp extra * Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) -
        nu * (⌈Real.log (finiteDenominators d i)⌉₊ : ℝ)) :=
      mul_le_mul_of_nonneg_left (heps i) (Real.exp_pos extra).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      change extra + ((Real.log (2 * (d.K : ℝ)) + nu) -
        nu * (⌈Real.log (finiteDenominators d i)⌉₊ : ℝ)) =
        (Real.log (2 * (d.K : ℝ)) + nu + extra) -
          nu * (⌈Real.log (finiteDenominators d i)⌉₊ : ℝ)
      ring

theorem errorBound_of_affine {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (scale shift omega : ℂ) (extra : ℝ) (hnu : 0 ≤ nu)
    (hcompat : scale * ((Real.log proxy : ℂ) - shift) = omega)
    (hscale : ‖scale‖ ≤ Real.exp extra) :
    ErrorBound d
      (fun i => scale *
        (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - shift))
      omega extra := by
  apply errorBound_of_comparison d _ omega extra hnu
  intro i
  have hid : scale *
      (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - shift) -
      omega = scale *
      (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
        (Real.log proxy : ℂ)) := by rw [← hcompat]; ring
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_right hscale (norm_nonneg _)

def choiceScalar {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (omega : ℂ) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℂ :=
  RowTranslation.rowScalar
    (fun i => (r.1.val : ℂ) * (centres i - omega))
    (fun i => RowTranslation.tail
      (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
      (PowerSeries.log ℂ))
    (beta d r) t.1.1 t.2.1 t.2.2

def choiceMatrix {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (z omega : ℂ) {H : ℝ} (selection : Row d H → Column d H)
    (f : ChoiceFamily d H) : Matrix (Row d H) (Row d H) ℂ :=
  fun r c => z ^ (r.1.val * ((selection c).1 0)) *
    PowerSeries.coeff (r.2.1 0 - (f r).2.2)
      ((MatrixTranslation.periodMonomial r.1.val omega
        ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

theorem norm_choiceScalar_le {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (omega : ℂ) (extra : ℝ)
    (hextra : 0 ≤ extra) (hnu : 0 ≤ nu) (herror : ErrorBound d centres omega extra)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d centres omega r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) +
        H * (d.translationError + extra / d.wstar)) := by
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hC : 0 ≤ Real.log (2 * (d.K : ℝ)) + nu + extra :=
    add_nonneg (add_nonneg (Real.log_nonneg (by linarith)) hnu) hextra
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply le_trans _ (rowOrder_le d r)
    exact_mod_cast Nat.le_of_lt_succ t.2.2.isLt
  have hT : ∀ i, 1 ≤ PiExponent.MatrixArithmetic.truncationOrders
      (finiteDenominators d) d.F0 d.v0 i :=
    fun i => MatrixTranslationBounds.truncationOrder_pos
      d.F0_pos d.v0_pos (fixedWeights_pos d i)
  have hTw : ∀ i, d.F0 * fixedWeights d i ≤
      (d.v0 : ℝ) * PiExponent.MatrixArithmetic.truncationOrders
        (finiteDenominators d) d.F0 d.v0 i :=
    fun _ => MatrixTranslationBounds.truncationOrder_budget d.v0_pos
  have hb := MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    (fun i => (r.1.val : ℂ) * (centres i - omega))
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (beta d r) t.1.1 t.2.1 t.2.2 (fixedWeights d)
    (Real.log (2 * (d.K : ℝ)) + nu + extra) nu H d.wstar d.v0 d.F0
    hC hnu d.wstar_pos d.v0_pos d.F0_pos (fixedWeights_lower d) (indexWeight_le d t.1)
    hk hT hTw (herror r.1)
  convert hb using 1 <;>
    simp only [choiceScalar, indexWeight, rowWeight, AlgebraicLog.AnalyticData.translationError]
  congr 1
  ring

theorem rowWeight_le_indexWeight_of_ne_zero {proxy nu rho : ℝ}
    (d : FixedData proxy nu rho) (centres : Fin d.m → ℂ) (omega : ℂ)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r)
    (ht : choiceScalar d centres omega r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  have h := RowTranslation.rowScalar_ne_zero_le _ _ _ _ _ _ ht
  unfold rowWeight indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast h i) (fixedWeights_pos d i).le

theorem norm_scalar_product_le {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (omega : ℂ) (extra : ℝ)
    (hextra : 0 ≤ extra) (hnu : 0 ≤ nu) (herror : ErrorBound d centres omega extra)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d centres omega r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * (d.translationError + extra / d.wstar)) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod₀ (fun r _ => norm_nonneg _)
    (fun r _ => norm_choiceScalar_le d centres omega extra hextra hnu herror r (f r))).trans
  rw [← Real.exp_sum]
  apply le_of_eq
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_rowWeight_eq d hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
  ring_nf

theorem norm_choiceMatrix_le {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (z omega : ℂ) (hz : Complex.exp omega = z) (homega : 100 * ‖omega‖ ≤ rho)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d z omega selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  have horders : ((∑ r : Row d H, (r.2.1 0 - ((f r).2.2 : ℕ)) : ℕ) : ℝ) ≤
      (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        exact le_trans (by exact_mod_cast Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ))
          (rowOrder_le d r)
      _ = _ := by simp; ring_nf
  have hb := ScaledCollision.formal_scaled_collision_bound omega rho d.rho_large homega
    (fun r => (f r).1) (fun A : Transverse d H => A.1)
    (fun r => r.1.val) (fun r => r.2.1 0 - ((f r).2.2 : ℕ))
    (fun c => (selection c).1 0) (fun c i => (selection c).1 i.succ) (fixedWeights d)
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) hH d.w0_pos d.wstar_pos (fixedWeights_lower d)
    (fun r => r.1.isLt)
    (fun c => InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c))
    horders
  simp_rw [Complex.exp_nat_mul, hz, ← pow_mul] at hb
  convert! hb using 1

theorem norm_summand_le {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (z omega : ℂ) (extra : ℝ)
    (hz : Complex.exp omega = z) (homega : 100 * ‖omega‖ ≤ rho)
    (hextra : 0 ≤ extra) (hnu : 0 ≤ nu) (herror : ErrorBound d centres omega extra)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(∏ r, choiceScalar d centres omega r (f r)) * (choiceMatrix d z omega selection f).det‖ ≤
      Real.exp ((actualRowCount d H : ℝ) * H *
        (d.analyticError + extra / d.wstar + Collision.collisionRemainder (actualRowCount d H) H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r, choiceScalar d centres omega r (f r)) = 0
  · simp [hs, Real.exp_nonneg]
  have hmono : (actualRowCount d H : ℝ) * H * actualMean d H ≤
      ∑ r, indexWeight d (f r).1 := by
    rw [← sum_rowWeight_eq d hH]
    apply Finset.sum_le_sum
    intro r _
    apply rowWeight_le_indexWeight_of_ne_zero d centres omega r (f r)
    exact Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r)
  have hb := DeterminantAnalyticBound.translated_summand_bound
    (fun r => (f r).1) (fun A : Transverse d H => indexWeight d A)
    (∏ r, choiceScalar d centres omega r (f r)) (choiceMatrix d z omega selection f).det
    hH d.base.A_pos.le d.base.eta_pos.le hnu collisionConstant_pos.le
    (by exact_mod_cast lowIndexCount_pos d hH)
    (indexWeight_nonneg d) hmono (low_transverse_capacity d H)
    (norm_scalar_product_le d centres omega extra hextra hnu herror hH f)
    (norm_choiceMatrix_le d z omega hz homega hH selection f)
  convert! hb using 1
  congr 1
  unfold AlgebraicLog.AnalyticData.analyticError collisionRate collisionConstant actualRowCount
  ring_nf

theorem minor_expansion {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (z omega : ℂ) {H : ℝ}
    (selection : Row d H → Column d H) :
    (minor d H selection z centres).det =
      ∑ f : ChoiceFamily d H,
        (∏ r, choiceScalar d centres omega r (f r)) * (choiceMatrix d z omega selection f).det := by
  classical
  have hp : ∀ r c : Row d H,
      (MatrixTranslation.periodMonomial r.1.val omega
        ((selection c).1 0) (fun i => (selection c).1 i.succ)).support ⊆
        MatrixTranslation.transverseIndices (fixedWeights d) H := by
    intro r c
    apply MatrixTranslation.periodMonomial_support_subset _ _ _ _ _ _ (fixedWeights_pos d)
    have hc := InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)
    have hz : 0 ≤ (d.w0 : ℝ) * ((selection c).1 0 : ℝ) :=
      mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
    linarith
  have he := ScaledTranslation.det_matrix_translation centres
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (fun r : Row d H => r.1.val) (fun r => r.2.1 0) omega
    (fun r i => r.2.1 i.succ) (fun c => (selection c).1 0)
    (fun c i => (selection c).1 i.succ)
    (fun r c => z ^ (r.1.val * ((selection c).1 0)))
    (MatrixTranslation.transverseIndices (fixedWeights d) H) hp
  convert! he using 1
  congr 1
  funext r c
  exact minor_entry d H selection z centres r c

/-- Full analytic saving at any compatible embedding, for one fixed selected
minor. The extra constant accounts only for a fixed multiplier in the errors. -/
theorem minor_analytic_bound {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (centres : Fin d.m → ℂ) (z omega : ℂ) (extra : ℝ)
    (hz : Complex.exp omega = z) (homega : 100 * ‖omega‖ ≤ rho)
    (hextra : 0 ≤ extra) (hnu : 0 ≤ nu) (herror : ErrorBound d centres omega extra)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (minor d H selection z centres).det ≠ 0) :
    Real.log ‖(minor d H selection z centres).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + extra / d.wstar + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by
  have hQ : (0 : ℝ) < translationTermCount d.m d.v0 H := by
    unfold translationTermCount
    positivity
  have hc : (Fintype.card (ChoiceFamily d H) : ℝ) ≤
      (translationTermCount d.m d.v0 H : ℝ) ^ actualRowCount d H := by
    exact_mod_cast card_choiceFamily_le d H
  have hb := DeterminantAnalyticBound.log_norm_sum_le
    (fun f : ChoiceFamily d H =>
      (∏ r, choiceScalar d centres omega r (f r)) * (choiceMatrix d z omega selection f).det)
    (minor d H selection z centres).det (actualRowCount_pos d hH) hH hQ hc
    (minor_expansion d centres z omega selection) hne
    (norm_summand_le d centres z omega extra hz homega hextra hnu herror hH selection)
  convert! hb using 1
  unfold analyticRemainder
  ring

end
end OAI.PairedAffine.Analytic

import Periodic.DeterminantData
import Logarithm.ScaledCollision
import Periodic.ScaledApproximationErrors
import OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound
import OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds

open OAI.Imaginary

namespace OAI

open scoped BigOperators

namespace Periodic.LiteralAnalytic
open Logarithm PiExponent
open Periodic.DeterminantData

noncomputable def fixedWeights {base : PeriodData} {nu : ℝ} (d : FixedData base nu) : Fin d.m → ℝ :=
  MatrixArithmetic.logWeights (finiteDenominators d)

abbrev Transverse {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  ↥(MatrixTranslation.transverseIndices (fixedWeights d) H)

noncomputable def beta {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (r : Row d H) : Fin d.m →₀ ℕ :=
  InterpolationMatrix.exponentVector (fun i => r.2.1 i.succ)

abbrev RowChoice {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) (r : Row d H) :=
  RowTranslation.RowChoices (MatrixTranslation.transverseIndices (fixedWeights d) H)
    (beta d r) (r.2.1 0)

abbrev ChoiceFamily {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  ∀ r : Row d H, RowChoice d H r

noncomputable def indexWeight {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (a : Transverse d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => a.1 i)

noncomputable def rowWeight {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (r : Row d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => beta d r i)

noncomputable def choiceScalar {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℂ :=
  RowTranslation.rowScalar
    (fun i => (r.1.val : ℂ) *
      (ScaledArithmetic.imaginaryCenters (finiteNumerators d) (finiteDenominators d) i - base.omega))
    (fun i => RowTranslation.tail
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) (PowerSeries.log ℂ))
    (beta d r) t.1.1 t.2.1 t.2.2

noncomputable def choiceMatrix {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) : Matrix (Row d H) (Row d H) ℂ :=
  fun r c => base.value ^ (r.1.val * ((selection c).1 0)) * PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((MatrixTranslation.periodMonomial r.1.val base.omega
      ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

theorem fixedWeights_pos {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    0 < fixedWeights d i := by
  change 0 < MatrixArithmetic.logWeights (finiteDenominators d) i
  rw [logWeights_eq]
  exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)

theorem fixedWeights_lower {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    d.wstar ≤ fixedWeights d i := by
  change d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i
  rw [logWeights_eq]
  exact d.wstar_lower i

theorem rowOrder_le {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (r : Row d H) :
    (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
  have hr := InterpolationMatrix.row_weight_lt d.v0_pos d.base.theta_pos (fixedWeights_pos d) r
  have hs : 0 ≤ (∑ i, fixedWeights d i * (r.2.1 i.succ : ℝ)) / (d.base.theta : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _))
      d.base.theta_pos.le
  apply (le_div_iff₀ d.v0_pos).mpr
  nlinarith

theorem indexWeight_nonneg {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (a : Transverse d H) :
    0 ≤ indexWeight d a := by
  unfold indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _)

theorem indexWeight_le {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (a : Transverse d H) :
    indexWeight d a ≤ H :=
  (MatrixTranslation.mem_transverseIndices (fixedWeights d) H (fixedWeights_pos d) a.1).mp a.2

theorem norm_choiceScalar_le {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (hnu : 0 ≤ nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) + H * (d.translationError + Real.log 2 / d.wstar)) := by
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hC : 0 ≤ Real.log (2 * (d.K : ℝ)) + nu + Real.log 2 :=
    add_nonneg (add_nonneg (Real.log_nonneg (by linarith)) hnu) (Real.log_nonneg (by norm_num))
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply le_trans _ (rowOrder_le d r)
    exact_mod_cast Nat.le_of_lt_succ t.2.2.isLt
  have hT : ∀ i, 1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i :=
    fun i => MatrixTranslationBounds.truncationOrder_pos d.F0_pos d.v0_pos (fixedWeights_pos d i)
  have hTw : ∀ i, d.F0 * fixedWeights d i ≤
      (d.v0 : ℝ) * MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i :=
    fun _ => MatrixTranslationBounds.truncationOrder_budget d.v0_pos
  have heps := ScaledApproximationErrors.actual_error_exp base.angle (finiteNumerators d) (finiteDenominators d)
    r.1.val d.K nu d.K_pos r.1.isLt.le hnu
    (fun i => le_trans (by decide : 1 ≤ 2) (finiteDenominators_two_le d i))
    (fun i => (d.approximations i.val).2.2)
  have hb := MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    (fun i => (r.1.val : ℂ) *
      (ScaledArithmetic.imaginaryCenters (finiteNumerators d) (finiteDenominators d) i - base.omega))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (beta d r) t.1.1 t.2.1 t.2.2 (fixedWeights d)
    (Real.log (2 * (d.K : ℝ)) + nu + Real.log 2) nu H d.wstar d.v0 d.F0
    hC hnu d.wstar_pos d.v0_pos d.F0_pos (fixedWeights_lower d) (indexWeight_le d t.1)
    hk hT hTw heps
  convert hb using 1 <;>
    simp only [choiceScalar, indexWeight, rowWeight, Logarithm.AdmissibleParameters.translationError] <;>
    congr 1 <;> ring

theorem rowWeight_le_indexWeight_of_ne_zero {base : PeriodData} {nu : ℝ} (d : FixedData base nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) (ht : choiceScalar d r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  have h := RowTranslation.rowScalar_ne_zero_le _ _ _ _ _ _ ht
  unfold rowWeight indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h i)
    (fixedWeights_pos d i).le

theorem actualRowCount_pos {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H :=
  MatrixArithmetic.actual_row_card_pos (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.v0_pos d.base.theta_pos hH
    (fixedWeights_pos d)

theorem sum_rowWeight_eq {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H * actualMean d H := by
  have hM : (actualRowCount d H : ℝ) ≠ 0 := by exact_mod_cast (actualRowCount_pos d hH).ne'
  unfold actualMean MatrixArithmetic.meanRowWeight
  change (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H *
    (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H /
      ((actualRowCount d H : ℝ) * H))
  rw [mul_div_cancel₀ _ (mul_ne_zero hM hH.ne')]
  unfold MatrixArithmetic.rowWeightedSum rowWeight MatrixTranslationBounds.weight beta fixedWeights
  simp only [InterpolationMatrix.exponentVector_apply, mul_comm]

theorem low_transverse_capacity {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun A => indexWeight d A ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤ lowIndexCount d H := by
  classical
  let f : {A : Transverse d H // indexWeight d A ≤ (d.base.A : ℝ) * H} →
      ↥(MatrixTranslation.transverseIndices (fixedWeights d) ((d.base.A : ℝ) * H)) :=
    fun A => ⟨A.1.1, (MatrixTranslation.mem_transverseIndices _ _ (fixedWeights_pos d) _).mpr A.2⟩
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    simpa only [f] using hh
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_subtype] at hh
  have hc : Fintype.card ↥(MatrixTranslation.transverseIndices (fixedWeights d)
      ((d.base.A : ℝ) * H)) = lowIndexCount d H := by
    simp only [Fintype.card_coe, MatrixTranslation.card_transverseIndices]
    rfl
  rw [hc] at hh
  exact_mod_cast hh

theorem lowIndexCount_pos {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (hH : 0 < H) :
    0 < lowIndexCount d H := by
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, ?_⟩
  apply (mem_realWeightedSimplex (fixedWeights_pos d)).mpr
  simp only [Nat.cast_zero, mul_zero, Finset.sum_const_zero]
  exact mul_nonneg d.base.A_pos.le hH.le

theorem norm_scalar_product_le {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) - (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * (d.translationError + Real.log 2 / d.wstar)) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod₀ (fun r _ => norm_nonneg _) (fun r _ => norm_choiceScalar_le d hnu r (f r))).trans
  rw [← Real.exp_sum]
  apply le_of_eq
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_rowWeight_eq d hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
  ring_nf

theorem norm_choiceMatrix_le {base : PeriodData} {nu : ℝ} (d : FixedData base nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
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
        exact le_trans (by exact_mod_cast Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ)) (rowOrder_le d r)
      _ = _ := by simp; ring_nf
  have hb := ScaledCollision.formal_scaled_collision_bound base.omega base.radius d.rho_large
    base.radius_covers_omega (fun r => (f r).1) (fun A : Transverse d H => A.1)
    (fun r => r.1.val) (fun r => r.2.1 0 - ((f r).2.2 : ℕ))
    (fun c => (selection c).1 0) (fun c i => (selection c).1 i.succ) (fixedWeights d)
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) hH d.w0_pos d.wstar_pos (fixedWeights_lower d)
    (fun r => r.1.isLt)
    (fun c => InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)) horders
  simp_rw [base.exp_nat_mul, ← pow_mul] at hb
  convert! hb using 1

theorem norm_actual_summand_le {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det‖ ≤
    Real.exp ((actualRowCount d H : ℝ) * H *
      ((d.analyticError + Real.log 2 / d.wstar) + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r, choiceScalar d r (f r)) = 0
  · simp [hs, Real.exp_nonneg]
  have hmono : (actualRowCount d H : ℝ) * H * actualMean d H ≤ ∑ r, indexWeight d (f r).1 := by
    rw [← sum_rowWeight_eq d hH]
    apply Finset.sum_le_sum
    intro r _
    apply rowWeight_le_indexWeight_of_ne_zero d r (f r)
    exact Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r)
  have hb := DeterminantAnalyticBound.translated_summand_bound
    (fun r => (f r).1) (fun A : Transverse d H => indexWeight d A)
    (∏ r, choiceScalar d r (f r)) (choiceMatrix d selection f).det
    hH d.base.A_pos.le d.base.eta_pos.le hnu collisionConstant_pos.le
    (by exact_mod_cast lowIndexCount_pos d hH)
    (indexWeight_nonneg d) hmono (low_transverse_capacity d H)
    (norm_scalar_product_le d hnu hH f) (norm_choiceMatrix_le d hH selection f)
  convert! hb using 1
  congr 1
  unfold Logarithm.AdmissibleParameters.analyticError collisionRate collisionConstant actualRowCount
  ring_nf

end Periodic.LiteralAnalytic

end OAI

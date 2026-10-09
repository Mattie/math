import AlgebraicLog.ConjugateDeterminant
import AlgebraicLog.AnalyticAggregate

namespace OAI.AlgebraicLog.ConjugateAggregate
open PiExponent Logarithm DeterminantData LiteralAnalytic Filter
open scoped BigOperators Topology

theorem rationalCenters_norm_le {base nu rho : ℝ} (d : FixedData base nu rho)
    (hnu : 0 ≤ nu) {R : ℝ} (hR : |Real.log base| + 1 ≤ R) (i : Fin d.m) :
    ‖ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i‖ ≤ R := by
  have hq : (1 : ℝ) ≤ d.q i.val := by exact_mod_cast (d.approximations i.val).1.trans' (by decide : 1 ≤ 2)
  have he := (d.approximations i.val).2.2
  have hp : (d.q i.val : ℝ) ^ (-nu) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  have ht := abs_add_le (Real.log base) ((d.p i.val : ℝ) / d.q i.val - Real.log base)
  have hh : |(d.p i.val : ℝ) / d.q i.val| ≤ R := by
    rw [abs_sub_comm] at he
    have hid : Real.log base + ((d.p i.val : ℝ) / d.q i.val - Real.log base) =
        (d.p i.val : ℝ) / d.q i.val := by ring
    rw [hid] at ht
    linarith
  have heq : ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i =
      (((d.p i.val : ℝ) / d.q i.val : ℝ) : ℂ) := by
    simp [ScaledArithmetic.rationalCenters, finiteNumerators, finiteDenominators]
  simpa only [heq, Complex.norm_real, Real.norm_eq_abs] using hh

noncomputable def conjugateCost {base nu rho : ℝ} (d : FixedData base nu rho)
    (kappa R : ℝ) : ℝ :=
  Real.log 2 / (d.v0 : ℝ) +
    ((d.K : ℝ) * kappa + Real.log (3 / 2 : ℝ)) / (d.w0 : ℝ) +
    Real.log (2 * ((d.K : ℝ) * R + 2)) / d.wstar

theorem entry_cost_le {base nu rho : ℝ} (d : FixedData base nu rho)
    {H kappa R : ℝ} (hkappa : 0 ≤ kappa) (hR : 0 ≤ R)
    (r : Row d H) (col : Column d H) :
    (r.2.val 0 : ℝ) * Real.log 2 +
      (col.val 0 : ℝ) * ((d.K : ℝ) * kappa + Real.log (3 / 2)) +
      (∑ i : Fin d.m, (col.val i.succ : ℝ)) * Real.log (2 * ((d.K : ℝ) * R + 2)) ≤
        conjugateCost d kappa R * H := by
  have hc := InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) col
  have hs : 0 ≤ ∑ i : Fin d.m, fixedWeights d i * (col.val i.succ : ℝ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _))
  have hw : 0 ≤ (d.w0 : ℝ) * (col.val 0 : ℝ) := mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
  have h0 : (col.val 0 : ℝ) ≤ H / (d.w0 : ℝ) :=
    (le_div_iff₀ d.w0_pos).mpr (by nlinarith)
  have hsum : (∑ i : Fin d.m, (col.val i.succ : ℝ)) ≤ H / d.wstar := by
    apply (le_div_iff₀ d.wstar_pos).mpr
    have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (fixedWeights_lower d i) (Nat.cast_nonneg (col.val i.succ)))
    rw [← Finset.mul_sum] at hbound
    nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog32 : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogR : 0 ≤ Real.log (2 * ((d.K : ℝ) * R + 2)) :=
    Real.log_nonneg (by nlinarith [mul_nonneg (Nat.cast_nonneg d.K) hR])
  have h1 := mul_le_mul_of_nonneg_right (rowOrder_le d r) hlog2
  have h2 := mul_le_mul_of_nonneg_right h0
    (show 0 ≤ (d.K : ℝ) * kappa + Real.log (3 / 2 : ℝ) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hsum hlogR
  calc
    _ ≤ H / (d.v0 : ℝ) * Real.log 2 +
        H / (d.w0 : ℝ) * ((d.K : ℝ) * kappa + Real.log (3 / 2)) +
        H / d.wstar * Real.log (2 * ((d.K : ℝ) * R + 2)) := by linarith only [h1, h2, h3]
    _ = _ := by unfold conjugateCost; ring

theorem complexMinor_norm_le {base nu rho : ℝ} (d : FixedData base nu rho)
    (hnu : 0 ≤ nu) {H kappa R : ℝ} (hkappa : 0 ≤ kappa)
    (hR : |Real.log base| + 1 ≤ R) (z : ℂ)
    (hz : Real.log (max 1 ‖z‖) ≤ kappa) (selection : Row d H → Column d H) :
    ‖(complexMinor d H selection z).det‖ ≤
      (actualRowCount d H).factorial *
        Real.exp (conjugateCost d kappa R * H * (actualRowCount d H : ℝ)) := by
  have hR0 : 0 ≤ R := by linarith [abs_nonneg (Real.log base)]
  have hb := ConjugateDeterminant.norm_minor_le z
    (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (fun r : Row d H => r.1.val) (fun r => r.2.val 0) (fun r i => r.2.val i.succ)
    (fun c => (selection c).val 0) (fun c i => (selection c).val i.succ)
    hR0 (rationalCenters_norm_le d hnu hR) (fun r => r.1.isLt.le)
    (U := conjugateCost d kappa R) (H := H) (fun r c => by
      have hh := entry_cost_le d hkappa hR0 r (selection c)
      have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ (d.K : ℝ) by positivity)
      have hm' := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ ((selection c).val 0 : ℝ) by positivity)
      nlinarith only [hh, hm'])
  simpa only [complexMinor, ScaledMatrix.truncatedLogMatrix, ScaledMatrix.matrix,
    Matrix.submatrix, Matrix.of_apply, id_eq, ← pow_mul, actualRowCount] using hb

noncomputable def conjugateRemainder {base nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℝ :=
  Real.log (actualRowCount d H) / H

theorem complexMinor_log_bound {base nu rho : ℝ} (d : FixedData base nu rho)
    (hnu : 0 ≤ nu) {H kappa R : ℝ} (hH : 0 < H) (hkappa : 0 ≤ kappa)
    (hR : |Real.log base| + 1 ≤ R) (z : ℂ)
    (hz : Real.log (max 1 ‖z‖) ≤ kappa) (selection : Row d H → Column d H)
    (hdet : (complexMinor d H selection z).det ≠ 0) :
    Real.log ‖(complexMinor d H selection z).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      conjugateCost d kappa R + conjugateRemainder d H := by
  have hb := complexMinor_norm_le d hnu hkappa hR z hz selection
  have hf := mul_le_mul_of_nonneg_right (Collision.factorial_le_exp_card_log (actualRowCount d H))
    (Real.exp_pos (conjugateCost d kappa R * H * (actualRowCount d H : ℝ))).le
  have he := hb.trans hf
  rw [← Real.exp_add] at he
  have hl := Real.log_le_log (norm_pos_iff.mpr hdet) he
  rw [Real.log_exp] at hl
  have hM : (0 : ℝ) < actualRowCount d H := by exact_mod_cast actualRowCount_pos d hH
  apply (div_le_iff₀ (mul_pos hM hH)).mpr
  unfold conjugateRemainder
  have hid : (conjugateCost d kappa R + Real.log (actualRowCount d H) / H) *
      ((actualRowCount d H : ℝ) * H) =
      (actualRowCount d H : ℝ) * Real.log (actualRowCount d H) +
        conjugateCost d kappa R * H * (actualRowCount d H : ℝ) := by
    field_simp
    <;> ring
  rwa [hid]

theorem tendsto_conjugateRemainder {base nu rho : ℝ} (d : FixedData base nu rho) :
    Tendsto (conjugateRemainder d) atTop (𝓝 0) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hcount := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.base.theta
    (finiteDenominators d) hv ht (finiteDenominators_two_le d)
  have hlead : 0 < (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i) := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos)
        (pow_pos d.base.theta_pos _)
    · exact mul_pos (mul_pos (by positivity) d.v0_pos)
        (Finset.prod_pos (fun i _ => fixedWeights_pos d i))
  change Tendsto (fun H : ℝ => Real.log (actualRowCount d H) / H) atTop (𝓝 0)
  exact tendsto_log_div_of_normalized_pow hcount hlead

end OAI.AlgebraicLog.ConjugateAggregate

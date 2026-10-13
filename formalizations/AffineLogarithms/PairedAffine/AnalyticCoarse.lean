import PairedAffine.Data
import AlgebraicLog.ConjugateAggregate

namespace OAI.PairedAffine.AnalyticCoarse

open scoped BigOperators
open PiExponent Logarithm AlgebraicLog.DeterminantData
open AlgebraicLog.LiteralAnalytic AlgebraicLog.ConjugateAggregate

noncomputable section

theorem affine_centres_norm_le {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (hnu : 0 ≤ nu) (scale shift : ℂ) (i : Fin d.m) :
    ‖scale *
      (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - shift)‖ ≤
      ‖scale‖ * (|Real.log proxy| + 1 + ‖shift‖) := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg scale)
  exact (norm_sub_le _ _).trans
    (add_le_add (rationalCenters_norm_le d hnu le_rfl i) le_rfl)

/-- A fixed multiplier of at most two in the good-embedding errors is paid
for by a larger fixed centre budget at the coarse embeddings. This allows
the existing parameter-existence theorem to be reused without a new limit. -/
theorem conjugateCost_add_log_two_le {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    (kappa : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    conjugateCost d kappa R + Real.log 2 / d.wstar ≤
      conjugateCost d kappa (2 * R + 2) := by
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hpos : 0 < 2 * ((d.K : ℝ) * R + 2) := by positivity
  have hlog : Real.log (2 * ((d.K : ℝ) * R + 2)) + Real.log 2 ≤
      Real.log (2 * ((d.K : ℝ) * (2 * R + 2) + 2)) := by
    rw [← Real.log_mul hpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    apply Real.log_le_log (mul_pos hpos (by norm_num))
    nlinarith
  have hd := div_le_div_of_nonneg_right hlog d.wstar_pos.le
  rw [add_div] at hd
  unfold conjugateCost
  linarith

/-- The coarse bound depends only on bounds for the embedded base and
centres, and applies to the same column selection as the good embeddings. -/
theorem minor_norm_le {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    {H kappa R : ℝ} (hkappa : 0 ≤ kappa) (hR : 0 ≤ R)
    (z : ℂ) (centres : Fin d.m → ℂ)
    (hz : Real.log (max 1 ‖z‖) ≤ kappa) (hcentres : ∀ i, ‖centres i‖ ≤ R)
    (selection : Row d H → Column d H) :
    ‖(minor d H selection z centres).det‖ ≤
      (actualRowCount d H).factorial *
        Real.exp (conjugateCost d kappa R * H * (actualRowCount d H : ℝ)) := by
  have hb := AlgebraicLog.ConjugateDeterminant.norm_minor_le z centres
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (fun r : Row d H => r.1.val) (fun r => r.2.val 0) (fun r i => r.2.val i.succ)
    (fun c => (selection c).val 0) (fun c i => (selection c).val i.succ)
    hR hcentres (fun r => r.1.isLt.le)
    (U := conjugateCost d kappa R) (H := H) (fun r c => by
      have hh := entry_cost_le d hkappa hR r (selection c)
      have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ (d.K : ℝ) by positivity)
      have hm' := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ ((selection c).val 0 : ℝ) by positivity)
      nlinarith only [hh, hm'])
  simpa only [minor, matrix, ScaledMatrix.truncatedLogMatrix, ScaledMatrix.matrix,
    Matrix.submatrix, Matrix.of_apply, id_eq, ← pow_mul, actualRowCount] using hb

theorem minor_log_bound {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
    {H kappa R : ℝ} (hH : 0 < H) (hkappa : 0 ≤ kappa) (hR : 0 ≤ R)
    (z : ℂ) (centres : Fin d.m → ℂ)
    (hz : Real.log (max 1 ‖z‖) ≤ kappa) (hcentres : ∀ i, ‖centres i‖ ≤ R)
    (selection : Row d H → Column d H)
    (hdet : (minor d H selection z centres).det ≠ 0) :
    Real.log ‖(minor d H selection z centres).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      conjugateCost d kappa R + conjugateRemainder d H := by
  have hb := minor_norm_le d hkappa hR z centres hz hcentres selection
  have hf := mul_le_mul_of_nonneg_right
    (Collision.factorial_le_exp_card_log (actualRowCount d H))
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
    ring
  rwa [hid]

end
end OAI.PairedAffine.AnalyticCoarse

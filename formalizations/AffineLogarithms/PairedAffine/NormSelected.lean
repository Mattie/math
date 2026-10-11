import PairedAffine.Arithmetic
import PairedAffine.Norm

namespace OAI.PairedAffine.Norm

noncomputable section
open scoped BigOperators NumberField
open PiExponent AlgebraicLog.DeterminantData

variable {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
variable {F : Type*} [Field F] [NumberField F]

/-- The degree-four norm comparison for the actual affine minor. The good
and bad estimates are normalized by the same row count and height. -/
theorem paired_selected_normalized_bound
    (hdegree : Module.finrank ℚ F = 4)
    (a u v : F) (ha : IsIntegral ℤ a) (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (σ₀ : F →ₐ[ℚ] ℂ)
    (hne : (minor d H selection (σ₀ a)
      (fun i => σ₀ u * ((finiteNumerators d i : ℂ) /
        (finiteDenominators d i : ℂ) - σ₀ v))).det ≠ 0)
    (good : Finset (F →ₐ[ℚ] ℂ)) (hgood : good.card = 2)
    (goodBound badBound : ℝ)
    (hgoodBound : ∀ σ ∈ good,
      Real.log ‖(minor d H selection (σ a)
        (fun i => σ u * ((finiteNumerators d i : ℂ) /
          (finiteDenominators d i : ℂ) - σ v))).det‖ /
          ((actualRowCount d H : ℝ) * H) ≤ goodBound)
    (hbadBound : ∀ σ ∉ good,
      Real.log ‖(minor d H selection (σ a)
        (fun i => σ u * ((finiteNumerators d i : ℂ) /
          (finiteDenominators d i : ℂ) - σ v))).det‖ /
          ((actualRowCount d H : ℝ) * H) ≤ badBound) :
    -2 * (1 - actualMean d H) -
      2 * AlgebraicLog.SelectedArithmetic.arithmeticError d 1 - badBound ≤ goodBound := by
  classical
  obtain ⟨B, hB, hmap⟩ := Arithmetic.exists_integral_selected_minor d a u v ha hu hv H selection
  have hC := AlgebraicLog.SelectedArithmetic.selectedScalar_pos d 1 (by norm_num) H selection
  have hdet : B.det ≠ 0 := by
    intro hz
    have he := hmap σ₀
    rw [hz, map_zero] at he
    exact mul_ne_zero (by exact_mod_cast hC.ne') hne he.symm
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  have hM : (0 : ℝ) < actualRowCount d H := by
    exact_mod_cast PiExponent.MatrixArithmetic.actual_row_card_pos
      (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.v0_pos d.base.theta_pos hH hw
  have hscale := mul_pos hM hH
  apply paired_normalized_bound hdegree B.det hB hdet
    (fun σ => (minor d H selection (σ a)
      (fun i => σ u * ((finiteNumerators d i : ℂ) /
        (finiteDenominators d i : ℂ) - σ v))).det)
    (AlgebraicLog.SelectedArithmetic.selectedScalar d 1 H selection) hC hmap
    good hgood ((actualRowCount d H : ℝ) * H) (actualMean d H)
    (AlgebraicLog.SelectedArithmetic.arithmeticError d 1) goodBound badBound hscale
    (Arithmetic.log_selectedScalar_le d H hH selection)
  · intro σ hσ
    simpa only [mul_comm] using (div_le_iff₀ hscale).mp (hgoodBound σ hσ)
  · intro σ hσ
    simpa only [mul_comm] using (div_le_iff₀ hscale).mp (hbadBound σ hσ)

end
end OAI.PairedAffine.Norm

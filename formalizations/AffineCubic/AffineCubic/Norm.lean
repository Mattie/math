import PairedAffine.NormSelected

namespace OAI.AffineCubic
noncomputable section
open scoped BigOperators NumberField
open PiExponent AlgebraicLog.DeterminantData PairedAffine
variable {F : Type*} [Field F] [NumberField F]

/-- One analytic embedding in a cubic field leaves two coarse charges. -/
theorem cubic_normalized_bound
    (hdegree : Module.finrank ℚ F = 3)
    (z : F) (hz : IsIntegral ℤ z) (hne : z ≠ 0)
    (values : (F →ₐ[ℚ] ℂ) → ℂ) (C : ℚ) (hC : 0 < C)
    (himage : ∀ σ : F →ₐ[ℚ] ℂ, σ z = (C : ℂ) * values σ)
    (good : Finset (F →ₐ[ℚ] ℂ)) (hgood : good.card = 1)
    (scale b E_ar goodBound badBound : ℝ) (hscale : 0 < scale)
    (hclear : Real.log (C : ℝ) ≤ scale * (1 - b + E_ar))
    (hgoodBound : ∀ σ ∈ good, Real.log ‖values σ‖ ≤ scale * goodBound)
    (hbadBound : ∀ σ ∉ good, Real.log ‖values σ‖ ≤ scale * badBound) :
    -3 * (1 - b) - 3 * E_ar - 2 * badBound ≤ goodBound := by
  classical
  have hnorm := PairedAffine.Norm.literal_log_sum_nonneg z hz hne values C hC himage
  have hcard : Fintype.card (F →ₐ[ℚ] ℂ) = 3 := by simpa using hdegree
  have hbadcard : (Finset.univ \ good).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ good), Finset.card_univ, hcard, hgood]
  have hgs : (∑ σ ∈ good, Real.log ‖values σ‖) ≤ scale * goodBound := by
    calc
      _ ≤ ∑ _σ ∈ good, scale * goodBound := Finset.sum_le_sum hgoodBound
      _ = _ := by simp [hgood]
  have hbs : (∑ σ ∈ Finset.univ \ good, Real.log ‖values σ‖) ≤
      2 * scale * badBound := by
    calc
      _ ≤ ∑ _σ ∈ Finset.univ \ good, scale * badBound := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact hbadBound σ (Finset.mem_sdiff.mp hσ).2
      _ = _ := by simp [hbadcard]; ring
  have hsplit := Finset.sum_sdiff (Finset.subset_univ good)
    (f := fun σ => Real.log ‖values σ‖)
  rw [hdegree] at hnorm
  norm_num only [Nat.cast_ofNat] at hnorm
  have hscaled : 0 ≤ scale * (3 * (1 - b) + 3 * E_ar + 2 * badBound + goodBound) := by
    nlinarith [hsplit]
  have hsum : 0 ≤ 3 * (1 - b) + 3 * E_ar + 2 * badBound + goodBound :=
    (mul_nonneg_iff_of_pos_left hscale).mp hscaled
  linarith


variable {proxy nu rho : ℝ} (d : FixedData proxy nu rho)

/-- The degree-three norm comparison for the actual affine minor. The good
and bad estimates are normalized by the same row count and height. -/
theorem cubic_selected_normalized_bound
    (hdegree : Module.finrank ℚ F = 3)
    (a u v : F) (ha : IsIntegral ℤ a) (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (σ₀ : F →ₐ[ℚ] ℂ)
    (hne : (minor d H selection (σ₀ a)
      (fun i => σ₀ u * ((finiteNumerators d i : ℂ) /
        (finiteDenominators d i : ℂ) - σ₀ v))).det ≠ 0)
    (good : Finset (F →ₐ[ℚ] ℂ)) (hgood : good.card = 1)
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
    -3 * (1 - actualMean d H) -
      3 * AlgebraicLog.SelectedArithmetic.arithmeticError d 1 - 2 * badBound ≤ goodBound := by
  classical
  obtain ⟨B, hB, hmap⟩ := PairedAffine.Arithmetic.exists_integral_selected_minor d a u v ha hu hv H selection
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
  apply cubic_normalized_bound hdegree B.det hB hdet
    (fun σ => (minor d H selection (σ a)
      (fun i => σ u * ((finiteNumerators d i : ℂ) /
        (finiteDenominators d i : ℂ) - σ v))).det)
    (AlgebraicLog.SelectedArithmetic.selectedScalar d 1 H selection) hC hmap
    good hgood ((actualRowCount d H : ℝ) * H) (actualMean d H)
    (AlgebraicLog.SelectedArithmetic.arithmeticError d 1) goodBound badBound hscale
    (PairedAffine.Arithmetic.log_selectedScalar_le d H hH selection)
  · intro σ hσ
    simpa only [mul_comm] using (div_le_iff₀ hscale).mp (hgoodBound σ hσ)
  · intro σ hσ
    simpa only [mul_comm] using (div_le_iff₀ hscale).mp (hbadBound σ hσ)


end
end OAI.AffineCubic

import AlgebraicLog.QuadraticNorm

namespace OAI.PairedAffine.Norm

noncomputable section
open scoped BigOperators NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- Every complex value is an embedding of one integral field element,
after the same positive rational clearing factor. -/
theorem literal_log_sum_nonneg (z : F) (hz : IsIntegral ℤ z) (hne : z ≠ 0)
    (values : (F →ₐ[ℚ] ℂ) → ℂ) (C : ℚ) (hC : 0 < C)
    (himage : ∀ σ : F →ₐ[ℚ] ℂ, σ z = (C : ℂ) * values σ) :
    0 ≤ (Module.finrank ℚ F : ℝ) * Real.log (C : ℝ) +
      ∑ σ : F →ₐ[ℚ] ℂ, Real.log ‖values σ‖ := by
  classical
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hnormC : ‖(C : ℂ)‖ = (C : ℝ) := by
    rw [Complex.norm_ratCast, abs_of_pos hCpos]
  have hvalues (σ : F →ₐ[ℚ] ℂ) : values σ ≠ 0 := by
    have hn : σ z ≠ 0 := (map_ne_zero σ).mpr hne
    rw [himage σ] at hn
    exact (mul_ne_zero_iff.mp hn).2
  have hemb (σ : F →ₐ[ℚ] ℂ) : 0 < ‖σ z‖ :=
    norm_pos_iff.mpr ((map_ne_zero σ).mpr hne)
  have hn := Real.log_nonneg
    (AlgebraicLog.QuadraticNorm.one_le_prod_norm_embeddings hne hz)
  rw [Real.log_prod (fun σ _ => (hemb σ).ne')] at hn
  simp_rw [himage, norm_mul, hnormC,
    Real.log_mul hCpos.ne' (norm_ne_zero_iff.mpr (hvalues _))] at hn
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  simpa using hn

/-- Two analytic embeddings in a degree-four field divide the norm cost by
two. The other two embeddings are charged at their coarse uniform bound. -/
theorem paired_normalized_bound
    (hdegree : Module.finrank ℚ F = 4)
    (z : F) (hz : IsIntegral ℤ z) (hne : z ≠ 0)
    (values : (F →ₐ[ℚ] ℂ) → ℂ) (C : ℚ) (hC : 0 < C)
    (himage : ∀ σ : F →ₐ[ℚ] ℂ, σ z = (C : ℂ) * values σ)
    (good : Finset (F →ₐ[ℚ] ℂ)) (hgood : good.card = 2)
    (scale b E_ar goodBound badBound : ℝ) (hscale : 0 < scale)
    (hclear : Real.log (C : ℝ) ≤ scale * (1 - b + E_ar))
    (hgoodBound : ∀ σ ∈ good, Real.log ‖values σ‖ ≤ scale * goodBound)
    (hbadBound : ∀ σ ∉ good, Real.log ‖values σ‖ ≤ scale * badBound) :
    -2 * (1 - b) - 2 * E_ar - badBound ≤ goodBound := by
  classical
  have hnorm := literal_log_sum_nonneg z hz hne values C hC himage
  have hcard : Fintype.card (F →ₐ[ℚ] ℂ) = 4 := by simpa using hdegree
  have hbadcard : (Finset.univ \ good).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ good), Finset.card_univ, hcard, hgood]
  have hgs : (∑ σ ∈ good, Real.log ‖values σ‖) ≤ 2 * scale * goodBound := by
    calc
      _ ≤ ∑ _σ ∈ good, scale * goodBound := Finset.sum_le_sum hgoodBound
      _ = _ := by simp [hgood]; ring
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
  have hscaled : 0 ≤ 2 * scale * (2 * (1 - b) + 2 * E_ar + badBound + goodBound) := by
    nlinarith [hsplit]
  have hsum : 0 ≤ 2 * (1 - b) + 2 * E_ar + badBound + goodBound :=
    (mul_nonneg_iff_of_pos_left (show 0 < 2 * scale by positivity)).mp hscaled
  linarith

end
end OAI.PairedAffine.Norm

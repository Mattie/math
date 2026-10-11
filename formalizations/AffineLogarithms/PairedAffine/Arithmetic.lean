import PairedAffine.Data
import PairedAffine.ArithmeticClearing
import AlgebraicLog.SelectedArithmetic

namespace OAI.PairedAffine.Arithmetic

noncomputable section
open scoped BigOperators NumberField
open PiExponent Logarithm AlgebraicLog.DeterminantData

variable {proxy nu rho : ℝ} (d : FixedData proxy nu rho)
variable {F : Type*} [Field F] [NumberField F]

/-- Integral affine numerators use the same positive rational clearing scalar
as the original rational-centre proof with an integral exponential base. -/
theorem exists_integral_selected_minor
    (a u v : F) (ha : IsIntegral ℤ a) (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (H : ℝ) (selection : Row d H → Column d H) :
    ∃ B : Matrix (Row d H) (Row d H) F, IsIntegral ℤ B.det ∧
      ∀ σ : F →ₐ[ℚ] ℂ, σ B.det =
        (AlgebraicLog.SelectedArithmetic.selectedScalar d 1 H selection : ℂ) *
          (minor d H selection (σ a)
            (fun i => σ u * ((finiteNumerators d i : ℂ) /
              (finiteDenominators d i : ℂ) - σ v))).det := by
  classical
  let T := PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0
  let e : Fin d.m → ℕ := fun i =>
    ⌊H / PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i⌋₊
  let z : Fin d.m → F := fun i =>
    u * ((finiteNumerators d i : F) - (finiteDenominators d i : F) * v)
  have hz (i : Fin d.m) : IsIntegral ℤ (z i) :=
    hu.mul ((isIntegral_intCast _).sub ((isIntegral_natCast _).mul hv))
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  have hq (i : Fin d.m) : finiteDenominators d i ≠ 0 := by
    have := finiteDenominators_two_le d i
    omega
  have hγ (c : Row d H) (i : Fin d.m) : (selection c).val i.succ ≤ e i :=
    PiExponent.MatrixArithmetic.column_coordinate_le_floor d.w0_pos hw (selection c) i
  choose B hB hmap using fun r c : Row d H =>
    exists_integral_entry_lift a ha T (finiteDenominators d) e z hz hq
      r.1.val (r.2.val 0) ((selection c).val 0)
      (fun i => r.2.val i.succ) (fun i => (selection c).val i.succ) (hγ c)
  refine ⟨B, IsIntegral.det hB, fun σ => ?_⟩
  let A := minor d H selection (σ a)
    (fun i => σ u * ((finiteNumerators d i : ℂ) / (finiteDenominators d i : ℂ) - σ v))
  let rowScale : Row d H → ℂ := fun r =>
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) /
      (∏ i, (finiteDenominators d i : ℂ) ^ r.2.val i.succ)
  let colScale : Row d H → ℂ := fun c =>
    ∏ i, (finiteDenominators d i : ℂ) ^ (selection c).val i.succ
  have hcentres (i : Fin d.m) : σ (z i) / (finiteDenominators d i : ℂ) =
      σ u * ((finiteNumerators d i : ℂ) / (finiteDenominators d i : ℂ) - σ v) := by
    have hqC : (finiteDenominators d i : ℂ) ≠ 0 := by exact_mod_cast hq i
    simp only [z, map_mul, map_sub, map_intCast, map_natCast]
    field_simp
  have hmatrix : Matrix.map B σ.toRingHom =
      Matrix.of (fun r c => rowScale r * colScale c * A r c) := by
    ext r c
    change σ (B r c) = rowScale r * colScale c *
      minor d H selection (σ a)
        (fun i => σ u * ((finiteNumerators d i : ℂ) /
          (finiteDenominators d i : ℂ) - σ v)) r c
    rw [hmap r c σ]
    simp_rw [hcentres]
    rw [minor_entry]
  have hdet : σ (Matrix.det B) = (Matrix.map B σ.toRingHom).det :=
    RingHom.map_det σ.toRingHom B
  rw [hmatrix, AlgebraicLog.MatrixArithmetic.det_row_column_scale] at hdet
  rw [hdet]
  have hscalar : (∏ r, rowScale r) * (∏ c, colScale c) =
      (AlgebraicLog.SelectedArithmetic.selectedScalar d 1 H selection : ℂ) := by
    simp [AlgebraicLog.SelectedArithmetic.selectedScalar,
      AlgebraicLog.ArithmeticBounds.clearingScalar,
      AlgebraicLog.ArithmeticBounds.rowScale,
      AlgebraicLog.ArithmeticBounds.columnScale, rowScale, colScale, T, e]
  rw [hscalar]

theorem selected_minor_ne_zero_all
    (a u v : F) (ha : IsIntegral ℤ a) (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (H : ℝ) (selection : Row d H → Column d H) (σ₀ : F →ₐ[ℚ] ℂ)
    (hne : (minor d H selection (σ₀ a)
      (fun i => σ₀ u * ((finiteNumerators d i : ℂ) /
        (finiteDenominators d i : ℂ) - σ₀ v))).det ≠ 0)
    (σ : F →ₐ[ℚ] ℂ) :
    (minor d H selection (σ a)
      (fun i => σ u * ((finiteNumerators d i : ℂ) /
        (finiteDenominators d i : ℂ) - σ v))).det ≠ 0 := by
  obtain ⟨B, _, hmap⟩ := exists_integral_selected_minor d a u v ha hu hv H selection
  have hC := AlgebraicLog.SelectedArithmetic.selectedScalar_pos d 1 (by norm_num) H selection
  have hB : B.det ≠ 0 := by
    intro hz
    have he := hmap σ₀
    rw [hz, map_zero] at he
    exact mul_ne_zero (by exact_mod_cast hC.ne') hne he.symm
  have he : σ B.det ≠ 0 := (map_ne_zero σ).mpr hB
  rw [hmap σ] at he
  exact (mul_ne_zero_iff.mp he).2

/-- The numerical clearing bound depends only on the row and column indices,
so algebraic centres preserve the inverse-row saving without modification. -/
theorem log_selectedScalar_le (H : ℝ) (hH : 0 < H)
    (selection : Row d H → Column d H) :
    Real.log (AlgebraicLog.SelectedArithmetic.selectedScalar d 1 H selection : ℝ) ≤
      (actualRowCount d H : ℝ) * H *
        (1 - actualMean d H + AlgebraicLog.SelectedArithmetic.arithmeticError d 1) := by
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  have hM : (0 : ℝ) ≤ actualRowCount d H := Nat.cast_nonneg _
  have hd := mul_le_mul_of_nonneg_left
    (PiExponent.MatrixArithmetic.log_denominator_le d.F0 d.v0 H
      d.F0_pos.le d.v0_pos hH hw) hM
  have hc := AlgebraicLog.SelectedArithmetic.columnCost_le d 1 H selection
  have hr := AlgebraicLog.SelectedArithmetic.rowCost_lower d H hH
  rw [AlgebraicLog.SelectedArithmetic.log_selectedScalar d 1 (by norm_num) H selection]
  simp only [AlgebraicLog.SelectedArithmetic.arithmeticError] at ⊢
  norm_num only [Real.log_one, mul_zero, zero_div, add_zero] at hc ⊢
  nlinarith only [hd, hc, hr]

end
end OAI.PairedAffine.Arithmetic

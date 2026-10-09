import AlgebraicLog.ArithmeticBounds
import AlgebraicLog.DeterminantData

namespace OAI.AlgebraicLog.SelectedArithmetic
noncomputable section
open scoped BigOperators
open PiExponent Logarithm DeterminantData

local instance {F : Type*} [Field F] [NumberField F] : DecidableEq (F →ₐ[ℚ] ℂ) :=
  Classical.decEq _

variable {base nu rho : ℝ} (d : FixedData base nu rho)

def selectedScalar (D : ℕ) (H : ℝ) (selection : Row d H → Column d H) : ℚ :=
  ArithmeticBounds.clearingScalar D d.K
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (finiteDenominators d)
    (fun i => ⌊H / PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i⌋₊)
    (fun r i => r.2.val i.succ) (fun c => (selection c).val 0)
    (fun c i => (selection c).val i.succ)

theorem selectedScalar_pos (D : ℕ) (hD : 0 < D) (H : ℝ)
    (selection : Row d H → Column d H) : 0 < selectedScalar d D H selection :=
  ArithmeticBounds.clearingScalar_pos _ _ _ _ _ _ _ _ hD
    (fun i => lt_of_lt_of_le (by decide : 0 < 2) (finiteDenominators_two_le d i))

theorem exists_integral_selected_minor {F : Type*} [Field F] [NumberField F]
    (a : F) (D : ℕ) (ha : IsIntegral ℤ ((D : F) * a)) (H : ℝ)
    (selection : Row d H → Column d H) :
    ∃ B : Matrix (Row d H) (Row d H) F, IsIntegral ℤ B.det ∧
      ∀ σ : F →ₐ[ℚ] ℂ, σ B.det =
        (selectedScalar d D H selection : ℂ) * (complexMinor d H selection (σ a)).det := by
  classical
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  obtain ⟨B, hB, hmap⟩ := MatrixArithmetic.exists_integral_minor_det_lift a D d.K ha
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (finiteDenominators d)
    (fun i => ⌊H / PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i⌋₊)
    (finiteNumerators d) (fun i => by have := finiteDenominators_two_le d i; omega)
    (fun r : Row d H => r.1.val) (fun r => r.2.val 0) (fun r i => r.2.val i.succ)
    (fun c => (selection c).val 0) (fun c i => (selection c).val i.succ)
    (fun r => r.1.isLt.le)
    (fun c => PiExponent.MatrixArithmetic.column_coordinate_le_floor d.w0_pos hw (selection c))
  refine ⟨B, hB, fun σ => ?_⟩
  have hm : complexMinor d H selection (σ a) = Matrix.of (fun r c : Row d H =>
      (σ a) ^ (r.1.val * (selection c).val 0) *
      InterpolationMatrix.entry (fun i => (finiteNumerators d i : ℂ) / (finiteDenominators d i : ℂ))
        (fun i => InterpolationMatrix.truncatedLog
          (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i))
        r.1.val (r.2.val 0) (fun i => r.2.val i.succ)
        ((selection c).val 0) (fun i => (selection c).val i.succ)) := by
    ext r c
    simp only [complexMinor, ScaledMatrix.truncatedLogMatrix, ScaledMatrix.matrix,
      Matrix.submatrix_apply, Matrix.of_apply, id_eq, ← pow_mul]
    rfl
  rw [hm]
  exact hmap σ

def columnCost (D : ℕ) (H : ℝ) (selection : Row d H → Column d H) : ℝ :=
  ∑ c, ((d.K : ℝ) * ((selection c).val 0 : ℝ) * Real.log D +
    ∑ i, ((selection c).val i.succ : ℝ) * Real.log (finiteDenominators d i))

theorem log_selectedScalar (D : ℕ) (hD : 0 < D) (H : ℝ)
    (selection : Row d H → Column d H) :
    Real.log (selectedScalar d D H selection : ℝ) =
      (actualRowCount d H : ℝ) * Real.log
        (PiExponent.MatrixArithmetic.denominator (finiteDenominators d)
          (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) H) +
      columnCost d D H selection -
        PiExponent.MatrixArithmetic.rowCost d.K d.v0 d.base.theta (finiteDenominators d) H := by
  exact ArithmeticBounds.log_clearingScalar _ _ _ _ _ _ _ _ hD
    (fun i => lt_of_lt_of_le (by decide : 0 < 2) (finiteDenominators_two_le d i))

theorem columnCost_le (D : ℕ) (H : ℝ) (selection : Row d H → Column d H) :
    columnCost d D H selection ≤ (actualRowCount d H : ℝ) * H *
      (1 + (d.K : ℝ) * Real.log D / (d.w0 : ℝ)) := by
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  have hc (c : Row d H) :
      (d.K : ℝ) * ((selection c).val 0 : ℝ) * Real.log D +
        ∑ i, ((selection c).val i.succ : ℝ) * Real.log (finiteDenominators d i) ≤
      H * (1 + (d.K : ℝ) * Real.log D / (d.w0 : ℝ)) := by
    have hcol := InterpolationMatrix.column_weight_le d.w0_pos hw (selection c)
    have hs : 0 ≤ ∑ i, PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i *
        ((selection c).val i.succ : ℝ) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (Nat.cast_nonneg _))
    have hh : ((selection c).val 0 : ℝ) ≤ H / (d.w0 : ℝ) := by
      apply (le_div_iff₀ d.w0_pos).mpr
      nlinarith only [hcol, hs]
    have he := PiExponent.MatrixArithmetic.column_log_cost_le_H
      (finiteDenominators d) (finiteDenominators_two_le d) d.w0_pos (selection c)
    have hb := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (Nat.cast_nonneg d.K) (Real.log_natCast_nonneg D))
    calc
      _ ≤ H + (d.K : ℝ) * Real.log D * (H / (d.w0 : ℝ)) := by nlinarith only [he, hb]
      _ = _ := by ring
  calc
    _ ≤ ∑ _c : Row d H, H * (1 + (d.K : ℝ) * Real.log D / (d.w0 : ℝ)) :=
      Finset.sum_le_sum (fun c _ => hc c)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]; ring

theorem quadratic_selected_log_lower {F : Type*} [Field F] [NumberField F]
    (a : F) (D : ℕ) (hD : 0 < D) (ha : IsIntegral ℤ ((D : F) * a))
    (hdegree : Module.finrank ℚ F = 2) (H : ℝ) (selection : Row d H → Column d H)
    (σ₀ : F →ₐ[ℚ] ℂ) (hne : (complexMinor d H selection (σ₀ a)).det ≠ 0) :
    -2 * Real.log (selectedScalar d D H selection : ℝ) -
      ∑ σ ∈ Finset.univ.erase σ₀, Real.log ‖(complexMinor d H selection (σ a)).det‖ ≤
        Real.log ‖(complexMinor d H selection (σ₀ a)).det‖ := by
  classical
  obtain ⟨B, hB, hmap⟩ := exists_integral_selected_minor d a D ha H selection
  have hC := selectedScalar_pos d D hD H selection
  have hdet : B.det ≠ 0 := by
    intro hz
    have he := hmap σ₀
    rw [hz, map_zero] at he
    exact mul_ne_zero (by exact_mod_cast hC.ne') hne he.symm
  exact QuadraticNorm.quadratic_literal_minor_log_bound hdegree B hB hdet
    (fun σ => complexMinor d H selection (σ a)) _ hC hmap σ₀

def arithmeticError (D : ℕ) : ℝ :=
  Arithmetic.lcmConstant * d.F0 * d.m / (d.v0 : ℝ) +
    Arithmetic.lcmConstant * ∑ i, 1 / PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i +
    (d.base.theta : ℝ) / d.wstar + (d.K : ℝ) * Real.log D / (d.w0 : ℝ)

theorem complexMinor_det_ne_zero_all {F : Type*} [Field F] [NumberField F]
    (a : F) (D : ℕ) (hD : 0 < D) (ha : IsIntegral ℤ ((D : F) * a))
    (H : ℝ) (selection : Row d H → Column d H) (σ₀ : F →ₐ[ℚ] ℂ)
    (hne : (complexMinor d H selection (σ₀ a)).det ≠ 0) (σ : F →ₐ[ℚ] ℂ) :
    (complexMinor d H selection (σ a)).det ≠ 0 := by
  classical
  obtain ⟨B, _, hmap⟩ := exists_integral_selected_minor d a D ha H selection
  have hC := selectedScalar_pos d D hD H selection
  have hdet : B.det ≠ 0 := by
    intro hz
    have he := hmap σ₀
    rw [hz, map_zero] at he
    exact mul_ne_zero (by exact_mod_cast hC.ne') hne he.symm
  have he : σ B.det ≠ 0 := (map_ne_zero σ).mpr hdet
  rw [hmap σ] at he
  exact (mul_ne_zero_iff.mp he).2

theorem rowCost_lower (H : ℝ) (hH : 0 < H) :
    (actualRowCount d H : ℝ) * H * actualMean d H -
      (actualRowCount d H : ℝ) * H * ((d.base.theta : ℝ) / d.wstar) ≤
        PiExponent.MatrixArithmetic.rowCost d.K d.v0 d.base.theta (finiteDenominators d) H := by
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  have hM : (0 : ℝ) < actualRowCount d H := by
    exact_mod_cast PiExponent.MatrixArithmetic.actual_row_card_pos
      (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.v0_pos d.base.theta_pos hH hw
  have hrow (r : Row d H) := Arithmetic.row_log_cost_lower Finset.univ
    (fun i => r.2.val i.succ) (finiteDenominators d) d.wstar (H * d.base.theta)
    d.wstar_pos (fun i _ => by
      change d.wstar ≤ PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i
      rw [logWeights_eq]
      exact d.wstar_lower i)
    (PiExponent.MatrixArithmetic.row_weighted_cost_le d.v0_pos d.base.theta_pos hw r)
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hrow r)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hr
  have hb : (actualRowCount d H : ℝ) * H * actualMean d H =
      PiExponent.MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H := by
    unfold actualMean PiExponent.MatrixArithmetic.meanRowWeight
    change (actualRowCount d H : ℝ) * H * (_ / ((actualRowCount d H : ℝ) * H)) = _
    rw [mul_div_cancel₀ _ (mul_pos hM hH).ne']
  rw [hb]
  simpa only [PiExponent.MatrixArithmetic.rowWeightedSum, PiExponent.MatrixArithmetic.rowCost,
    PiExponent.MatrixArithmetic.logWeights, actualRowCount, mul_div_assoc, mul_assoc] using hr

/-- The complete normalized arithmetic side for the literal selected minor.
The sole remaining analytic input is the upper bound on the other embedding. -/
theorem normalized_selected_lower {F : Type*} [Field F] [NumberField F]
    (a : F) (D : ℕ) (hD : 0 < D) (ha : IsIntegral ℤ ((D : F) * a))
    (hdegree : Module.finrank ℚ F = 2) (H : ℝ) (hH : 0 < H)
    (selection : Row d H → Column d H) (σ₀ : F →ₐ[ℚ] ℂ)
    (hne : (complexMinor d H selection (σ₀ a)).det ≠ 0) (U remainder : ℝ)
    (hconj : (∑ σ ∈ Finset.univ.erase σ₀,
      Real.log ‖(complexMinor d H selection (σ a)).det‖) ≤
        (actualRowCount d H : ℝ) * H * (U + remainder)) :
    -2 * (1 - actualMean d H) - 2 * arithmeticError d D - U - remainder ≤
      Real.log ‖(complexMinor d H selection (σ₀ a)).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  classical
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  have hM : (0 : ℝ) < actualRowCount d H := by
    exact_mod_cast PiExponent.MatrixArithmetic.actual_row_card_pos
      (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.v0_pos d.base.theta_pos hH hw
  have hc := quadratic_selected_log_lower d a D hD ha hdegree H selection σ₀ hne
  rw [log_selectedScalar d D hD H selection] at hc
  have hb := ArithmeticBounds.normalized_quadratic_bound _ _ _ _ _ _ _ _ _ _ _ U remainder hM hH hc
    (PiExponent.MatrixArithmetic.log_denominator_le d.F0 d.v0 H d.F0_pos.le d.v0_pos hH hw)
    (columnCost_le d D H selection) (rowCost_lower d H hH) hconj
  simpa only [arithmeticError, add_assoc] using hb

end
end OAI.AlgebraicLog.SelectedArithmetic

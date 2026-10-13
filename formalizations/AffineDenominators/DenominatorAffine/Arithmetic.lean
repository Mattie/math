import PairedAffine.Data
import AlgebraicLog.SelectedArithmetic

namespace OAI.DenominatorAffine.Arithmetic
noncomputable section
open scoped BigOperators NumberField
open PairedAffine PiExponent Logarithm AlgebraicLog.DeterminantData
variable {proxy nu rho : ℝ} (d : FixedData proxy nu rho)

/-- The numerical clearing bound depends only on the row and column indices,
so the base denominator preserves the inverse-row saving. -/
theorem log_selectedScalar_le (D : ℕ) (hD : 0 < D) (H : ℝ) (hH : 0 < H)
    (selection : Row d H → Column d H) :
    Real.log (AlgebraicLog.SelectedArithmetic.selectedScalar d D H selection : ℝ) ≤
      (actualRowCount d H : ℝ) * H *
        (1 - actualMean d H + AlgebraicLog.SelectedArithmetic.arithmeticError d D) := by
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i :=
    fun i => PiExponent.MatrixArithmetic.ceil_log_weight_pos (finiteDenominators_two_le d i)
  have hM : (0 : ℝ) ≤ actualRowCount d H := Nat.cast_nonneg _
  have hd := mul_le_mul_of_nonneg_left
    (PiExponent.MatrixArithmetic.log_denominator_le d.F0 d.v0 H
      d.F0_pos.le d.v0_pos hH hw) hM
  have hc := AlgebraicLog.SelectedArithmetic.columnCost_le d D H selection
  have hr := AlgebraicLog.SelectedArithmetic.rowCost_lower d H hH
  rw [AlgebraicLog.SelectedArithmetic.log_selectedScalar d D hD H selection]
  simp only [AlgebraicLog.SelectedArithmetic.arithmeticError] at ⊢
  nlinarith only [hd, hc, hr]

end
end OAI.DenominatorAffine.Arithmetic

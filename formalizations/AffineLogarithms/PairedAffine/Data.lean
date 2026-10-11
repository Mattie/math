import AlgebraicLog.DeterminantData

namespace OAI.PairedAffine

open PiExponent Logarithm AlgebraicLog.DeterminantData

noncomputable section

/-- The approximation data determine the indices and truncations. The base
and additive centres are supplied separately so every field embedding can
evaluate the same matrix. -/
def matrix {proxy nu rho : ℝ} (d : FixedData proxy nu rho) (H : ℝ)
    (z : ℂ) (centres : Fin d.m → ℂ) : Matrix (Row d H) (Column d H) ℂ :=
  ScaledMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (PiExponent.MatrixArithmetic.logWeights (finiteDenominators d)) H
    (fun j => z ^ j.val) centres
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

/-- A fixed column selection is retained while the base and centres vary. -/
def minor {proxy nu rho : ℝ} (d : FixedData proxy nu rho) (H : ℝ)
    (selection : Row d H → Column d H) (z : ℂ) (centres : Fin d.m → ℂ) :
    Matrix (Row d H) (Row d H) ℂ :=
  (matrix d H z centres).submatrix id selection

theorem minor_entry {proxy nu rho : ℝ} (d : FixedData proxy nu rho) (H : ℝ)
    (selection : Row d H → Column d H) (z : ℂ) (centres : Fin d.m → ℂ)
    (r c : Row d H) :
    minor d H selection z centres r c =
      z ^ (r.1.val * (selection c).val 0) *
        InterpolationMatrix.entry centres
          (fun i => InterpolationMatrix.truncatedLog
            (PiExponent.MatrixArithmetic.truncationOrders
              (finiteDenominators d) d.F0 d.v0 i))
          r.1.val (r.2.val 0) (fun i => r.2.val i.succ)
          ((selection c).val 0) (fun i => (selection c).val i.succ) := by
  simp only [minor, matrix, ScaledMatrix.truncatedLogMatrix,
    ScaledMatrix.matrix, Matrix.submatrix_apply, id_eq, ← pow_mul]

end
end OAI.PairedAffine

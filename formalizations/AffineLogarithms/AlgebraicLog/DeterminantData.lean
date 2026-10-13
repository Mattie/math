import AlgebraicLog.AnalyticData
import Logarithm.ScaledArithmetic

namespace OAI

open Filter
open scoped Topology

namespace AlgebraicLog.DeterminantData
open PiExponent Logarithm

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

abbrev FixedData (base : ℝ) (nu rho : ℝ) := AnalyticData (Real.log base) nu rho

noncomputable def finiteNumerators {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) : Fin d.m → ℕ :=
  fun i => d.q i.val

theorem finiteDenominators_two_le {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (i : Fin d.m) :
    PiExponent.MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

abbrev Row {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (PiExponent.MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (PiExponent.MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  ScaledMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (PiExponent.MatrixArithmetic.logWeights (finiteDenominators d)) H
    (fun j => (base : ℂ) ^ j.val) (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  (actualMatrix d H).submatrix id selection

/-- The same selected minor at an arbitrary complex value of the algebraic
base. Only the base is varied; the rows, columns and rational centres are fixed. -/
noncomputable def complexMinor {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ)
    (selection : Row d H → Column d H) (z : ℂ) : Matrix (Row d H) (Row d H) ℂ :=
  (ScaledMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (PiExponent.MatrixArithmetic.logWeights (finiteDenominators d)) H
    (fun j => z ^ j.val) (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (PiExponent.MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)).submatrix id selection

theorem complexMinor_at_base {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ)
    (selection : Row d H → Column d H) :
    complexMinor d H selection (base : ℂ) = actualMinor d H selection := rfl

noncomputable def actualMean {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℝ :=
  PiExponent.MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℕ :=
  (realWeightedSimplex (PiExponent.MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

theorem actualMean_bounds {base : ℝ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  exact ⟨PiExponent.MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    PiExponent.MatrixArithmetic.meanRowWeight_le_theta (finiteDenominators d)
      (finiteDenominators_two_le d) (Nat.zero_lt_of_lt d.K_pos)
      d.v0_pos d.base.theta_pos hH⟩


end AlgebraicLog.DeterminantData
end OAI

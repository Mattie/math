import Logarithm.AdmissibleParameters
import Logarithm.ScaledArithmetic

namespace OAI

open Filter
open scoped Topology

namespace Logarithm.DeterminantData
open PiExponent

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

abbrev FixedData (base : ℚ) (nu rho : ℝ) := Logarithm.AdmissibleParameters (Real.log (base : ℝ)) nu Arithmetic.lcmConstant collisionConstant rho (Real.log base.den)

noncomputable def finiteNumerators {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) : Fin d.m → ℕ :=
  fun i => d.q i.val

theorem finiteDenominators_two_le {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

abbrev Row {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  ScaledMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (fun j => (base : ℂ) ^ j.val) (ScaledArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  ScaledArithmetic.selectedMinor base d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def actualMean {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

theorem actual_minor_arithmetic_lower_bound {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  have hh := ScaledArithmetic.selectedMinor_arithmetic_lower_bound base
    (finiteNumerators d) (finiteDenominators d) (finiteDenominators_two_le d)
    (Nat.zero_lt_of_lt d.K_pos) d.w0_pos d.v0_pos d.base.theta_pos d.F0_pos.le hH
    d.wstar_pos (fun i => by rw [logWeights_eq]; exact d.wstar_lower i) selection hdet
  simpa only [actualMinor, actualMean, actualRowCount,
    Logarithm.AdmissibleParameters.arithmeticError, logWeights_eq, mul_comm] using hh

theorem actualMean_bounds {base : ℚ} {nu rho : ℝ} (d : FixedData base nu rho) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  exact ⟨MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    MatrixArithmetic.meanRowWeight_le_theta (finiteDenominators d)
      (finiteDenominators_two_le d) (Nat.zero_lt_of_lt d.K_pos)
      d.v0_pos d.base.theta_pos hH⟩


end Logarithm.DeterminantData
end OAI

import Logarithm.AdmissibleParameters
import QuadraticImag5.ScaledArithmetic

namespace OAI

open Filter
open scoped Topology

namespace QuadraticImag5.DeterminantData
open Logarithm PiExponent

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

abbrev FixedData (base : PeriodData) (nu : ℝ) := Logarithm.AdmissibleParameters base.angle nu (Arithmetic.lcmConstant + Real.log 3) collisionConstant base.radius (Real.log base.den)

/-- Rotate the rational approximations without changing the interpolation weights. -/
noncomputable def toGeometryData {base : PeriodData} {nu : ℝ}
    (d : FixedData base nu) : Logarithm.GeometryData where
  m := d.m
  K := d.K
  curveDegreeWeights := d.curveDegreeWeights
  curveJetWeights := d.curveJetWeights
  curveDegreeWeights_pos := d.curveDegreeWeights_pos
  curveJetWeights_pos := d.curveJetWeights_pos
  sigma := d.sigma
  sigma_pos := d.sigma_pos
  curveY := fun j => base.value ^ j.val
  curveY_ne_zero := fun _ => pow_ne_zero _ base.value_ne_zero
  curveY_injective := fun _ _ h => Fin.ext (base.powers_injective h)
  curveCenters := fun j i =>
    (j.val : ℂ) * ((rotation * (d.p i.val : ℂ)) / (d.q i.val : ℂ))
  curve_volume := d.curve_volume
  curve_coordinate_ratio := d.curve_coordinate_ratio
  curve_separated_weight_products := d.curve_separated_weight_products

noncomputable def finiteNumerators {base : PeriodData} {nu : ℝ} (d : FixedData base nu) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {base : PeriodData} {nu : ℝ} (d : FixedData base nu) : Fin d.m → ℕ :=
  fun i => d.q i.val

theorem finiteDenominators_two_le {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

abbrev Row {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  ScaledMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (fun j => base.value ^ j.val) (ScaledArithmetic.imaginaryCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  ScaledArithmetic.selectedMinor base d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def actualMean {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {base : PeriodData} {nu : ℝ} (d : FixedData base nu) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

theorem actual_minor_arithmetic_lower_bound {base : PeriodData} {nu : ℝ} (d : FixedData base nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - (d.arithmeticError - Real.log 3 / d.wstar) ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  have hh := ScaledArithmetic.selectedMinor_arithmetic_lower_bound base
    (finiteNumerators d) (finiteDenominators d) (finiteDenominators_two_le d)
    (Nat.zero_lt_of_lt d.K_pos) d.w0_pos d.v0_pos d.base.theta_pos d.F0_pos.le hH
    d.wstar_pos (fun i => by rw [logWeights_eq]; exact d.wstar_lower i) selection hdet
  have hsum : 1 / d.wstar ≤ ∑ i : Fin d.m, 1 / d.x (i.val + 1) := by
    obtain ⟨i, hi⟩ := d.wstar_attained
    rw [hi]
    exact Finset.single_le_sum (f := fun j : Fin d.m => 1 / d.x (j.val + 1))
      (fun j _ => div_nonneg zero_le_one (zero_le_one.trans (d.x_one_le (j.val + 1))))
      (Finset.mem_univ i)
  have hbonus : 0 ≤ Real.log 3 * d.F0 * (d.m : ℝ) / (d.v0 : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.log_nonneg (by norm_num)) d.F0_pos.le)
      (Nat.cast_nonneg _)) d.v0_pos.le
  have hreserve := mul_le_mul_of_nonneg_left hsum
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
  simp only [logWeights_eq] at hh
  unfold Logarithm.AdmissibleParameters.arithmeticError
  change _ ≤ Real.log ‖(ScaledArithmetic.selectedMinor base d.K d.w0 d.v0 d.base.theta
    d.F0 H (finiteNumerators d) (finiteDenominators d) selection).det‖ /
    ((Fintype.card (InterpolationMatrix.Row d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) : ℝ) * H)
  dsimp [actualMean]
  ring_nf at hh hreserve hbonus ⊢
  linarith

theorem actualMean_bounds {base : PeriodData} {nu : ℝ} (d : FixedData base nu) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  exact ⟨MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    MatrixArithmetic.meanRowWeight_le_theta (finiteDenominators d)
      (finiteDenominators_two_le d) (Nat.zero_lt_of_lt d.K_pos)
      d.v0_pos d.base.theta_pos hH⟩


end QuadraticImag5.DeterminantData
end OAI

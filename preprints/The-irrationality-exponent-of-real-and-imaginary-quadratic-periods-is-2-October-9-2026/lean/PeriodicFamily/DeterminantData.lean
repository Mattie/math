import PeriodicGeometry.GeometryData
import Logarithm.AdmissibleParameters
import PeriodicFamily.ScaledArithmetic

open OAI.PeriodicFamily

namespace OAI

open Filter
open scoped Topology

namespace PeriodicFamily.DeterminantData
variable {rad : ℕ} [Fact (0 < rad)]
open Logarithm PiExponent

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

abbrev FixedData (base : PeriodData rad) (nu : ℝ) := Logarithm.AdmissibleParameters base.angle nu (PeriodicFamily.Arithmetic.lcmConstant + slopeCost rad) collisionConstant base.radius (Real.log base.den)

/-- Rotate the rational approximations without changing the interpolation weights. -/
noncomputable def toGeometryData {base : PeriodData rad} {nu : ℝ}
    (d : FixedData base nu) : PiExponent.PeriodicGeometryData where
  m := d.m
  m_pos := by have := d.m_pos; omega
  K := d.K
  curveDegreeWeights := d.curveDegreeWeights
  curveJetWeights := d.curveJetWeights
  curveDegreeWeights_pos := d.curveDegreeWeights_pos
  curveJetWeights_pos := d.curveJetWeights_pos
  sigma := d.sigma
  sigma_pos := d.sigma_pos
  curveCenters := fun j i =>
    (j.val : ℂ) * (((rotation rad) * (d.p i.val : ℂ)) / (d.q i.val : ℂ))
  curveCenters_injective := by
    intro i j k h
    have hp : (d.p i.val : ℂ) ≠ 0 := by exact_mod_cast (d.approximations i.val).2.1
    have hq : (d.q i.val : ℂ) ≠ 0 := by
      exact_mod_cast (show d.q i.val ≠ 0 by have := (d.approximations i.val).1; omega)
    have hr : (rotation rad) * (d.p i.val : ℂ) / (d.q i.val : ℂ) ≠ 0 :=
      div_ne_zero (mul_ne_zero rotation_ne_zero hp) hq
    have he := mul_right_cancel₀ hr h
    apply Fin.ext
    exact_mod_cast he
  curve_volume := d.curve_volume
  curve_fibre_volume := d.curve_fibre_volume
  curve_coordinate_ratio := d.curve_coordinate_ratio
  curve_separated_weight_products := d.curve_separated_weight_products

noncomputable def finiteNumerators {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) : Fin d.m → ℕ :=
  fun i => d.q i.val

theorem finiteDenominators_two_le {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

abbrev Row {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  ScaledMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (fun j => base.value ^ j.val) (ScaledArithmetic.imaginaryCenters (rad := rad) (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  ScaledArithmetic.selectedMinor base d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def actualMean {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

theorem actual_minor_arithmetic_lower_bound {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - (d.arithmeticError - slopeCost rad / d.wstar) ≤
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
  have hbonus : 0 ≤ slopeCost rad * d.F0 * (d.m : ℝ) / (d.v0 : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (slopeCost_nonneg rad) d.F0_pos.le)
      (Nat.cast_nonneg _)) d.v0_pos.le
  have hreserve := mul_le_mul_of_nonneg_left hsum
    (slopeCost_nonneg rad)
  simp only [logWeights_eq] at hh
  unfold Logarithm.AdmissibleParameters.arithmeticError
  change _ ≤ Real.log ‖(ScaledArithmetic.selectedMinor base d.K d.w0 d.v0 d.base.theta
    d.F0 H (finiteNumerators d) (finiteDenominators d) selection).det‖ /
    ((Fintype.card (InterpolationMatrix.Row d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) : ℝ) * H)
  dsimp [actualMean]
  ring_nf at hh hreserve hbonus ⊢
  linarith

theorem actualMean_bounds {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  exact ⟨MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    MatrixArithmetic.meanRowWeight_le_theta (finiteDenominators d)
      (finiteDenominators_two_le d) (Nat.zero_lt_of_lt d.K_pos)
      d.v0_pos d.base.theta_pos hH⟩


end PeriodicFamily.DeterminantData
end OAI

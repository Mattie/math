import AlgebraicLog.CurveWeights
import Logarithm.GeometryData
import Logarithm.RationalCenters

namespace OAI.AlgebraicLog.AdmissibleParameters
open Logarithm
noncomputable section
variable {ξ nu Lambda c rho delta kappa R : ℝ}
variable (d : AdmissibleParameters ξ nu Lambda c rho delta kappa R)

theorem real_power_centers_nonzero (a : ℝ) (ha : 0 < a) (K : ℕ) :
    ∀ j : Fin K, (a : ℂ) ^ j.val ≠ 0 := by
  intro j
  apply pow_ne_zero
  exact_mod_cast ha.ne'

theorem real_power_centers_injective (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1)
    (K : ℕ) : Function.Injective (fun j : Fin K => (a : ℂ) ^ j.val) := by
  intro j k h
  dsimp only at h
  have hq : a ^ j.val = a ^ k.val := by exact_mod_cast h
  exact Fin.ext (pow_right_injective₀ ha ha1 hq)
/-- The selected approximation weights and rational-power centers really
satisfy the checked geometric hypotheses. No interpolation premise is added. -/
def toGeometryData (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) : GeometryData where
  m := d.m
  K := d.K
  curveDegreeWeights := d.curveDegreeWeights
  curveJetWeights := d.curveJetWeights
  curveDegreeWeights_pos := d.curveDegreeWeights_pos
  curveJetWeights_pos := d.curveJetWeights_pos
  sigma := d.sigma
  sigma_pos := d.sigma_pos
  curveY := fun j => (a : ℂ) ^ j.val
  curveY_ne_zero := real_power_centers_nonzero a ha d.K
  curveY_injective := real_power_centers_injective a ha ha1 d.K
  curveCenters := fun j i => (j.val : ℂ) * (d.p i.val : ℂ) / (d.q i.val : ℂ)
  curve_volume := d.curve_volume
  curve_coordinate_ratio := d.curve_coordinate_ratio
  curve_separated_weight_products := d.curve_separated_weight_products

end
end OAI.AlgebraicLog.AdmissibleParameters

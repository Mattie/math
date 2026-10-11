import Logarithm.CurveWeights
import Logarithm.GeometryData
import Logarithm.RationalCenters

namespace OAI.Logarithm.AdmissibleParameters
noncomputable section
variable {ξ nu Lambda c rho delta : ℝ}
variable (d : AdmissibleParameters ξ nu Lambda c rho delta)

/-- The selected approximation weights and rational-power centers really
satisfy the checked geometric hypotheses. No interpolation premise is added. -/
def toGeometryData (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1) : GeometryData where
  m := d.m
  K := d.K
  curveDegreeWeights := d.curveDegreeWeights
  curveJetWeights := d.curveJetWeights
  curveDegreeWeights_pos := d.curveDegreeWeights_pos
  curveJetWeights_pos := d.curveJetWeights_pos
  sigma := d.sigma
  sigma_pos := d.sigma_pos
  curveY := fun j => (a : ℂ) ^ j.val
  curveY_ne_zero := rational_power_centers_nonzero a ha d.K
  curveY_injective := rational_power_centers_injective a ha ha1 d.K
  curveCenters := fun j i => (j.val : ℂ) * (d.p i.val : ℂ) / (d.q i.val : ℂ)
  curve_volume := d.curve_volume
  curve_coordinate_ratio := d.curve_coordinate_ratio
  curve_separated_weight_products := d.curve_separated_weight_products

end
end OAI.Logarithm.AdmissibleParameters

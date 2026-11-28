import PiTwoCaseBridge.CurveGeometry
import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality

namespace OAI.PiExponent.AdmissibleParameters

noncomputable section
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

/-- The π construction supplies a special case of the general bridge data. -/
def bridgeData : BridgeData where
  m := d.m
  K := d.K
  W := d.curveDegreeWeights
  V := d.curveJetWeights
  W_pos := d.curveDegreeWeights_pos
  V_pos := d.curveJetWeights_pos
  centers := d.curveCenters
  centers_injective := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    intro j k h
    exact d.curveCenters_injective i (congrFun h i)

theorem bridgeData_curveBound : BridgeGeometry.CurveBound d.bridgeData (1 + d.sigma) := by
  intro E _ _ _ y x hgen htrdeg
  simpa only [BridgeGeometry.contactSum, BridgeGeometry.poleDegree, bridgeData,
    Rat.cast_add, Rat.cast_one] using
    d.exact_weighted_curve_inequality y x hgen htrdeg

end
end OAI.PiExponent.AdmissibleParameters

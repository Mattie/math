import Logarithm.CurveModelDegrees
import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem

namespace OAI
noncomputable section
namespace Logarithm.BlowupMargin
open PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
open BlowupGeometry
variable (d : GeometryData)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := CurveModel.existsModelData d C hn hm
  exact ⟨CurveModel.degreeData d C r⟩

end Logarithm.BlowupMargin

namespace Logarithm.BlowupGeometry
open AlgebraicGeometry
open PiExponent PiExponentSeshadri.Geometry
variable (d : GeometryData)

theorem uniform_curve_margin :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (BlowupMargin.affineCurveDegreeData d)

/-- Actual ampleness from the proved distinct-center curve inequality and the
concrete curve models; no ampleness or interpolation premise is assumed. -/
theorem interpolationBundle_ample : (interpolationBundle d).IsAmple :=
  NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) (H_ample d) (uniformMargin d)
    (uniformMargin_pos d) (uniform_curve_margin d)

end Logarithm.BlowupGeometry
end
end OAI

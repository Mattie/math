-- Adapted from the frozen periodic pi geometry; see extraction-manifest.json.
import PeriodicGeometry.PeriodicCurveModelDegrees

namespace OAI

noncomputable section
namespace PiExponent.PeriodicBlowupMargin
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PeriodicBlowupGeometry CurveNormalizationModel
variable (d : PeriodicGeometryData)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := PeriodicCurveModel.existsModelData d C hn hm
  exact ⟨PeriodicCurveModel.degreeData d C r⟩

end PiExponent.PeriodicBlowupMargin

namespace PiExponent.PeriodicBlowupGeometry
open AlgebraicGeometry
variable (d : PeriodicGeometryData)

theorem uniform_curve_margin :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (PeriodicBlowupMargin.affineCurveDegreeData d)

end PiExponent.PeriodicBlowupGeometry

end

end OAI

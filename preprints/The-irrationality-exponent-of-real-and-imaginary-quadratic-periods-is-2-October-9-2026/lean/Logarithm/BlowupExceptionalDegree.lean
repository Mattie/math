import Logarithm.BlowupGeometry
import Logarithm.ExceptionalCurveDegree

namespace OAI
noncomputable section
namespace Logarithm
open AlgebraicGeometry CategoryTheory
open PiExponent PiExponentSeshadri.Geometry

/-- The actual exceptional bundle has degree minus radius times total contact
on every normalized curve entering the affine chart. -/
theorem blowup_exceptional_degree_eq_neg_contact_sum
    (d : GeometryData)
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (z : Fin (d.m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    letI := hfinite f hf
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    ∀ (g : CurveNormalizationModel.parameterCurve f hf ⟶ BlowupGeometry.blowup d),
    CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g ≫
      BlowupGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
        BlowupGeometry.affineChart d →
    ((eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        ((BlowupGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        (structureSheaf (CurveNormalizationModel.parameterCurve f hf)) : ℤ) : ℝ) =
      -((BlowupGeometry.scale d).radius : ℝ) *
        ∑ p ∈ ContactFamily.places hfinite z d.curveY d.curveY_ne_zero d.curveCenters hz,
          (ContactFamily.contact hres hfinite z d.curveY d.curveY_ne_zero
            d.curveCenters hz d.curveJetWeights p : ℝ) := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  dsimp only
  intro g hgeneric
  have h := ExceptionalCurveDegree.compactIdeal_degree_eq_neg_contact_sum f hf
    d.curveY d.curveY_ne_zero d.curveY_injective d.curveCenters
    (BlowupGeometry.logCutoff d) (BlowupGeometry.scale d).jetPowers
    (BlowupGeometry.scale d).jetPowers_pos d.curveJetWeights d.curveJetWeights_pos
    (BlowupGeometry.scale d).radius (BlowupGeometry.scale d).jetPowers_eq
    (BlowupGeometry.logCutoff_strict d) (BlowupGeometry.affineChart d)
    (BlowupGeometry.compactificationStructureMap d) (BlowupGeometry.affineChart_over d)
    (BlowupGeometry.projection d) (BlowupGeometry.J d)
    (BlowupGeometry.exceptionalInclusion d) (BlowupGeometry.exceptional_presents d)
    g z hz hgeneric hres hfinite
  exact_mod_cast h

end Logarithm
end
end OAI

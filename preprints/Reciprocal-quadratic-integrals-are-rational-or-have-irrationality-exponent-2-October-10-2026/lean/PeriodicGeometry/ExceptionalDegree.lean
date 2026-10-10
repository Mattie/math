import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree
import PeriodicGeometry.PeriodicBlowupPolarization
namespace OAI.PiExponent.PeriodicExceptionalDegree
noncomputable section
open AlgebraicGeometry CategoryTheory PiExponentSeshadri.Geometry
open ExceptionalCurveDegree
theorem degree_eq_neg_contactSum
    (d : PeriodicGeometryData)
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    letI := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg f hf
    ∀ (g : CurveNormalizationModel.parameterCurve f hf ⟶ PeriodicBlowupGeometry.blowup d),
    CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g ≫
      PeriodicBlowupGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        PeriodicBlowupGeometry.affineChart d →
    ((eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        ((PeriodicBlowupGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        (structureSheaf (CurveNormalizationModel.parameterCurve f hf)) : ℤ) : ℝ) =
      -((PeriodicBlowupGeometry.scale d).radius : ℝ) *
        PeriodicCurveMargin.contactSum d y x hgen htrdeg := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  intro g hgeneric
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  have hc : Function.Injective d.curveCenters := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    intro j k h
    exact d.curveCenters_injective i (congrFun h i)
  have h := compactIdeal_degree_eq_neg_contact_sum f hf d.curveCenters hc
    (PeriodicBlowupGeometry.logCutoff d) (PeriodicBlowupGeometry.scale d).jetPowers
    (PeriodicBlowupGeometry.scale d).jetPowers_pos d.curveJetWeights d.curveJetWeights_pos
    (PeriodicBlowupGeometry.scale d).radius (PeriodicBlowupGeometry.scale d).jetPowers_eq
    (PeriodicBlowupGeometry.logCutoff_strict d) (PeriodicBlowupGeometry.affineChart d)
    (PeriodicBlowupGeometry.compactificationStructureMap d)
    (PeriodicBlowupGeometry.affineChart_over d)
    (PeriodicBlowupGeometry.projection d) (PeriodicBlowupGeometry.J d)
    (PeriodicBlowupGeometry.exceptionalInclusion d)
    (PeriodicBlowupGeometry.exceptional_presents d) g z hz hgeneric hres hfinite
  change _ = -((PeriodicBlowupGeometry.scale d).radius : ℝ) *
    ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ)
  exact_mod_cast h

end
end OAI.PiExponent.PeriodicExceptionalDegree

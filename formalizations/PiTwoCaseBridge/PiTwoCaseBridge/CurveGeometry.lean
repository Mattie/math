import PiTwoCaseBridge.CurveGeometryModel
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree
import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer

/-! The strict pole-degree versus logarithmic branch-contact inequality implies
ampleness of the hyperplane pullback tensored with the exceptional ideal.
Weights are arbitrary positive rationals and only tuplewise distinct centers
are required. The normalization and degree transfer follow OAI's PiExponent
geometry; the curve inequality is supplied by the caller. -/

namespace OAI.PiExponent

noncomputable section
namespace BridgeGeometry

variable (d : BridgeData)
variable {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

def contactSum (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  ∑ q ∈ CurveContactFamily.places hfinite z d.centers hz,
    (CurveContactFamily.contact hres hfinite z d.centers hz d.V q : ℝ)

def poleDegree (y : E) (x : Fin d.m → E) (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  CurveContactSum.weightedDegree
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg)
    (Fin.cases y x : Fin (d.m+1) → E) d.W

/-- The branch-contact inequality for every affine integral curve, expressed in
its function field with the generating affine coordinates. -/
def CurveBound (s : ℚ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1),
    (s : ℝ) * contactSum d y x hgen htrdeg ≤ poleDegree d y x htrdeg

open AlgebraicGeometry CategoryTheory
open NumericalAmpleness

structure AffineCurveDegreeData (C : IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  y : E
  x : Fin d.m → E
  coordinates_generate : IntermediateField.adjoin ℂ
    (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  hyperplane_degree : (curveDegree (structureMap d) (A d) C : ℝ) =
    ((scale d).radius : ℝ) * poleDegree d y x trdeg_one
  exceptional_degree : (curveDegree (structureMap d) (J d) C : ℝ) =
    -((scale d).radius : ℝ) * contactSum d y x coordinates_generate trdeg_one

open PiExponentSeshadri.Geometry CurveNormalizationModel

theorem exceptional_degree_eq_neg_contactSum
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    letI := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg f hf
    ∀ (g : CurveNormalizationModel.parameterCurve f hf ⟶ BridgeGeometry.blowup d),
    CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g ≫
      BridgeGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        BridgeGeometry.affineChart d →
    ((eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        ((BridgeGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        (structureSheaf (CurveNormalizationModel.parameterCurve f hf)) : ℤ) : ℝ) =
      -((BridgeGeometry.scale d).radius : ℝ) *
        contactSum d y x hgen htrdeg := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  intro g hgeneric
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  have h := ExceptionalCurveDegree.compactIdeal_degree_eq_neg_contact_sum f hf d.centers d.centers_injective
    (BridgeGeometry.logCutoff d) (BridgeGeometry.scale d).jetPowers
    (BridgeGeometry.scale d).jetPowers_pos d.V d.V_pos
    (BridgeGeometry.scale d).radius (BridgeGeometry.scale d).jetPowers_eq
    (BridgeGeometry.logCutoff_strict d) (BridgeGeometry.affineChart d)
    (BridgeGeometry.compactificationStructureMap d)
    (BridgeGeometry.affineChart_over d)
    (BridgeGeometry.projection d) (BridgeGeometry.J d)
    (BridgeGeometry.exceptionalInclusion d)
    (BridgeGeometry.exceptional_presents d) g z hz hgeneric hres hfinite
  change _ = -((BridgeGeometry.scale d).radius : ℝ) *
    ∑ p ∈ CurveContactFamily.places hfinite z d.centers hz,
      (CurveContactFamily.contact hres hfinite z d.centers hz d.V p : ℝ)
  exact_mod_cast h


def degreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (r : BridgeCurveModel.ModelData d C) : AffineCurveDegreeData d C := by
  letI := r.field
  letI := r.algebra
  letI := r.essFiniteType
  letI := r.parameterFinite
  letI := r.normalizationFinite
  letI := r.chartIso
  let y := r.coordinates 0
  let x := fun i : Fin d.m => r.coordinates i.succ
  have htuple : (Fin.cases y x : Fin (d.m+1) → r.E) = r.coordinates := by
    funext i
    cases i using Fin.cases <;> rfl
  have hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → r.E)) = ⊤ := by
    rw [htuple]
    exact r.coordinates_generate
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ r.E r.trdeg_one
  have hA : (NumericalAmpleness.curveDegree (structureMap d) (A d) C : ℝ) =
      ((scale d).radius : ℝ) * poleDegree d y x r.trdeg_one := by
    change _ = ((scale d).radius : ℝ) *
      CurveContactSum.weightedDegree hfinite (Fin.cases y x) d.W
    rw [htuple]
    exact CurveNormalizedDegreeTransfer.weighted_curveDegree
      (exponents d) r.coordinates (constantIndex d)
      ((scale d).exponents_constant d.W_pos)
      (coordinateIndex d) ((scale d).exponents_coordinate d.W_pos)
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty
      (projection d) r.generic_coordinates d.W d.W_pos
      (by exact_mod_cast (scale d).radius_pos) (scale d).degreePowers
      (scale d).degreePowers_eq (pureIndex d)
      ((scale d).exponents_pure d.W_pos)
      ((scale d).budget d.W_pos) hfinite
  have hgeneric : parameterCurveGenericPoint r.parameter r.parameter_transcendental ≫
      (r.normalization ≫ C.embedding) ≫ projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        affineChart d := by
    have heval : (MvPolynomial.aeval r.coordinates).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℂ r.E) r.coordinates := by
      apply RingHom.ext
      intro P
      exact MvPolynomial.aeval_def r.coordinates P
    rw [htuple, heval]
    simpa only [Category.assoc, CurveMonomialMap.genericMonomialMap, affineChart] using
      r.generic_coordinates
  have hJ : (NumericalAmpleness.curveDegree (structureMap d) (J d) C : ℝ) =
      -((scale d).radius : ℝ) * contactSum d y x hgen r.trdeg_one := by
    have hd := CurveNormalizedDegreeTransfer.curveDegree_eq_normalized
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty (J d)
    have hn := exceptional_degree_eq_neg_contactSum
      d y x hgen r.trdeg_one r.parameter r.parameter_transcendental
      (r.normalization ≫ C.embedding) hgeneric
    exact (congrArg (fun n : ℤ => (n : ℝ)) hd).trans hn
  exact { E := r.E
          field := r.field
          algebra := r.algebra
          essFiniteType := r.essFiniteType
          y := y
          x := x
          coordinates_generate := hgen
          trdeg_one := r.trdeg_one
          hyperplane_degree := hA
          exceptional_degree := hJ }

/-- Numerical ampleness follows from the single strict inequality on branches.
The contracted and boundary cases use the geometry of the same blowup. -/
theorem interpolationBundle_ample (s : ℚ) (hs : 1 < s) (hc : CurveBound d s) :
    (interpolationBundle d).IsAmple := by
  let σ : ℝ := (s : ℝ) - 1
  have hσ : 0 < σ := sub_pos.mpr (by exact_mod_cast hs)
  let a := ampleExponent d
  have ha := ampleExponent_gt_one d
  have hamp := H_ample d
  apply NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) hamp
    (BlowupCurveMargin.marginCoefficient a σ) (BlowupCurveMargin.marginCoefficient_pos ha hσ)
  intro C
  by_cases hconst : ∃ x : compactification d,
      Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)
  · obtain ⟨x,hx⟩ := hconst
    exact BlowupCurveMargin.margin_of_contracted (structureMap d) (projection d)
      (hyperplane d) (J d) a ha hamp σ hσ C x hx
  by_cases hchart : ∃ c : C.scheme,
      (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange
  · obtain ⟨model⟩ := BridgeCurveModel.existsModelData d C hconst hchart
    let r := degreeData d C model
    let := r.field
    let := r.algebra
    let := r.essFiniteType
    apply BlowupCurveMargin.margin_of_nonnegative_degree (structureMap d) (A d) (J d)
      a ha hamp σ hσ C
    rw [r.hyperplane_degree, r.exceptional_degree]
    have h := hc r.E r.y r.x r.coordinates_generate r.trdeg_one
    have hR : 0 ≤ ((scale d).radius : ℝ) := by exact_mod_cast (scale d).radius_pos.le
    have hscaled := mul_le_mul_of_nonneg_left h hR
    dsimp only [σ]
    linarith only [hscaled]
  · exact BlowupCurveMargin.margin_of_image_outside_chart (structureMap d) (centerIdeal d)
      (projection d) (A d) (J d) (exceptionalInclusion d) (exceptional_presents d)
      a ha hamp σ hσ C (affineChart d).opensRange (centerIdeal_support_subset_chart d)
      (fun c h => hchart ⟨c,h⟩)

end BridgeGeometry
end
end OAI.PiExponent

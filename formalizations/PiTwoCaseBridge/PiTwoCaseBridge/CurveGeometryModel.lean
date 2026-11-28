import PiTwoCaseBridge.CurveGeometryCore
import OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage
import OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism
import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic

/-! The curve normalization and its generic affine coordinates, following the OAI
PiExponent curve-image construction with general weights and centers. -/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.BridgeCurveImage
open BridgeGeometry CurveBlowupImage
variable (d : BridgeData)

theorem center_point_isClosed (x : compactification d)
    (hx : x ∈ (centerIdeal d).support) : IsClosed ({x} : Set (compactification d)) := by
  change x ∈ ((centerIdeal d).support : Set (compactification d)) at hx
  rw [centerIdeal_support d] at hx
  obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hx
  let q := CompactLogJetIdeal.point (d.centers j) ≫ affineChart d
  let : IsClosedImmersion q := CompactJetIdeal.section_isClosedImmersion
    (compactificationStructureMap d) q (by
      dsimp [q]
      rw [Category.assoc, affineChart_over, CompactLogJetIdeal.point_section])
  have he : Set.range q = {q z} := by
    ext x
    constructor
    · rintro ⟨z',rfl⟩
      exact congrArg q (Subsingleton.elim z' z)
    · rintro rfl
      exact ⟨z,rfl⟩
  rw [← he]
  exact q.isClosedEmbedding.isClosed_range

theorem meets_center_complement (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (centerIdeal d).support.compl :=
  exists_image_outside_closed_points (C.embedding ≫ projection d)
    (centerIdeal d).support (center_point_isClosed d) hn

instance projection_restrict_isIso :
    IsIso (projection d ∣_ (centerIdeal d).support.compl) :=
  blowup_restrict_isIso (isBlowup d)

abbrev imageCurve (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :=
  CurveBlowupImage.imageCurve (projection d) C hn

def functionFieldIso (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    (imageCurve d C hn).scheme.functionField ≅ C.scheme.functionField :=
  imageFunctionFieldIso (projection d) C hn (centerIdeal d).support.compl
    (meets_center_complement d C hn)

theorem functionFieldIso_generic (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    Spec.map (functionFieldIso d C hn).hom ≫
      (imageCurve d C hn).scheme.fromSpecStalk (genericPoint (imageCurve d C hn).scheme) ≫
      (imageCurve d C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ projection d :=
  imageFunctionFieldIso_generic (projection d) C hn (centerIdeal d).support.compl
    (meets_center_complement d C hn)

theorem image_meets_chart (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    ∃ c : (imageCurve d C hn).scheme,
      (imageCurve d C hn).embedding c ∈ (affineChart d).opensRange := by
  obtain ⟨c,hc⟩ := hm
  refine ⟨CurveBlowupImage.imageMap (projection d) C hn c, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, CurveBlowupImage.imageMap_comp] using hc

end PiExponent.BridgeCurveImage

end

noncomputable section
namespace PiExponent.BridgeCurveCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
open BridgeGeometry
open CurveImageAffineCoordinates
variable (d : BridgeData)
variable (C : NumericalAmpleness.IntegralCurve (blowup d))
variable (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})

abbrev imageCurve := BridgeCurveImage.imageCurve d C hn
abbrev sourceStructure := C.embedding ≫ structureMap d
abbrev imageStructure := (imageCurve d C hn).embedding ≫ compactificationStructureMap d
@[instance_reducible] def sourceAlgebra : Algebra ℂ C.scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (sourceStructure d C)
@[instance_reducible] def imageAlgebra :
    Algebra ℂ (imageCurve d C hn).scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (imageStructure d C hn)

def fieldEquiv :
    letI := imageAlgebra d C hn
    letI := sourceAlgebra d C
    (imageCurve d C hn).scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
  fieldAlgEquiv (imageStructure d C hn) (sourceStructure d C)
    (BridgeCurveImage.functionFieldIso d C hn) (by
      simpa only [imageStructure, sourceStructure, structureMap, Category.assoc] using
        congrArg (fun f => f ≫ compactificationStructureMap d)
          (BridgeCurveImage.functionFieldIso_generic d C hn))

abbrev chart := affinePart (imageCurve d C hn).embedding (affineChart d)
abbrev chartPresentation := affinePresentation (imageCurve d C hn).embedding (affineChart d)

variable (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange)

include hm in
theorem chart_nonempty : Nonempty (chart d C hn).1 :=
  affinePart_nonempty _ _ (BridgeCurveImage.image_meets_chart d C hn hm)

def imageCoordinates : Fin (d.m+1) → (imageCurve d C hn).scheme.functionField :=
  letI := chart_nonempty d C hn hm
  CurveImageAffineCoordinates.coordinates (chart d C hn) (chartPresentation d C hn)

def coordinates : Fin (d.m+1) → C.scheme.functionField :=
  letI := imageAlgebra d C hn
  letI := sourceAlgebra d C
  fieldEquiv d C hn ∘ imageCoordinates d C hn hm

def y : C.scheme.functionField := coordinates d C hn hm 0

def x : Fin d.m → C.scheme.functionField := fun i => coordinates d C hn hm i.succ

@[simp] theorem full_coordinates :
    (Fin.cases (y d C hn hm) (x d C hn hm) : Fin (d.m+1) → C.scheme.functionField) =
      coordinates d C hn hm := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem field_properties :
    letI := sourceAlgebra d C
    Algebra.EssFiniteType ℂ C.scheme.functionField ∧
      Algebra.trdeg ℂ C.scheme.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates d C hn hm)) = ⊤ := by
  let := sourceAlgebra d C
  let := imageAlgebra d C hn
  let := chart_nonempty d C hn hm
  obtain ⟨ht,hd,hg⟩ := CurveImageAffineCoordinates.field_properties
    (imageStructure d C hn) (imageCurve d C hn).dimension
    (chart d C hn) (chartPresentation d C hn)
    (affinePresentation_over (compactificationStructureMap d) _ _ (affineChart_over d))
  let := ht
  exact transport_field_properties (fieldEquiv d C hn)
    (imageCoordinates d C hn hm) hd hg

theorem coordinates_generic_map :
    letI := sourceAlgebra d C
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm)).toRingHom) ≫
      affineChart d = C.scheme.fromSpecStalk (genericPoint C.scheme) ≫
        C.embedding ≫ projection d := by
  let := sourceAlgebra d C
  let := imageAlgebra d C hn
  let := chart_nonempty d C hn hm
  have himage := CurveImageAffineCoordinates.coordinates_generic_map
    (imageStructure d C hn) (chart d C hn) (chartPresentation d C hn)
    (affinePresentation_over (compactificationStructureMap d) _ _ (affineChart_over d))
    (affineChart d) (imageCurve d C hn).embedding (affinePresentation_comp _ _)
  have he : (MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm)).toRingHom =
      (BridgeCurveImage.functionFieldIso d C hn).hom.hom.comp
        (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)).toRingHom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (R := ℂ) (coordinates d C hn hm) =
        (fieldEquiv d C hn).toAlgHom.comp
          (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)) from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := ℂ) (imageCoordinates d C hn hm)).toRingHom) ≫ affineChart d =
      (imageCurve d C hn).scheme.fromSpecStalk (genericPoint (imageCurve d C hn).scheme) ≫
        (imageCurve d C hn).embedding from himage]
  exact BridgeCurveImage.functionFieldIso_generic d C hn

end PiExponent.BridgeCurveCoordinates

end

noncomputable section
namespace PiExponent.BridgeCurveModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open BridgeGeometry CurveNormalizationModel
variable (d : BridgeData)

structure ModelData (C : NumericalAmpleness.IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (d.m+1) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ structureMap d =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
      (normalization ≫ C.embedding ≫ projection d) =
    CurveMonomialMap.genericMonomialMap (exponents d) (constantIndex d)
      ((scale d).exponents_constant d.W_pos) (coordinateIndex d)
      ((scale d).exponents_coordinate d.W_pos) coordinates

theorem existsModelData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ t : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {t})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (ModelData d C) := by
  let := BridgeCurveCoordinates.sourceAlgebra d C
  have hp := BridgeCurveCoordinates.field_properties d C hn hm
  let := hp.1
  let z := BridgeCurveCoordinates.coordinates d C hn hm
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField hp.2.1
  obtain ⟨i,hi⟩ := CurveInequality.nonconstant_coordinates z hp.2.2 hp.2.1
  let f := z i
  have hf : Transcendental ℂ f := hi
  let := hfinite f hf
  obtain ⟨g,hg,hgeneric,hgfinite,W,hW,hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism
      (C.embedding ≫ structureMap d) C.dimension f hf
  let := hgfinite
  let := hWiso
  have hWne : W ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection d) =
      CurveMonomialMap.genericMonomialMap (exponents d) (constantIndex d)
        ((scale d).exponents_constant d.W_pos) (coordinateIndex d)
        ((scale d).exponents_coordinate d.W_pos) z := by
    change parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection d) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart d
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    exact (BridgeCurveCoordinates.coordinates_generic_map d C hn hm).symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := hp.1
           coordinates := z
           coordinates_generate := hp.2.2
           trdeg_one := hp.2.1
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

end PiExponent.BridgeCurveModel

end

end OAI

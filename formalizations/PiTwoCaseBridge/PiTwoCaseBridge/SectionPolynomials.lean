import OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations
import OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover
import OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame
import OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import PiTwoCaseBridge.CurveGeometry

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace OAI.PiExponent OAI.PiExponentSeshadri.Geometry

namespace PiTwoCaseBridge

/-- Finite sections with one more exceptional factor than source factors. -/
theorem strict_section_cover_of_ample_tensor {X : Scheme.{0}} [NoetherianSpace X]
    (A J : LineBundle X) (h : (A.tensor J).IsAmple) :
    ∃ a : ℕ, 0 < a ∧ ∃ k : ℕ,
      ∃ s : Fin k → GlobalSections X (((A.pow a).tensor (J.pow (a + 1))).sheaf),
        (⨆ i, sectionOpen X (s i)) = ⊤ := by
  let : J.sheaf.IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  obtain ⟨N, hN⟩ := AmpleGlobalGeneration.ample_eventual_global_generators
    (A.tensor J) h J.sheaf
  let a := N + 1
  obtain ⟨G, hG⟩ := hN a (Nat.le_succ N)
  let e : ((moduleTwistFunctor (A.tensor J) a).obj J.sheaf) ≅
      ((A.pow a).tensor (J.pow (a + 1))).sheaf :=
    moduleTwistPowerIso (A.tensor J) J.sheaf a ≪≫
      moduleTensorIso (Iso.refl _) (lineTensorPow A J a) ≪≫
      (lineTensorAssoc J (A.pow a) (J.pow a)).symm ≪≫
      moduleTensorIso (moduleTensorComm J.sheaf (A.pow a).sheaf) (Iso.refl _) ≪≫
      lineTensorAssoc (A.pow a) J (J.pow a)
  let G' := SheafOfModules.GeneratingSections.equivOfIso e G
  let : G'.IsFiniteType := ⟨hG.finite⟩
  exact ⟨a, Nat.succ_pos N,
    GeneratorsSectionCover.exists_fin_section_cover ((A.pow a).tensor (J.pow (a + 1))) G'⟩

private theorem germ_top_transport (X : Scheme.{0}) {x y : X} (h : x = y) :
    X.presheaf.germ ⊤ x trivial ≫
      eqToHom (congrArg (fun z => X.presheaf.stalk z) h) = X.presheaf.germ ⊤ y trivial := by
  subst y
  simp

/-- On an integral normal affine base, regular functions on a proper birational
modification descend. It suffices that the map be universally closed and be an
isomorphism over one nonempty open. -/
theorem appTop_surjective_of_normal_birational {B X : Scheme.{0}} [IsIntegral B]
    [IsIntegral X] [IsAffine X] [IsIntegrallyClosed Γ(X, ⊤)]
    (f : B ⟶ X) [UniversallyClosed f] [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    Function.Surjective f.appTop := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Nonempty (⊤ : B.Opens) := ⟨⟨genericPoint B, trivial⟩⟩
  let e := CurveBlowupImage.functionFieldIso f U hU
  let g := B.germToFunctionField ⊤ ≫ e.inv
  have hcomp : f.appTop ≫ B.germToFunctionField ⊤ = X.germToFunctionField ⊤ ≫ e.hom := by
    change _ = _ ≫ eqToHom (congrArg (fun x => X.presheaf.stalk x)
      (CurveBlowupImage.genericPoint_eq_of_isDominant f).symm) ≫ f.stalkMap _
    rw [← Category.assoc, germ_top_transport X
      (CurveBlowupImage.genericPoint_eq_of_isDominant f).symm]
    exact (f.germ_stalkMap ⊤ (genericPoint B) trivial).symm
  have hg : g.hom.comp f.appTop.hom = algebraMap Γ(X, ⊤) X.functionField := by
    change (f.appTop ≫ B.germToFunctionField ⊤ ≫ e.inv).hom = (X.germToFunctionField ⊤).hom
    rw [← Category.assoc, hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let := functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  intro z
  have hz := ((isIntegral_appTop_of_universallyClosed f) z).map g.hom
  rw [hg] at hz
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hz
  refine ⟨P, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.inv).injective.comp
    (B.germToFunctionField_injective ⊤)
  change (g.hom.comp f.appTop.hom) P = g.hom z
  rw [hg]
  exact hP

/-- Descent for powers reduces to descent of ordinary regular functions by
the projection formula for a line bundle. -/
theorem pullbackPowerSection_surjective_of_unit {B X : Scheme.{0}}
    (f : B ⟶ X) [IsIso (CurveNormalizationDegree.unitMap f)]
    (L : LineBundle X) (a : ℕ) :
    Function.Surjective (pullbackPowerSection L f a) := by
  let u : structureSheaf X ⟶ (Scheme.Modules.pushforward f).obj (structureSheaf B) :=
    OAI.PiExponentSeshadri.IdealModule.structureMap f
  let : IsIso u := inferInstanceAs (IsIso (CurveNormalizationDegree.unitMap f))
  let h := (moduleTwistFunctor L a).mapIso (asIso u)
  intro t
  let q := (ProjectiveSectionExtension.quotientSectionsEquiv L f a).symm t
  refine ⟨(q ≫ h.inv) ≫ (moduleTwistUnitIso L a).hom, ?_⟩
  rw [← ProjectiveSectionExtension.quotientSectionsEquiv_restriction]
  apply (ProjectiveSectionExtension.quotientSectionsEquiv L f a).eq_symm_apply.mp
  change ((q ≫ h.inv) ≫ (moduleTwistUnitIso L a).hom) ≫
      (moduleTwistUnitIso L a).inv ≫ h.hom = q
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

open OAI.PiExponentSeshadri.Frames AffineJetCoefficientInterface
open BridgeGeometry

/-- These are the actual sections of the exceptional twist and their
representatives downstairs, expressed in a single affine frame. -/
structure GeneratingPolynomials (d : BridgeData) where
  a : ℕ
  a_pos : 0 < a
  k : ℕ
  sections : Fin k → GlobalSections (blowup d) ((((J d).pow (a + 1)).tensor ((A d).pow a)).sheaf)
  cover : (⨆ i, sectionOpen (blowup d) (sections i)) = ⊤
  downstairs : Fin k → Sections (hyperplane d) a
  represents : ∀ i, pullbackPowerSection (hyperplane d) (projection d) a (downstairs i) =
    sections i ≫ tensorInclusion ((J d).pow (a + 1)) ((A d).pow a)
      (idealPowerInclusion (J d) (exceptionalInclusion d) (a + 1))
  frame : Frame (affineChart d) (hyperplane d)
  sourceDegree : ∀ i, WeightedSliceDegree.SupportBound (fun j => (d.W j : ℝ))
    ((a : ℝ) * (scale d).radius)
    (AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) a frame (downstairs i))

def GeneratingPolynomials.polynomial {d : BridgeData} (G : GeneratingPolynomials d) (i : Fin G.k) :=
  AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) G.a G.frame (G.downstairs i)

/-- Construct the finite source family from ampleness, descent, and the degree
law for all hyperplane sections downstairs. -/
theorem strict_generating_polynomials (d : BridgeData)
    [IsIso (CurveNormalizationDegree.unitMap (projection d))]
    (s : ℚ) (hs : 1 < s) (hc : CurveBound d s)
    (degree : ∀ n (e : Frame (affineChart d) (hyperplane d)) (t : Sections (hyperplane d) n),
      WeightedSliceDegree.SupportBound (fun i => (d.W i : ℝ)) ((n : ℝ) * (scale d).radius)
        (AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) n e t)) :
    Nonempty (GeneratingPolynomials d) := by
  obtain ⟨a, ha, k, t, ht⟩ := strict_section_cover_of_ample_tensor (A d) (J d)
    (interpolationBundle_ample d s hs hc)
  let swap := moduleTensorComm ((A d).pow a).sheaf ((J d).pow (a + 1)).sheaf
  let S := fun i : Fin k => t i ≫ swap.hom
  have hS : (⨆ i, sectionOpen (blowup d) (S i)) = ⊤ := by
    calc
      _ = ⨆ i, sectionOpen (blowup d) (t i) :=
        iSup_congr fun i => AmpleIso.sectionOpen_postcomp_iso (t i) swap
      _ = ⊤ := ht
  let inc := tensorInclusion ((J d).pow (a + 1)) ((A d).pow a)
    (idealPowerInclusion (J d) (exceptionalInclusion d) (a + 1))
  choose down hdown using fun i => pullbackPowerSection_surjective_of_unit
    (projection d) (hyperplane d) a (S i ≫ inc)
  obtain ⟨e⟩ := AdmissibleMatrixInterpolation.monomialFrame_exists (R := ℂ)
    (exponents d) (constantIndex d) ((scale d).exponents_constant d.W_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.W_pos)
  exact ⟨⟨a, ha, k, S, hS, down, hdown, e, fun i => degree a e (down i)⟩⟩

private lemma map_comp_iso_cancel {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N N' : C} {V : D} (v : V ⟶ F.obj M) (t : M ⟶ N) (e : N ≅ N') :
    (v ≫ F.map (t ≫ e.hom)) ≫ F.map e.inv = v ≫ F.map t := by
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    Category.comp_id]

/-- Evaluate the downstairs representatives on a lifted affine arc. A single
frame works for all the sections, including after their exceptional factors
are included in the structure sheaf. -/
theorem GeneratingPolynomials.exists_arc_frame {d : BridgeData} (G : GeneratingPolynomials d)
    {S : Type} [CommRing S] (ev : CompactLogJetIdeal.coordinateRing d.m →+* S)
    (u : Spec (CommRingCat.of S) ⟶ blowup d)
    (hu : u ≫ projection d = Spec.map (CommRingCat.ofHom ev) ≫ affineChart d) :
    ∃ E : ((((A d).pow G.a).pullback u).sheaf ≅ O _), ∀ i,
      LocalSectionOrder.localCoefficient E (pullbackSection u (G.sections i ≫
        tensorInclusion ((J d).pow (G.a + 1)) ((A d).pow G.a)
          (idealPowerInclusion (J d) (exceptionalInclusion d) (G.a + 1)))) =
        ev (G.polynomial i) := by
  let j := affineChart d
  let f := projection d
  let L := hyperplane d
  let U := j.opensRange
  let g := Spec.map (CommRingCat.ofHom ev) ≫ j.isoOpensRange.hom
  let F := AffineJetCoefficientFrame.untwistPowerFrame L U G.frame G.a
  have hw : u ≫ f = g ≫ U.ι := by
    change u ≫ projection d = (Spec.map (CommRingCat.ofHom ev) ≫ j.isoOpensRange.hom) ≫ j.opensRange.ι
    rw [Category.assoc, j.isoOpensRange_hom_ι]
    exact hu
  have hframe : ∃ C : (Scheme.Modules.pullback (u ≫ f)).obj (modulePow _ L.sheaf G.a) ≅ O _,
      ∀ t : Sections L G.a, OAI.PiExponentSeshadri.Frames.coefficient C
        (pullbackSection (u ≫ f) t) = g.appTop
          (OAI.PiExponentSeshadri.Frames.coefficient F (restrictSection U.ι t)) := by
    rw [hw]
    exact PullbackFrameCoefficient.exists_frame_of_factors_through_open U g F
  obtain ⟨C, hC⟩ := hframe
  obtain ⟨D, hD⟩ := CompositePullbackCoefficient.exists_frame u f C
  let powerIso := OAI.PiExponentSeshadri.PullbackTensor.powIso f L G.a
  let E := (Scheme.Modules.pullback u).mapIso powerIso.symm ≪≫ D
  refine ⟨E, fun i => ?_⟩
  erw [← G.represents i]
  let t : O (compactification d) ⟶ modulePow _ L.sheaf G.a := G.downstairs i
  change (Scheme.ΓSpecIso _).hom (OAI.PiExponentSeshadri.Frames.coefficient E
    (pullbackSection u (pullbackPowerSection L f G.a t))) = ev (G.polynomial i)
  have hcancel : pullbackSection u (pullbackPowerSection L f G.a t) ≫
      ((Scheme.Modules.pullback u).mapIso powerIso.symm).hom =
      pullbackSection u (pullbackSection f t) := by
    change ((pullbackUnitIso u).inv ≫ (Scheme.Modules.pullback u).map
      (pullbackSection f t ≫ powerIso.hom)) ≫ (Scheme.Modules.pullback u).map powerIso.inv = _
    exact map_comp_iso_cancel (Scheme.Modules.pullback u) (pullbackUnitIso u).inv
      (pullbackSection f t) powerIso
  change (Scheme.ΓSpecIso _).hom (OAI.PiExponentSeshadri.Frames.coefficient
    ((Scheme.Modules.pullback u).mapIso powerIso.symm ≪≫ D)
    (pullbackSection u (pullbackPowerSection L f G.a t))) = _
  erw [coefficient_transport, hcancel, hD t, hC t]
  let b := OAI.PiExponentSeshadri.Frames.coefficient F (restrictSection U.ι t)
  have hpoly : G.polynomial i = (Scheme.ΓSpecIso _).hom (j.isoOpensRange.hom.appTop b) := by
    unfold GeneratingPolynomials.polynomial AffineJetCoefficientInterface.coefficient
      AffineJetPolynomial.polynomialCoefficient
    erw [AffineJetCoefficientFrame.globalSectionCoefficient_eq]
    change (Scheme.ΓSpecIso _).hom (j.isoOpensRange.hom.appTop
      (U.topIso.inv (U.topIso.hom b))) = _
    rw [U.topIso.hom_inv_id_apply]
  rw [hpoly]
  exact CategoryTheory.congr_fun (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ev))
    (j.isoOpensRange.hom.appTop b)

end PiTwoCaseBridge

import PiTwoCaseBridge.CurveGeometryModel
import PiTwoCaseBridge.SectionPolynomials
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Descent of regular functions along the blowup projection. -/

namespace PiTwoCaseBridge

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI OAI.PiExponent OAI.PiExponentSeshadri
open CurveNormalizationDegree BridgeGeometry

private theorem interchange_restrict_isIso {B X : Scheme.{0}} (f : B ⟶ X) (U V : X.Opens)
    [IsIso (f ∣_ V)] : IsIso (f ∣_ U ∣_ U.ι ⁻¹ᵁ V) := by
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V.ι ''ᵁ (V.ι ⁻¹ᵁ U) := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]
  let e := morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq f he ≪≫
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U)).symm
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mpr
    (inferInstanceAs (IsIso (f ∣_ V ∣_ V.ι ⁻¹ᵁ U)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem app_basicOpen_isIso {B X : Scheme.{0}} (f : B ⟶ X) [IsAffine X]
    [CompactSpace B] [QuasiSeparatedSpace B] [IsIso f.appTop] (r : Γ(X, ⊤)) :
    IsIso (f.app (X.basicOpen r)) := by
  have hs : IsPushout f.appTop (X.presheaf.map (homOfLE le_top).op)
      (B.presheaf.map (homOfLE le_top).op) (f.appLE (X.basicOpen r)
        (B.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge) := by
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (f.appTop r)
    refine CommRingCat.isPushout_of_isLocalization f.appTop.hom (f.appLE _ _ _).hom ?_ (.powers r)
    change CommRingCat.Hom.hom (X.presheaf.map _ ≫ f.appLE _ _ _) =
      CommRingCat.Hom.hom (f.appTop ≫ B.presheaf.map _)
    rw [f.map_appLE, Scheme.Hom.appLE]
  have hi := hs.isIso_inr_of_isIso
  rw [← f.appLE_eq_app]
  exact (f.appLE_congr _ rfl (Scheme.preimage_basicOpen_top f r).symm (fun t => IsIso t)).mp hi

private theorem unitMap_restrict_of_appTop {B X : Scheme.{0}} (f : B ⟶ X) (U : X.Opens)
    [IsAffine U.toScheme] [CompactSpace (f ⁻¹ᵁ U).toScheme]
    [QuasiSeparatedSpace (f ⁻¹ᵁ U).toScheme] [IsIso (f ∣_ U).appTop] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (unitMap f)) := by
  let g := (Scheme.Modules.restrictFunctor U.ι).map (unitMap f)
  let F := SheafOfModules.toSheaf U.toScheme.ringCatSheaf
  have hg : IsIso (F.map g) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_basicOpen U.toScheme)
    intro r
    let V := U.toScheme.basicOpen r
    have hi : IsIso ((f ∣_ U).app V) := app_basicOpen_isIso (f ∣_ U) r
    rw [morphismRestrict_app] at hi
    have : IsIso (f.app (U.ι ''ᵁ V)) :=
      (isIso_comp_right_iff _ (B.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).mp hi
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConcreteCategory.bijective_of_isIso (f.app (U.ι ''ᵁ V)))
  let : IsIso ((Scheme.Modules.toPresheaf U.toScheme).map g) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ AddCommGrpCat).map (F.map g)))
  exact isIso_of_reflects_iso g (Scheme.Modules.toPresheaf U.toScheme)

/-- Regular functions on the weighted-center blowup descend to its compactification.
Over the polynomial chart this follows from normal affine birational descent.
The projection is an isomorphism over the complement of the center support. -/
theorem projection_unitMap_isIso
    (d : BridgeData) : IsIso (unitMap (projection d)) := by
  let f := projection d
  let U := (affineChart d).opensRange
  let V := (centerIdeal d).support.compl
  let : IsIso (f ∣_ V) := BridgeCurveImage.projection_restrict_isIso d
  apply SectionOpens.isIso_of_locally_isIso
  intro x
  by_cases hx : x ∈ (centerIdeal d).support
  · refine ⟨U, centerIdeal_support_subset_chart d hx, ?_⟩
    let : IsAffine U.toScheme := isAffineOpen_opensRange (affineChart d)
    let e := ExceptionalAffineChart.chartFunctionsEquiv (affineChart d)
    let : IsIntegrallyClosed Γ(U.toScheme, ⊤) := IsIntegrallyClosed.of_equiv e.symm
    let W := U.ι ⁻¹ᵁ V
    let g := f ∣_ U
    let : IsIso (g ∣_ W) := interchange_restrict_isIso f U V
    let z : U.toScheme := ⟨affineChart d (origin d), ⟨origin d,rfl⟩⟩
    have hz : z ∈ W := origin_avoids_center d
    let : Nonempty U := ⟨z⟩
    let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    have hW : W ≠ ⊥ := fun h => by rw [h] at hz; exact hz
    let : IsDominant g := dominant_of_iso_restrict g W hW
    let : Surjective g := inferInstance
    obtain ⟨b, hb⟩ := g.surjective z
    have hbW : b ∈ g ⁻¹ᵁ W := show g b ∈ W from hb ▸ hz
    let : Nonempty (f ⁻¹ᵁ U) := ⟨b⟩
    let : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isDominant g
    let : IsIso g.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨g.app_injective ⊤, appTop_surjective_of_normal_birational g W ⟨⟨b, hbW⟩⟩⟩
    let : CompactSpace (f ⁻¹ᵁ U).toScheme := QuasiCompact.compactSpace_of_compactSpace g
    exact unitMap_restrict_of_appTop f U
  · exact ⟨V, hx, unitMap_restrict_isIso f V⟩

end

end PiTwoCaseBridge

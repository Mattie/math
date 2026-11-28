import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
import OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple
import OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale
import OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist
import OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap
import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal

/-! Geometry of the weighted monomial compactification and ordinary blowup used in
Theorem 5.1. The construction specializes the OAI PiExponent blowup geometry to
arbitrary positive rational weights and finite, jointly distinct centers. -/

namespace OAI

/-- The affine data of the bridge. The first coordinate of every center is `1`. -/
structure PiExponent.BridgeData where
  m : ℕ
  K : ℕ
  W : Fin (m + 1) → ℚ
  V : Fin (m + 1) → ℚ
  W_pos : ∀ i, 0 < W i
  V_pos : ∀ i, 0 < V i
  centers : Fin K → Fin m → ℂ
  centers_injective : Function.Injective centers

noncomputable section
namespace PiExponent.BridgeGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable (d : BridgeData)

def scale : Scale d.W d.V :=
  chooseScale d.W d.V
    d.W_pos d.V_pos

abbrev Index := (scale d).Index
abbrev exponents : Index d → Fin (d.m+1) →₀ ℕ := (scale d).exponents
abbrev constantIndex : Index d := (scale d).constantIndex d.W_pos
abbrev coordinateIndex : Fin (d.m+1) → Index d :=
  (scale d).coordinateIndex d.W_pos
abbrev pureIndex : Fin (d.m+1) → Index d :=
  (scale d).pureIndex d.W_pos

instance index_nonempty : Nonempty (Index d) := ⟨constantIndex d⟩

abbrev compactification : Scheme := Proj (WeightedCompactification.imageGrade (R := ℂ) (exponents d))

def compactificationStructureMap : compactification d ⟶ Spec (.of ℂ) :=
  WeightedCompactification.projection (exponents d)

instance compactificationStructureMap_proper : IsProper (compactificationStructureMap d) := by
  dsimp [compactificationStructureMap]
  infer_instance

def affineChart : CompactLogJetIdeal.affineSpace d.m ⟶ compactification d :=
  WeightedCompactification.affineChartMap (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.W_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.W_pos)

instance affineChart_isOpenImmersion : IsOpenImmersion (affineChart d) := by
  dsimp [affineChart]
  infer_instance

def origin : CompactLogJetIdeal.affineSpace d.m :=
  ⟨WeightedBezout.pointIdeal (0 : Fin (d.m+1) → ℂ),inferInstance⟩

instance compactification_nonempty : Nonempty (compactification d) := ⟨affineChart d (origin d)⟩
instance compactification_isIntegral : IsIntegral (compactification d) := by infer_instance
instance compactification_isLocallyNoetherian : IsLocallyNoetherian (compactification d) :=
  LocallyOfFiniteType.isLocallyNoetherian (compactificationStructureMap d)
instance compactification_compact : CompactSpace (compactification d) :=
  QuasiCompact.compactSpace_of_compactSpace (compactificationStructureMap d)
instance compactification_isNoetherian : IsNoetherian (compactification d) := {}
instance affineChart_quasiCompact : QuasiCompact (affineChart d) := by infer_instance

theorem affineChart_over : affineChart d ≫ compactificationStructureMap d =
    CompactLogJetIdeal.structureMap d.m :=
  CurveMonomialMap.affineChartMap_projection (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.W_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.W_pos)

def hyperplane : LineBundle (compactification d) := WeightedCompactification.lineBundle (exponents d)
theorem hyperplane_ample : (hyperplane d).IsAmple :=
  WeightedCompactification.lineBundle_ample (exponents d)

def logCutoff : Fin d.m → ℕ :=
  (exists_log_cutoff d.V (d.V_pos 0)).choose

theorem logCutoff_strict (i : Fin d.m) :
    d.V i.succ < (logCutoff d i : ℚ) * d.V 0 :=
  (exists_log_cutoff d.V (d.V_pos 0)).choose_spec i

def centerIdeal : (compactification d).IdealSheafData :=
  CompactLogJetIdeal.compactIdeal d.centers (logCutoff d) (scale d).jetPowers (affineChart d)

theorem centerIdeal_restrict : (centerIdeal d).comap (affineChart d) =
    CompactLogJetIdeal.affineIdeal d.centers (logCutoff d) (scale d).jetPowers :=
  CompactLogJetIdeal.restrict_compactIdeal _ _ _ _

theorem centerIdeal_support : ((centerIdeal d).support : Set (compactification d)) =
    ⋃ j : Fin d.K, Set.range (CompactLogJetIdeal.point (d.centers j) ≫ affineChart d) :=
  CompactLogJetIdeal.support_compactIdeal _ _ _ (scale d).jetPowers_pos _
    (compactificationStructureMap d) (affineChart_over d)

theorem centerIdeal_support_finite :
    ((centerIdeal d).support : Set (compactification d)).Finite := by
  rw [centerIdeal_support]
  exact Set.finite_iUnion (fun _ => Set.finite_range _)

theorem centerIdeal_support_subset_chart :
    ((centerIdeal d).support : Set (compactification d)) ⊆ (affineChart d).opensRange := by
  rw [centerIdeal_support]
  intro x hx
  obtain ⟨j,z,rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨CompactLogJetIdeal.point (d.centers j) z,rfl⟩

theorem centerIdeal_coherent :
    (PiExponentSeshadri.IdealModule.closedModule (centerIdeal d)).IsFinitePresentation :=
  CompactLogJetIdeal.compactIdeal_isFinitePresentation _ _ _ _

theorem origin_ne_center (c : Fin d.m → ℂ) : origin d ≠ CompactJetPolynomial.centerPoint c := by
  intro h
  have hx : MvPolynomial.X (0 : Fin (d.m+1)) ∈ (origin d).asIdeal := by
    change MvPolynomial.aeval (0 : Fin (d.m+1) → ℂ) (MvPolynomial.X 0) = 0
    simp
  rw [h] at hx
  change MvPolynomial.aeval (CompactJetPolynomial.center c) (MvPolynomial.X 0) = 0 at hx
  simp [CompactJetPolynomial.center] at hx

theorem origin_avoids_center : affineChart d (origin d) ∉ (centerIdeal d).support := by
  change affineChart d (origin d) ∉ ((centerIdeal d).support : Set (compactification d))
  rw [centerIdeal_support]
  intro h
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
  obtain ⟨z,hz⟩ := hj
  have he : CompactLogJetIdeal.point (d.centers j) z = origin d :=
    (affineChart d).isOpenEmbedding.injective hz
  have hc : CompactLogJetIdeal.point (d.centers j) z =
      CompactJetPolynomial.centerPoint (d.centers j) := by
    apply Set.mem_singleton_iff.mp
    erw [← CompactLogJetIdeal.range_point]
    exact ⟨z,rfl⟩
  exact origin_ne_center d _ (he.symm.trans hc)

theorem centerIdeal_support_ne_top : (centerIdeal d).support ≠ ⊤ := by
  intro h
  exact origin_avoids_center d (by rw [h]; trivial)

abbrev blowup : Scheme := PiExponentSeshadri.BlowupGluing.scheme (centerIdeal d)
abbrev projection : blowup d ⟶ compactification d :=
  PiExponentSeshadri.BlowupGluing.projection (centerIdeal d)
def structureMap : blowup d ⟶ Spec (.of ℂ) := projection d ≫ compactificationStructureMap d

instance projection_proper : IsProper (projection d) := by infer_instance
instance structureMap_proper : IsProper (structureMap d) := by
  dsimp [structureMap]
  infer_instance
instance blowup_isIntegral : IsIntegral (blowup d) :=
  PiExponentSeshadri.BlowupGluing.scheme_isIntegral (centerIdeal d) (centerIdeal_support_ne_top d)
instance blowup_isLocallyNoetherian : IsLocallyNoetherian (blowup d) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap d)
instance blowup_compact : CompactSpace (blowup d) :=
  QuasiCompact.compactSpace_of_compactSpace (structureMap d)
instance blowup_isNoetherian : IsNoetherian (blowup d) := {}

def A : LineBundle (blowup d) := (hyperplane d).pullback (projection d)
abbrev J : LineBundle (blowup d) :=
  PiExponentSeshadri.BlowupGluing.exceptionalLineBundle (centerIdeal d)
abbrev exceptionalInclusion : (J d).sheaf ⟶ structureSheaf (blowup d) :=
  PiExponentSeshadri.BlowupGluing.exceptionalInclusion (centerIdeal d)

theorem exceptional_presents :
    PresentsPullbackIdeal (centerIdeal d) (projection d) (J d) (exceptionalInclusion d) :=
  PiExponentSeshadri.BlowupGluing.exceptional_presents (centerIdeal d)

theorem isBlowup : IsBlowup (centerIdeal d) (projection d) :=
  PiExponentSeshadri.BlowupGluing.isBlowup (centerIdeal d)

abbrev affinePolynomialIdeal :=
  CompactLogJetIdeal.polynomialIdeal d.centers (logCutoff d) (scale d).jetPowers

theorem exists_ampleExponent : ∃ a : ℕ, 1 < a ∧ (((A d).pow a).tensor (J d)).IsAmple :=
  PiExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one
    (centerIdeal d) (centerIdeal_support_ne_top d) (hyperplane d) (hyperplane_ample d)

def ampleExponent : ℕ := (exists_ampleExponent d).choose

theorem ampleExponent_gt_one : 1 < ampleExponent d := (exists_ampleExponent d).choose_spec.1

def H : LineBundle (blowup d) := ((A d).pow (ampleExponent d)).tensor (J d)

theorem H_ample : (H d).IsAmple := (exists_ampleExponent d).choose_spec.2

def interpolationBundle : LineBundle (blowup d) := (A d).tensor (J d)

end PiExponent.BridgeGeometry

end

end OAI

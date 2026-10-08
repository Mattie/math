import Logarithm.JetIdeals
import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal

namespace OAI
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace Logarithm.CompactIdeal

variable {m : ℕ}

abbrev coordinateRing (m : ℕ) := PiExponent.CompactLogJetIdeal.coordinateRing m
abbrev affineSpace (m : ℕ) := PiExponent.CompactLogJetIdeal.affineSpace m
abbrev base := PiExponent.CompactLogJetIdeal.base
abbrev structureMap (m : ℕ) := PiExponent.CompactLogJetIdeal.structureMap m

/-- The actual scheme point with coordinates `(y,c)`. -/
def point (y : ℂ) (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (fullCenter y c)).toRingHom)

theorem point_section (y : ℂ) (c : Fin m → ℂ) :
    point y c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (fullCenter y c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (y : ℂ) (c : Fin m → ℂ) :
    Set.range (point y c) = {JetIdeals.centerPoint y c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (fullCenter y c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (PiExponent.WeightedBezout.pointIdeal (fullCenter y c))

def affineIdeal {J : Type*} [Fintype J] (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : (affineSpace m).IdealSheafData :=
  PiExponentSeshadri.IdealPullback.specIdeal (JetIdeals.polynomialIdeal y c T e)

/-- The affine ideal has exactly the intended finite set of centers as support. -/
theorem support_affineIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal y c T e).support : Set (affineSpace m)) =
      ⋃ a, Set.range (point (y a) (c a)) := by
  rw [affineIdeal, PiExponent.CompactLogJetIdeal.support_specIdeal,
    JetIdeals.zeroLocus_polynomialIdeal y c T e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
    exact ⟨a, (Set.mem_singleton_iff.mp ha).symm⟩

/-- Extend the concrete jet ideal across an affine chart of a compactification. -/
def compactIdeal {J : Type*} [Fintype J] (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) : X.IdealSheafData :=
  PiExponent.CompactJetIdeal.extend (affineIdeal y c T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal y c T e j).comap j = affineIdeal y c T e :=
  PiExponent.CompactJetIdeal.restrict_extend _ j

theorem support_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdeal y c T e j).support : Set X) =
      ⋃ a, Set.range (point (y a) (c a) ≫ j) := by
  rw [compactIdeal, PiExponent.CompactJetIdeal.support_extend (affineIdeal y c T e) j π
    (fun a => point (y a) (c a)) (fun a => by
      rw [Category.assoc, hπ, point_section]) (support_affineIdeal y c T e he),
    support_affineIdeal y c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem compactIdeal_isFinitePresentation {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} [IsLocallyNoetherian X] (j : affineSpace m ⟶ X) :
    (PiExponentSeshadri.IdealModule.closedModule (compactIdeal y c T e j)).IsFinitePresentation :=
  PiExponent.CompactJetIdeal.extend_isFinitePresentation _ j

end Logarithm.CompactIdeal
end
end OAI

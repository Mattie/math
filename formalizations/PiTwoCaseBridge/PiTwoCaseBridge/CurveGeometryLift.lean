import PiTwoCaseBridge.CurveGeometryCore
import OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal

/-! The affine test curves in Theorem 5.1 lift to the ordinary blowup whenever
the substitution sends the center ideal to a nonzero principal ideal. -/

namespace OAI.PiExponent.BridgeGeometry

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri PiExponentSeshadri.Geometry

variable (d : BridgeData) {S : Type} [CommRing S]

/-- Compute the entire pullback ideal sheaf on an affine test scheme. -/
theorem centerIdeal_comap_specMap (φ : CompactLogJetIdeal.coordinateRing d.m →+* S) :
    (centerIdeal d).comap (Spec.map (CommRingCat.ofHom φ) ≫ affineChart d) =
      IdealPullback.specIdeal ((affinePolynomialIdeal d).map φ) := by
  rw [Scheme.IdealSheafData.comap_comp, centerIdeal_restrict]
  exact IdealPullback.specIdeal_comap _ φ

/-- An affine substitution with a regular principal center ideal lifts uniquely.
This also works over rings with zero divisors when the generator is regular. -/
theorem existsUnique_lift_of_principal (φ : CompactLogJetIdeal.coordinateRing d.m →+* S)
    (r : S) (hr : IsRegular r)
    (hI : (affinePolynomialIdeal d).map φ = Ideal.span {r}) :
    ∃! g : Spec (CommRingCat.of S) ⟶ blowup d,
      g ≫ projection d = Spec.map (CommRingCat.ofHom φ) ≫ affineChart d := by
  apply (isBlowup d).2
  let I := IdealPullback.specIdeal (Ideal.span {r})
  have he : (centerIdeal d).comap (Spec.map (CommRingCat.ofHom φ) ≫ affineChart d) =
      I.comap (𝟙 _) := by rw [Scheme.IdealSheafData.comap_id, centerIdeal_comap_specMap, hI]
  apply (InvertibleLocal.invertible_congr he).mpr
  apply InvertibleLocal.invertible_of_affine_equations
  intro x
  let e := (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, e.symm r, ?_, ?_⟩
  · have hleft : IsLeftRegular (e.symm r) := by
      intro a b hab
      apply e.injective
      apply hr.1
      simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
    exact ⟨hleft, hleft.right_of_commute (fun a => mul_comm _ a)⟩
  · rw [show I = IdealPullback.specIdeal (Ideal.span {r}) from rfl,
      IdealPullback.specIdeal_top, Ideal.map_span, Set.image_singleton]
    rfl

end OAI.PiExponent.BridgeGeometry

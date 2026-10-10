import Logarithm.CompactJetIdeal
import Logarithm.ContactIdealLength
import Logarithm.JetCenterIdentification
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree

namespace OAI
noncomputable section
namespace Logarithm.ExceptionalCurveDegree
open AlgebraicGeometry CategoryTheory
open PiExponent PiExponent.ExceptionalCurveDegree
open PiExponentSeshadri.Geometry PiExponent.CurveNormalizationModel
open PiExponent.CurveValuationCenter PiExponent.CurvePlaceCenter

variable {X Y : Scheme.{0}}

theorem localIdeal_compactIdeal {A : Type} [CommRing A]
    {m : ℕ} {K : Type} [Fintype K] (y : K → ℂ) (c : K → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (j : CompactIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (φ : CompactIdeal.coordinateRing m →+* A) :
    localIdeal (CompactIdeal.compactIdeal y c T e j)
      (Spec.map (CommRingCat.ofHom φ) ≫ j) =
        (JetIdeals.polynomialIdeal y c T e).map φ := by
  unfold localIdeal
  rw [Scheme.IdealSheafData.comap_comp, CompactIdeal.restrict_compactIdeal]
  exact localIdeal_specIdeal _ φ

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem compactIdeal_comap_ne_bot_of_generic {m : ℕ} {K : Type} [Fintype K]
    (y : K → ℂ) (c : K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    (j : CompactIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j) :
    (CompactIdeal.compactIdeal y c T e j).comap g ≠ ⊥ := by
  have htop : localIdeal (CompactIdeal.compactIdeal y c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊤ := by
    rw [hgeneric, localIdeal_compactIdeal]
    unfold JetIdeals.polynomialIdeal
    change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
    rw [map_prod]
    have ht : ∀ k : K, (JetIdeals.powerIdeal (y k) (c k) T e).map
        (MvPolynomial.aeval z).toRingHom = ⊤ :=
      fun k => Logarithm.map_powerIdeal_eq_top_of_transcendental z hz (y k) (c k) T e he
    simp only [Ideal.mapHom_apply, ht]
    rw [← Ideal.one_eq_top]
    exact Finset.prod_const_one
  intro hzero
  have hb : localIdeal (CompactIdeal.compactIdeal y c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊥ := by
    simp only [localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

theorem centerMorphism_eq_centeredLift [X.IsSeparated]
    {m : ℕ} (j : CompactIdeal.affineSpace m ⟶ X)
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (y : ℂ) (c : Fin m → ℂ)
    (hc : CurveCenters.Centered z (fullCenter y c) p) :
    centerMorphism f hf p ≫ g =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z (fullCenter y c) hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z (fullCenter y c) hc P

theorem localIdeal_length_eq_logContact [X.IsSeparated]
    {m K : ℕ} (y : Fin K → ℂ) (hy : ∀ k, y k ≠ 0) (hyinj : Function.Injective y)
    (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]
    (k : Fin K) (hcenter : CurveCenters.Centered z (fullCenter (y k) (c k)) p) :
    ((Module.length (PlaceValuationRing.ring p)
      ((PlaceValuationRing.ring p) ⧸ localIdeal (CompactIdeal.compactIdeal y c T e j)
        (centerMorphism f hf p ≫ g))).toNat : ℚ) =
      R * logContact p z (y k) (hy k) (c k) hcenter
        (ContactFamily.nonconstant z (y k) (c k) hz) v := by
  rw [centerMorphism_eq_centeredLift f hf j g z hgeneric p (y k) (c k) hcenter,
    localIdeal_compactIdeal]
  exact polynomialIdeal_colength_eq_logContact p z y hy hyinj c k hcenter
    (ContactFamily.nonconstant z (y k) (c k) hz) T e v hv R he hT

theorem compactIdeal_degree_eq_neg_contact_sum [X.IsSeparated]
    {m K : ℕ} (y : Fin K → ℂ) (hy : ∀ k, y k ≠ 0) (hyinj : Function.Injective y)
    (c : Fin K → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (pX : X ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pX]
    (hj : j ≫ pX = CompactIdeal.structureMap m)
    (π : Y ⟶ X) (J : LineBundle Y) (ι : J.sheaf ⟶ PiExponentSeshadri.Frames.O Y)
    (hJ : PresentsPullbackIdeal (CompactIdeal.compactIdeal y c T e j) π J ι)
    (g : parameterCurve f hf ⟶ Y) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (hfinite : ∀ t : E, Transcendental ℂ t →
      FiniteDimensional (IntermediateField.adjoin ℂ {t}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -R * ∑ p ∈ ContactFamily.places hfinite z y hy c hz,
        ContactFamily.contact hres hfinite z y hy c hz v p := by
  classical
  let I := CompactIdeal.compactIdeal y c T e j
  have hg : I.comap (g ≫ π) ≠ ⊥ :=
    compactIdeal_comap_ne_bot_of_generic f hf y c T e hepos j (g ≫ π) z hz hgeneric
  let D := idealDivisor f hf I π J ι hJ g hg
  let P := ContactFamily.places hfinite z y hy c hz
  have hzero (p : NormalizedPlace ℂ E) (hp : p ∉ P) : D p = 0 := by
    have havoid : (centerMorphism f hf p ≫ g ≫ π)
        (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ∉ I.support := by
      intro hmem
      change _ ∈ ((CompactIdeal.compactIdeal y c T e j).support : Set X) at hmem
      rw [CompactIdeal.support_compactIdeal y c T e hepos j pX hj] at hmem
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨a, ha⟩ := hk
      have hap : CompactIdeal.point (y k) (c k) a = JetIdeals.centerPoint (y k) (c k) := by
        have h := Set.mem_range_self (f := CompactIdeal.point (y k) (c k)) a
        rw [CompactIdeal.range_point] at h
        exact h
      have hclosed : (centerMorphism f hf p ≫ g ≫ π)
          (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
          j (JetIdeals.centerPoint (y k) (c k)) := by
        exact ha.symm.trans (congrArg j hap)
      have hfield : Spec.map (CommRingCat.ofHom
          (algebraMap (PlaceValuationRing.ring p) E)) ≫
          (centerMorphism f hf p ≫ g ≫ π) =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
        rw [← Category.assoc, centerMorphism_generic]
        exact hgeneric
      apply hp
      exact (ContactFamily.mem_places hfinite z y hy c hz p).mpr
        ⟨k, JetCenterIdentification.centered_of_closedPoint_eq p z (y k) (c k) j _ hfield hclosed⟩
    change idealDivisor f hf I π J ι hJ g hg p = 0
    rw [idealDivisor_apply, localIdeal_eq_top_of_not_mem I _ havoid]
    simp
  have hsupport : D.support ⊆ P := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue (p : NormalizedPlace ℂ E) (hp : p ∈ P) :
      (D p : ℚ) = R * ContactFamily.contact hres hfinite z y hy c hz v p := by
    let := hres p
    have hp' : p ∈ ContactFamily.places hfinite z y hy c hz := hp
    let k := ContactFamily.center hfinite z y hy c hz p hp
    have hcenter := ContactFamily.centered hfinite z y hy c hz p hp
    have h := localIdeal_length_eq_logContact f hf y hy hyinj c T e v hv R he hT j (g ≫ π)
      z hz hgeneric p k hcenter
    change (idealDivisor f hf I π J ι hJ g hg p : ℚ) = _
    rw [idealDivisor_apply]
    simpa only [ContactFamily.contact, dite_eq_left hp', I, k] using h
  have hsum : D.sum (fun _ n => (n : ℚ)) =
      R * ∑ p ∈ P, ContactFamily.contact hres hfinite z y hy c hz v p := by
    rw [D.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hd := degree_eq_neg_idealDivisor_sum f hf I π J ι hJ g hg
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -D.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul, P] using hdq

end Logarithm.ExceptionalCurveDegree
end
end OAI

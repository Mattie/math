import Logarithm.BranchOrder

namespace OAI
noncomputable section
namespace Logarithm.ContactFamily
open PiExponent PiExponent.CurveValuationCenter PiExponent.CurveCenters PiExponent.PlaceValuationRing
variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (_hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (fun j => fullCenter (y j) (c j)) hz hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (p : NormalizedPlace ℂ E) :
    p ∈ places hfinite z y hy c hz ↔ ∃ j : Fin K, Centered z (fullCenter (y j) (c j)) p := by
  exact mem_centerPlaces z (fun j => fullCenter (y j) (c j)) hz hfinite p

def center
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y hy c hz) : Fin K :=
  Classical.choose ((mem_places hfinite z y hy c hz p).mp hp)

theorem centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y hy c hz) :
    Centered z (fullCenter (y (center hfinite z y hy c hz p hp)) (c (center hfinite z y hy c hz p hp))) p :=
  Classical.choose_spec ((mem_places hfinite z y hy c hz p).mp hp)

theorem nonconstant (z : Fin (m+1) → E) (y : ℂ) (c : Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ i, z i ≠ algebraMap ℂ E ((fullCenter y c) i) :=
  Centered.exists_nonzero_difference z (fullCenter y c) hz

def contact
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ)
    (p : NormalizedPlace ℂ E) : ℚ := by
  classical
  letI := hres p
  exact if hp : p ∈ places hfinite z y hy c hz then
    Logarithm.logContact p z (y (center hfinite z y hy c hz p hp)) (hy _) (c (center hfinite z y hy c hz p hp))
      (centered hfinite z y hy c hz p hp) (nonconstant z _ _ hz) v
  else 0

theorem contact_pos
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y hy c hz) :
    0 < contact hres hfinite z y hy c hz v p := by
  let := hres p
  simpa only [contact, dite_eq_left hp] using
    Logarithm.logContact_pos p z (y (center hfinite z y hy c hz p hp)) (hy _) (c (center hfinite z y hy c hz p hp))
      (centered hfinite z y hy c hz p hp) (nonconstant z _ _ hz) v hv

theorem contact_nonneg
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) : 0 ≤ contact hres hfinite z y hy c hz v p := by
  by_cases hp : p ∈ places hfinite z y hy c hz
  · exact (contact_pos hres hfinite z y hy c hz v hv p hp).le
  · simp only [contact, dite_eq_right hp, le_refl]

theorem logWord_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : PiExponentApprox.FramePolynomial m)
    (hF : ∀ j, ScaledFormalJet.formalJet (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word F) ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y hy c hz) :
    contact hres hfinite z y hy c hz v p * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word F)) : ℚ) := by
  let := hres p
  have h := Logarithm.logWord_field_order_lower p z (y (center hfinite z y hy c hz p hp)) (hy _)
    (c (center hfinite z y hy c hz p hp)) (centered hfinite z y hy c hz p hp)
    (nonconstant z _ _ hz) v hv H F (hF _) word hne
  simpa only [contact, dite_eq_left hp] using h


end Logarithm.ContactFamily
end
end OAI

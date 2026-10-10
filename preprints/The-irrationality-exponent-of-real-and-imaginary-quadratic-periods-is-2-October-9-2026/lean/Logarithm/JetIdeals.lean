import Logarithm.Scaling
import OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial

namespace OAI
noncomputable section
namespace Logarithm.JetIdeals
open scoped BigOperators
open PiExponent

variable {m : ℕ}

/-- Pull back the rectangular truncated-log ideal from the normalized chart. -/
def powerIdeal (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) : Ideal (PiExponentApprox.FramePolynomial m) :=
  (CompactJetPolynomial.powerIdeal c (CompactJetPolynomial.logPolynomials T) e).comap
    (scaleY y).toRingHom

theorem radical_powerIdeal (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (powerIdeal y c T e).radical = WeightedBezout.pointIdeal (fullCenter y c) := by
  rw [powerIdeal, ← Ideal.comap_radical,
    CompactJetPolynomial.radical_powerIdeal c _
      (CompactJetPolynomial.logPolynomials_eval_zero T) e he]
  have h : (MvPolynomial.aeval (CompactJetPolynomial.center c)).comp (scaleY y) =
      MvPolynomial.aeval (fullCenter y c) := by
    ext i
    cases i using Fin.cases <;>
      simp [scaleY, CompactJetPolynomial.center, fullCenter]
  ext F
  change MvPolynomial.aeval (CompactJetPolynomial.center c) (scaleY y F) = 0 ↔
    MvPolynomial.aeval (fullCenter y c) F = 0
  rw [← AlgHom.comp_apply, h]

def centerPoint (y : ℂ) (c : Fin m → ℂ) :
    PrimeSpectrum (PiExponentApprox.FramePolynomial m) :=
  ⟨WeightedBezout.pointIdeal (fullCenter y c), inferInstance⟩

theorem zeroLocus_powerIdeal (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (powerIdeal y c T e : Set _) = {centerPoint y c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdeal y c T e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

/-- This comap really is the image of the old ideal by the inverse chart. -/
theorem powerIdeal_eq_map_inverse (y : ℂ) (hy : y ≠ 0)
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    powerIdeal y c T e =
      (CompactJetPolynomial.powerIdeal c (CompactJetPolynomial.logPolynomials T) e).map
        (scaleY y⁻¹).toRingHom := by
  let I := CompactJetPolynomial.powerIdeal c (CompactJetPolynomial.logPolynomials T) e
  have h := Ideal.map_comap_of_surjective (scaleY y).toRingHom (scaleY_surjective y hy) I
  have hh := congrArg (Ideal.map (scaleY (m := m) y⁻¹).toRingHom) h
  rw [Ideal.map_map] at hh
  have hi : (scaleY (m := m) y⁻¹).toRingHom.comp (scaleY y).toRingHom = RingHom.id _ := by
    have he := congrArg AlgHom.toRingHom (show (scaleY (m := m) y⁻¹).comp (scaleY y) =
        AlgHom.id ℂ _ by rw [scaleY_comp, inv_mul_cancel₀ hy, scaleY_one])
    exact he
  rw [hi, Ideal.map_id] at hh
  exact hh

theorem formalJet_mem_weighted_of_mem_pow
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (F : PiExponentApprox.FramePolynomial m) (hF : F ∈ powerIdeal y c T e ^ n) :
    ScaledFormalJet.formalJet y c F ∈ JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  rw [← formalJet_scaleY]
  apply CompactJetPolynomial.formalJet_mem_weighted_of_mem_pow c T e v hv hT R he n
  exact Ideal.le_comap_pow (scaleY y).toRingHom n hF

def polynomialIdeal {J : Type*} [Fintype J] (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal (PiExponentApprox.FramePolynomial m) :=
  ∏ j, powerIdeal (y j) (c j) T e

theorem zeroLocus_polynomialIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (polynomialIdeal y c T e : Set _) =
      Set.range (fun j => centerPoint (y j) (c j)) := by
  classical
  have hf (s : Finset J) :
      PrimeSpectrum.zeroLocus (((∏ j ∈ s, powerIdeal (y j) (c j) T e) :
        Ideal (PiExponentApprox.FramePolynomial m)) : Set _) =
      (fun j => centerPoint (y j) (c j)) '' (s : Set J) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
        zeroLocus_powerIdeal (y j) (c j) T e he, ih]
      simp
  simpa only [polynomialIdeal, Finset.coe_univ, Set.image_univ] using hf Finset.univ

theorem polynomialIdeal_pow_le {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (n : ℕ) (j : J) :
    polynomialIdeal y c T e ^ n ≤ powerIdeal (y j) (c j) T e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))

/-- Ordinary powers of the finite-center ideal annihilate the required packets;
equality with a weighted monomial ideal is unnecessary. -/
theorem packet_zero_of_mem_polynomialIdeal_pow {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (F : PiExponentApprox.FramePolynomial m) (hF : F ∈ polynomialIdeal y c T e ^ n)
    (j : J) :
    JetGeometry.rationalCoefficientPacket v (n * R) (ScaledFormalJet.formalJet (y j) (c j) F) =
      (fun _ => (0 : ℂ)) := by
  funext d
  exact formalJet_mem_weighted_of_mem_pow (y j) (c j) T e v hv hT R he n F
    (polynomialIdeal_pow_le y c T e n j hF) d.val d.property

end Logarithm.JetIdeals
end
end OAI

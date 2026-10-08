import Logarithm.JetIdeals
import OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI
noncomputable section
namespace Logarithm.JetPackets
open PiExponent Logarithm.JetIdeals

variable {m : ℕ}

theorem formalJet_packet_surjective (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun F : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (ScaledFormalJet.formalJet y c F)) := by
  intro packet
  obtain ⟨P, hP⟩ := AlgebraicJetPackets.formalJet_packet_surjective c v hv H packet
  obtain ⟨Q, hQ⟩ := scaleY_surjective y hy P
  refine ⟨Q, ?_⟩
  dsimp only
  rw [← formalJet_scaleY, hQ]
  exact hP

theorem powerIdeal_pairwise_isCoprime {J : Type*}
    (y : J → ℂ) (c : J → Fin m → ℂ) (hy : Function.Injective y)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun i j => IsCoprime (powerIdeal (y i) (c i) T e)
      (powerIdeal (y j) (c j) T e)) := by
  intro i j hij
  have hp : IsCoprime (WeightedBezout.pointIdeal (fullCenter (y i) (c i)))
      (WeightedBezout.pointIdeal (fullCenter (y j) (c j))) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    have hc := JetPowerIdealCoprime.pointIdeal_injective heq
    exact hij (hy (congrFun hc 0))
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_powerIdeal (y i) (c i) T e he,
    radical_powerIdeal (y j) (c j) T e he, hp.sup_eq, Ideal.radical_top]

theorem packet_eq_of_sub_mem_pow
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P Q : PiExponentApprox.FramePolynomial m)
    (hPQ : P - Q ∈ powerIdeal y c T e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n * R) (ScaledFormalJet.formalJet y c P) =
      JetGeometry.rationalCoefficientPacket v (n * R) (ScaledFormalJet.formalJet y c Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n * R) _ _).mpr
  simpa only [map_sub] using formalJet_mem_weighted_of_mem_pow y c T e v hv hT R he n
    (P - Q) hPQ

/-- Finite jet interpolation at distinct nonzero Y centers, without a degree bound.
The asymptotically sharp weighted degree bound requires the global geometric step. -/
theorem formalJet_packets_surjective {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (hyinj : Function.Injective y)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m => fun j =>
      JetGeometry.rationalCoefficientPacket v (n * R) (ScaledFormalJet.formalJet (y j) (c j) P)) := by
  classical
  intro packets
  choose P hP using fun j => formalJet_packet_surjective (y j) (hy j) (c j)
    v hv (n * R) (packets j)
  have hcop : Pairwise (fun i j => IsCoprime (powerIdeal (y i) (c i) T e ^ n)
      (powerIdeal (y j) (c j) T e ^ n)) := by
    intro i j hij
    exact (powerIdeal_pairwise_isCoprime y c hyinj T e hepos hij).pow
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, ?_⟩
  funext j
  exact (packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n Q (P j) (hQ j)).trans (hP j)

/-- The exact remaining algebraic interface for the degree-controlled global
construction: representatives modulo the ordinary ideal power suffice. -/
theorem packets_surjective_of_polynomialIdeal_quotient {α J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (hyinj : Function.Injective y)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → PiExponentApprox.FramePolynomial m)
    (hf : Function.Surjective (fun a =>
      Ideal.Quotient.mk (polynomialIdeal y c T e ^ n) (f a))) :
    Function.Surjective (fun a j =>
      JetGeometry.rationalCoefficientPacket v (n * R) (ScaledFormalJet.formalJet (y j) (c j) (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJet_packets_surjective y hy c hyinj T e hepos v hv hT R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  have hdiff : f a - P ∈ polynomialIdeal y c T e ^ n := Ideal.Quotient.eq.mp ha
  refine ⟨a, ?_⟩
  funext j
  exact (packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n (f a) P (polynomialIdeal_pow_le y c T e n j hdiff)).trans (congrFun hP j)

end Logarithm.JetPackets
end
end OAI

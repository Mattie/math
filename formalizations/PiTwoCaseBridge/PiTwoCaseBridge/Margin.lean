import PiTwoCaseBridge.Packets
import PiTwoCaseBridge.RationalWeights
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree

/-!
# From integral packets to the real-cutoff logarithmic statement

The ceiling contributes only a fixed additive cost. By the filtered shear,
the very same source space interpolates the formal logarithmic jets.
-/

namespace PiTwoCaseBridge

open OAI OAI.PiExponent PiExponentApprox MvPolynomial

/-- All exponents in a logarithmic jet packet with real cutoff `T`. -/
def RealPacketExponent {m : ℕ} (V : Fin (m+1) → ℚ) (T : ℝ) :=
  {a : Fin (m+1) →₀ ℕ // Finsupp.weight (fun i => (V i : ℝ)) a < T}

/-- The conclusion of Theorem 5.1 up to the eventual equal-cutoff corollary. -/
def StrictInterpolation {m : ℕ} {J : Type*} (W V : Fin (m+1) → ℚ)
    (c : J → Fin m → ℂ) : Prop :=
  ∃ κ B : ℝ, 0 < κ ∧ κ < 1 ∧ 0 ≤ B ∧ ∀ T : ℝ, 0 < T →
    ∀ y : J → RealPacketExponent V T → ℂ,
      ∃ P : FramePolynomial m,
        WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) (κ * T + B) P ∧
        ∀ j a, MvPowerSeries.coeff a.1 (FormalLogJet.formalJet (c j) P) = y j a

private theorem integral_weight_rat {σ : Type*} [Fintype σ]
    (u : σ → ℕ) (a : σ →₀ ℕ) :
    Finsupp.weight (fun i => (u i : ℚ)) a = (Finsupp.weight u a : ℚ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul]
  exact Finset.sum_congr rfl (fun i _ => by norm_cast)

theorem strictInterpolation_of_integral_polynomialPackets {m : ℕ} {J : Type*}
    [Fintype J] (W V : Fin (m+1) → ℚ) (c : J → Fin m → ℂ)
    (C : Fin m → ℕ)
    (T₀ : ∀ i, V i.succ ≤ (C i : ℚ) * V 0)
    (dw dv : ℕ) (hdw : 0 < dw) (hdv : 0 < dv) (w v : Fin (m+1) → ℕ)
    (hW : ∀ i, (W i : ℝ) = (w i : ℝ) / dw)
    (hV : ∀ i, (V i : ℝ) = (v i : ℝ) / dv)
    (L d B : ℕ) (hd : 0 < d) (hmargin : d * dv < L * dw)
    (hpacket : ∀ N : ℕ, Function.Surjective
      (polynomialPacket (fun j => logarithmicChart (c j) C) w v L (d * N + L * B) N)) :
    StrictInterpolation W V c := by
  classical
  have hl : 0 < L := by
    by_contra! h
    simp [Nat.le_zero.mp h] at hmargin
  have hdwR : (0 : ℝ) < dw := by exact_mod_cast hdw
  have hdvR : (0 : ℝ) < dv := by exact_mod_cast hdv
  have hlR : (0 : ℝ) < L := by exact_mod_cast hl
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hDen : (0 : ℝ) < L * dw := mul_pos hlR hdwR
  let κ : ℝ := (d : ℝ) * dv / (L * dw)
  let B' : ℝ := (d : ℝ) / (L * dw) + (B : ℝ) / dw
  refine ⟨κ, B', div_pos (mul_pos hdR hdvR) hDen, ?_, by positivity, ?_⟩
  · apply (div_lt_iff₀ hDen).mpr
    exact_mod_cast (show d * dv < 1 * (L * dw) by simpa using hmargin)
  intro T hT y
  let N : ℕ := ⌈(dv : ℝ) * T⌉₊
  let u : Fin (m+1) → ℚ := fun i => v i
  have hNV (a : Fin (m+1) →₀ ℕ) :
      Finsupp.weight u a < (N : ℚ) ↔ Finsupp.weight (fun i => (V i : ℝ)) a < T := by
    rw [integral_weight_rat]
    have hcast : (Finsupp.weight v a : ℚ) < (N : ℚ) ↔ Finsupp.weight v a < N := by
      exact_mod_cast (Iff.rfl : Finsupp.weight v a < N ↔ Finsupp.weight v a < N)
    rw [hcast, Nat.lt_ceil, real_weight_eq_integer_div V v dv a hV, div_lt_iff₀ hdvR,
      mul_comm T]
  have hu (i : Fin m) : u i.succ ≤ (C i : ℚ) * u 0 := by
    have h : (V i.succ : ℝ) ≤ (C i : ℝ) * (V 0 : ℝ) := by exact_mod_cast T₀ i
    rw [hV, hV, ← mul_div_assoc] at h
    have h' := (div_le_div_iff_of_pos_right hdvR).mp h
    dsimp [u]
    exact_mod_cast h'
  let domain := sourceBudget (K := ℂ) w L (d * N + L * B)
  have htrunc : Function.Surjective (fun P : domain => fun j =>
      JetGeometry.rationalCoefficientPacket u N
        (FormalLogTruncation.truncatedFormalJet (c j) C P.1)) := by
    intro target
    obtain ⟨P, hP⟩ := hpacket N (fun row =>
      target row.1 ⟨row.2.1, by
        rw [integral_weight_rat]
        exact_mod_cast row.2.2⟩)
    refine ⟨P, ?_⟩
    funext j a
    change MvPowerSeries.coeff a.1 (FormalLogTruncation.truncatedFormalJet (c j) C P.1) =
      target j a
    rw [← logarithmicChart_coeff]
    have hN : Finsupp.weight v a.1 < N := by
      have ha := a.2
      rw [integral_weight_rat] at ha
      exact_mod_cast ha
    exact congrFun hP (j, ⟨a.1, hN⟩)
  have hlog := (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    u (fun i => by dsimp [u]; positivity) N C hu c (fun P : domain => P.1)).mpr htrunc
  obtain ⟨P, hp⟩ := hlog (fun j a => y j ⟨a.1, (hNV a.1).mp a.2⟩)
  refine ⟨P.1, ?_, ?_⟩
  · intro a ha
    have hbound : (L : ℝ) * (Finsupp.weight w a : ℝ) ≤
        (d : ℝ) * N + (L : ℝ) * B := by exact_mod_cast P.2 a ha
    have hN := (Nat.ceil_lt_add_one (show 0 ≤ (dv : ℝ) * T by positivity)).le
    rw [real_weight_eq_integer_div W w dw a hW]
    calc
      _ = ((L : ℝ) * (Finsupp.weight w a : ℝ)) / (L * dw) := by
        field_simp
      _ ≤ ((d : ℝ) * N + (L : ℝ) * B) / (L * dw) :=
        div_le_div_of_nonneg_right hbound hDen.le
      _ ≤ ((d : ℝ) * ((dv : ℝ) * T + 1) + (L : ℝ) * B) / (L * dw) :=
        div_le_div_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hN hdR.le) le_rfl) hDen.le
      _ = κ * T + B' := by dsimp [κ, B']; field_simp; ring
  · intro j a
    exact congrFun (congrFun hp j) ⟨a.1, (hNV a.1).mpr a.2⟩

end PiTwoCaseBridge

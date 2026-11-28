import PiTwoCaseBridge.Certificate
import PiTwoCaseBridge.WeightedArcs

/-!
# From sections on weighted arcs to the finite bridge

A section family spans the pulled-back exceptional power on each nonzero
direction. The coefficient of the corresponding power is its weighted
initial form. The common zero locus is therefore only the origin.
-/

namespace PiTwoCaseBridge

open OAI OAI.PiExponent PiExponentApprox MvPolynomial

theorem strictInterpolation_of_weightedArcImages {m : ℕ} {J ι : Type*}
    [Fintype J] [Finite ι] (W V : Fin (m+1) → ℚ)
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (C : Fin m → ℕ) (hC : ∀ i, V i.succ ≤ (C i : ℚ) * V 0)
    (dw dv : ℕ) (hdw : 0 < dw) (hdv : 0 < dv) (w v : Fin (m+1) → ℕ)
    (hw : ∀ i, (W i : ℝ) = (w i : ℝ) / dw)
    (hv : ∀ i, (V i : ℝ) = (v i : ℝ) / dv)
    (hvpos : ∀ i, 0 < v i) (a R : ℕ) (ha : 0 < a) (hR : 0 < R)
    (P : ι → FramePolynomial m)
    (hdegree : ∀ i, WeightedSliceDegree.SupportBound (fun k => (W k : ℝ))
      ((a : ℝ) * R) (P i))
    (hArc : ∀ j (z : Fin (m+1) → ℂ), z ≠ 0 →
      Ideal.span (Set.range fun i =>
        (↑(WeightedArcs.arc v z (logarithmicChart (c j) C (P i))) : PowerSeries ℂ)) =
        Ideal.span {PowerSeries.X ^ (dv * (a+1) * R)}) :
    StrictInterpolation W V c := by
  let L := dv * (a+1) * R
  let d := dw * a * R
  have hL : 0 < L := Nat.mul_pos (Nat.mul_pos hdv (Nat.succ_pos a)) hR
  have hd : 0 < d := Nat.mul_pos (Nat.mul_pos hdw ha) hR
  have hgap : d * dv < L * dw := by
    change (dw * a * R) * dv < (dv * (a+1) * R) * dw
    calc
      _ = a * (dw * dv * R) := by ring
      _ < (a+1) * (dw * dv * R) := Nat.mul_lt_mul_of_pos_right
        (Nat.lt_succ_self a) (Nat.mul_pos (Nat.mul_pos hdw hdv) hR)
      _ = _ := by ring
  have hdeg (i : ι) : weightedTotalDegree w (P i) ≤ d := by
    apply Finset.sup_le
    intro x hx
    have h := hdegree i x hx
    rw [real_weight_eq_integer_div W w dw x hw] at h
    have hp : (0 : ℝ) < dw := by exact_mod_cast hdw
    have hb := (div_le_iff₀ hp).mp h
    exact_mod_cast (show (Finsupp.weight w x : ℝ) ≤ (d : ℝ) by
      dsimp [d]
      push_cast
      convert hb using 1; ring)
  have hforms (j : J) := WeightedArcs.initialForms_of_series_span v
    (fun i => logarithmicChart (c j) C (P i)) L (hArc j)
  apply strictInterpolation_of_initialForms W V c hc C hC dw dv hdw hdv w v
    hw hv hvpos L d hL hd hgap P hdeg
  · intro j i x hx
    have h := congrArg (fun p : FramePolynomial m => p.coeff x) ((hforms j).1 i _ hx)
    simpa [coeff_weightedHomogeneousComponent] using h
  · intro j
    rw [zeroLocus_span]
    ext z
    change (∀ p ∈ Set.range _, aeval z p = 0) ↔ z ∈ ({0} : Set (Fin (m+1) → ℂ))
    rw [Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hz
      obtain ⟨i, hi⟩ := (hforms j).2 z hz
      exact hi (h _ (Set.mem_range_self i))
    · rintro rfl _ ⟨i,rfl⟩
      simp [MvPolynomial.constantCoeff_eq, coeff_weightedHomogeneousComponent, hL.ne'.symm]

end PiTwoCaseBridge

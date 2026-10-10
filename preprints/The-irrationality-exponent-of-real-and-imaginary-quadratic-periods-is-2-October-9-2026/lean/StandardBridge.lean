import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Tactic

set_option autoImplicit false

namespace CompareChallenge

/-- The literal eventual bound rules out rational values and every Liouville exponent above two. -/
theorem standard_exponent_two_of_eventual_bound (x : ℝ)
    (hbound : ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (1 : ℝ) / (q : ℝ) ^ ν ≤ |x - (p : ℝ) / (q : ℝ)|) :
    Irrational x ∧ ∀ ν : ℝ, 2 < ν → ¬ LiouvilleWith ν x := by
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨Q, hQ, h⟩ := hbound 3 (by norm_num)
    have hQpos : 0 < Q := by omega
    have hden : 1 ≤ r.den := r.pos
    have hlarge : Q ≤ Q * r.den := by nlinarith
    have hQreal : (Q : ℝ) ≠ 0 := by positivity
    have heq : (((Q : ℤ) * r.num : ℤ) : ℝ) / ((Q * r.den : ℕ) : ℝ) = (r : ℝ) := by
      push_cast
      rw [mul_div_mul_left _ _ hQreal, Rat.cast_def]
    have hb := h ((Q : ℤ) * r.num) (Q * r.den) hlarge
    rw [heq, sub_self, abs_zero] at hb
    have : 0 < (1 : ℝ) / ((Q * r.den : ℕ) : ℝ) ^ (3 : ℝ) := by positivity
    linarith
  · intro ν hν hl
    let μ : ℝ := (2 + ν) / 2
    have hμ : 2 < μ := by dsimp [μ]; linarith
    have hμν : μ < ν := by dsimp [μ]; linarith
    obtain ⟨Q, hQ, h⟩ := hbound μ hμ
    have hf := hl.frequently_lt_rpow_neg hμν
    obtain ⟨q, ⟨p, hpne, hp⟩, hq⟩ :=
      (hf.and_eventually (Filter.eventually_ge_atTop Q)).exists
    have hb := h p q hq
    rw [Real.rpow_neg (Nat.cast_nonneg q), ← one_div] at hp
    exact (not_lt_of_ge hb) hp

end CompareChallenge

#print axioms CompareChallenge.standard_exponent_two_of_eventual_bound

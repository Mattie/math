import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace PairedAffineVerification

/-- Any exponent strictly above four is excluded by the literal eventual bound. -/
theorem not_liouvilleWith_of_eventual_bound (x : ℝ)
    (hbound : ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |x - (p : ℝ) / (q : ℝ)|) :
    ∀ nu : ℝ, 4 < nu → ¬ LiouvilleWith nu x := by
  intro nu hnu hl
  let mu : ℝ := (4 + nu) / 2
  have hmu : 4 < mu := by dsimp [mu]; linarith
  have hmunu : mu < nu := by dsimp [mu]; linarith
  obtain ⟨Q, _, hb⟩ := hbound mu hmu
  have hf := hl.frequently_lt_rpow_neg hmunu
  obtain ⟨q, ⟨p, _, hp⟩, hq⟩ :=
    (hf.and_eventually (Filter.eventually_ge_atTop Q)).exists
  exact (not_lt_of_ge (hb p q hq)) hp

end PairedAffineVerification


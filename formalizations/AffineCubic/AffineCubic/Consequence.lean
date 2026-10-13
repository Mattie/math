import OAI.NumberTheory.PiExponent.Approximation.Exponent
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

namespace OAI.AffineCubic
open PiExponent

/-- The conventional unreduced integer-denominator lower bound with cutoff
exponent six. The threshold is allowed to depend on the real number and `nu`. -/
def EventualLowerBoundSix (x : ℝ) : Prop :=
  ∀ nu : ℝ, 6 < nu → ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ,
    Q ≤ q → (q : ℝ) ^ (-nu) ≤ |x - (p : ℝ) / q|

theorem irrational_of_eventualLowerBoundSix {x : ℝ}
    (h : EventualLowerBoundSix x) : Irrational x := by
  rintro ⟨r, hr⟩
  obtain ⟨Q, hQ, hb⟩ := h 7 (by norm_num)
  have hQpos : 0 < Q := by omega
  have hden : 1 ≤ r.den := r.pos
  have hq : Q ≤ Q * r.den := by nlinarith
  have hqpos : 0 < Q * r.den := Nat.mul_pos hQpos r.pos
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQpos
  have hdR : (r.den : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt r.pos
  have heq : (((Q : ℤ) * r.num : ℤ) : ℝ) / ((Q * r.den : ℕ) : ℝ) = (r : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    field_simp [hQR, hdR]
  have hlower := hb ((Q : ℤ) * r.num) (Q * r.den) hq
  rw [heq, hr, sub_self, abs_zero] at hlower
  exact (not_lt_of_ge hlower)
    (Real.rpow_pos_of_pos (by exact_mod_cast hqpos) (-7))

theorem finite_good_approximations_of_eventualLowerBoundSix {x nu : ℝ}
    (h : EventualLowerBoundSix x) (hnu : 6 < nu) :
    (GoodRationalApproximations x nu).Finite := by
  obtain ⟨Q, _, hb⟩ := h nu hnu
  apply (finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hltQ : r.den < Q := by
    by_contra hq
    have he := hb r.num r.den (by omega)
    rw [← Rat.cast_def] at he
    exact (not_lt_of_ge he) hr.2.2
  refine ⟨hltQ.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast r.pos) (by linarith)

theorem irrationalityExponent_le_six_of_eventualLowerBoundSix {x : ℝ}
    (h : EventualLowerBoundSix x) : irrationalityExponent x ≤ 6 := by
  have htwo := two_mem_approximationExponents (irrational_of_eventualLowerBoundSix h)
  have hb : ∀ nu ∈ ApproximationExponents x, nu ≤ 6 := by
    intro nu hnu
    by_contra hlt
    exact (finite_good_approximations_of_eventualLowerBoundSix h (by linarith)).not_infinite hnu.2
  exact csSup_le ⟨2, htwo⟩ hb

end OAI.AffineCubic

namespace OAI.AffineCubic
/-- Negating arbitrarily large exceptional approximations gives the endpoint. -/
theorem eventualLowerBoundSix_of_not_unbounded {x : ℝ}
    (h : ∀ nu : ℝ, 6 < nu → ¬ (∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |x - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu))) :
    EventualLowerBoundSix x := by
  intro nu hnu
  have hn := h nu hnu
  push Not at hn
  obtain ⟨Q, hQ⟩ := hn
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  intro p q hq
  exact (hQ p q ((le_max_left Q 2).trans hq)).le
end OAI.AffineCubic

namespace OAI.AffineCubic
/-- Any exponent strictly above six is excluded by the literal eventual bound. -/
theorem not_liouvilleWith_of_eventual_bound (x : ℝ)
    (hbound : ∀ nu : ℝ, 6 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |x - (p : ℝ) / (q : ℝ)|) :
    ∀ nu : ℝ, 6 < nu → ¬ LiouvilleWith nu x := by
  intro nu hnu hl
  let mu : ℝ := (6 + nu) / 2
  have hmu : 6 < mu := by dsimp [mu]; linarith
  have hmunu : mu < nu := by dsimp [mu]; linarith
  obtain ⟨Q, _, hb⟩ := hbound mu hmu
  have hf := hl.frequently_lt_rpow_neg hmunu
  obtain ⟨q, ⟨p, _, hp⟩, hq⟩ :=
    (hf.and_eventually (Filter.eventually_ge_atTop Q)).exists
  exact (not_lt_of_ge (hb p q hq)) hp

end OAI.AffineCubic


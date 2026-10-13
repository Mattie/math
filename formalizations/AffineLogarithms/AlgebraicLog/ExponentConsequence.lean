import OAI.NumberTheory.PiExponent.Approximation.Exponent

namespace OAI.AlgebraicLog
open PiExponent

/-- The conventional unreduced integer-denominator lower bound with cutoff
exponent four. The threshold is allowed to depend on the real number and `nu`. -/
def EventualLowerBoundFour (x : ℝ) : Prop :=
  ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ,
    Q ≤ q → (q : ℝ) ^ (-nu) ≤ |x - (p : ℝ) / q|

theorem irrational_of_eventualLowerBoundFour {x : ℝ}
    (h : EventualLowerBoundFour x) : Irrational x := by
  rintro ⟨r, hr⟩
  obtain ⟨Q, hQ, hb⟩ := h 5 (by norm_num)
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
    (Real.rpow_pos_of_pos (by exact_mod_cast hqpos) (-5))

theorem finite_good_approximations_of_eventualLowerBoundFour {x nu : ℝ}
    (h : EventualLowerBoundFour x) (hnu : 4 < nu) :
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

theorem irrationalityExponent_le_four_of_eventualLowerBoundFour {x : ℝ}
    (h : EventualLowerBoundFour x) : irrationalityExponent x ≤ 4 := by
  have htwo := two_mem_approximationExponents (irrational_of_eventualLowerBoundFour h)
  have hb : ∀ nu ∈ ApproximationExponents x, nu ≤ 4 := by
    intro nu hnu
    by_contra hlt
    exact (finite_good_approximations_of_eventualLowerBoundFour h (by linarith)).not_infinite hnu.2
  exact csSup_le ⟨2, htwo⟩ hb

end OAI.AlgebraicLog

import PairedAffine.Concrete
import PairedAffine.Endpoint

namespace OAI.PairedAffine
noncomputable section

/-- The shifted quadratic period has an eventual lower bound for every
approximation exponent strictly greater than four. -/
theorem shifted_period_eventualLowerBound :
    AlgebraicLog.EventualLowerBoundFour
      (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) := by
  classical
  apply Endpoint.paired_eventualLowerBound Field.base Field.sqrtTwo Field.sqrtThree
    Field.base_integral Field.sqrtTwo_integral Field.sqrtThree_integral
    Field.degree (Field.sigma true true) Concrete.realBase
    (lt_trans zero_lt_one Concrete.realBase_gt_one)
    (ne_of_gt Concrete.realBase_gt_one)
    (by simp [Concrete.realBase, Field.signedRoot])
    Concrete.target (ne_of_gt Concrete.target_pos) Concrete.good Concrete.good_card
  · intro σ hσ
    simp only [Concrete.good, Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl
    · exact Concrete.compatible true
    · exact Concrete.compatible false
  · intro σ hσ
    simp only [Concrete.good, Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl
    · exact Concrete.scale_norm_le true
    · exact Concrete.scale_norm_le false

/-- Quantifiers are explicit: the denominator threshold depends on the
exponent, and the inequality then holds for every integer numerator. -/
theorem shifted_period_explicit_bound (nu : ℝ) (hnu : 4 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤
        |(Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) - (p : ℝ) / q| :=
  shifted_period_eventualLowerBound nu hnu

theorem shifted_period_irrational :
    Irrational (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) :=
  AlgebraicLog.irrational_of_eventualLowerBoundFour shifted_period_eventualLowerBound

theorem shifted_period_irrationalityExponent_le_four :
    PiExponent.irrationalityExponent
      (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) ≤ 4 :=
  AlgebraicLog.irrationalityExponent_le_four_of_eventualLowerBoundFour
    shifted_period_eventualLowerBound

end
end OAI.PairedAffine

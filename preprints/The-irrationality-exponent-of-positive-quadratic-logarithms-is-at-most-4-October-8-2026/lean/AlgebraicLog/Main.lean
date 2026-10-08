import AlgebraicLog.DeterminantContradiction
import AlgebraicLog.FieldRealization
import AlgebraicLog.ExponentConsequence

namespace OAI.AlgebraicLog
noncomputable section
open PiExponent DeterminantData

theorem eventualLowerBoundFour_of_not_unbounded {x : ℝ}
    (h : ∀ nu : ℝ, 4 < nu → ¬ ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |x - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) : EventualLowerBoundFour x := by
  intro nu hnu
  have hbad := h nu hnu
  push Not at hbad
  obtain ⟨Q, hQ⟩ := hbad
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  intro p q hq
  exact (hQ p q ((le_max_left Q 2).trans hq)).le

/-- Every positive real algebraic number of degree two other than one has the
rational-approximation lower bound at each exponent strictly above four. The
base may be nonintegral and its other conjugate may be negative. -/
theorem quadratic_log_eventualLowerBound (alpha : ℝ) (hpos : 0 < alpha)
    (hone : alpha ≠ 1) (halg : IsAlgebraic ℚ alpha)
    (hdegree : (minpoly ℚ alpha).natDegree = 2) :
    EventualLowerBoundFour (Real.log alpha) := by
  let F := FieldRealization.RealField alpha
  letI : NumberField F := FieldRealization.realField_numberField halg
  let a : F := FieldRealization.generator alpha
  let σ₀ : F →ₐ[ℚ] ℂ := FieldRealization.distinguishedEmbedding alpha
  have hdeg : Module.finrank ℚ F = 2 := FieldRealization.realField_finrank halg hdegree
  obtain ⟨D, hD, hint⟩ := FieldRealization.exists_positive_integral_multiple a
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  have hlog : Real.log alpha ≠ 0 := by
    intro hz
    have he := Real.exp_log hpos
    rw [hz, Real.exp_zero] at he
    exact hone he.symm
  let rho : ℝ := 100 * max 1 |Real.log alpha|
  have hrho : 100 ≤ rho := by
    dsimp [rho]
    nlinarith [le_max_left (1 : ℝ) |Real.log alpha|]
  have hrhoTarget : 100 * |Real.log alpha| ≤ rho := by
    dsimp [rho]
    nlinarith [le_max_right (1 : ℝ) |Real.log alpha|]
  apply eventualLowerBoundFour_of_not_unbounded
  intro nu hnu hbad
  obtain ⟨d⟩ := exists_admissible_parameters (Real.log alpha) nu
    Arithmetic.lcmConstant collisionConstant rho (Real.log D)
    (EmbeddingBudget.embeddingCost a) (|Real.log alpha| + 1) hnu
    Arithmetic.lcmConstant_pos collisionConstant_pos hlog hrho hrhoTarget
    (Real.log_natCast_nonneg D) (EmbeddingBudget.embeddingCost_nonneg a) (by positivity) hbad
  exact DeterminantContradiction.no_fixed_data a hdeg σ₀ alpha hpos hone
    (FieldRealization.distinguishedEmbedding_generator alpha) D hDpos hint hnu d

/-- Explicit unreduced denominator statement, including its quantifier order. -/
theorem quadratic_log_explicit_bound (alpha : ℝ) (hpos : 0 < alpha)
    (hone : alpha ≠ 1) (halg : IsAlgebraic ℚ alpha)
    (hdegree : (minpoly ℚ alpha).natDegree = 2) (nu : ℝ) (hnu : 4 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.log alpha - (p : ℝ) / q| :=
  quadratic_log_eventualLowerBound alpha hpos hone halg hdegree nu hnu

theorem quadratic_log_irrational (alpha : ℝ) (hpos : 0 < alpha)
    (hone : alpha ≠ 1) (halg : IsAlgebraic ℚ alpha)
    (hdegree : (minpoly ℚ alpha).natDegree = 2) : Irrational (Real.log alpha) :=
  irrational_of_eventualLowerBoundFour
    (quadratic_log_eventualLowerBound alpha hpos hone halg hdegree)

theorem quadratic_log_irrationalityExponent_le_four (alpha : ℝ) (hpos : 0 < alpha)
    (hone : alpha ≠ 1) (halg : IsAlgebraic ℚ alpha)
    (hdegree : (minpoly ℚ alpha).natDegree = 2) :
    irrationalityExponent (Real.log alpha) ≤ 4 :=
  irrationalityExponent_le_four_of_eventualLowerBoundFour
    (quadratic_log_eventualLowerBound alpha hpos hone halg hdegree)

end
end OAI.AlgebraicLog

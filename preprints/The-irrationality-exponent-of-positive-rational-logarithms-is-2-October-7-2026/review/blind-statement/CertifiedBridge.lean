import Logarithm.Main

/-- The independently frozen Mathlib-only specification, now with a proof.
The specification file Challenge.lean is deliberately not imported. -/
theorem log_rational_challenge (a : ℚ) (ha : 0 < a) (ha_ne_one : a ≠ 1) :
    Irrational (Real.log (a : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ Q : ℕ, 2 ≤ Q ∧
          ∀ (p : ℤ) (q : ℕ), Q ≤ q →
            Real.rpow (q : ℝ) (-(2 + ε)) ≤
              |Real.log (a : ℝ) - (p : ℝ) / (q : ℝ)| := by
  have h := OAI.Logarithm.DeterminantContradiction.rational_log_eventualLowerBound
    a ha ha_ne_one
  refine ⟨OAI.LogarithmExtension.irrational_of_eventualLowerBound h, ?_⟩
  intro ε hε
  exact h (2 + ε) (by linarith)

#print axioms log_rational_challenge
#print log_rational_challenge

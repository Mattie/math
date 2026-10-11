import AlgebraicLog.Examples
#check OAI.AlgebraicLog.quadratic_log_explicit_bound
#check OAI.AlgebraicLog.quadratic_log_irrationalityExponent_le_four
#print OAI.AlgebraicLog.EventualLowerBoundFour
#print OAI.PiExponent.GoodRationalApproximations
#print OAI.PiExponent.ApproximationExponents
#print OAI.PiExponent.irrationalityExponent
#print axioms OAI.AlgebraicLog.quadratic_log_explicit_bound
#print axioms OAI.AlgebraicLog.quadratic_log_irrational
#print axioms OAI.AlgebraicLog.quadratic_log_irrationalityExponent_le_four
#print axioms OAI.AlgebraicLog.Examples.first_sample_bound
#print axioms OAI.AlgebraicLog.Examples.second_sample_bound
#print axioms OAI.AlgebraicLog.Examples.first_sample_conjugate_check
#print axioms OAI.AlgebraicLog.Examples.second_sample_conjugate_check

-- Literal target from the independently written specification, without using
-- the extension's EventualLowerBoundFour definition in the proposition.
example (alpha : ℝ) (hpos : 0 < alpha) (hone : alpha ≠ 1)
    (halg : IsAlgebraic ℚ alpha) (hdegree : (minpoly ℚ alpha).natDegree = 2)
    (nu : ℝ) (hnu : 4 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.log alpha - (p : ℝ) / q| :=
  OAI.AlgebraicLog.quadratic_log_explicit_bound alpha hpos hone halg hdegree nu hnu

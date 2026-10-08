import Logarithm.DeterminantContradiction

namespace OAI.Logarithm

/-- The irrationality exponent of the real logarithm of a positive rational
number other than one is exactly two. -/
theorem rational_log_irrationalityExponent_eq_two (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1) :
    PiExponent.irrationalityExponent (Real.log (a : ℝ)) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (DeterminantContradiction.rational_log_eventualLowerBound a ha ha1)

theorem log_two_irrationalityExponent_eq_two :
    PiExponent.irrationalityExponent (Real.log 2) = 2 := by
  simpa using rational_log_irrationalityExponent_eq_two 2 (by norm_num) (by norm_num)

theorem log_three_irrationalityExponent_eq_two :
    PiExponent.irrationalityExponent (Real.log 3) = 2 := by
  simpa using rational_log_irrationalityExponent_eq_two 3 (by norm_num) (by norm_num)

/-- The endpoint also supplies the original unreduced integer formulation. -/
theorem rational_log_integer_eventualLowerBound (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1) :
    PiExponent.IntegerEventualLowerBound (Real.log (a : ℝ)) :=
  (PiExponent.eventualLowerBound_iff_integer _).mp
    (DeterminantContradiction.rational_log_eventualLowerBound a ha ha1)

theorem rational_log_explicit_bound (a : ℚ) (ha : 0 < a) (ha1 : a ≠ 1)
    (ν : ℝ) (hν : 2 < ν) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ)^(-ν) ≤ |Real.log (a : ℝ) - (p : ℝ)/(q : ℝ)| :=
  rational_log_integer_eventualLowerBound a ha ha1 ν hν

end OAI.Logarithm

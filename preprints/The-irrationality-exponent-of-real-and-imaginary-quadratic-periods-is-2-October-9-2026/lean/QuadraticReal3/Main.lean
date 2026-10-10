import QuadraticReal3.Endpoint
import QuadraticReal3.DeterminantContradiction
import Logarithm.ExponentConsequence

namespace OAI.QuadraticReal3
open PiExponent
noncomputable section

theorem period_irrationalityExponent_eq_two (base : PeriodData) :
    irrationalityExponent base.angle = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (DeterminantContradiction.period_eventualLowerBound base)

theorem normalized_log_sqrt_three_eventualLowerBound :
    EventualLowerBound (Real.log (2 + Real.sqrt 3) / Real.sqrt 3) :=
  DeterminantContradiction.period_eventualLowerBound sqrtThreePeriod

theorem normalized_log_sqrt_three_irrationalityExponent_eq_two :
    irrationalityExponent (Real.log (2 + Real.sqrt 3) / Real.sqrt 3) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    normalized_log_sqrt_three_eventualLowerBound

theorem normalized_log_sqrt_three_integer_eventualLowerBound :
    IntegerEventualLowerBound (Real.log (2 + Real.sqrt 3) / Real.sqrt 3) :=
  (eventualLowerBound_iff_integer _).mp normalized_log_sqrt_three_eventualLowerBound

/-- Fully expanded target, with no arithmetic, interpolation, or analytic premise. -/
theorem normalized_log_sqrt_three_explicit_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤
        |Real.log (2 + Real.sqrt 3) / Real.sqrt 3 - (p : ℝ) / (q : ℝ)| :=
  normalized_log_sqrt_three_integer_eventualLowerBound nu hnu

end
end OAI.QuadraticReal3

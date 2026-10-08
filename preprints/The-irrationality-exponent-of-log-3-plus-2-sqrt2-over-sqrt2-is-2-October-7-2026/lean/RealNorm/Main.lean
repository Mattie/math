import RealNorm.Endpoint
import RealNorm.DeterminantContradiction
import Logarithm.ExponentConsequence

namespace OAI.RealNorm
open PiExponent
noncomputable section

theorem period_irrationalityExponent_eq_two (base : PeriodData) :
    irrationalityExponent base.angle = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (DeterminantContradiction.period_eventualLowerBound base)

theorem normalized_log_sqrt_two_eventualLowerBound :
    EventualLowerBound (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) :=
  DeterminantContradiction.period_eventualLowerBound sqrtTwoPeriod

theorem normalized_log_sqrt_two_irrationalityExponent_eq_two :
    irrationalityExponent (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    normalized_log_sqrt_two_eventualLowerBound

theorem normalized_log_sqrt_two_integer_eventualLowerBound :
    IntegerEventualLowerBound (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) :=
  (eventualLowerBound_iff_integer _).mp normalized_log_sqrt_two_eventualLowerBound

/-- Fully expanded target, with no arithmetic, interpolation, or analytic premise. -/
theorem normalized_log_sqrt_two_explicit_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤
        |Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 - (p : ℝ) / (q : ℝ)| :=
  normalized_log_sqrt_two_integer_eventualLowerBound nu hnu

end
end OAI.RealNorm

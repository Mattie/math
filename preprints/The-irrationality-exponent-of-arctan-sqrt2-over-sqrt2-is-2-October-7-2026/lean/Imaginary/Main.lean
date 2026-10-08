import Imaginary.Endpoint
import Imaginary.DeterminantContradiction
import Imaginary.Scaling

namespace OAI.Imaginary
open PiExponent
noncomputable section

theorem period_irrationalityExponent_eq_two (base : PeriodData) :
    irrationalityExponent base.angle = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (DeterminantContradiction.period_eventualLowerBound base)

theorem normalized_arctan_sqrt_two_eventualLowerBound :
    EventualLowerBound (Real.arctan (Real.sqrt 2) / Real.sqrt 2) := by
  have hh := eventualLowerBound_div_nat
    (DeterminantContradiction.period_eventualLowerBound sqrtTwoPeriod) 2 (by norm_num)
  convert hh using 1
  simp only [sqrtTwoPeriod, normalizedAngle, Nat.cast_ofNat]
  ring

theorem normalized_arctan_sqrt_two_irrationalityExponent_eq_two :
    irrationalityExponent (Real.arctan (Real.sqrt 2) / Real.sqrt 2) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    normalized_arctan_sqrt_two_eventualLowerBound

theorem normalized_arctan_sqrt_two_integer_eventualLowerBound :
    IntegerEventualLowerBound (Real.arctan (Real.sqrt 2) / Real.sqrt 2) :=
  (eventualLowerBound_iff_integer _).mp normalized_arctan_sqrt_two_eventualLowerBound

/-- Fully expanded target, with no arithmetic, interpolation, or analytic premise. -/
theorem normalized_arctan_sqrt_two_explicit_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤
        |Real.arctan (Real.sqrt 2) / Real.sqrt 2 - (p : ℝ) / (q : ℝ)| :=
  normalized_arctan_sqrt_two_integer_eventualLowerBound nu hnu

end
end OAI.Imaginary

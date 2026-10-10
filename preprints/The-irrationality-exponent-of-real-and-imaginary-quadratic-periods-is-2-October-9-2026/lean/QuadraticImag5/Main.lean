import QuadraticImag5.Endpoint
import QuadraticImag5.DeterminantContradiction
import QuadraticImag5.Scaling

namespace OAI.QuadraticImag5
open PiExponent
noncomputable section

theorem period_irrationalityExponent_eq_two (base : PeriodData) :
    irrationalityExponent base.angle = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (DeterminantContradiction.period_eventualLowerBound base)

theorem normalized_arctan_sqrt_five_eventualLowerBound :
    EventualLowerBound (Real.arctan (Real.sqrt 5) / Real.sqrt 5) := by
  have hh := eventualLowerBound_div_nat
    (DeterminantContradiction.period_eventualLowerBound sqrtFivePeriod) 2 (by norm_num)
  convert hh using 1
  simp only [sqrtFivePeriod, normalizedAngle, Nat.cast_ofNat]
  ring

theorem normalized_arctan_sqrt_five_irrationalityExponent_eq_two :
    irrationalityExponent (Real.arctan (Real.sqrt 5) / Real.sqrt 5) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    normalized_arctan_sqrt_five_eventualLowerBound

theorem normalized_arctan_sqrt_five_integer_eventualLowerBound :
    IntegerEventualLowerBound (Real.arctan (Real.sqrt 5) / Real.sqrt 5) :=
  (eventualLowerBound_iff_integer _).mp normalized_arctan_sqrt_five_eventualLowerBound

/-- Fully expanded target, with no arithmetic, interpolation, or analytic premise. -/
theorem normalized_arctan_sqrt_five_explicit_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤
        |Real.arctan (Real.sqrt 5) / Real.sqrt 5 - (p : ℝ) / (q : ℝ)| :=
  normalized_arctan_sqrt_five_integer_eventualLowerBound nu hnu

end
end OAI.QuadraticImag5

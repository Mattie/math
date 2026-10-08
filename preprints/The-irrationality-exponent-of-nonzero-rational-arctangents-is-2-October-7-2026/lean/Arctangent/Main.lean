import Arctangent.ArctanCenters
import Arctangent.DeterminantContradiction
import Arctangent.Scaling
import OAI.NumberTheory.PiExponent.Main

namespace OAI.Arctangent
open PiExponent
noncomputable section

/-- The first target uses the advertised numerator 3+4i and denominator 5. -/
def halfPeriod : PeriodData where
  num := ⟨3, 4⟩
  den := 5
  den_pos := by norm_num
  angle := 2 * Real.arctan (1 / 2)
  angle_ne_zero := by positivity
  exp_angle := by
    have hh := exp_two_arctan (1 / 2)
    norm_num [alpha, realPart, imagPart] at hh
    push_cast
    rw [hh]
    simp [GaussianInt.toComplex_def']
    ring
  powers_injective := by
    have hh := alpha_powers_injective (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    norm_num [alpha, realPart, imagPart] at hh
    convert hh using 1
    ext n
    congr 1
    simp [GaussianInt.toComplex_def']
    ring

theorem arctan_half_eventualLowerBound : EventualLowerBound (Real.arctan (1 / 2)) := by
  have hh := eventualLowerBound_div_nat
    (DeterminantContradiction.period_eventualLowerBound halfPeriod) 2 (by norm_num)
  simpa [halfPeriod] using hh

theorem arctan_half_irrationalityExponent_eq_two :
    irrationalityExponent (Real.arctan (1 / 2)) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound arctan_half_eventualLowerBound

/-- Every nonzero rational arctangent has exponent two. The exceptional torsion
centers r=1 and r=-1 are handled by the certified bound for pi. -/
theorem rational_arctan_eventualLowerBound (r : ℚ) (hr : r ≠ 0) :
    EventualLowerBound (Real.arctan (r : ℝ)) := by
  have hpi4 := eventualLowerBound_div_nat pi_eventual_lower_bound 4 (by norm_num)
  by_cases hr1 : r = 1
  · subst r
    simpa [Real.arctan_one] using hpi4
  by_cases hrm1 : r = -1
  · subst r
    simpa [Real.arctan_neg, Real.arctan_one] using eventualLowerBound_neg hpi4
  have hh := eventualLowerBound_div_nat
    (DeterminantContradiction.period_eventualLowerBound (arctanPeriod r hr hr1 hrm1))
    2 (by norm_num)
  simpa [arctanPeriod] using hh

theorem rational_arctan_irrationalityExponent_eq_two (r : ℚ) (hr : r ≠ 0) :
    irrationalityExponent (Real.arctan (r : ℝ)) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (rational_arctan_eventualLowerBound r hr)

theorem rational_arctan_integer_eventualLowerBound (r : ℚ) (hr : r ≠ 0) :
    IntegerEventualLowerBound (Real.arctan (r : ℝ)) :=
  (eventualLowerBound_iff_integer _).mp (rational_arctan_eventualLowerBound r hr)

/-- Fully expanded approximation bound; no non-torsion or interpolation premise remains. -/
theorem rational_arctan_explicit_bound (r : ℚ) (hr : r ≠ 0) (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.arctan (r : ℝ) - (p : ℝ) / (q : ℝ)| :=
  rational_arctan_integer_eventualLowerBound r hr nu hnu

theorem arctan_half_explicit_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.arctan (1 / 2) - (p : ℝ) / (q : ℝ)| :=
  (eventualLowerBound_iff_integer _).mp arctan_half_eventualLowerBound nu hnu

end
end OAI.Arctangent

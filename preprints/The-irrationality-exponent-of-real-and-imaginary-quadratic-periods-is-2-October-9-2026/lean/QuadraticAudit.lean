import QuadraticReal3.Main
import QuadraticImag5.Main

namespace QuadraticPilotSpecification

/-- The threshold precedes both integer variables and depends on the exponent. -/
def Real3Bound : Prop := ∀ nu : ℝ, 2 < nu →
  ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
    (q : ℝ) ^ (-nu) ≤
      |Real.log (2 + Real.sqrt 3) / Real.sqrt 3 - (p : ℝ) / (q : ℝ)|

def Imag5Bound : Prop := ∀ nu : ℝ, 2 < nu →
  ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
    (q : ℝ) ^ (-nu) ≤
      |Real.arctan (Real.sqrt 5) / Real.sqrt 5 - (p : ℝ) / (q : ℝ)|

theorem real3_bound : Real3Bound :=
  OAI.QuadraticReal3.normalized_log_sqrt_three_explicit_bound

theorem imag5_bound : Imag5Bound :=
  OAI.QuadraticImag5.normalized_arctan_sqrt_five_explicit_bound

theorem real3_exponent : OAI.PiExponent.irrationalityExponent
    (Real.log (2 + Real.sqrt 3) / Real.sqrt 3) = 2 :=
  OAI.QuadraticReal3.normalized_log_sqrt_three_irrationalityExponent_eq_two

theorem imag5_exponent : OAI.PiExponent.irrationalityExponent
    (Real.arctan (Real.sqrt 5) / Real.sqrt 5) = 2 :=
  OAI.QuadraticImag5.normalized_arctan_sqrt_five_irrationalityExponent_eq_two

theorem real3_irrational : Irrational (Real.log (2 + Real.sqrt 3) / Real.sqrt 3) :=
  OAI.LogarithmExtension.irrational_of_eventualLowerBound
    OAI.QuadraticReal3.normalized_log_sqrt_three_eventualLowerBound

theorem imag5_irrational : Irrational (Real.arctan (Real.sqrt 5) / Real.sqrt 5) :=
  OAI.LogarithmExtension.irrational_of_eventualLowerBound
    OAI.QuadraticImag5.normalized_arctan_sqrt_five_eventualLowerBound

end QuadraticPilotSpecification

#print axioms QuadraticPilotSpecification.real3_bound
#print axioms QuadraticPilotSpecification.imag5_bound
#print axioms QuadraticPilotSpecification.real3_exponent
#print axioms QuadraticPilotSpecification.imag5_exponent
#print axioms QuadraticPilotSpecification.real3_irrational
#print axioms QuadraticPilotSpecification.imag5_irrational
#print OAI.PiExponent.EventualLowerBound
#print OAI.PiExponent.irrationalityExponent
#print OAI.QuadraticReal3.PeriodData
#print OAI.QuadraticImag5.PeriodData

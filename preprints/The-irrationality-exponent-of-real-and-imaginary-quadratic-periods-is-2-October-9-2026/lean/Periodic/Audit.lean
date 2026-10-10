import Periodic.Main
import PeriodicGeometry.Nonvacuity

set_option pp.universes true
set_option pp.explicit true

#print OAI.Periodic.scaled_pi_explicit_bound
#print OAI.Periodic.scaled_pi_integer_explicit_bound
#print OAI.Periodic.scaled_pi_irrationalityExponent_eq_two
#print OAI.PiExponent.irrationalityExponent
#print OAI.PiExponent.EventualLowerBound
#print OAI.Periodic.PeriodData
#print OAI.PiExponent.PeriodicGeometryData

#print axioms OAI.PiExponent.PeriodicGeometryData.exact_weighted_curve_inequality
#print axioms OAI.PiExponent.PeriodicBlowupGeometry.interpolationBundle_ample
#print axioms OAI.PiExponent.PeriodicInterpolation.eventual_packets
#print axioms OAI.Periodic.GlobalMatrixInterpolation.cofinal_actualMatrix
#print axioms OAI.Periodic.DeterminantContradiction.period_eventualLowerBound
#print axioms OAI.Periodic.scaled_pi_explicit_bound
#print axioms OAI.Periodic.scaled_pi_irrationalityExponent_eq_two
#print axioms OAI.PiExponent.PeriodicNonvacuity.sample

/-- Literal independent target proposition; no approximation data binder. -/
example (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt 2 - (p : ℝ) / q| :=
  OAI.Periodic.scaled_pi_explicit_bound nu hnu

example (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt 2 - (p : ℝ) / (q : ℝ)| :=
  OAI.Periodic.scaled_pi_integer_explicit_bound nu hnu

example : OAI.PiExponent.irrationalityExponent (Real.pi / Real.sqrt 2) = 2 :=
  OAI.Periodic.scaled_pi_irrationalityExponent_eq_two

example : OAI.PiExponent.PeriodicGeometryData :=
  OAI.PiExponent.PeriodicNonvacuity.sample

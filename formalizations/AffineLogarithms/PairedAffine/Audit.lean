import PairedAffine.Main

namespace OAI.PairedAffine.Audit

/-- A literal-expression witness keeps the target and quantifier order
visible without referring to either concrete target alias. -/
theorem literal_bound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤
          |Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3 - (p : ℝ) / q| :=
  shifted_period_explicit_bound

/-- The named invariant uses reduced rational denominators and a strict
nonzero approximation error. This identity exposes its definition. -/
theorem exponent_definition (x : ℝ) :
    PiExponent.irrationalityExponent x =
      sSup {nu : ℝ | 0 < nu ∧
        ({r : ℚ | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧
          |x - (r : ℝ)| < (r.den : ℝ) ^ (-nu)} : Set ℚ).Infinite} := rfl

end OAI.PairedAffine.Audit

#check OAI.PairedAffine.shifted_period_eventualLowerBound
#check OAI.PairedAffine.shifted_period_explicit_bound
#check OAI.PairedAffine.shifted_period_irrational
#check OAI.PairedAffine.shifted_period_irrationalityExponent_le_four
#check OAI.PairedAffine.Audit.literal_bound
#check OAI.PairedAffine.Audit.exponent_definition

#print axioms OAI.PairedAffine.shifted_period_eventualLowerBound
#print axioms OAI.PairedAffine.shifted_period_explicit_bound
#print axioms OAI.PairedAffine.shifted_period_irrational
#print axioms OAI.PairedAffine.shifted_period_irrationalityExponent_le_four
#print axioms OAI.PairedAffine.Audit.literal_bound

/- The guards enforce the foundation-only policy for every required endpoint.
The unguarded commands above retain the corresponding reports in the log. -/

/-- info: 'OAI.PairedAffine.shifted_period_eventualLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.PairedAffine.shifted_period_eventualLowerBound

/-- info: 'OAI.PairedAffine.shifted_period_explicit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.PairedAffine.shifted_period_explicit_bound

/-- info: 'OAI.PairedAffine.shifted_period_irrational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.PairedAffine.shifted_period_irrational

/-- info: 'OAI.PairedAffine.shifted_period_irrationalityExponent_le_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms OAI.PairedAffine.shifted_period_irrationalityExponent_le_four

/-- info: 'OAI.PairedAffine.Audit.literal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OAI.PairedAffine.Audit.literal_bound

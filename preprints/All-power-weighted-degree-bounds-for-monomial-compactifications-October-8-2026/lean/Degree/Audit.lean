import Degree.LogarithmBridge

set_option pp.proofs false

#print Degree.monomial_all_supportBound
#print Degree.logarithm_all_supportBound
#print Degree.admissible_all_supportBound
#print axioms Degree.supportBound_of_pow
#print axioms Degree.positive_supportBound
#print axioms Degree.zero_supportBound
#print axioms Degree.monomial_all_supportBound
#print axioms Degree.logarithm_all_supportBound
#print axioms Degree.admissible_all_supportBound

namespace Degree.Audit
noncomputable section
open AlgebraicGeometry CategoryTheory
open OAI.PiExponent OAI.PiExponentSeshadri.Geometry
open WeightedSliceDegree AffineJetCoefficientInterface

/-- The two coordinates 1 and x give the usual projective-line example. -/
def exponents (j : Fin 2) : Fin 1 →₀ ℕ :=
  if j = 0 then 0 else Finsupp.single 0 1

lemma constant_exponent : exponents 0 = 0 := by simp [exponents]
lemma coordinate_exponent (i : Fin 1) : exponents 1 = Finsupp.single i 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  simp [exponents, hi]

lemma exponent_budget (j : Fin 2) : Finsupp.weight (fun _ : Fin 1 => (1 : ℝ))
    (exponents j) ≤ 1 := by
  fin_cases j <;> simp [exponents, Finsupp.weight_single]

def chart := WeightedCompactification.affineChartMap (R := ℂ)
  exponents 0 constant_exponent (fun _ => 1) coordinate_exponent
def bundle := WeightedCompactification.lineBundle (R := ℂ) exponents

instance chart_isOpenImmersion : IsOpenImmersion chart := by
  unfold chart
  infer_instance

/-- This specialization has explicit, satisfiable numerical data, including power zero. -/
theorem projective_line_example (n : ℕ) (e : Frame chart bundle) (s : Sections bundle n) :
    SupportBound (fun _ : Fin 1 => (1 : ℝ)) (n : ℝ)
      (AffineJetCoefficientInterface.coefficient chart bundle n e s) := by
  unfold chart bundle at *
  simpa only [mul_one] using monomial_all_supportBound (K := ℂ)
    exponents 0 constant_exponent (fun _ => 1) coordinate_exponent
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) 1 exponent_budget n e s

end
end Degree.Audit

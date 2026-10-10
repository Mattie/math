import OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity

namespace OAI
noncomputable section
namespace Logarithm
open scoped BigOperators
open PiExponent PiExponentApprox PiExponent.PersistentWeightComparison
open PiExponent.CurveCenters PiExponent.CurveValuationCenter PiExponent.CurveFieldRigidity
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem logarithmic_coordinate_eq_center {m : ℕ}
    (x : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (ha : a 0 ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : Centered x a p)
    (hheight : (coordinateKernel x).height ≤ m)
    (rho : Fin (m+1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m+1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m+1) cost (sigma / ((m : ℝ)+2)) N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (hvanish : ∀ word : List (Fin (m+1)), frameWordCost cost word ≤ sigma*N →
      MvPolynomial.aeval x (polynomialFrameWord m word F) = 0)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    x 0 = algebraMap ℂ E (a 0) := by
  have hx0 : x 0 ≠ 0 := by
    intro hz
    have hc := hp.constant_coordinate 0 0 (by simpa using hz)
    exact ha hc.symm
  have hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel x := by
    simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hx0
  have hepsilon : 0 < sigma / ((m : ℝ)+2) := by positivity
  have hbound : ((m : ℝ)+2) * ((sigma / ((m : ℝ)+2))*N) = sigma*N := by
    have hm : (m : ℝ)+2 ≠ 0 := by positivity
    field_simp
  obtain ⟨c, hc⟩ := CurveComponentRigidity.coordinate_constant_of_persistent_comparison
    (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma)
    ((sigma / ((m : ℝ)+2))*N) (fun i => (hcost i).le) (by positivity)
    F hF0 (coordinateKernel x) inferInstance hheight hY
    (fun word hword => hvanish word (by simpa only [hbound] using hword))
    (logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma hN hrect
      F hF (coordinateKernel x) hY) hseparated
  have hxc : x 0 = algebraMap ℂ E c := by
    simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hc
  have hc1 := hp.constant_coordinate 0 c hxc
  simpa only [hc1] using hxc


end Logarithm
end
end OAI

import Logarithm.AuxiliaryJet
import Logarithm.DerivativeVanishing
import Logarithm.CurveRigidity
import Logarithm.ConstantFiber

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Topology
namespace Logarithm
open PiExponent PiExponentApprox PiExponent.CurveValuationCenter PiExponent.PlaceValuationRing
open Logarithm.ContactFamily PiExponent.PersistentWeightComparison

theorem excess_implies_constant_Y
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y hy c hz, (contact hres hfinite z y hy c hz v p : ℝ)) :
    ∃ a : ℂ, z 0 = algebraMap ℂ E a := by
  have hvR (i : Fin (m+1)) : (0 : ℝ) < v i := by exact_mod_cast hv i
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have haux := eventually_exists_formalJet_auxiliaryPolynomial_nat w v hw hv K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol) y c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniformRectangles (m+1) (fun i => (v i : ℝ)) hvR
      ((sigma : ℝ)/((m : ℝ)+2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := Logarithm.CurveDerivativeVanishing.logarithmic_words_vanish hres hfinite z y hy c hz
    w v hw hv sigma hsigma N hN F hF hjet hexcess
  have hS : (places hfinite z y hy c hz).Nonempty := by
    by_contra h
    have he : places hfinite z y hy c hz = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨p,hp⟩ := hS
  refine ⟨y (center hfinite z y hy c hz p hp), ?_⟩
  exact logarithmic_coordinate_eq_center z
    (fullCenter (y (center hfinite z y hy c hz p hp)) (c (center hfinite z y hy c hz p hp))) (hy _) p
    (centered hfinite z y hy c hz p hp) hheight w hw (fun i => (v i : ℝ)) hvR
    sigma N hsR (by exact_mod_cast hN) hrectN F hF0 hF hwords hseparated


/-- The distinct-Y curve inequality. Only the ambient volume inequality is used;
there is no transverse volume or injectivity hypothesis on the X coordinates. -/
theorem distinct_Y_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hyinj : Function.Injective y)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y hy c hz,
      (contact hres hfinite z y hy c hz v p : ℝ) ≤
      CurveContactSum.weightedDegree hfinite z w := by
  apply le_of_not_gt
  intro hexcess
  have hY := excess_implies_constant_Y hres hfinite z y hy c hz hheight
    w v hw hv sigma hsigma hvol hseparated hexcess
  exact no_excess_of_constant_Y hres hfinite z y hy c hyinj hz
    w v hw hv sigma hsigma hratio hY hexcess

end Logarithm
end
end OAI

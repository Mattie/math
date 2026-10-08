import Logarithm.CurveInequality
import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic

namespace OAI
noncomputable section
namespace Logarithm
open scoped BigOperators
open PiExponent PiExponent.CurveValuationCenter PiExponent.PlaceValuationRing
open Logarithm.ContactFamily PiExponent.PersistentWeightComparison

/-- Intrinsic form over an essentially finite type complex function field of
transcendence degree one. The auxiliary valuation hypotheses are discharged. -/
theorem weighted_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E] {m K : ℕ}
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hyinj : Function.Injective y)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y hy c hz,
      (contact hres hfinite z y hy c hz v p : ℝ) ≤
      CurveContactSum.weightedDegree hfinite z w :=
  distinct_Y_curve_inequality (PlaceLocalRing.residue_integral htrdeg.le)
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg) z y hy c hyinj
    (CurveInequality.nonconstant_coordinates z hgen htrdeg)
    (CurvePrimeHeight.kernel_height_succ_le z hgen htrdeg)
    w v hw hv sigma hsigma hvol hseparated hratio

end Logarithm
end
end OAI

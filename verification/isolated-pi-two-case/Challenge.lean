import OAI.NumberTheory.PiExponent.Statement
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily
import OAI.NumberTheory.PiExponent.Geometry.CurveContactSum
import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic

/-! Trusted statements for the two-case pi paper. The challenge imports only
pinned upstream definitions. Its proofs are intentionally admitted. -/

open scoped BigOperators
open OAI OAI.PiExponent

namespace OAI.PiExponent

structure BridgeData where
  m : ℕ
  K : ℕ
  W : Fin (m + 1) → ℚ
  V : Fin (m + 1) → ℚ
  W_pos : ∀ i, 0 < W i
  V_pos : ∀ i, 0 < V i
  centers : Fin K → Fin m → ℂ
  centers_injective : Function.Injective centers

namespace BridgeGeometry

/-- The strict curve inequality uses all places above all centers. -/
noncomputable def CurveBound (d : BridgeData) (s : ℚ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m + 1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1),
    let z : Fin (d.m + 1) → E := Fin.cases y x
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    (s : ℝ) * (∑ q ∈ CurveContactFamily.places hfinite z d.centers hz,
      (CurveContactFamily.contact (PlaceLocalRing.residue_integral htrdeg.le)
        hfinite z d.centers hz d.V q : ℝ)) ≤
      CurveContactSum.weightedDegree hfinite z d.W

end BridgeGeometry
end OAI.PiExponent

namespace PiTwoCaseBridge

open OAI.PiExponent.BridgeGeometry

/-- Theorem 5.1 with one strict affine degree budget for every positive real cutoff. -/
theorem theorem_5_1 (d : BridgeData) (s : ℚ) (hs : 1 < s) (hc : CurveBound d s) :
    ∃ κ B : ℝ, 0 < κ ∧ κ < 1 ∧ 0 ≤ B ∧ ∀ T : ℝ, 0 < T →
      ∀ values : Fin d.K →
          {a : Fin (d.m + 1) →₀ ℕ // Finsupp.weight (fun i => (d.V i : ℝ)) a < T} → ℂ,
        ∃ P : PiExponentApprox.FramePolynomial d.m,
          WeightedSliceDegree.SupportBound (fun i => (d.W i : ℝ)) (κ * T + B) P ∧
          ∀ j a, MvPowerSeries.coeff a.1 (FormalLogJet.formalJet (d.centers j) P) = values j a := by
  sorry

theorem pi_irrationalityExponent_eq_two : irrationalityExponent Real.pi = 2 := by
  sorry

/-- The exposed replay root gives the eventual bound and the supremum directly. -/
theorem main :
    (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
      ∀ p q : ℤ, Q ≤ q → (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
    sSup {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |Real.pi - (r : ℝ)| ∧
        |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  sorry

end PiTwoCaseBridge

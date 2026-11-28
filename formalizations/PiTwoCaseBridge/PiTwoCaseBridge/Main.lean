import PiTwoCaseBridge.CurveGeometryAdmissible
import PiTwoCaseBridge.Determinant
import PiTwoCaseBridge.ProjectionUnit
import PiTwoCaseBridge.SectionInitials
import PiTwoCaseBridge.MonomialDegree

/-!
# The strict interpolation bridge and its π consequence

Theorem 5.1 of the October two-case manuscript. The input is the branch
curve inequality, and the output is one affine cost for all real cutoffs.
-/

namespace PiTwoCaseBridge

open OAI OAI.PiExponent OAI.PiExponent.BridgeGeometry

theorem theorem_5_1 (d : BridgeData) (s : ℚ) (hs : 1 < s) (hc : CurveBound d s) :
    StrictInterpolation d.W d.V d.centers := by
  let := projection_unitMap_isIso d
  obtain ⟨G⟩ := strict_generating_polynomials d s hs hc (MonomialDegree.supportBound_via_monomial_curves d)
  exact G.strictInterpolation

theorem theorem_5_1_eventual (d : BridgeData) (s : ℚ) (hs : 1 < s) (hc : CurveBound d s) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ y : Fin d.K → RealPacketExponent d.V H → ℂ,
        ∃ P : OAI.PiExponentApprox.FramePolynomial d.m,
          WeightedSliceDegree.SupportBound (fun i => (d.W i : ℝ)) H P ∧
          ∀ j a, MvPowerSeries.coeff a.1 (FormalLogJet.formalJet (d.centers j) P) = y j a :=
  eventualEqualInterpolation_of_strict d.W d.V d.centers (theorem_5_1 d s hs hc)

theorem admissible_strictInterpolation {ν : ℝ} (d : DeterminantContradiction.FixedData ν) :
    StrictInterpolation d.curveDegreeWeights d.curveJetWeights d.curveCenters := by
  have hσ : (0 : ℚ) < d.sigma := by exact_mod_cast d.sigma_pos
  exact theorem_5_1 d.bridgeData (1 + d.sigma) (by linarith) d.bridgeData_curveBound

theorem pi_eventual_lower_bound : PiEventualLowerBound :=
  piEventualLowerBound_of_strictInterpolation (fun _ _ d => admissible_strictInterpolation d)

theorem pi_integer_eventual_lower_bound : IntegerEventualLowerBound Real.pi :=
  (eventualLowerBound_iff_integer Real.pi).mp pi_eventual_lower_bound

theorem pi_irrationalityExponent_eq_two : irrationalityExponent Real.pi = 2 :=
  pi_irrationalityExponent_eq_two_of_eventualLowerBound pi_eventual_lower_bound

theorem main :
    (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
      ∀ p q : ℤ, Q ≤ q → (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
    sSup {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |Real.pi - (r : ℝ)| ∧
        |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  refine ⟨pi_integer_eventual_lower_bound, ?_⟩
  change irrationalityExponent Real.pi = 2
  exact pi_irrationalityExponent_eq_two

end PiTwoCaseBridge

import PeriodicGeometry.PeriodicJetAmpleness
import PeriodicGeometry.PeriodicJetPackets
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame
import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete

namespace OAI.PiExponent.PeriodicInterpolation
noncomputable section
open AlgebraicGeometry CategoryTheory Filter PiExponentSeshadri.Geometry
open PeriodicBlowupGeometry AffineJetCoefficientInterface BlowupJetSurjectivity
attribute [local irreducible] PeriodicBlowupGeometry.affineChart
  PeriodicBlowupGeometry.hyperplane PeriodicBlowupGeometry.centerIdeal
  WeightedCompactification.lineBundle WeightedCompactification.affineChartMap
variable (d : PeriodicGeometryData)

theorem actualFrame_exists : Nonempty (Frame (affineChart d) (hyperplane d)) := by
  unfold PeriodicBlowupGeometry.affineChart PeriodicBlowupGeometry.hyperplane
  exact AdmissibleMatrixInterpolation.monomialFrame_exists (R := ℂ)
    (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

theorem exponent_budget (j : Index d) :
    Finsupp.weight (fun i => (d.curveDegreeWeights i : ℝ))
      (exponents d j) ≤ (scale d).radius := by
  have hq := (scale d).budget d.curveDegreeWeights_pos j
  have hr : (∑ i, (d.curveDegreeWeights i : ℝ) * (exponents d j i : ℝ)) ≤
      (scale d).radius := by exact_mod_cast hq
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

theorem eventual_supportBound :
    ProjectiveCoefficientBound.EventualBound (affineChart d) (hyperplane d)
      (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius := by
  unfold PeriodicBlowupGeometry.affineChart PeriodicBlowupGeometry.hyperplane
  exact WeightedGlobalSectionBound.eventual_supportBound (K := ℂ) (ι := Fin (d.m+1))
    (σ := Index d) (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius (exponent_budget d)

def WeightedPolynomials (n : ℕ) :=
  {P : PiExponentApprox.FramePolynomial d.m //
    WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (scale d).radius) P}

def packetMap (n : ℕ) (P : WeightedPolynomials d n) :=
  fun j : Fin d.K => JetGeometry.rationalCoefficientPacket d.curveJetWeights
    ((n : ℚ) * (scale d).radius)
    (FormalLogJet.formalJet (d.curveCenters j) P.val)

/-- Actual sections provide weighted packets with the identical budget nR.
The eventual threshold changes; the leading degree coefficient does not. -/
theorem eventual_packets :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n) := by
  obtain ⟨N, hN⟩ := eventual_supportBound d
  obtain ⟨e⟩ := actualFrame_exists d
  obtain ⟨J, hJ⟩ := eventual_blowup_jetRestriction_surjective
    (compactificationStructureMap d) (centerIdeal d) (hyperplane d)
    (PeriodicJetAmpleness.blowupBundle_ample d)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop J] with n hnN hnJ
  intro packets
  obtain ⟨s, hs⟩ := PeriodicJetPackets.formalPackets_surjective_of_jetRestriction
    d n e (hJ n hnJ) packets
  exact ⟨⟨PeriodicJetPackets.sectionPolynomial d n e s, hN n hnN e s⟩, hs⟩

end
end OAI.PiExponent.PeriodicInterpolation

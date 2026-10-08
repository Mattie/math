import Logarithm.Interpolation
import Logarithm.ApproximationGeometry
import RealNorm.DeterminantData

namespace OAI.RealNorm.GlobalMatrixInterpolation
set_option maxHeartbeats 4000000
noncomputable section
open Filter Logarithm PiExponent DeterminantData
variable {base : PeriodData} {nu : ℝ} (d : FixedData base nu)

theorem degreeWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveDegreeWeights i : ℝ) = InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Logarithm.AdmissibleParameters.curveDegreeWeights_succ, d.cast_rationalWeight,
      InterpolationMatrix.columnWeights, Fin.cases_succ, logWeights_eq]

theorem jetWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveJetWeights i : ℝ) = InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Logarithm.AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, InterpolationMatrix.rowWeights, Fin.cases_succ, logWeights_eq]

theorem actual_truncation_weight_bound (i : Fin d.m) :
    d.curveJetWeights i.succ ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℚ) *
        d.curveJetWeights 0 := by
  have hw : 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    rw [logWeights_eq]; exact zero_lt_one.trans_le (d.x_one_le _)
  have hF : 1 / (d.base.theta : ℝ) < d.F0 :=
    (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) d.base.theta_pos).trans d.F0_large
  have hceil := Nat.le_ceil
    (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ))
  have hbound : MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.v0 : ℝ) := by
    calc
      _ = (1 / (d.base.theta : ℝ)) *
          MatrixArithmetic.logWeights (finiteDenominators d) i := by ring
      _ ≤ d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i :=
        mul_le_mul_of_nonneg_right hF.le hw.le
      _ ≤ _ := (div_le_iff₀ d.v0_pos).mp hceil
  have hcast : (d.curveJetWeights i.succ : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.curveJetWeights 0 : ℝ) := by
    simpa only [Logarithm.AdmissibleParameters.curveJetWeights_zero,
      Logarithm.AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, logWeights_eq] using hbound
  exact_mod_cast hcast

theorem matrix_degree_of_supportBound (H : ℝ) (P : PiExponentApprox.FramePolynomial d.m)
    (hP : WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ)) H P) :
    PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d))) H P := by
  intro a ha
  have h := hP a ha
  have hw : (fun i => (d.curveDegreeWeights i : ℝ)) =
      InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) := funext (degreeWeights_eq_matrix d)
  rw [hw] at h
  simpa only [PiExponentApprox.monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul] using h

theorem cofinal_actualMatrix (L : ℝ) :
    ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin := by
  classical
  let g := toGeometryData d
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_weighted_logarithmic_interpolation g)
  let n := max N (Nat.ceil (L / ((BlowupGeometry.scale g).radius : ℝ)))
  let H : ℚ := (n : ℚ) * (BlowupGeometry.scale g).radius
  have hR : (0 : ℝ) < (BlowupGeometry.scale g).radius := by
    exact_mod_cast (BlowupGeometry.scale g).radius_pos
  have hL : L ≤ (H : ℝ) := by
    change L ≤ ((n : ℚ) * (BlowupGeometry.scale g).radius : ℚ)
    push_cast
    apply (div_le_iff₀ hR).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right N
      (Nat.ceil (L / ((BlowupGeometry.scale g).radius : ℝ)))))
  refine ⟨H, hL, ?_⟩
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    rw [logWeights_eq]; exact zero_lt_one.trans_le (d.x_one_le _)
  apply ScaledMatrix.truncatedLogMatrix_surjective_of_formalLog_packets
    d.K d.w0 d.v0 d.base.theta (MatrixArithmetic.logWeights (finiteDenominators d)) H
    d.w0_pos hw d.curveJetWeights d.curveJetWeights_pos
    (jetWeights_eq_matrix d) (fun j => base.value^j.val)
    (ScaledArithmetic.realCenters base.slope (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (actual_truncation_weight_bound d)
    (fun P : GeometricInterpolation.WeightedPolynomials g n => P.val)
  · intro P
    apply matrix_degree_of_supportBound d
    have hp := P.property
    change WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (BlowupGeometry.scale g).radius) P.val at hp
    simpa only [H, Rat.cast_mul, Rat.cast_natCast] using hp
  · have hh := hN n (le_max_left _ _)
    have hc : (fun j i => (j.val : ℂ) *
        ScaledArithmetic.realCenters base.slope (finiteNumerators d) (finiteDenominators d) i) =
        g.curveCenters := by
      funext j i
      simp only [ScaledArithmetic.realCenters, finiteNumerators, finiteDenominators,
        g, toGeometryData, mul_div_assoc]
    have hcpoint (j : Fin d.K) : (fun i => (j.val : ℂ) *
        ScaledArithmetic.realCenters base.slope (finiteNumerators d) (finiteDenominators d) i) =
        g.curveCenters j := congrFun hc j
    simp_rw [hcpoint]
    exact hh

end
end OAI.RealNorm.GlobalMatrixInterpolation

import PairedAffine.Data
import AlgebraicLog.GlobalMatrixInterpolation

namespace OAI.PairedAffine.Geometry

open Filter PiExponent Logarithm AlgebraicLog.DeterminantData
open AlgebraicLog.GlobalMatrixInterpolation

noncomputable section

variable {proxy nu Lambda c rho delta kappa R : ℝ}
  (d : AlgebraicLog.AdmissibleParameters (Real.log proxy) nu Lambda c rho delta kappa R)

/-- Changing additive centres preserves every geometric hypothesis. The
positive multiplicative base supplies distinct nonzero power centres. -/
def geometryData (base : ℝ) (hbase : 0 < base) (hbase1 : base ≠ 1)
    (centres : Fin d.m → ℂ) : GeometryData :=
  { d.toGeometryData base hbase hbase1 with
    curveCenters := fun j i => (j.val : ℂ) * centres i }

/-- The actual affine-centre matrix has full row rank at cofinally many
heights. No interpolation assumption is added to the approximation data. -/
theorem cofinal_matrix (base : ℝ) (hbase : 0 < base) (hbase1 : base ≠ 1)
    (centres : Fin d.m → ℂ) (L : ℝ) :
    ∃ H : ℝ, L ≤ H ∧
      Function.Surjective (matrix d.toAnalyticData H (base : ℂ) centres).mulVecLin := by
  classical
  let g := geometryData d base hbase hbase1 centres
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_weighted_logarithmic_interpolation g)
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
  have hw : ∀ i, 0 < PiExponent.MatrixArithmetic.logWeights
      (finiteDenominators d.toAnalyticData) i := by
    intro i
    rw [logWeights_eq]
    exact zero_lt_one.trans_le (d.x_one_le _)
  apply ScaledMatrix.truncatedLogMatrix_surjective_of_formalLog_packets
    d.K d.w0 d.v0 d.base.theta
    (PiExponent.MatrixArithmetic.logWeights (finiteDenominators d.toAnalyticData)) H
    d.w0_pos hw d.curveJetWeights d.curveJetWeights_pos
    (jetWeights_eq_matrix d) (fun j => (base : ℂ) ^ j.val) centres
    (PiExponent.MatrixArithmetic.truncationOrders
      (finiteDenominators d.toAnalyticData) d.F0 d.v0)
    (actual_truncation_weight_bound d)
    (fun P : GeometricInterpolation.WeightedPolynomials g n => P.val)
  · intro P
    apply matrix_degree_of_supportBound d
    have hp := P.property
    change WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (BlowupGeometry.scale g).radius) P.val at hp
    simpa only [H, Rat.cast_mul, Rat.cast_natCast] using hp
  · exact hN n (le_max_left _ _)

/-- One selection from the distinguished matrix is suitable for every later
embedding estimate; the theorem does not choose a selection per embedding. -/
theorem cofinal_nonzero_minor (base : ℝ) (hbase : 0 < base) (hbase1 : base ≠ 1)
    (centres : Fin d.m → ℂ) (L : ℝ) :
    ∃ H : ℝ, L ≤ H ∧ ∃ selection : Row d.toAnalyticData H → Column d.toAnalyticData H,
      (minor d.toAnalyticData H selection (base : ℂ) centres).det ≠ 0 := by
  obtain ⟨H, hH, hsurj⟩ := cofinal_matrix d base hbase hbase1 centres L
  obtain ⟨selection, _, hdet⟩ :=
    InterpolationMatrix.exists_full_row_minor_of_surjective
      (matrix d.toAnalyticData H (base : ℂ) centres) hsurj
  exact ⟨H, hH, selection, hdet⟩

end
end OAI.PairedAffine.Geometry

import Logarithm.ScalingMonomials
import Logarithm.ScaledTruncation
import OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity

namespace OAI
noncomputable section
namespace Logarithm.ScaledMatrix
open scoped BigOperators
open PiExponent MvPowerSeries

/-- The first coordinate contributes its center value to the Y monomial. -/
def matrix {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Matrix (InterpolationMatrix.Row K v0 theta w H) (InterpolationMatrix.Column w0 w H) ℂ :=
  fun row col => y row.1 ^ col.val 0 *
    InterpolationMatrix.entry r G row.1.val (row.2.val 0)
      (fun i => row.2.val i.succ) (col.val 0) (fun i => col.val i.succ)

def truncatedLogMatrix {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ)
    (H : ℝ) (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (InterpolationMatrix.Row K v0 theta w H) (InterpolationMatrix.Column w0 w H) ℂ :=
  matrix K w0 v0 theta w H y r (fun i => InterpolationMatrix.truncatedLog (T i))

theorem scaleY_polynomialOfCoefficients {m : ℕ} (y : ℂ)
    (S : Finset (Fin (m+1) → ℕ)) (x : S → ℂ) :
    scaleY y (polynomialOfCoefficients S x) =
      polynomialOfCoefficients S (fun c => y ^ c.val 0 * x c) := by
  classical
  change scaleY y (∑ c : S, MvPolynomial.monomial
    (InterpolationMatrix.exponentVector c.val) (x c)) =
    ∑ c : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector c.val) (y ^ c.val 0 * x c)
  simp only [map_sum, scaleY_monomial, InterpolationMatrix.exponentVector_apply,
    MvPolynomial.C_mul_monomial]

theorem truncatedLogMatrix_mulVec_eq_coeff {m : ℕ}
    (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (row : InterpolationMatrix.Row K v0 theta w H) :
    (truncatedLogMatrix K w0 v0 theta w H y r T).mulVecLin x row =
      coeff (InterpolationMatrix.exponentVector row.2.val)
        (ScaledTruncation.truncatedFormalJet (y row.1)
          (fun i => (row.1.val : ℂ) * r i) T
          (polynomialOfCoefficients
            (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H) x)) := by
  rw [ScaledTruncation.truncatedFormalJet, AlgHom.comp_apply, scaleY_polynomialOfCoefficients,
    ← FormalMatrixBridge.truncatedLogMatrix_mulVec_eq_coeff]
  change (∑ c, y row.1 ^ c.val 0 *
    InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
      row.1.val (row.2.val 0) (fun i => row.2.val i.succ) (c.val 0) (fun i => c.val i.succ) * x c) =
    ∑ c, InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
      row.1.val (row.2.val 0) (fun i => row.2.val i.succ) (c.val 0) (fun i => c.val i.succ) *
      (y row.1 ^ c.val 0 * x c)
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem truncatedLogMatrix_surjective_of_rational_packets {m : ℕ} {alpha : Type*}
    (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 theta w i)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (P : alpha → PiExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin K =>
      JetGeometry.rationalCoefficientPacket V H
        (ScaledTruncation.truncatedFormalJet (y j) (fun i => (j.val : ℂ) * r i) T (P a)))) :
    Function.Surjective (truncatedLogMatrix K w0 v0 theta w (H : ℝ) y r T).mulVecLin := by
  classical
  have hrow' : (fun i => (V i : ℝ)) = InterpolationMatrix.rowWeights v0 theta w := funext hrow
  have hW : ∀ i, 0 < InterpolationMatrix.columnWeights w0 w i := by
    intro i
    exact Fin.cases hw0 hw i
  intro packet
  let e := FormalMatrixBridge.rationalJetIndexEquiv V hV H
  let target : Fin K → JetGeometry.RationalCoefficientPacket (R := ℂ) V H :=
    fun j d => packet (j, ⟨(e d).val, by simpa only [← hrow'] using (e d).property⟩)
  obtain ⟨a, ha⟩ := hpacket target
  let x : InterpolationMatrix.Column w0 w (H : ℝ) → ℂ :=
    fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)
  refine ⟨x, ?_⟩
  funext row
  rw [truncatedLogMatrix_mulVec_eq_coeff]
  change coeff (InterpolationMatrix.exponentVector row.2.val)
    (ScaledTruncation.truncatedFormalJet (y row.1) (fun i => (row.1.val : ℂ) * r i) T
      (polynomialOfCoefficients
        (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) (H : ℝ))
        (fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)))) = packet row
  rw [FormalMatrixBridge.polynomialOfCoefficients_of_weighted _ hW _ (P a) (hdegree a)]
  let b : ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ)) :=
    ⟨row.2.val, by simpa only [hrow'] using row.2.property⟩
  have hh := congrFun (congrFun ha row.1) (e.symm b)
  change coeff (e.symm b).val
    (ScaledTruncation.truncatedFormalJet (y row.1) (fun i => (row.1.val : ℂ) * r i) T (P a)) =
      target row.1 (e.symm b) at hh
  simpa only [e, FormalMatrixBridge.rationalJetIndexEquiv_symm_val, b, target,
    Equiv.apply_symm_apply] using hh

theorem truncatedLogMatrix_surjective_of_formalLog_packets {m : ℕ} {alpha : Type*}
    (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 theta w i)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hT : ∀ i, V i.succ ≤ (T i : ℚ) * V 0)
    (P : alpha → PiExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin K =>
      JetGeometry.rationalCoefficientPacket V H
        (ScaledFormalJet.formalJet (y j) (fun i => (j.val : ℂ) * r i) (P a)))) :
    Function.Surjective (truncatedLogMatrix K w0 v0 theta w (H : ℝ) y r T).mulVecLin := by
  apply truncatedLogMatrix_surjective_of_rational_packets
    K w0 v0 theta w H hw0 hw V hV hrow y r T P hdegree
  exact (ScaledTruncation.formalLog_packets_surjective_iff_truncated V
    (fun i => (hV i).le) H T hT y (fun j i => (j.val : ℂ) * r i) P).mp hpacket

end Logarithm.ScaledMatrix
end
end OAI

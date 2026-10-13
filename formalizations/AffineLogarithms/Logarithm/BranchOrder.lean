import Logarithm.Scaling

namespace OAI
noncomputable section
namespace Logarithm
open PiExponent PiExponentApprox PiExponent.CurveCenters PiExponent.CurveValuationCenter

variable {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]

/-- The old DVR estimate transfers exactly to the scaled logarithmic chart. -/
theorem logWord_field_order_lower
    (z : Fin (m+1) → E) (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (hp : Centered z (fullCenter y c) p)
    (hz : ∃ i, z i ≠ algebraMap ℂ E (fullCenter y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (F : FramePolynomial m)
    (hF : ScaledFormalJet.formalJet y c F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word F) ≠ 0) :
    logContact p z y hy c hp hz v * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℚ) := by
  have he : MvPolynomial.aeval (normalized z y)
      (polynomialFrameWord m word (scaleY y F)) =
      MvPolynomial.aeval z (polynomialFrameWord m word F) := by
    rw [← scaleY_frameWord, aeval_normalized_scaleY z y hy]
  have hb := PlaceCenteredBranch.logWord_field_order_lower p (normalized z y) c
    (centered_normalized z y hy c p hp) (normalized_nonconstant z y hy c hz)
    v hv H (scaleY y F) (by rwa [formalJet_scaleY]) word (by rwa [he])
  simpa only [logContact, he] using hb

/-- In a constant Y fiber the logarithmic contact is the ordinary transverse contact. -/
theorem logContact_constant_Y
    (z : Fin (m+1) → E) (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (hp : Centered z (fullCenter y c) p)
    (hz : ∃ i, z i ≠ algebraMap ℂ E (fullCenter y c i))
    (hY : z 0 = algebraMap ℂ E y)
    (hx : ∃ i : Fin m, z i.succ ≠ algebraMap ℂ E (c i))
    (v : Fin (m+1) → ℚ) :
    logContact p z y hy c hp hz v =
      PlaceCenteredBranch.ordinaryContact p (fun i => z i.succ) c
        (fun i => hp i.succ) hx (fun i => v i.succ) := by
  have he : normalized z y = Fin.cases (1 : E) (fun i => z i.succ) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [normalized, hY, hy]
    | succ i => rfl
  have hp' := he ▸ centered_normalized z y hy c p hp
  have hn' := he ▸ normalized_nonconstant z y hy c hz
  simpa only [logContact, he] using
    PlaceCenteredBranch.logContact_one p (fun i => z i.succ) c hp' hn' v

end Logarithm
end
end OAI

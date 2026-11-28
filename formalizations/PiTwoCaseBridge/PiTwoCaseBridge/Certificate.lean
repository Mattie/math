import PiTwoCaseBridge.FiniteInterpolation
import PiTwoCaseBridge.Margin

/-!
# Applying the finite bridge to strict initial-form data

The geometric proof constructs the polynomials in this lemma. This statement
only packages the algebra from those explicit polynomials to logarithmic jets.
-/

namespace PiTwoCaseBridge

open OAI OAI.PiExponent PiExponentApprox MvPolynomial

theorem strictInterpolation_of_initialForms {m : ℕ} {J ι : Type*}
    [Fintype J] [Finite ι] (W V : Fin (m+1) → ℚ)
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (C : Fin m → ℕ) (hC : ∀ i, V i.succ ≤ (C i : ℚ) * V 0)
    (dw dv : ℕ) (hdw : 0 < dw) (hdv : 0 < dv) (w v : Fin (m+1) → ℕ)
    (hw : ∀ i, (W i : ℝ) = (w i : ℝ) / dw)
    (hv : ∀ i, (V i : ℝ) = (v i : ℝ) / dv)
    (hvpos : ∀ i, 0 < v i) (L d : ℕ) (hL : 0 < L)
    (hd : 0 < d) (hmargin : d * dv < L * dw)
    (P : ι → FramePolynomial m)
    (hdegree : ∀ i, weightedTotalDegree w (P i) ≤ d)
    (horder : ∀ j i a, Finsupp.weight v a < L →
      (logarithmicChart (c j) C (P i)).coeff a = 0)
    (hzero : ∀ j, zeroLocus ℂ
      (Ideal.span (Set.range fun i =>
        weightedHomogeneousComponent v L (logarithmicChart (c j) C (P i)))) = {0}) :
    StrictInterpolation W V c := by
  have hinj : Function.Injective (fun j => CompactJetPolynomial.center (c j)) := by
    intro j k h
    apply hc
    funext i
    exact congrFun h i.succ
  obtain ⟨B, hp⟩ := exists_polynomialPackets_of_zeroLocus w v hvpos
    (fun j => CompactJetPolynomial.center (c j)) hinj
    (fun j => logarithmicChart (c j) C)
    (fun j Q => eval_zero_logarithmicChart (c j) C Q) L d hL P hdegree horder hzero
  exact strictInterpolation_of_integral_polynomialPackets W V c C hC dw dv hdw hdv w v
    hw hv L d B hd hmargin hp

end PiTwoCaseBridge

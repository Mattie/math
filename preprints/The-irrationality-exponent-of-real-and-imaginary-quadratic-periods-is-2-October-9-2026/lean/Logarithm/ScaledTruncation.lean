import Logarithm.Scaling
import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation

namespace OAI
noncomputable section
namespace Logarithm.ScaledTruncation
open PiExponent PiExponent.FormalLogTruncation PiExponent.JetGeometry

/-- Polynomial logarithm substitution at an arbitrary Y center. -/
def truncatedFormalJet {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (FormalLogTruncation.truncatedFormalJet c T).comp (scaleY y)

theorem shiftMap_truncatedFormalJet {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (P : PiExponentApprox.FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedFormalJet y c T P) = ScaledFormalJet.formalJet y c P := by
  simp only [truncatedFormalJet, AlgHom.comp_apply,
    FormalLogTruncation.shiftMap_truncatedFormalJet, formalJet_scaleY]

/-- Truncating log is a common invertible change on the weighted packet space,
also when the Y centers differ. -/
theorem formalLog_packets_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (y : J → ℂ) (c : J → Fin m → ℂ) (P : α → PiExponentApprox.FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H
      (ScaledFormalJet.formalJet (y j) (c j) (P a))) ↔
    Function.Surjective (fun a j => rationalCoefficientPacket v H
      (truncatedFormalJet (y j) (c j) T (P a))) := by
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedFormalJet (y j) (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedFormalJet] using hh

end Logarithm.ScaledTruncation
end
end OAI

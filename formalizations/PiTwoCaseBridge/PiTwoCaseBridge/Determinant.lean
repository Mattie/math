import PiTwoCaseBridge.Margin
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixInterpolation
import OAI.NumberTheory.PiExponent.Approximation.InterpolationConsequence

/-!
# Connecting the strict interpolation margin to the original determinant

This adapter uses the actual matrix and the original two-case analytic and
arithmetic estimates. It accepts simultaneous strict interpolation as its
input, so the old cohomological interpolation theorem is unnecessary here.
-/

namespace PiTwoCaseBridge

open OAI OAI.PiExponent PiExponentApprox

theorem eventualEqualInterpolation_of_strict {m : ℕ} {J : Type*}
    (W V : Fin (m+1) → ℚ) (c : J → Fin m → ℂ) (h : StrictInterpolation W V c) :
    ∃ H₀ : ℝ, 0 < H₀ ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ y : J → RealPacketExponent V H → ℂ,
        ∃ P : FramePolynomial m,
          WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) H P ∧
          ∀ j a, MvPowerSeries.coeff a.1 (FormalLogJet.formalJet (c j) P) = y j a := by
  obtain ⟨κ, B, _, hk, _, hmain⟩ := h
  refine ⟨max 1 (B / (1 - κ)), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro H hH y
  have hpos : 0 < H := zero_lt_one.trans_le ((le_max_left _ _).trans hH)
  have hbudget : κ * H + B ≤ H := by
    have hgap : 0 < 1 - κ := sub_pos.mpr hk
    have hineq : B ≤ H * (1 - κ) :=
      (div_le_iff₀ hgap).mp ((le_max_right _ _).trans hH)
    linarith [show H * (1 - κ) = H - κ * H by ring]
  obtain ⟨P, hP, hCoeff⟩ := hmain H hpos y
  exact ⟨P, hP.mono hbudget, hCoeff⟩

theorem eventual_determinantPackets_of_strict {ν : ℝ}
    (d : DeterminantContradiction.FixedData ν)
    (h : StrictInterpolation d.curveDegreeWeights d.curveJetWeights d.curveCenters) :
    ∀ᶠ n : ℕ in Filter.atTop, Function.Surjective (AdmissibleMatrixInterpolation.packetMap d n) := by
  obtain ⟨H₀, _, hpacket⟩ :=
    eventualEqualInterpolation_of_strict d.curveDegreeWeights d.curveJetWeights d.curveCenters h
  let R := (AdmissibleBlowupGeometry.scale d).radius
  have hR : 0 < (R : ℝ) := by
    exact_mod_cast (AdmissibleBlowupGeometry.scale d).radius_pos
  apply Filter.eventually_atTop.mpr
  refine ⟨⌈H₀ / (R : ℝ)⌉₊, ?_⟩
  intro n hn y
  let H : ℝ := (n : ℝ) * (R : ℝ)
  have hH : H₀ ≤ H := (div_le_iff₀ hR).mp
    ((Nat.le_ceil _).trans (by exact_mod_cast hn))
  have hrat (a : Fin (d.m+1) →₀ ℕ) :
      Finsupp.weight d.curveJetWeights a < (n : ℚ) * (R : ℚ) ↔
        Finsupp.weight (fun i => (d.curveJetWeights i : ℝ)) a < H := by
    rw [← rational_weight_cast]
    dsimp [H]
    exact_mod_cast (Iff.rfl : Finsupp.weight d.curveJetWeights a < (n : ℚ) * (R : ℚ) ↔
      Finsupp.weight d.curveJetWeights a < (n : ℚ) * (R : ℚ))
  obtain ⟨P, hP, hCoeff⟩ := hpacket H hH
    (fun j a => y j ⟨a.1, (hrat a.1).mpr a.2⟩)
  refine ⟨⟨P, hP⟩, ?_⟩
  funext j a
  exact hCoeff j ⟨a.1, (hrat a.1).mp a.2⟩

theorem piEventualLowerBound_of_strictInterpolation
    (h : ∀ (ν : ℝ), 2 < ν → ∀ d : DeterminantContradiction.FixedData ν,
      StrictInterpolation d.curveDegreeWeights d.curveJetWeights d.curveCenters) :
    PiEventualLowerBound :=
  piEventualLowerBound_of_globalInterpolation
    (AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_packets
      (fun ν hν d => eventual_determinantPackets_of_strict d (h ν hν d)))

theorem piExponent_of_strictInterpolation
    (h : ∀ (ν : ℝ), 2 < ν → ∀ d : DeterminantContradiction.FixedData ν,
      StrictInterpolation d.curveDegreeWeights d.curveJetWeights d.curveCenters) :
    irrationalityExponent Real.pi = 2 :=
  pi_irrationalityExponent_eq_two_of_eventualLowerBound
    (piEventualLowerBound_of_strictInterpolation h)

end PiTwoCaseBridge

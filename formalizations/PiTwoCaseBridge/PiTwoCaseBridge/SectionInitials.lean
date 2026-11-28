import PiTwoCaseBridge.CurveGeometryArcs
import PiTwoCaseBridge.SectionArcBridge
import PiTwoCaseBridge.SectionPolynomials

namespace PiTwoCaseBridge

noncomputable section

open AlgebraicGeometry CategoryTheory
open OAI OAI.PiExponent OAI.PiExponentSeshadri.Geometry OAI.PiExponentSeshadri.Frames
open OAI.PiExponent.BridgeGeometry OAI.PiExponent.LocalSectionOrder
open OAI.PiExponent.ExceptionalCurveDegree OAI.PiExponentApprox

/-- The arc images of the globally generating sections span the precise exceptional power.
The frame hypothesis identifies the affine-chart polynomials with those very same sections. -/
theorem weightedArcImages_of_section_cover (d : BridgeData) {ι : Type}
    (a dv : ℕ) (hdv : 0 < dv) (v : Fin (d.m+1) → ℕ)
    (hv : ∀ i, (d.V i : ℝ) = (v i : ℝ) / dv)
    (s : ι → GlobalSections (blowup d) (((J d).pow (a+1)).tensor ((A d).pow a)).sheaf)
    (hcov : (⨆ k, sectionOpen (blowup d) (s k)) = ⊤)
    (P : ι → FramePolynomial d.m)
    (hframe : ∀ (j : Fin d.K) (z : Fin (d.m+1) → ℂ)
      (g : Spec (CommRingCat.of (PowerSeries ℂ)) ⟶ blowup d),
      g ≫ projection d = arcMap d j v z →
      ∃ e : ((((A d).pow a).pullback g).sheaf ≅ O _), ∀ k,
        localCoefficient e (pullbackSection g (s k ≫
          tensorInclusion ((J d).pow (a+1)) ((A d).pow a)
            (idealPowerInclusion (J d) (exceptionalInclusion d) (a+1)))) =
          arcSubstitution d j v z (P k)) :
    ∀ j (z : Fin (d.m+1) → ℂ), z ≠ 0 →
      Ideal.span (Set.range fun k =>
        (↑(WeightedArcs.arc v z (logarithmicChart (d.centers j) (logCutoff d) (P k))) :
          PowerSeries ℂ)) = Ideal.span {PowerSeries.X ^ (dv * (a+1) * (scale d).radius)} := by
  let R := dv * (scale d).radius
  have hR : 0 < R := Nat.mul_pos hdv (scale d).radius_pos
  have hweight (i) : v i * (scale d).jetPowers i = R := by
    have hp : (0 : ℝ) < dv := by exact_mod_cast hdv
    have hs : (d.V i : ℝ) * ((scale d).jetPowers i : ℝ) = ((scale d).radius : ℝ) := by
      exact_mod_cast (scale d).jetPowers_eq i
    rw [hv i, div_mul_eq_mul_div, div_eq_iff hp.ne', mul_comm _ (dv : ℝ)] at hs
    exact_mod_cast hs
  intro j z hne
  obtain ⟨g, hg, _⟩ := existsUnique_weightedArcLift d j v R hR hweight z hne
  obtain ⟨e, he⟩ := hframe j z g hg
  have hspan := WeightedArcs.projected_span (centerIdeal d) (projection d) (J d) ((A d).pow a)
    (exceptionalInclusion d) (exceptional_presents d) (a+1) s hcov g e
  simp_rw [he] at hspan
  rw [hg] at hspan
  have hI : localIdeal (centerIdeal d) (arcMap d j v z) =
      Ideal.span ({PowerSeries.X ^ R} : Set (PowerSeries ℂ)) := by
    exact (localIdeal_compactIdeal d.centers (logCutoff d) (scale d).jetPowers
      (affineChart d) (arcSubstitution d j v z)).trans (arc_ideal d j v R hR hweight z hne)
  rw [hI, Ideal.span_singleton_pow, ← pow_mul] at hspan
  have heq : R * (a+1) = dv * (a+1) * (scale d).radius := by dsimp [R]; ring
  rw [heq] at hspan
  exact hspan


/-- A finite generating family, expressed by polynomials of the stated source budget in
the same affine frames along the arcs, interpolates all simultaneous logarithmic jets. -/
theorem strictInterpolation_of_section_cover (d : BridgeData) {ι : Type} [Finite ι]
    (a : ℕ) (ha : 0 < a)
    (s : ι → GlobalSections (blowup d) (((J d).pow (a+1)).tensor ((A d).pow a)).sheaf)
    (hcov : (⨆ k, sectionOpen (blowup d) (s k)) = ⊤)
    (P : ι → FramePolynomial d.m)
    (hdegree : ∀ k, WeightedSliceDegree.SupportBound (fun i => (d.W i : ℝ))
      ((a : ℝ) * (scale d).radius) (P k))
    (hframe : ∀ (j : Fin d.K) (v : Fin (d.m+1) → ℕ) (z : Fin (d.m+1) → ℂ)
      (g : Spec (CommRingCat.of (PowerSeries ℂ)) ⟶ blowup d),
      g ≫ projection d = arcMap d j v z →
      ∃ e : ((((A d).pow a).pullback g).sheaf ≅ O _), ∀ k,
        localCoefficient e (pullbackSection g (s k ≫
          tensorInclusion ((J d).pow (a+1)) ((A d).pow a)
            (idealPowerInclusion (J d) (exceptionalInclusion d) (a+1)))) =
          arcSubstitution d j v z (P k)) :
    StrictInterpolation d.W d.V d.centers := by
  obtain ⟨dw, hdw, w, _, hw⟩ := exists_integer_weights d.W d.W_pos
  obtain ⟨dv, hdv, v, hvpos, hv⟩ := exists_integer_weights d.V d.V_pos
  apply strictInterpolation_of_weightedArcImages d.W d.V d.centers d.centers_injective
    (logCutoff d) (fun i => (logCutoff_strict d i).le) dw dv hdw hdv w v hw hv hvpos
    a (scale d).radius ha (scale d).radius_pos P hdegree
  exact weightedArcImages_of_section_cover d a dv hdv v hv s hcov P (fun j => hframe j v)


/-- The original source polynomials supplied by global generation give the complete
simultaneous logarithmic interpolation estimate. -/
theorem GeneratingPolynomials.strictInterpolation {d : BridgeData} (G : GeneratingPolynomials d) :
    StrictInterpolation d.W d.V d.centers :=
  strictInterpolation_of_section_cover d G.a G.a_pos G.sections G.cover G.polynomial G.sourceDegree
    (fun j v z g hg => G.exists_arc_frame (arcSubstitution d j v z) g hg)

end
end PiTwoCaseBridge


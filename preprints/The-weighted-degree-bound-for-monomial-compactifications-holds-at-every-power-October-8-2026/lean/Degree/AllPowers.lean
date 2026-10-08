import Degree.SectionDegrees
import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
import OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame

namespace Degree
noncomputable section
open AlgebraicGeometry CategoryTheory
open OAI.PiExponentSeshadri.Geometry OAI.PiExponentSeshadri.Frames
open OAI.PiExponent
open WeightedSliceDegree AffineJetCoefficientInterface AffineJetCoefficientFrame
open AffineJetSupport ExceptionalAffineChart AffineJetPolynomial

variable {ι K : Type} [LinearOrder ι] [Field K] {X : Scheme}

lemma restrictSection_precompose (U : X.Opens) {M : X.Modules}
    (a : structureSheaf X ⟶ structureSheaf X) (t : GlobalSections X M) :
    restrictSection U.ι (a ≫ t) =
      (restrictSection U.ι a ≫ (Scheme.Modules.restrictUnitIso U.ι).hom) ≫
        restrictSection U.ι t := by
  unfold restrictSection
  erw [Functor.map_comp]
  symm
  erw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc]

/-- A section invertible on the affine chart supplies the degree-zero case. -/
theorem zero_supportBound
    (j : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (w : ι → NNReal) (B : ℝ)
    (heventual : ProjectiveCoefficientBound.EventualBound j A (fun i => (w i : ℝ)) B)
    (t : Sections A 1)
    (ht : IsIso ((Scheme.Modules.restrictFunctor (chartOpen j).1.ι).map t))
    (e : Frame j A) (s : Sections A 0) :
    SupportBound (fun i => (w i : ℝ)) 0
      (AffineJetCoefficientInterface.coefficient j A 0 e s) := by
  let U := (chartOpen j).1
  let E := untwistPowerFrame A U e 1
  let r := chartCoefficientMap j
  let f := r (U.ι.appTop (endValue s))
  have htunit : IsUnit (r (OAI.PiExponentSeshadri.Frames.coefficient E
      (restrictSection U.ι t))) := by
    apply IsUnit.map r
    apply (coefficient_isUnit_iff E _).mpr
    unfold restrictSection
    exact IsIso.comp_isIso' (Scheme.Modules.restrictUnitIso U.ι).isIso_inv ht
  have hfpow : ∀ k : ℕ, 0 < k → SupportBound (fun i => (w i : ℝ)) B (f ^ k) := by
    intro k hk
    let v : Sections A 1 := endPower s k ≫ t
    have hv := positive_supportBound j A w B heventual (by omega : 0 < 1) e v
    rw [polynomialCoefficient_open] at hv
    have hc : OAI.PiExponentSeshadri.Frames.coefficient E (restrictSection U.ι v) =
        (U.ι.appTop (endValue s)) ^ k *
          OAI.PiExponentSeshadri.Frames.coefficient E (restrictSection U.ι t) := by
      dsimp only [v]
      erw [restrictSection_precompose, coefficient_precompose, endValue_restrict,
        endValue_endPower, map_pow]
    change SupportBound (fun i => (w i : ℝ)) ((1 : ℕ) * B : ℝ)
      (r (OAI.PiExponentSeshadri.Frames.coefficient E (restrictSection U.ι v))) at hv
    erw [hc, map_mul, map_pow, Nat.cast_one, one_mul, mul_comm] at hv
    exact (supportBound_unit_mul_iff _ B _ _ htunit).mp hv
  have hf := supportBound_zero_of_pow_bounded w B f hfpow
  have hraw : SupportBound (fun i => (w i : ℝ)) 0
      (r (OAI.PiExponentSeshadri.Frames.coefficient (Scheme.Modules.restrictUnitIso U.ι)
        (restrictSection U.ι s))) := by
    change SupportBound (fun i => (w i : ℝ)) 0
      (r (endValue (restrictSection U.ι s ≫ (Scheme.Modules.restrictUnitIso U.ι).hom)))
    erw [endValue_restrict]
    exact hf
  rw [polynomialCoefficient_open]
  exact supportBound_change_open_frame j _ 0 (Scheme.Modules.restrictUnitIso U.ι)
    (untwistPowerFrame A U e 0) s hraw

/-- Every-power version of the section-degree bound, with a nonvacuous zero-power bridge. -/
theorem all_supportBound
    (j : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (w : ι → NNReal) (B : ℝ)
    (heventual : ProjectiveCoefficientBound.EventualBound j A (fun i => (w i : ℝ)) B)
    (t : Sections A 1)
    (ht : IsIso ((Scheme.Modules.restrictFunctor (chartOpen j).1.ι).map t))
    (n : ℕ) (e : Frame j A) (s : Sections A n) :
    SupportBound (fun i => (w i : ℝ)) ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient j A n e s) := by
  cases n with
  | zero => simpa using zero_supportBound j A w B heventual t ht e s
  | succ n => exact positive_supportBound j A w B heventual (Nat.zero_lt_succ n) e s

variable {σ : Type} [Fintype σ]

/-- The exact weighted monomial compactification has the bound at every power and frame. -/
theorem monomial_all_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (B : ℝ)
    (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
    (e : Frame (WeightedCompactification.affineChartMap (R := K) a z hz coordinate hcoordinate)
      (WeightedCompactification.lineBundle (R := K) a))
    (s : Sections (WeightedCompactification.lineBundle (R := K) a) n) :
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient
        (WeightedCompactification.affineChartMap (R := K) a z hz coordinate hcoordinate)
        (WeightedCompactification.lineBundle (R := K) a) n e s) := by
  let j := WeightedCompactification.affineChartMap (R := K) a z hz coordinate hcoordinate
  let A := WeightedCompactification.lineBundle (R := K) a
  let u := WeightedCompactification.coordinateSection (R := K) a z
  let t : Sections A 1 := u ≫ (moduleTensorRightUnit A.sheaf).inv
  have hu : IsIso ((Scheme.Modules.restrictFunctor (chartOpen j).1.ι).map u) := by
    have hopen : OAI.PiExponentSeshadri.SectionOpens.isoOpen u = (chartOpen j).1 :=
      WeightedAffineFrame.affineChart_isoOpen a z hz coordinate hcoordinate
    rw [← hopen]
    exact OAI.PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen u
  have ht : IsIso ((Scheme.Modules.restrictFunctor (chartOpen j).1.ι).map t) := by
    dsimp only [t]
    erw [Functor.map_comp]
    exact IsIso.comp_isIso' hu
      ((Scheme.Modules.restrictFunctor (chartOpen j).1.ι).mapIso
        (moduleTensorRightUnit A.sheaf)).isIso_inv
  exact all_supportBound j A (fun i => ⟨ρ i, hρ i⟩) B
    (WeightedGlobalSectionBound.eventual_supportBound a z hz coordinate hcoordinate ρ B ha)
    t ht n e s

end
end Degree

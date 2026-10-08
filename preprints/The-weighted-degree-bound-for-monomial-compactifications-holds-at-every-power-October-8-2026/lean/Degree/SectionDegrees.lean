import Degree.PolynomialPowers
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound
import OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws
import OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens
import OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame

namespace Degree
noncomputable section
open AlgebraicGeometry CategoryTheory
open OAI.PiExponentSeshadri.Geometry OAI.PiExponentSeshadri.Frames
open OAI.PiExponent
open WeightedSliceDegree AffineJetCoefficientInterface AffineJetCoefficientFrame
open AffineJetSupport ExceptionalAffineChart AffineJetPolynomial

variable {ι K : Type} [LinearOrder ι] [Field K] {X : Scheme}

def chartCoefficientMap (j : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X)
    [IsOpenImmersion j] : Γ((chartOpen j).1.toScheme, ⊤) →+* MvPolynomial ι K :=
  (functionsOnOpenEquiv j).toRingHom.comp (chartOpen j).1.topIso.hom.hom

omit [LinearOrder ι] in
lemma polynomialCoefficient_open (j : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X)
    [IsOpenImmersion j] (A : LineBundle X) (n : ℕ) (e : Frame j A)
    (s : Sections A n) :
    AffineJetCoefficientInterface.coefficient j A n e s =
      chartCoefficientMap j (OAI.PiExponentSeshadri.Frames.coefficient
        (untwistPowerFrame A (chartOpen j).1 e n)
        (restrictSection (chartOpen j).1.ι s)) := by
  unfold AffineJetCoefficientInterface.coefficient polynomialCoefficient
  erw [globalSectionCoefficient_eq]
  rfl

omit [LinearOrder ι] in
lemma supportBound_unit_mul_iff (w : ι → ℝ) (B : ℝ)
    (u p : MvPolynomial ι K) (hu : IsUnit u) :
    SupportBound w B (u * p) ↔ SupportBound w B p := by
  obtain ⟨u, rfl⟩ := hu
  constructor
  · intro h
    have ht := WeightedFrameDegree.supportBound_unit_mul w B
      ((↑(u⁻¹)) : MvPolynomial ι K) ((↑u : MvPolynomial ι K) * p)
      (Units.isUnit _) h
    simpa [← mul_assoc] using ht
  · exact WeightedFrameDegree.supportBound_unit_mul w B _ _ (Units.isUnit _)

omit [LinearOrder ι] in
lemma supportBound_change_open_frame
    (j : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion j]
    (w : ι → ℝ) (B : ℝ) {M : X.Modules}
    (E F : M.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (s : GlobalSections X M)
    (h : SupportBound w B (chartCoefficientMap j
      (OAI.PiExponentSeshadri.Frames.coefficient E (restrictSection (chartOpen j).1.ι s)))) :
    SupportBound w B (chartCoefficientMap j
      (OAI.PiExponentSeshadri.Frames.coefficient F (restrictSection (chartOpen j).1.ι s))) := by
  rw [coefficient_change E F, map_mul]
  exact WeightedFrameDegree.supportBound_unit_mul w B _ _
    ((frameChange E F).isUnit.map (chartCoefficientMap j)) h

/-- The existing eventual bound implies the same bound at every positive power. -/
theorem positive_supportBound
    (j : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (w : ι → NNReal) (B : ℝ)
    (heventual : ProjectiveCoefficientBound.EventualBound j A (fun i => (w i : ℝ)) B)
    {n : ℕ} (hn : 0 < n) (e : Frame j A) (s : Sections A n) :
    SupportBound (fun i => (w i : ℝ)) ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient j A n e s) := by
  obtain ⟨N, hN⟩ := heventual
  let k := N + 1
  have hk : 0 < k := Nat.zero_lt_succ N
  have hnk : N ≤ n * k := by dsimp [k]; nlinarith
  let U := (chartOpen j).1
  let E := untwistPowerFrame A U e n
  let t : Sections A (n * k) := powerSection s k ≫ (linePowerMul A n k).hom
  let F : (modulePow X A.sheaf (n * k)).restrict U.ι ≅ structureSheaf U.toScheme :=
    ((Scheme.Modules.restrictFunctor U.ι).mapIso (linePowerMul A n k)).symm ≪≫
      localPowerFrame U E k
  have ht := hN (n * k) hnk e t
  rw [polynomialCoefficient_open] at ht
  have hF := supportBound_change_open_frame j (fun i => (w i : ℝ))
    (((n * k : ℕ) : ℝ) * B) (untwistPowerFrame A U e (n * k)) F t ht
  have hcoef : OAI.PiExponentSeshadri.Frames.coefficient F (restrictSection U.ι t) =
      endValue (powerRestrictionUnit U k).hom *
        OAI.PiExponentSeshadri.Frames.coefficient E (restrictSection U.ι s) ^ k := by
    have htransport : restrictSection U.ι t ≫
        ((Scheme.Modules.restrictFunctor U.ι).mapIso (linePowerMul A n k)).inv =
          restrictSection U.ι (powerSection s k) := by
      dsimp only [t, restrictSection, Functor.mapIso_inv]
      erw [Functor.map_comp]
      erw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
    dsimp only [F]
    erw [coefficient_transport, htransport]
    exact local_powerSection_coefficient U E s k
  rw [hcoef, map_mul, map_pow] at hF
  have hpow := (supportBound_unit_mul_iff (fun i => (w i : ℝ))
    (((n * k : ℕ) : ℝ) * B) _ _
    ((local_powerSection_coefficient_unit U k).map (chartCoefficientMap j))).mp hF
  have hpow' : SupportBound (fun i => (w i : ℝ))
      ((k : ℝ) * ((n : ℝ) * B))
      (chartCoefficientMap j (OAI.PiExponentSeshadri.Frames.coefficient E
        (restrictSection U.ι s)) ^ k) := by
    convert hpow using 1
    push_cast
    ring
  rw [polynomialCoefficient_open]
  exact supportBound_of_pow w ((n : ℝ) * B) _ hk hpow'

end
end Degree

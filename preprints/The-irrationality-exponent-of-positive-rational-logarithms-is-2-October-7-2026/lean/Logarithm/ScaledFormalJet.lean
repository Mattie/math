import OAI.NumberTheory.PiExponent.Jets.FormalLogJet

namespace OAI
noncomputable section
namespace Logarithm.ScaledFormalJet
open MvPowerSeries PiExponent PiExponent.FormalLogJet PiExponent.FormalJetDerivatives
variable {R : Type*} [CommRing R]

def formalJet {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (C y * (1 + X 0))
    (fun i => C (c i) + X i.succ + formalLog m))

@[simp] theorem formalJet_Y {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    formalJet y c (MvPolynomial.X (0 : Fin (m+1))) = C y * (1 + X 0) := by
  simp [formalJet]

@[simp] theorem formalJet_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (i : Fin m) :
    formalJet y c (MvPolynomial.X i.succ) = C (c i) + X i.succ + formalLog m := by
  simp [formalJet]

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (δ : Derivation R S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ R) : φ (D p) = δ (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

theorem formalJet_frame_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (i j : Fin (m+1)) :
    formalJet y c (PiExponentApprox.polynomialFrame m i (MvPolynomial.X j)) =
      jetFrame m i (formalJet y c (MvPolynomial.X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X]
    | succ j =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X,
        Pi.single_apply, MvPowerSeries.pderiv_X_of_ne,
        one_add_X_mul_pderiv_formalLog]
  | succ i =>
    rw [PiExponentApprox.polynomialFrame_pos m i.succ (Fin.succ_ne_zero i),
      jetFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp [MvPowerSeries.pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_polynomialFrame {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (i : Fin (m+1)) (p : PiExponentApprox.FramePolynomial m) :
    formalJet y c (PiExponentApprox.polynomialFrame m i p) =
      jetFrame m i (formalJet y c p) :=
  derivation_map_of_X (formalJet y c) (PiExponentApprox.polynomialFrame m i)
    (jetFrame m i) (formalJet_frame_X y c i) p

theorem formalJet_polynomialFrameWord {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (word : List (Fin (m+1))) (p : PiExponentApprox.FramePolynomial m) :
    formalJet y c (PiExponentApprox.polynomialFrameWord m word p) =
      jetFrameWord m word (formalJet y c p) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    rw [PiExponentApprox.polynomialFrameWord_cons, formalJet_polynomialFrame, ih]
    rfl

theorem formalJet_polynomialFrameWord_vanishing {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet y c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin (m+1))) :
    formalJet y c (PiExponentApprox.polynomialFrameWord m word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJet_polynomialFrameWord]
  exact jetFrameWord_mem_rationalWeightedIdeal v hv H (formalJet y c p) hp word

end Logarithm.ScaledFormalJet

end

end OAI

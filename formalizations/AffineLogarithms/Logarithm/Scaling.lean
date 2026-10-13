import Logarithm.ScaledFormalJet
import Logarithm.GeneralizedCenters

namespace OAI
noncomputable section
namespace Logarithm
open PiExponent PiExponentApprox MvPolynomial

/-- Pullback by multiplication of Y by the center coordinate. -/
def scaleY {m : ℕ} (y : ℂ) : FramePolynomial m →ₐ[ℂ] FramePolynomial m :=
  MvPolynomial.aeval (Fin.cases (C y * X 0) (fun i => X i.succ))

theorem scaleY_comp {m : ℕ} (y z : ℂ) :
    (scaleY (m := m) y).comp (scaleY z) = scaleY (y*z) := by
  ext i
  cases i using Fin.cases <;> simp [scaleY, map_mul, mul_comm, mul_left_comm]

theorem scaleY_one {m : ℕ} : scaleY (m := m) 1 = AlgHom.id ℂ _ := by
  ext i
  cases i using Fin.cases <;> simp [scaleY]

def scaleYEquiv {m : ℕ} (y : ℂ) (hy : y ≠ 0) :
    FramePolynomial m ≃ₐ[ℂ] FramePolynomial m :=
  AlgEquiv.ofAlgHom (scaleY y) (scaleY y⁻¹)
    (by rw [scaleY_comp, mul_inv_cancel₀ hy, scaleY_one])
    (by rw [scaleY_comp, inv_mul_cancel₀ hy, scaleY_one])

theorem scaleY_surjective {m : ℕ} (y : ℂ) (hy : y ≠ 0) :
    Function.Surjective (scaleY (m := m) y) :=
  (scaleYEquiv y hy).surjective

theorem scaleY_frame_X {m : ℕ} (y : ℂ) (i j : Fin (m+1)) :
    scaleY y (polynomialFrame m i (X j)) =
      polynomialFrame m i (scaleY y (X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [scaleY, polynomialFrame_zero, logarithmicDerivation_apply,
        MvPolynomial.pderiv_X]
    | succ j => simp [scaleY, polynomialFrame_zero, logarithmicDerivation_apply,
        MvPolynomial.pderiv_X, Pi.single_apply]
  | succ i =>
    rw [polynomialFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp [scaleY, MvPolynomial.pderiv_X]
    | succ j =>
      by_cases hij : i = j
      · subst j; simp [scaleY]
      · simp [scaleY, MvPolynomial.pderiv_X, Ne.symm hij]

theorem scaleY_frame {m : ℕ} (y : ℂ) (i : Fin (m+1)) (F : FramePolynomial m) :
    scaleY y (polynomialFrame m i F) = polynomialFrame m i (scaleY y F) :=
  FormalLogJet.derivation_map_of_X (scaleY y) (polynomialFrame m i)
    (polynomialFrame m i) (scaleY_frame_X y i) F

theorem scaleY_frameWord {m : ℕ} (y : ℂ) (word : List (Fin (m+1)))
    (F : FramePolynomial m) :
    scaleY y (polynomialFrameWord m word F) =
      polynomialFrameWord m word (scaleY y F) := by
  induction word with
  | nil => rfl
  | cons i word ih => rw [polynomialFrameWord_cons, scaleY_frame, ih]; rfl

theorem formalJet_scaleY {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (F : FramePolynomial m) :
    FormalLogJet.formalJet c (scaleY y F) = ScaledFormalJet.formalJet y c F := by
  have h : (FormalLogJet.formalJet c).comp (scaleY y) =
      ScaledFormalJet.formalJet y c := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;>
      simp [scaleY, ScaledFormalJet.formalJet, FormalLogJet.formalJet,
        MvPowerSeries.c_eq_algebraMap]
  exact DFunLike.congr_fun h F

theorem aeval_normalized_scaleY {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (z : Fin (m+1) → E) (y : ℂ) (hy : y ≠ 0) (F : FramePolynomial m) :
    MvPolynomial.aeval (normalized z y) (scaleY y F) = MvPolynomial.aeval z F := by
  have h : (MvPolynomial.aeval (normalized z y)).comp (scaleY y) =
      MvPolynomial.aeval z := by
    ext i
    cases i using Fin.cases with
    | zero =>
      simp [scaleY, normalized, map_inv₀, mul_comm,
        (map_ne_zero (algebraMap ℂ E)).mpr hy]
    | succ i => simp [scaleY, normalized]
  exact DFunLike.congr_fun h F

end Logarithm
end
end OAI

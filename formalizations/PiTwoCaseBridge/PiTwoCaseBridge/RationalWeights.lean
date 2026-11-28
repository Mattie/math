import OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale
import OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets
import OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial

/-!
# Positive rational weights and logarithmic charts

Clearing denominators does not change any weighted cutoff. The real cutoff
conversion uses an integer ceiling because the cleared monomial weights are
integers and the target inequality is strict.
-/

namespace PiTwoCaseBridge

open OAI OAI.PiExponent PiExponentApprox MvPolynomial

/-- Clear the denominators in a positive rational weight vector. -/
theorem exists_integer_weights {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) :
    ∃ D : ℕ, 0 < D ∧ ∃ u : Fin n → ℕ, (∀ i, 0 < u i) ∧
      ∀ i, (w i : ℝ) = (u i : ℝ) / (D : ℝ) :=
  positive_rational_weights_common_denominator w hw

theorem real_weight_eq_integer_div {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (u : σ → ℕ) (D : ℕ) (a : σ →₀ ℕ)
    (h : ∀ i, (w i : ℝ) = (u i : ℝ) / (D : ℝ)) :
    Finsupp.weight (fun i => (w i : ℝ)) a =
      (Finsupp.weight u a : ℝ) / (D : ℝ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, h]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc]
  norm_cast

theorem rational_weight_cast {σ : Type*} [Fintype σ]
    (w : σ → ℚ) (a : σ →₀ ℕ) :
    (Finsupp.weight w a : ℝ) = Finsupp.weight (fun i => (w i : ℝ)) a := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]

/-- At center `(1,c)`, replace the formal logarithm by a polynomial cutoff. -/
noncomputable def logarithmicChart {m : ℕ} (c : Fin m → ℂ) (cutoff : Fin m → ℕ) :
    FramePolynomial m ≃ₐ[ℂ] FramePolynomial m :=
  AlgebraicJetPackets.triangularEquiv c
    (fun i => PowerSeries.trunc (cutoff i) (PowerSeries.log ℂ))

theorem logarithmicChart_coeff {m : ℕ} (c : Fin m → ℂ) (cutoff : Fin m → ℕ)
    (P : FramePolynomial m) (a : Fin (m+1) →₀ ℕ) :
    (logarithmicChart c cutoff P).coeff a =
      MvPowerSeries.coeff a (FormalLogTruncation.truncatedFormalJet c cutoff P) := by
  rw [AlgebraicJetPackets.truncatedFormalJet_eq_polynomial]
  exact (MvPolynomial.coeff_coe _ _).symm

theorem eval_zero_logarithmicChart {m : ℕ} (c : Fin m → ℂ) (cutoff : Fin m → ℕ)
    (P : FramePolynomial m) :
    MvPolynomial.eval 0 (logarithmicChart c cutoff P) =
      MvPolynomial.eval (CompactJetPolynomial.center c) P := by
  have he :
      (MvPolynomial.aeval (0 : Fin (m+1) → ℂ)).comp (logarithmicChart c cutoff).toAlgHom =
        MvPolynomial.aeval (CompactJetPolynomial.center c) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      change MvPolynomial.aeval (0 : Fin (m+1) → ℂ)
        (AlgebraicJetPackets.triangularMap c _ (X 0)) = _
      simp [CompactJetPolynomial.center]
    | succ i =>
      change MvPolynomial.aeval (0 : Fin (m+1) → ℂ)
        (AlgebraicJetPackets.triangularMap c _ (X i.succ)) = _
      rw [AlgebraicJetPackets.triangularMap_X_succ]
      have hz : (PowerSeries.trunc (cutoff i) (PowerSeries.log ℂ)).eval 0 = 0 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, PowerSeries.coeff_trunc]
        simp [PowerSeries.coeff_log]
      have hp : MvPolynomial.aeval (0 : Fin (m+1) → ℂ)
          (Polynomial.aeval (X (0 : Fin (m+1)) : MvPolynomial (Fin (m+1)) ℂ)
            (PowerSeries.trunc (cutoff i) (PowerSeries.log ℂ))) = 0 := by
        rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
        change Polynomial.aeval (0 : ℂ) _ = 0
        rw [← Polynomial.coeff_zero_eq_eval_zero] at hz
        simpa [Polynomial.aeval_def] using hz
      rw [map_add, map_add, hp]
      simp [CompactJetPolynomial.center]
  exact DFunLike.congr_fun he P

end PiTwoCaseBridge

import Logarithm.JetIdeals
import OAI.NumberTheory.PiExponent.Jets.JetProductLocalization

namespace OAI
noncomputable section
namespace Logarithm.JetProductLocalization
open scoped BigOperators
open PiExponent Logarithm.JetIdeals

variable {A : Type*} [CommRing A] [Algebra ℂ A] {m : ℕ}

/-- The affine ideal at a nonzero Y center is the old logarithmic ideal in its
normalized Y coordinate. -/
theorem map_powerIdeal_aeval (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (a : A) (x : Fin m → A) :
    (powerIdeal y c T e).map (MvPolynomial.aeval (Fin.cases a x)).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal c (a * algebraMap ℂ A y⁻¹) x T e := by
  rw [powerIdeal_eq_map_inverse y hy, Ideal.map_map]
  have he : (MvPolynomial.aeval (Fin.cases a x)).toRingHom.comp
      (scaleY y⁻¹).toRingHom =
        (MvPolynomial.aeval (Fin.cases (a * algebraMap ℂ A y⁻¹) x)).toRingHom := by
    have he' : (MvPolynomial.aeval (Fin.cases a x)).comp (scaleY y⁻¹) =
        MvPolynomial.aeval (Fin.cases (a * algebraMap ℂ A y⁻¹) x) := by
      apply MvPolynomial.algHom_ext
      intro i
      cases i using Fin.cases <;> simp [scaleY, mul_comm]
    exact congrArg AlgHom.toRingHom he'
  rw [he]
  exact CompactJetPolynomial.map_powerIdeal_aeval c T e _ x

variable [IsLocalRing A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

/-- Other Y centers become unit ideals in the selected local ring. -/
theorem map_powerIdeal_eq_top_of_ne {J : Type*}
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (hyinj : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (a : A) (x : Fin m → A) (j k : J) (hkj : k ≠ j)
    (ha : CurveLocalOrder.residueAugmentation ℂ A a = y j) :
    (powerIdeal (y k) (c k) T e).map
      (MvPolynomial.aeval (Fin.cases a x)).toRingHom = ⊤ := by
  rw [map_powerIdeal_aeval (y k) (hy k)]
  apply PiExponent.JetProductLocalization.logarithmicIdeal_eq_top_of_residue_ne
  rintro ⟨h, _⟩
  rw [map_mul, CurveLocalOrder.residueAugmentation_algebraMap, ha] at h
  apply hkj
  apply hyinj
  exact (mul_inv_eq_one₀ (hy k)).mp h |>.symm

omit [IsLocalRing A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)] in
theorem map_polynomialIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (a : A) (x : Fin m → A) :
    (polynomialIdeal y c T e).map (MvPolynomial.aeval (Fin.cases a x)).toRingHom =
      ∏ j, LogarithmicContactIdeal.logarithmicIdeal (c j)
        (a * algebraMap ℂ A (y j)⁻¹) x T e := by
  unfold polynomialIdeal
  change Ideal.mapHom (MvPolynomial.aeval (Fin.cases a x)).toRingHom _ = _
  rw [map_prod]
  exact Finset.prod_congr rfl (fun j _ => map_powerIdeal_aeval (y j) (hy j) (c j) T e a x)

/-- Distinct Y values alone select one factor of the finite-center ideal. -/
theorem map_polynomialIdeal_eq_selected {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (hyinj : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (a : A) (x : Fin m → A) (j : J)
    (ha : CurveLocalOrder.residueAugmentation ℂ A a = y j) :
    (polynomialIdeal y c T e).map (MvPolynomial.aeval (Fin.cases a x)).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal (c j)
        (a * algebraMap ℂ A (y j)⁻¹) x T e := by
  classical
  rw [map_polynomialIdeal y hy]
  apply Finset.prod_eq_single j
  · intro k _ hkj
    rw [Ideal.one_eq_top, ← map_powerIdeal_aeval (y k) (hy k)]
    exact map_powerIdeal_eq_top_of_ne y hy hyinj c T e a x j k hkj ha
  · simp

end Logarithm.JetProductLocalization
end
end OAI

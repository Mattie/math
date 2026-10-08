import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI.AlgebraicLog.FieldRealization
open scoped IntermediateField nonZeroDivisors

/-- The field used for a real algebraic input is its actual rational adjunction. -/
noncomputable abbrev RealField (alpha : ℝ) := IntermediateField.adjoin ℚ ({alpha} : Set ℝ)

noncomputable def generator (alpha : ℝ) : RealField alpha :=
  IntermediateField.AdjoinSimple.gen ℚ alpha

noncomputable def distinguishedEmbedding (alpha : ℝ) : RealField alpha →ₐ[ℚ] ℂ :=
  ((algebraMap ℝ ℂ).comp (RealField alpha).subtype).toRatAlgHom

@[simp] theorem distinguishedEmbedding_generator (alpha : ℝ) :
    distinguishedEmbedding alpha (generator alpha) = (alpha : ℂ) := rfl

theorem realField_numberField {alpha : ℝ} (ha : IsAlgebraic ℚ alpha) :
    NumberField (RealField alpha) := by
  letI := IntermediateField.adjoin.finiteDimensional ha.isIntegral
  exact NumberField.of_module_finite ℚ (RealField alpha)

theorem realField_finrank {alpha : ℝ} (ha : IsAlgebraic ℚ alpha)
    (hdegree : (minpoly ℚ alpha).natDegree = 2) :
    Module.finrank ℚ (RealField alpha) = 2 := by
  exact (IntermediateField.adjoin.finrank ha.isIntegral).trans hdegree

/-- A positive natural denominator clears an arbitrary number-field element;
the input is not required to be an algebraic integer. -/
theorem exists_positive_integral_multiple {F : Type*} [Field F] [NumberField F]
    (a : F) : ∃ d : ℕ, 1 ≤ d ∧ IsIntegral ℤ ((d : F) * a) := by
  have ha : IsIntegral ℚ a := (Algebra.IsAlgebraic.of_finite ℚ F).1 a |>.isIntegral
  obtain ⟨d, hd⟩ := ha.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) a
  have hd0 : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  change IsIntegral ℤ ((d : ℤ) • a) at hd
  obtain ⟨n, hn | hn⟩ := (d : ℤ).eq_nat_or_neg
  · refine ⟨n, ?_, ?_⟩
    · have hn0 : n ≠ 0 := by intro h; apply hd0; simp [hn, h]
      omega
    · simpa [hn, Algebra.smul_def] using hd
  · refine ⟨n, ?_, ?_⟩
    · have hn0 : n ≠ 0 := by intro h; apply hd0; simp [hn, h]
      omega
    · simpa [hn, Algebra.smul_def] using hd.neg

end OAI.AlgebraicLog.FieldRealization

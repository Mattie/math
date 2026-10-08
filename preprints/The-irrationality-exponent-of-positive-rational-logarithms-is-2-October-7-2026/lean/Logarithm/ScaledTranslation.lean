import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation

namespace OAI
noncomputable section
namespace Logarithm.ScaledTranslation
open scoped BigOperators
open PiExponent PiExponent.MatrixTranslation PiExponent.RowTranslation

theorem det_matrix_translation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ι → ℕ) (omega : ℂ) (b : ι → Fin m → ℕ)
    (h : ι → ℕ) (a : ι → Fin m → ℕ) (factor : ι → ι → ℂ)
    (S : Finset (Fin m →₀ ℕ))
    (hp : ∀ i c, (periodMonomial (j i) omega (h c) (a c)).support ⊆ S) :
    Matrix.det (fun i c => factor i c * InterpolationMatrix.entry r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      ∑ f : (∀ i, RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i)),
        (∏ i, rowScalar (fun k => (j i : ℂ) * (r k - omega))
          (fun k => tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) (f i).1.1 (f i).2.1 (f i).2.2) *
          Matrix.det (fun i c => factor i c * PowerSeries.coeff (s i - (f i).2.2)
            ((periodMonomial (j i) omega (h c) (a c)).coeff (f i).1.1)) := by
  classical
  have he : (fun i c => factor i c * InterpolationMatrix.entry r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      (fun i c => ∑ t : RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i),
        rowScalar (fun k => (j i : ℂ) * (r k - omega))
          (fun k => tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) t.1.1 t.2.1 t.2.2 *
          (factor i c * PowerSeries.coeff (s i - t.2.2)
            ((periodMonomial (j i) omega (h c) (a c)).coeff t.1.1))) := by
    funext i c
    rw [matrix_entry_translation_choices r T (j i) (s i) omega (b i) (h c) (a c) S (hp i c),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [he]
  exact det_dependent_row_sum _ _

end Logarithm.ScaledTranslation
end
end OAI

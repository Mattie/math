import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

open scoped NNReal ENNReal

noncomputable section

namespace Zeta2Blueprint

def IrrMeasureLE (x c : ℝ) : Prop :=
  ∀ δ > 0,
    {r : ℚ | |x - (r : ℝ)| < (r.den : ℝ) ^ (-(c + δ))}.Finite

def irrationalityMeasure (x : ℝ) : EReal :=
  ⨅ (c : ℝ) (_ : IrrMeasureLE x c), (c : EReal)

end Zeta2Blueprint

namespace PrimeNumerator.WindowFinal

abbrev bound : ℝ := 821200073639400000000 / 178914706731744129841

theorem irrationality_measure_pi_sq :
    Zeta2Blueprint.irrationalityMeasure (Real.pi ^ 2) < ((4.589897 : ℝ) : EReal) := by
  sorry

theorem rational_upper_bound :
    Zeta2Blueprint.irrationalityMeasure (Real.pi ^ 2) ≤ (bound : EReal) := by
  sorry

theorem finite_good_ratios :
    {r : ℚ | |Real.pi ^ 2 - (r : ℝ)| < (r.den : ℝ) ^ (-(4.589897 : ℝ))}.Finite := by
  sorry

end PrimeNumerator.WindowFinal

example : (@SupSet.sSup ENNReal (@CompletePartialOrder.toSupSet ENNReal (@CompleteLattice.toCompletePartialOrder ENNReal (@CompletelyDistribLattice.toCompleteLattice ENNReal (@CompleteLinearOrder.toCompletelyDistribLattice ENNReal ENNReal.instCompleteLinearOrder))))) = (sSup : Set ENNReal → ENNReal) := rfl

namespace PrimeNumerator.WindowCatalogue

theorem pi_sq_catalogue_bound :
    @SupSet.sSup ENNReal (@CompletePartialOrder.toSupSet ENNReal (@CompleteLattice.toCompletePartialOrder ENNReal (@CompletelyDistribLattice.toCompleteLattice ENNReal (@CompleteLinearOrder.toCompletelyDistribLattice ENNReal ENNReal.instCompleteLinearOrder)))) (((↑) : ℝ≥0 → ℝ≥0∞) '' {p : ℝ≥0 | LiouvilleWith p (Real.pi ^ 2)}) ≤
      ENNReal.ofReal WindowFinal.bound := by sorry

theorem pi_sq_catalogue_lt :
    @SupSet.sSup ENNReal (@CompletePartialOrder.toSupSet ENNReal (@CompleteLattice.toCompletePartialOrder ENNReal (@CompletelyDistribLattice.toCompleteLattice ENNReal (@CompleteLinearOrder.toCompletelyDistribLattice ENNReal ENNReal.instCompleteLinearOrder)))) (((↑) : ℝ≥0 → ℝ≥0∞) '' {p : ℝ≥0 | LiouvilleWith p (Real.pi ^ 2)}) <
      ENNReal.ofReal (4.589897 : ℝ) := by sorry

end PrimeNumerator.WindowCatalogue


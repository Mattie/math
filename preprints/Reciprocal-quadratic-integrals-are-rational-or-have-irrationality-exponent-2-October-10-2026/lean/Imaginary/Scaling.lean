import Logarithm.ExponentConsequence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI.Imaginary
open Filter PiExponent

/-- Division by a positive integer preserves the explicit exponent-two bound.
A smaller exponent absorbs the fixed multiplier; no algebraic scaling is used. -/
theorem eventualLowerBound_div_nat {x : ℝ} (hx : EventualLowerBound x)
    (n : ℕ) (hn : 0 < n) : EventualLowerBound (x / n) := by
  intro nu hnu
  let mu : ℝ := (nu + 2) / 2
  have hmu : 2 < mu := by dsimp [mu]; linarith
  have hgap : 0 < nu - mu := by dsimp [mu]; linarith
  obtain ⟨Q, hQ, hb⟩ := hx mu hmu
  have hgrowth : Tendsto (fun q : ℕ => (q : ℝ) ^ (nu - mu)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hgrowth.eventually (eventually_ge_atTop (n : ℝ)))
  refine ⟨max Q N, le_trans hQ (le_max_left _ _), ?_⟩
  intro p q hq
  have hqQ : Q ≤ q := (le_max_left _ _).trans hq
  have hqN : N ≤ q := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < Q) hqQ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpower : (n : ℝ) * (q : ℝ) ^ (-nu) ≤ (q : ℝ) ^ (-mu) := by
    have hh := mul_le_mul_of_nonneg_right (hN q hqN)
      (Real.rpow_nonneg hqpos.le (-nu))
    rw [← Real.rpow_add hqpos] at hh
    simpa only [show nu - mu + -nu = -mu by ring] using hh
  have happrox := hb ((n : ℤ) * p) q hqQ
  have heq : x - (((n : ℤ) * p : ℤ) : ℝ) / (q : ℝ) =
      (n : ℝ) * (x / n - (p : ℝ) / q) := by
    push_cast
    field_simp
  rw [heq, abs_mul, abs_of_pos hnpos] at happrox
  exact (mul_le_mul_iff_right₀ hnpos).mp (hpower.trans happrox)

theorem eventualLowerBound_neg {x : ℝ} (hx : EventualLowerBound x) :
    EventualLowerBound (-x) := by
  intro nu hnu
  obtain ⟨Q, hQ, hb⟩ := hx nu hnu
  refine ⟨Q, hQ, fun p q hq => ?_⟩
  have hh := hb (-p) q hq
  have heq : -x - (p : ℝ) / q = -(x - ((-p : ℤ) : ℝ) / q) := by push_cast; ring
  rw [heq, abs_neg]
  exact hh

end OAI.Imaginary

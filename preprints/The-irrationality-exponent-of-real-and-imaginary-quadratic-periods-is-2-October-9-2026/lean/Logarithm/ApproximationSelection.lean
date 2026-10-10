import Mathlib

namespace OAI.Logarithm

/-- Unbounded approximations to any nonzero real target give arbitrarily large
logarithmic denominator weights, with nonzero numerators. -/
theorem exists_large_log_approximation
    (ξ nu X : ℝ) (hξ : ξ ≠ 0) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |ξ - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |ξ - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  let Y := max X (-(Real.log |ξ|) / nu)
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp Y)
  obtain ⟨p, q, hq, happrox⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hNq : N ≤ q := le_trans (le_max_right _ _) hq
  have hexp : Real.exp Y < (q : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNq)
  have hlogY : Y < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos Y) hexp
  have hlog : X < Real.log q := (le_max_left _ _).trans_lt hlogY
  have hmargin : -(Real.log |ξ|) / nu < Real.log q :=
    (le_max_right _ _).trans_lt hlogY
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpow : (q : ℝ) ^ (-nu) < |ξ| := by
    rw [Real.rpow_def_of_pos hqpos]
    have hmul := (div_lt_iff₀ hnu).mp hmargin
    calc
      Real.exp (Real.log q * (-nu)) < Real.exp (Real.log |ξ|) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      _ = |ξ| := Real.exp_log (abs_pos.mpr hξ)
  have hp : p ≠ 0 := by
    intro hp0
    have hsmall : |ξ| ≤ (q : ℝ) ^ (-nu) := by simpa [hp0] using happrox
    exact (not_le_of_gt hpow) hsmall
  exact ⟨p, q, hq2, hlog, hp, happrox⟩

end OAI.Logarithm

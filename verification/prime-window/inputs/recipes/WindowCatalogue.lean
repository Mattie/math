import WindowFinal
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-!
# The irrationality exponent of π² in the Formal Conjectures definition

[Formal Conjectures, entry 7a](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/OptimizationConstants/7a.lean)
defines the exponent of a real number as the supremum of its nonnegative
`LiouvilleWith` exponents. Here we evaluate that same expression at π².
The paper bounds the exponent by counting exceptional reduced fractions.
`liouvilleWith_le_of_bound` connects the two formulations, and
`pi_sq_catalogue_lt` gives the strict upper bound 4.589897.
-/

open Filter Set Zeta2Blueprint
open scoped NNReal ENNReal Topology

namespace PrimeNumerator.WindowCatalogue

/-- A finite set of reduced approximants excludes frequent approximations at a
larger exponent, even when the latter are written with unreduced denominators. -/
theorem liouvilleWith_le_of_bound {x μ ν : ℝ} (hμ : 0 ≤ μ)
    (bound : IrrMeasureLE x μ) (hν : LiouvilleWith ν x) : ν ≤ μ := by
  by_contra! h
  obtain ⟨s, hμs, hsν⟩ := exists_between h
  have hs : 0 < s := hμ.trans_lt hμs
  let S := {r : ℚ | |x - (r : ℝ)| < (r.den : ℝ) ^ (-s)}
  have hS : S.Finite := WindowPi.finite_lt bound hμs
  have small : ∀ᶠ n : ℕ in atTop, ∀ r ∈ S, x ≠ (r : ℝ) →
      (n : ℝ) ^ (-s) < |x - (r : ℝ)| := by
    refine hS.eventually_all.mpr fun r _ ↦ ?_
    by_cases hr : x = (r : ℝ)
    · simp [hr]
    · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-s)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
      exact (hlim.eventually_lt_const (abs_pos.mpr (sub_ne_zero.mpr hr))).mono fun _ hn _ ↦ hn
  obtain ⟨n, ⟨m, hne, happ⟩, hn, hsmall⟩ :=
    ((hν.frequently_lt_rpow_neg hsν).and_eventually ((eventually_ge_atTop 1).and small)).exists
  let r := Rat.divInt m n
  have hcast : (r : ℝ) = m / n := by simpa only [Int.cast_natCast] using (Rat.cast_divInt (α := ℝ) m (n : ℤ))
  have hdvd : r.den ∣ n := by exact_mod_cast Rat.den_dvd m (n : ℤ)
  have hd : (r.den : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hdvd
  have hr : r ∈ S := by
    change |x - (r : ℝ)| < (r.den : ℝ) ^ (-s)
    rw [hcast]
    exact happ.trans_le (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast r.den_pos) hd (by linarith))
  rw [← hcast] at hne happ
  exact (hsmall r hr hne).asymm happ

/-- The supremum of the approximation exponents of π² is at most the exact
rational bound in `WindowFinal.bound`. -/
theorem pi_sq_catalogue_bound :
    sSup (((↑) : ℝ≥0 → ℝ≥0∞) '' {p : ℝ≥0 | LiouvilleWith p (Real.pi ^ 2)}) ≤
      ENNReal.ofReal WindowFinal.bound := by
  apply sSup_le
  rintro _ ⟨p, hp, rfl⟩
  have h := liouvilleWith_le_of_bound (by norm_num [WindowFinal.bound]) WindowFinal.pi_sq_bound hp
  simpa using ENNReal.ofReal_le_ofReal h

/-- The irrationality exponent of π² in the supremum formulation is strictly
less than 4.589897. Strictness comes from the exact rational comparison. -/
theorem pi_sq_catalogue_lt :
    sSup (((↑) : ℝ≥0 → ℝ≥0∞) '' {p : ℝ≥0 | LiouvilleWith p (Real.pi ^ 2)}) <
      ENNReal.ofReal (4.589897 : ℝ) :=
  pi_sq_catalogue_bound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr WindowFinal.bound_lt)

#print axioms liouvilleWith_le_of_bound
#print axioms pi_sq_catalogue_bound
#print axioms pi_sq_catalogue_lt
end PrimeNumerator.WindowCatalogue

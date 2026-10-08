import OAI.NumberTheory.PiExponent.Main
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!+# Flint Hills and Cookson Hills catalogue endpoints

Flint Hills convergence is already proved in OpenAI's released library.
The Cookson comparison below transfers it to the cosine series.
-/
namespace SmallDivisors

theorem sin_nat_ne_zero {n : ℕ} (hn : 0 < n) : Real.sin (n : ℝ) ≠ 0 :=
  OAI.PiExponent.sin_nat_ne_zero hn

theorem cos_nat_ne_zero {n : ℕ} (hn : 0 < n) : Real.cos (n : ℝ) ≠ 0 := by
  intro h
  have hz := sin_nat_ne_zero (n := 2 * n) (by omega)
  apply hz
  simp only [Nat.cast_mul, Nat.cast_ofNat, Real.sin_two_mul, h, mul_zero]

theorem cookson_term_le_flint_even {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ)^3 * Real.cos n ^ 2) ≤
      32 * (1 / (((2 * n : ℕ) : ℝ)^3 * Real.sin (2 * n : ℕ)^2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := sin_nat_ne_zero hn
  have hc := cos_nat_ne_zero hn
  have hsq : Real.sin (n : ℝ)^2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (n : ℝ), sq_nonneg (Real.cos (n : ℝ))]
  have hc2 : 0 < Real.cos (n : ℝ)^2 := sq_pos_of_ne_zero hc
  have hs2 : 0 < Real.sin (n : ℝ)^2 := sq_pos_of_ne_zero hs
  simp only [Nat.cast_mul, Nat.cast_ofNat, Real.sin_two_mul, mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)^3 * Real.cos (n : ℝ)^2 by positivity)
    (sub_nonneg.mpr hsq)]

theorem flint_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.sin (n + 1)^2))) := by
  simpa only [Nat.cast_add, Nat.cast_one] using OAI.PiExponent.flint_hills_summable

theorem cookson_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.cos (n + 1)^2))) := by
  have hf := OAI.PiExponent.flintHills_summable_of_eventual_lower_bound
    OAI.PiExponent.pi_eventual_lower_bound
  have he := hf.comp_injective (show Function.Injective (fun n : ℕ => 2 * (n + 1)) by
    intro a b hab
    dsimp only at hab
    omega)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (he.mul_left 32)
  intro n
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one]
    using cookson_term_le_flint_even (Nat.succ_pos n)

#print axioms flint_hills_series_converges
#print axioms cookson_hills_series_converges
#print axioms cos_nat_ne_zero

end SmallDivisors

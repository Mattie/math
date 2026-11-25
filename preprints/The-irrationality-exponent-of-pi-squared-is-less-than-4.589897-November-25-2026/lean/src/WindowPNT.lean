import WindowAggregate
import RateBridge
import Zeta2FourTrajectoryMatrices.ArithmeticRate.arith_rate

/-!
# Growth of the common divisor from the prime number theorem

For each fixed window, the prime number theorem gives a limit for the sum
of log primes divided by the level. We sum these limits over six windows in
each of one million fixed periods. Their total exceeds 0.10868226, so
eventually the logarithm of the common divisor is at least 0.10868226 times
the level.
-/

open Filter Topology Finset

noncomputable section
namespace PrimeNumerator.WindowPNT

open WindowGeometry

private def width (t : ℕ) (j : Fin 6) : ℝ :=
  (aden j : ℝ) / (aden j * t + anum j : ℕ) - 13 / (13 * t + knum j : ℕ)

private theorem window_limit (i : ℕ) (j : Fin 6) :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ window N (i+1) j, Real.log (p : ℝ)) / N) atTop (𝓝 (width (i+1) j)) := by
  apply Zeta2ArithRate.open_window_tendsto
  all_goals fin_cases j <;> norm_num [anum, aden, knum] <;> omega

private theorem algebraic_width (i : ℕ) (j : Fin 6) :
    width (i+1) j =
      ((1 / (((i+1 : ℕ) : ℚ) + (anum j : ℚ) / aden j) -
        1 / (((i+1 : ℕ) : ℚ) + (knum j : ℚ) / 13) : ℚ) : ℝ) := by
  unfold width
  fin_cases j <;> norm_num [anum, aden, knum] <;> field_simp

private theorem sum_widths :
    (∑ i ∈ range 1000000, ∑ j : Fin 6, width (i+1) j) = (RateBridge.millionRate : ℝ) := by
  have by_interval (j : Fin 6) :
      (∑ i ∈ range 1000000, width (i+1) j) =
        (RateBridge.intervalSum ((anum j : ℚ) / aden j) ((knum j : ℚ) / 13) : ℝ) := by
    simp only [RateBridge.intervalSum, Rat.cast_sum, algebraic_width]
  rw [sum_comm]
  simp_rw [by_interval]
  simp [RateBridge.millionRate, Fin.sum_univ_succ, anum, aden, knum]
  ring

/-- The normalized sum of logarithms over the six windows in each of the first
million periods converges to the exact rational finite-window rate. -/
theorem finite_windows_limit :
    Tendsto (fun N : ℕ => (∑ i ∈ range 1000000, ∑ j : Fin 6,
      ∑ p ∈ window N (i+1) j, Real.log (p : ℝ)) / N) atTop (𝓝 (RateBridge.millionRate : ℝ)) := by
  rw [← sum_widths]
  have h := tendsto_finsetSum (range 1000000) fun i _ =>
    tendsto_finsetSum (univ : Finset (Fin 6)) fun j _ => window_limit i j
  simpa only [Finset.sum_div] using h

/-- The common divisor of the two integer entries grows at least at the
certified finite-window rate. -/
theorem translatedProduct_rate : ∀ᶠ N : ℕ in atTop,
    (10868226 / 100000000 : ℝ) ≤ Real.log (KernelEndToEnd.translatedProduct N : ℝ) / N := by
  have bound : (10868226 / 100000000 : ℝ) < (RateBridge.millionRate : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr RateBridge.millionRate_gt
  filter_upwards [finite_windows_limit.eventually (lt_mem_nhds bound),
    eventually_ge_atTop (50*1000001^2 : ℕ)] with N hwin hN
  exact hwin.le.trans (div_le_div_of_nonneg_right (WindowAggregate.sum_windows_le hN)
    (Nat.cast_nonneg N))

#print axioms finite_windows_limit
#print axioms translatedProduct_rate

end PrimeNumerator.WindowPNT

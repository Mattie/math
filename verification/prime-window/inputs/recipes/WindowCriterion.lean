import KernelReduction
import Zeta2FourTrajectoryMatrices.Blueprint.blueprint

/-!
# Applying the irrationality criterion to ζ(2)

Dividing the integer linear forms of Leibtag et al. by the common prime
product lowers the upper bound `sigma` on coefficient growth and raises the
lower bound `tau` on error decay by the same saving. Their three-level independence estimate
then gives the exponent bound `1 + sigma / tau`. The hypothesis
`ProductGrowth` in `zeta2_bound` is proved by `WindowPNT.translatedProduct_rate`.
-/

open Filter Topology Real Zeta2Blueprint
noncomputable section

namespace PrimeNumerator.WindowCriterion

open KernelEndToEnd

/-- Certified lower rate required of the extra common divisor. -/
def saving : ℝ := 10868226 / 100000000

/-- Upper bound on the source normalization rate, retaining its rational precision. -/
def normRate : ℝ := 143297092558247390159 / 13110552000000000000

/-- Eventually the log of the common prime product, divided by the level,
is at least `saving`. -/
def ProductGrowth : Prop :=
  ∀ᶠ n : ℕ in atTop, saving ≤ Real.log (translatedProduct n) / n

def sigma : ℝ := 38.168733 + normRate - saving
def tau : ℝ := 24.467842 - normRate + saving
def exponent : ℝ := 821200073639400000000 / 178914706731744129841

theorem exponent_pos : 0 < exponent := by norm_num [exponent]
theorem exponent_lt : exponent < 4589897 / 1000000 := by
  norm_num [exponent]

private def multiplier (n : ℕ) : ℝ := kN n / translatedProduct n

private theorem product_pos (n : ℕ) : (0 : ℝ) < translatedProduct n := by
  exact_mod_cast KernelReduction.translatedProduct_pos n

private theorem multiplier_pos (n : ℕ) : 0 < multiplier n :=
  div_pos (kN_rate.1 n) (product_pos n)

private theorem multiplier_rate (g : ProductGrowth) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, multiplier n ≤ exp ((normRate - saving + ε) * n) := by
  have hL : 25 - gammaRate - 233/120 < normRate + ε := by
    have h := gamma_bounds.1
    unfold normRate
    linarith
  filter_upwards [arith_rate.eventually (gt_mem_nhds hL), g, eventually_ge_atTop 1]
    with n hk hg hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hu := (div_lt_iff₀ hn').1 hk
  have hl := (le_div_iff₀ hn').1 hg
  rw [← Real.exp_log (multiplier_pos n), multiplier,
    Real.log_div (kN_rate.1 n).ne' (product_pos n).ne']
  apply Real.exp_le_exp.2
  linarith only [hu, hl]

/-- The actual integer readout after division has exactly the reduced multiplier. -/
private theorem reduced_column (n : ℕ) : ∃ w : Fin 2 → ℤ, 1 ≤ n → ∀ i,
    (w i : ℝ) = multiplier n * ((CN n : ℝ) * (readout n i 0 : ℝ)) := by
  by_cases hn : 1 ≤ n
  · obtain ⟨z, hz⟩ := KernelContent.published_column_exists n hn
    obtain ⟨w, hw⟩ := published_column_factor hz
    refine ⟨w, fun _ i => ?_⟩
    have hi := congrArg (fun q : ℚ => (q : ℝ)) (hz i)
    push_cast at hi
    have hsource : (z i : ℝ) = kN n * ((CN n : ℝ) * (readout n i 0 : ℝ)) := by
      rw [← hi, kN]
      push_cast
      ring
    have hfactor : (z i : ℝ) = (translatedProduct n : ℝ) * w i := by exact_mod_cast hw i
    rw [multiplier, div_mul_eq_mul_div, eq_div_iff (product_pos n).ne',
      mul_comm, ← hfactor, hsource]
  · exact ⟨0, fun h => (hn h).elim⟩

/-- The sharpened criterion at ζ(2), using the source's height, error and
three-level independence theorems on the genuinely divided integer pair. -/
theorem zeta2_bound (g : ProductGrowth) : IrrMeasureLE zeta2 exponent := by
  choose W hW using reduced_column
  have hCN : ∀ n, (CN n : ℝ) ≠ 0 := fun n => Nat.cast_ne_zero.2
    (Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
      (Nat.choose_pos (by omega))).ne'
  rw [show exponent = 1 + sigma / tau by norm_num [exponent, sigma, tau, normRate, saving]]
  apply irrMeasure_criterion zeta2 sigma tau (by norm_num [sigma, normRate, saving])
    (by norm_num [tau, normRate, saving]) (fun n => W n 0) (fun n => W n 1)
  · intro ε hε
    filter_upwards [multiplier_rate g (ε/2) (by positivity), readout_rates 0 (ε/2) (by positivity),
      eventually_ge_atTop 1] with n hk hr hn
    rw [hW n hn 1, abs_mul, abs_of_pos (multiplier_pos n)]
    calc multiplier n * |(CN n : ℝ) * (readout n 1 0 : ℝ)|
        ≤ exp ((normRate - saving + ε/2) * n) * exp ((38.168733 + ε/2) * n) :=
          mul_le_mul hk hr.1 (abs_nonneg _) (exp_pos _).le
      _ = exp ((sigma + ε) * n) := by rw [← Real.exp_add]; congr 1; unfold sigma; ring
  · intro ε hε
    filter_upwards [multiplier_rate g (ε/2) (by positivity), readout_rates 0 (ε/2) (by positivity),
      eventually_ge_atTop 1] with n hk hr hn
    have he : (W n 1 : ℝ) * zeta2 - W n 0 = multiplier n * ((CN n : ℝ) * Err n 0) := by
      rw [hW n hn 1, hW n hn 0, Err]; ring
    rw [he, abs_mul, abs_of_pos (multiplier_pos n)]
    calc multiplier n * |(CN n : ℝ) * Err n 0|
        ≤ exp ((normRate - saving + ε/2) * n) * exp ((-24.467842 + ε/2) * n) :=
          mul_le_mul hk hr.2 (abs_nonneg _) (exp_pos _).le
      _ = exp ((-tau + ε) * n) := by rw [← Real.exp_add]; congr 1; unfold tau; ring
  · filter_upwards [bounded_gap, eventually_ge_atTop 1] with n hg hn a b hb
    obtain ⟨i, hi⟩ := hg a b hb
    refine ⟨i, fun h0 => hi ?_⟩
    have hn' : 1 ≤ n + (i : ℕ) := by omega
    have h' : (((b : ℤ) * W (n + i) 0 - a * W (n + i) 1 : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, hW _ hn' 0, hW _ hn' 1] at h'
    have h2 : multiplier (n+i) * (CN (n+i) : ℝ) *
        ((b : ℝ) * (Pread (n+i) 0 : ℝ) - a * (Qread (n+i) 0 : ℝ)) = 0 := by
      push_cast at h'
      linear_combination h'
    have h3 := (mul_eq_zero.1 h2).resolve_left
      (mul_ne_zero (multiplier_pos _).ne' (hCN _))
    exact_mod_cast h3

#print axioms zeta2_bound
#print axioms exponent_lt

end PrimeNumerator.WindowCriterion

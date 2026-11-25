import Rate
import FiniteRate

/-!
# From the arithmetic certificate to the sum of interval widths

For one interval with endpoints `a < b`, period `t` contributes
`1/(t+a) - 1/(t+b)`. Applying the finite telescoping bound to all six
intervals proves that their total over periods 1 through 1,000,000 exceeds
0.10868226. `WindowPNT` uses this strict inequality to bound the prime product.
-/

namespace PrimeNumerator.RateBridge

open Finset

/-- The direct finite sum through period one million for a single interval. -/
def intervalSum (a b : ℚ) : ℚ :=
  ∑ i ∈ range 1000000, (1 / (((i+1 : ℕ) : ℚ) + a) - 1 / (((i+1 : ℕ) : ℚ) + b))

private theorem rising_eq (x : ℚ) (j : ℕ) : Rate.rising x j = FiniteRate.rising x j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Rate.rising, FiniteRate.rising, ih]

private theorem listRange (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range]

theorem intervalLower_le {a b : ℚ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Rate.intervalLower a b ≤ intervalSum a b := by
  unfold Rate.intervalLower intervalSum
  simp only [listRange, rising_eq]
  rw [show (1000000 : ℕ) = 12 + 999988 by rfl, sum_range_add]
  apply add_le_add_right
  have h := FiniteRate.finite_tail_lower ha hab hb (show (0:ℚ) ≤ 13 by decide) 999988 12
  have hcast (i : ℕ) : ((12 + i + 1 : ℕ) : ℚ) = 13 + i := by push_cast; ring
  simp only [hcast]
  rw [show (13 : ℚ) + 1 = 14 by norm_num, show (14 : ℚ) + (999988 : ℕ) = 1000002 by norm_num] at h
  exact h

/-- The six fixed interval sums, one term per period and per interval. -/
def millionRate : ℚ :=
  intervalSum (1/8) (2/13) + intervalSum (2/9) (3/13) +
  intervalSum (3/10) (4/13) + intervalSum (3/8) (5/13) +
  intervalSum (4/9) (6/13) + intervalSum (8/9) (12/13)

theorem lowerRate_le : Rate.lowerRate ≤ millionRate := by
  unfold Rate.lowerRate millionRate
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_) ?_
  all_goals apply intervalLower_le <;> norm_num

/-- The six intervals together contribute strictly more than the saving
used in the irrationality criterion. -/
theorem millionRate_gt : (10868226 : ℚ) / 100000000 < millionRate :=
  Rate.twelve_term_certificate.trans_le lowerRate_le

#print axioms intervalLower_le
#print axioms lowerRate_le
#print axioms millionRate_gt

end PrimeNumerator.RateBridge

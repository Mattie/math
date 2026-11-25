import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Finite rising-factorial lower bounds for sums of reciprocal differences. -/

namespace PrimeNumerator.FiniteRate

open Finset

def rising (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => rising x j * (x + j)

def remainder (a t : ℚ) (j : ℕ) : ℚ :=
  rising (1-a) j / ((t+a) * rising (t+1) j)

private theorem rising_pos {x : ℚ} (hx : 0 < x) (j : ℕ) : 0 < rising x j := by
  induction j with
  | zero => norm_num [rising]
  | succ j h => exact mul_pos h (by positivity)

private theorem rising_mono {x y : ℚ} (hx : 0 < x) (hxy : x ≤ y) (j : ℕ) :
    rising x j ≤ rising y j := by
  induction j with
  | zero => rfl
  | succ j h =>
    exact mul_le_mul h (add_le_add_left hxy _) (by positivity) (rising_pos (hx.trans_le hxy) j).le

/-- Consecutive remainders yield a single term. -/
theorem remainder_step {a t : ℚ} (ha : 0 < a) (ht : 0 ≤ t) (j : ℕ) :
    remainder a t j - remainder a t (j+1) =
      rising (1-a) j / rising (t+1) (j+1) := by
  have hr := (rising_pos (show 0 < t + 1 by linarith) j).ne'
  have hta : t + a ≠ 0 := by positivity
  have htj : t + 1 + j ≠ 0 := by positivity
  simp only [remainder, rising]
  field_simp
  ring

/-- The exact finite expansion, including the last remainder. -/
theorem expansion {a t : ℚ} (ha : 0 < a) (ht : 0 ≤ t) (N : ℕ) :
    1/(t+a) = (∑ j ∈ range N, rising (1-a) j / rising (t+1) (j+1)) + remainder a t N := by
  induction N with
  | zero => simp [remainder, rising]
  | succ j ih =>
    rw [sum_range_succ, ← remainder_step ha ht j]
    linarith

/-- Moving the lower endpoint a to b decreases the remainder. -/
theorem remainder_antitone {a b t : ℚ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (ht : 0 ≤ t) (j : ℕ) : remainder b t j ≤ remainder a t j := by
  have hd := rising_pos (show 0 < t+1 by linarith) j
  apply div_le_div₀ (rising_pos (show 0 < 1-a by linarith) j).le
    (rising_mono (show 0 < 1-b by linarith) (show 1-b ≤ 1-a by linarith) j)
    (mul_pos (show 0 < t+a by linarith) hd)
  exact mul_le_mul_of_nonneg_right (by linarith) hd.le

/-- Dropping the difference of remainders gives the finite lower bound. -/
theorem reciprocal_difference_lower {a b t : ℚ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (ht : 0 ≤ t) (N : ℕ) :
    (∑ j ∈ range N, (rising (1-a) j - rising (1-b) j) / rising (t+1) (j+1)) ≤
      1/(t+a) - 1/(t+b) := by
  simp_rw [sub_div]
  rw [sum_sub_distrib, expansion ha ht N, expansion (ha.trans hab) ht N]
  linarith [remainder_antitone ha hab hb ht N]

private theorem rising_shift (x : ℚ) (j : ℕ) :
    x * rising (x+1) j = rising x (j+1) := by
  induction j with
  | zero => simp [rising]
  | succ j ih =>
    change x * (rising (x+1) j * (x+1+j)) = rising x (j+1) * (x + (j+1 : ℕ))
    rw [← mul_assoc, ih, Nat.cast_succ]
    ring

/-- The t-direction difference used for each nonconstant correction. -/
theorem inverse_step {x : ℚ} (hx : 0 < x) {j : ℕ} (hj : 0 < j) :
    1 / rising x (j+1) = (1 / rising x j - 1 / rising (x+1) j) / j := by
  have hp := (rising_pos hx j).ne'
  have hq := (rising_pos (show 0 < x+1 by linarith) j).ne'
  have hr := (rising_pos hx (j+1)).ne'
  have hj' : (j : ℚ) ≠ 0 := by positivity
  have h1 := rising_shift x j
  have h2 : rising x (j+1) = rising x j * (x + j) := rfl
  field_simp
  linear_combination -(rising (x+1) j) * h2 - (rising x j) * h1

/-- A finite interval starting at x telescopes exactly. -/
theorem inverse_sum {x : ℚ} (hx : 0 < x) {j : ℕ} (hj : 0 < j) (N : ℕ) :
    (∑ i ∈ range N, 1 / rising (x+i) (j+1)) =
      (1 / rising x j - 1 / rising (x+N) j) / j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, inverse_step (show 0 < x + N by positivity) hj, Nat.cast_succ]
    rw [← add_assoc]
    ring

/-- The correction terms j=1,...,J bound N consecutive reciprocal differences
with first period t. Substitution t=m+1 gives the endpoints m+2 and m+N+2. -/
theorem finite_tail_lower {a b t : ℚ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (ht : 0 ≤ t) (N J : ℕ) :
    (∑ j ∈ range J, ((rising (1-a) (j+1) - rising (1-b) (j+1)) / (j+1 : ℕ)) *
      (1 / rising (t+1) (j+1) - 1 / rising (t+1+N) (j+1))) ≤
      ∑ i ∈ range N, (1/(t+i+a) - 1/(t+i+b)) := by
  let term (j i : ℕ) :=
    (rising (1-a) j - rising (1-b) j) / rising (t+i+1) (j+1)
  have hsum (j : ℕ) :
      (∑ i ∈ range N, term (j+1) i) =
        ((rising (1-a) (j+1) - rising (1-b) (j+1)) / (j+1 : ℕ)) *
          (1 / rising (t+1) (j+1) - 1 / rising (t+1+N) (j+1)) := by
    have ht' : 0 < t+1 := by linarith
    have h : ∀ i : ℕ, t + i + 1 = t + 1 + i := fun i => by ring
    simp only [term, div_eq_mul_inv, h, ← Finset.mul_sum]
    have htel := inverse_sum ht' (Nat.zero_lt_succ j) N
    simp only [div_eq_mul_inv, one_mul] at htel
    rw [htel]
    ring
  simp_rw [← hsum]
  rw [sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  have bound := reciprocal_difference_lower ha hab hb (show 0 ≤ t+i by positivity) (J+1)
  rw [sum_range_succ'] at bound
  simpa [term, rising] using bound

#print axioms finite_tail_lower

#print axioms expansion
#print axioms remainder_antitone
#print axioms reciprocal_difference_lower
#print axioms inverse_sum

end PrimeNumerator.FiniteRate

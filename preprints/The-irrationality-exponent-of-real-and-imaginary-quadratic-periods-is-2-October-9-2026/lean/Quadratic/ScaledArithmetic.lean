import Quadratic.PeriodData
import Quadratic.Arithmetic

namespace OAI
noncomputable section
namespace Quadratic.ScaledArithmetic
variable {f : Context}
open scoped BigOperators
open PiExponent PiExponent.InterpolationMatrix Logarithm

def realCenters (slope : ℂ) {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℂ :=
  fun i => (slope * (p i : ℂ)) / (q i : ℂ)

def selectedMinor {m : ℕ} (base : (PeriodData f)) (K : ℕ) (w0 v0 theta F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) :
    Matrix (Row K v0 theta (MatrixArithmetic.logWeights q) H)
      (Row K v0 theta (MatrixArithmetic.logWeights q) H) ℂ :=
  (ScaledMatrix.truncatedLogMatrix K w0 v0 theta (MatrixArithmetic.logWeights q) H
    (fun j => base.value ^ j.val) (realCenters base.slope p q)
    (MatrixArithmetic.truncationOrders q F v0)).submatrix id selection

/-- A column-wide denominator clears every quadratic rational Y-center contribution. -/
def columnScale {m : ℕ} (base : (PeriodData f)) (K : ℕ) (q : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℝ :=
  MatrixArithmetic.columnScale q a * (base.den : ℝ) ^ (K*h)

theorem columnScale_pos {m : ℕ} (base : (PeriodData f)) (K : ℕ) {q : Fin m → ℕ}
    (hq : ∀ i, 0 < q i) (h : ℕ) (a : Fin m → ℕ) :
    0 < columnScale base K q h a :=
  mul_pos (MatrixArithmetic.columnScale_pos hq a)
    (pow_pos (by exact_mod_cast base.den_pos) _)

theorem log_columnScale {m : ℕ} (base : (PeriodData f)) (K : ℕ) {q : Fin m → ℕ}
    (hq : ∀ i, 0 < q i) (h : ℕ) (a : Fin m → ℕ) :
    Real.log (columnScale base K q h a) =
      (∑ i, (a i : ℝ) * Real.log (q i)) + (K : ℝ) * h * Real.log base.den := by
  rw [columnScale, Real.log_mul (MatrixArithmetic.columnScale_pos hq a).ne'
    (pow_ne_zero _ (by exact_mod_cast base.den_pos.ne')), MatrixArithmetic.log_columnScale hq,
    Real.log_pow]
  push_cast
  ring


def columnCost {m K : ℕ} {w0 v0 theta H : ℝ} (base : (PeriodData f)) (q : Fin m → ℕ)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) : ℝ :=
  ∑ row : Row K v0 theta (MatrixArithmetic.logWeights q) H,
    ((∑ i, ((selection row).val i.succ : ℝ) * Real.log (q i)) +
      (K : ℝ) * ((selection row).val 0 : ℝ) * Real.log base.den)


def clearedMinor {m : ℕ} (base : (PeriodData f)) (K : ℕ) (w0 v0 theta F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) :
    Matrix (Row K v0 theta (MatrixArithmetic.logWeights q) H)
      (Row K v0 theta (MatrixArithmetic.logWeights q) H) (RealInt f) := fun row col =>
  base.num ^ (row.1.val * ((selection col).val 0)) *
    (base.den : (RealInt f)) ^ ((K - row.1.val) * ((selection col).val 0)) *
      Arithmetic.clearedEntry (MatrixArithmetic.truncationOrders q F v0) q
        (fun i => ⌊H / MatrixArithmetic.logWeights q i⌋₊) p
        row.1.val (row.2.val 0) ((selection col).val 0)
        (fun i => row.2.val i.succ) (fun i => (selection col).val i.succ)

theorem quadratic_power_cleared (base : (PeriodData f)) (j K h : ℕ) (hj : j ≤ K) :
    (base.den : ℂ) ^ (K * h) * base.value ^ (j * h) =
      RealInt.embedding base.sign base.num ^ (j * h) *
        (base.den : ℂ) ^ ((K-j) * h) := by
  have hB : (base.den : ℂ) ≠ 0 := by exact_mod_cast base.den_pos.ne'
  have hk : K * h = j * h + (K-j) * h := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hj]
  rw [hk, pow_add, PeriodData.value, div_pow]
  field_simp

/-- Evaluating the explicit order matrix gives exactly the selected minor,
with every row and column factor retained. This applies to either sign. -/
theorem map_clearedMinor {m K : ℕ} {w0 v0 theta F H : ℝ}
    (base : (PeriodData f)) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) :
    (clearedMinor base K w0 v0 theta F H p q selection).map
      (RealInt.embedding base.sign) = fun row col =>
      (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H : ℂ) *
        (MatrixArithmetic.rowScale q (fun i => row.2.val i.succ) : ℂ) *
          ((columnScale base K q ((selection col).val 0)
            (fun i => (selection col).val i.succ) : ℂ) *
            selectedMinor base K w0 v0 theta F H p q selection row col) := by
  ext row col
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  simp only [Matrix.map_apply, clearedMinor, map_mul, map_pow, map_natCast]
  rw [Arithmetic.map_clearedEntry base.sign _ _ _ _ (fun i => by have := hq i; omega)
    _ _ _ _ _ (MatrixArithmetic.column_coordinate_le_floor hw0 hw (selection col)),
    ← quadratic_power_cleared base row.1.val K ((selection col).val 0) row.1.isLt.le]
  simp only [MatrixArithmetic.denominator, MatrixArithmetic.rowScale,
    MatrixArithmetic.columnScale, columnScale, selectedMinor, PeriodData.slope,
    ScaledMatrix.truncatedLogMatrix, ScaledMatrix.matrix, Matrix.submatrix_apply, id_eq,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_inv, Complex.ofReal_mul, ← pow_mul]
  rw [show realCenters ((rotation f) base.sign) p q =
    (fun i => (rotation f) base.sign * (p i : ℂ) / (q i : ℂ)) from rfl]
  ring

/-- The sign-flipped evaluation uses this very same cleared matrix and selection. -/
theorem map_clearedMinor_flip {m K : ℕ} {w0 v0 theta F H : ℝ}
    (base : (PeriodData f)) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) :
    (clearedMinor base K w0 v0 theta F H p q selection).map
      (RealInt.embedding (!base.sign)) = fun row col =>
      (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H : ℂ) *
        (MatrixArithmetic.rowScale q (fun i => row.2.val i.succ) : ℂ) *
          ((columnScale base K q ((selection col).val 0)
            (fun i => (selection col).val i.succ) : ℂ) *
            selectedMinor base.flip K w0 v0 theta F H p q selection row col) :=
  map_clearedMinor base.flip p q hq hw0 selection

theorem selectedMinor_clearing_bound {m K : ℕ} {w0 v0 theta F H : ℝ}
    (base : (PeriodData f)) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H)
    (hdet : (selectedMinor base K w0 v0 theta F H p q selection).det ≠ 0) :
    (selectedMinor base.flip K w0 v0 theta F H p q selection).det ≠ 0 ∧
    -(Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) : ℝ) *
      Real.log (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H) -
      columnCost base q selection + MatrixArithmetic.rowCost K v0 theta q H ≤
      (Real.log ‖(selectedMinor base K w0 v0 theta F H p q selection).det‖ +
        Real.log ‖(selectedMinor base.flip K w0 v0 theta F H p q selection).det‖) / 2 := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  obtain ⟨hne, hc⟩ := Arithmetic.cleared_det_pair_bound_with_denominator base.sign
    (selectedMinor base K w0 v0 theta F H p q selection)
    (selectedMinor base.flip K w0 v0 theta F H p q selection)
    (clearedMinor base K w0 v0 theta F H p q selection)
    (fun row => MatrixArithmetic.rowScale q (fun i => row.2.val i.succ))
    (fun col => columnScale base K q ((selection col).val 0) (fun i => (selection col).val i.succ))
    (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H)
    (MatrixArithmetic.denominator_pos _ _ _) (fun row => MatrixArithmetic.rowScale_pos hqpos _)
    (fun col => columnScale_pos base K hqpos _ _) hdet
    (map_clearedMinor base p q hq hw0 selection)
    (map_clearedMinor_flip base p q hq hw0 selection)
  refine ⟨hne, ?_⟩
  simp only [MatrixArithmetic.log_rowScale hqpos, log_columnScale base K hqpos,
    Finset.sum_neg_distrib, sub_neg_eq_add] at hc
  dsimp [columnCost, MatrixArithmetic.rowCost]
  linarith

theorem column_log_cost_le {m K : ℕ} {w0 H : ℝ}
    (base : (PeriodData f)) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (col : Column w0 (MatrixArithmetic.logWeights q) H) :
    (∑ i, (col.val i.succ : ℝ) * Real.log (q i)) +
      (K : ℝ) * (col.val 0 : ℝ) * Real.log base.den ≤
      H * (1 + (K : ℝ) * Real.log base.den / w0) := by
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  have hc := column_weight_le hw0 hw col
  have hs : 0 ≤ ∑ i, MatrixArithmetic.logWeights q i * (col.val i.succ : ℝ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (Nat.cast_nonneg _))
  have hh : (col.val 0 : ℝ) ≤ H / w0 := by
    apply (le_div_iff₀ hw0).mpr
    nlinarith only [hc, hs]
  have hcost := MatrixArithmetic.column_log_cost_le_H q hq hw0 col
  have hbase := mul_le_mul_of_nonneg_left hh
    (mul_nonneg (Nat.cast_nonneg K) (Real.log_natCast_nonneg base.den))
  calc
    _ ≤ H + (K : ℝ) * Real.log base.den * (H / w0) := by
      nlinarith only [hcost, hbase]
    _ = _ := by ring

theorem columnCost_le {m K : ℕ} {w0 v0 theta H : ℝ}
    (base : (PeriodData f)) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) :
    columnCost base q selection ≤
      (Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) : ℝ) * H *
        (1 + (K : ℝ) * Real.log base.den / w0) := by
  unfold columnCost
  calc
    _ ≤ ∑ _row : Row K v0 theta (MatrixArithmetic.logWeights q) H,
        H * (1 + (K : ℝ) * Real.log base.den / w0) :=
      Finset.sum_le_sum (fun row _ => column_log_cost_le base q hq hw0 (selection row))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem normalized_arithmetic_bound_extra
    (M H b E delta gamma logD column row logAbsDet : ℝ)
    (hM : 0 < M) (hH : 0 < H)
    (hclear : -M * logD - column + row ≤ logAbsDet)
    (hden : logD ≤ H * E)
    (hcol : column ≤ M * H * (1+gamma))
    (hrow : M * H * b - M * H * delta ≤ row) :
    -(1-b) - (E + delta + gamma) ≤ logAbsDet / (M*H) := by
  apply (le_div_iff₀ (mul_pos hM hH)).mpr
  have hd := mul_le_mul_of_nonneg_left hden hM.le
  nlinarith only [hclear, hd, hcol, hrow]

/-- The only additional arithmetic penalty is K*log(den(base))/w0. -/
theorem selectedMinor_arithmetic_lower_bound {m K : ℕ} {w0 v0 theta F H wmin : ℝ}
    (base : (PeriodData f)) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H)
    (hdet : (selectedMinor base K w0 v0 theta F H p q selection).det ≠ 0) :
    -(1 - MatrixArithmetic.meanRowWeight K v0 theta q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / MatrixArithmetic.logWeights q i + theta / wmin +
          (K : ℝ) * Real.log base.den / w0) ≤
      ((Real.log ‖(selectedMinor base K w0 v0 theta F H p q selection).det‖ +
        Real.log ‖(selectedMinor base.flip K w0 v0 theta F H p q selection).det‖) / 2) /
        ((Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  have hM : (0 : ℝ) < Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) := by
    exact_mod_cast MatrixArithmetic.actual_row_card_pos hK hv0 htheta hH hw
  apply normalized_arithmetic_bound_extra _ _ _ _ _ _ _ _ _ _ hM hH
  · exact (selectedMinor_clearing_bound base p q hq hw0 selection hdet).2
  · exact MatrixArithmetic.log_denominator_le F v0 H hF hv0 hH hw
  · exact columnCost_le base q hq hw0 selection
  · have hrow (r : Row K v0 theta (MatrixArithmetic.logWeights q) H) :=
      PiExponent.Arithmetic.row_log_cost_lower Finset.univ (fun i => r.2.val i.succ) q
        wmin (H * theta) hmin (fun i _ => hwmin i)
        (MatrixArithmetic.row_weighted_cost_le hv0 htheta hw r)
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hrow r)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hr
    have hb : (Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) : ℝ) * H *
        MatrixArithmetic.meanRowWeight K v0 theta q H =
        MatrixArithmetic.rowWeightedSum K v0 theta q H := by
      unfold MatrixArithmetic.meanRowWeight
      field_simp [(mul_pos hM hH).ne']
    rw [hb]
    simpa only [MatrixArithmetic.rowWeightedSum, MatrixArithmetic.rowCost,
      MatrixArithmetic.logWeights, mul_div_assoc, mul_assoc] using hr

end Quadratic.ScaledArithmetic
end
end OAI

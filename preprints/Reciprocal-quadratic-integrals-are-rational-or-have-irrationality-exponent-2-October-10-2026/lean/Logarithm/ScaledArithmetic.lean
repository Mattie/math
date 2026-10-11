import Logarithm.ScaledMatrix
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

namespace OAI
noncomputable section
namespace Logarithm.ScaledArithmetic
open scoped BigOperators
open PiExponent PiExponent.InterpolationMatrix

theorem integer_center_cast (j : ℕ) (p : ℤ) :
    (((⟨(j : ℤ) * p, 0⟩ : GaussianInt) : ℂ)) =
      (j : ℂ) * (p : ℂ) := by
  simp only [GaussianInt.toComplex_def', Int.cast_zero, Int.cast_mul,
    Int.cast_natCast]
  ring

theorem entry_truncatedLog_cleared_gaussian {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      entry (fun i => (p i : ℂ) / (q i : ℂ))
        (fun i => truncatedLog (T i)) j s β h α ∈ GaussianInt.toComplex.range := by
  classical
  by_cases hβα : ∀ i, β i ≤ α i
  swap
  · rw [entry_eq_zero_of_not_le _ _ _ _ _ _ _ hβα, mul_zero]
    exact GaussianInt.toComplex.range.zero_mem
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) =
      ∏ i, (q i : ℂ) ^ (α i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hβα i)).symm
  let z : Fin m → GaussianInt := fun i => ⟨(j : ℤ) * p i, 0⟩
  have hz (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
        truncatedLog (T i)) =
      Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
        PowerSeries.trunc (T i) (PowerSeries.log ℂ) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    rw [show (z i : ℂ) = (j : ℂ) * ((p i : ℂ)) from
      integer_center_cast j (p i)]
    field_simp [hqC i]
  have hclear := Arithmetic.shifted_truncation_product_coeff_gaussian Finset.univ
    T q e (fun i => α i - β i) z ((1 + Polynomial.X) ^ h)
    (fun i hi => (Nat.sub_le (α i) (β i)).trans (hα i)) s
  have hP : (((1 + Polynomial.X) ^ h : Polynomial GaussianInt).map GaussianInt.toComplex) =
      (1 + Polynomial.X) ^ h := by simp
  simp only [hP] at hclear
  have hchoose : (∏ i, ((α i).choose (β i) : ℂ)) ∈ GaussianInt.toComplex.range := by
    apply GaussianInt.toComplex.range.prod_mem
    intro i hi
    exact ⟨((α i).choose (β i) : GaussianInt), by simp⟩
  have hscalar := scalar_product_mul_coeff (fun i => (q i : ℂ)) (fun i => α i - β i)
    ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
      truncatedLog (T i)) s
  simp_rw [hz] at hscalar
  rw [mul_div_assoc, hratio, entry_eq_binomial_product]
  have he := GaussianInt.toComplex.range.mul_mem hchoose hclear
  rw [← hscalar] at he
  convert he using 1
  ring

theorem rational_power_cleared (base : ℚ) (j K h : ℕ) (hj : j ≤ K) :
    (base.den : ℂ) ^ (K * h) * (base : ℂ) ^ (j * h) =
      (base.num : ℂ) ^ (j * h) * (base.den : ℂ) ^ ((K-j) * h) := by
  have hB : (base.den : ℂ) ≠ 0 := by exact_mod_cast base.pos.ne'
  have hk : K * h = j * h + (K-j) * h := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hj]
  rw [hk, pow_add, Rat.cast_def, div_pow]
  field_simp

theorem rational_power_cleared_gaussian (base : ℚ) (j K h : ℕ) (hj : j ≤ K) :
    (base.den : ℂ) ^ (K * h) * (base : ℂ) ^ (j * h) ∈ GaussianInt.toComplex.range := by
  rw [rational_power_cleared base j K h hj]
  exact ⟨(base.num : GaussianInt) ^ (j * h) * (base.den : GaussianInt) ^ ((K-j)*h), by simp⟩

def rationalCenters {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℂ :=
  fun i => (p i : ℂ) / (q i : ℂ)

def selectedMinor {m : ℕ} (base : ℚ) (K : ℕ) (w0 v0 theta F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) :
    Matrix (Row K v0 theta (MatrixArithmetic.logWeights q) H)
      (Row K v0 theta (MatrixArithmetic.logWeights q) H) ℂ :=
  (ScaledMatrix.truncatedLogMatrix K w0 v0 theta (MatrixArithmetic.logWeights q) H
    (fun j => (base : ℂ) ^ j.val) (rationalCenters p q)
    (MatrixArithmetic.truncationOrders q F v0)).submatrix id selection

/-- A column-wide denominator clears every rational Y-center contribution. -/
def columnScale {m : ℕ} (base : ℚ) (K : ℕ) (q : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℝ :=
  MatrixArithmetic.columnScale q a * (base.den : ℝ) ^ (K*h)

theorem columnScale_pos {m : ℕ} (base : ℚ) (K : ℕ) {q : Fin m → ℕ}
    (hq : ∀ i, 0 < q i) (h : ℕ) (a : Fin m → ℕ) :
    0 < columnScale base K q h a :=
  mul_pos (MatrixArithmetic.columnScale_pos hq a)
    (pow_pos (by exact_mod_cast base.pos) _)

theorem log_columnScale {m : ℕ} (base : ℚ) (K : ℕ) {q : Fin m → ℕ}
    (hq : ∀ i, 0 < q i) (h : ℕ) (a : Fin m → ℕ) :
    Real.log (columnScale base K q h a) =
      (∑ i, (a i : ℝ) * Real.log (q i)) + (K : ℝ) * h * Real.log base.den := by
  rw [columnScale, Real.log_mul (MatrixArithmetic.columnScale_pos hq a).ne'
    (pow_ne_zero _ (by exact_mod_cast base.pos.ne')), MatrixArithmetic.log_columnScale hq,
    Real.log_pow]
  push_cast
  ring

theorem selectedMinor_entries_gaussian {m K : ℕ} {w0 v0 theta F H : ℝ}
    (base : ℚ) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H)
    (row col : Row K v0 theta (MatrixArithmetic.logWeights q) H) :
    (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H : ℂ) *
      (MatrixArithmetic.rowScale q (fun i => row.2.val i.succ) : ℂ) *
        ((columnScale base K q ((selection col).val 0) (fun i => (selection col).val i.succ) : ℂ) *
          selectedMinor base K w0 v0 theta F H p q selection row col) ∈
        GaussianInt.toComplex.range := by
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  have he := entry_truncatedLog_cleared_gaussian
    (MatrixArithmetic.truncationOrders q F v0) q
    (fun i => ⌊H / MatrixArithmetic.logWeights q i⌋₊) p
    (fun i => by have := hq i; omega) row.1.val (row.2.val 0) ((selection col).val 0)
    (fun i => row.2.val i.succ) (fun i => (selection col).val i.succ)
    (MatrixArithmetic.column_coordinate_le_floor hw0 hw (selection col))
  have hb := rational_power_cleared_gaussian base row.1.val K ((selection col).val 0)
    row.1.isLt.le
  have hm := GaussianInt.toComplex.range.mul_mem hb he
  have hcenters : rationalCenters p q = (fun i => (p i : ℂ) / (q i : ℂ)) := rfl
  simp only [MatrixArithmetic.denominator, MatrixArithmetic.rowScale,
    MatrixArithmetic.columnScale, columnScale, selectedMinor,
    ScaledMatrix.truncatedLogMatrix, ScaledMatrix.matrix,
    Matrix.submatrix_apply, id_eq,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_inv, Complex.ofReal_mul, ← pow_mul]
  rw [hcenters]
  convert hm using 1
  ring

def columnCost {m K : ℕ} {w0 v0 theta H : ℝ} (base : ℚ) (q : Fin m → ℕ)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H) : ℝ :=
  ∑ row : Row K v0 theta (MatrixArithmetic.logWeights q) H,
    ((∑ i, ((selection row).val i.succ : ℝ) * Real.log (q i)) +
      (K : ℝ) * ((selection row).val 0 : ℝ) * Real.log base.den)

theorem selectedMinor_clearing_bound {m K : ℕ} {w0 v0 theta F H : ℝ}
    (base : ℚ) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : Row K v0 theta (MatrixArithmetic.logWeights q) H →
      Column w0 (MatrixArithmetic.logWeights q) H)
    (hdet : (selectedMinor base K w0 v0 theta F H p q selection).det ≠ 0) :
    -(Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) : ℝ) *
      Real.log (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H) -
      columnCost base q selection + MatrixArithmetic.rowCost K v0 theta q H ≤
      Real.log ‖(selectedMinor base K w0 v0 theta F H p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hc := Arithmetic.cleared_det_log_bound_with_denominator
    (selectedMinor base K w0 v0 theta F H p q selection)
    (fun row => MatrixArithmetic.rowScale q (fun i => row.2.val i.succ))
    (fun col => columnScale base K q ((selection col).val 0) (fun i => (selection col).val i.succ))
    (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H)
    (MatrixArithmetic.denominator_pos _ _ _) (fun row => MatrixArithmetic.rowScale_pos hqpos _)
    (fun col => columnScale_pos base K hqpos _ _) hdet
    (selectedMinor_entries_gaussian base p q hq hw0 selection)
  simp only [MatrixArithmetic.log_rowScale hqpos, log_columnScale base K hqpos,
    Finset.sum_neg_distrib, sub_neg_eq_add] at hc
  dsimp [columnCost, MatrixArithmetic.rowCost]
  linarith

theorem column_log_cost_le {m K : ℕ} {w0 H : ℝ}
    (base : ℚ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
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
    (base : ℚ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
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
    (base : ℚ) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
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
      Real.log ‖(selectedMinor base K w0 v0 theta F H p q selection).det‖ /
        ((Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  have hM : (0 : ℝ) < Fintype.card (Row K v0 theta (MatrixArithmetic.logWeights q) H) := by
    exact_mod_cast MatrixArithmetic.actual_row_card_pos hK hv0 htheta hH hw
  apply normalized_arithmetic_bound_extra _ _ _ _ _ _ _ _ _ _ hM hH
  · exact selectedMinor_clearing_bound base p q hq hw0 selection hdet
  · exact MatrixArithmetic.log_denominator_le F v0 H hF hv0 hH hw
  · exact columnCost_le base q hq hw0 selection
  · have hrow (r : Row K v0 theta (MatrixArithmetic.logWeights q) H) :=
      Arithmetic.row_log_cost_lower Finset.univ (fun i => r.2.val i.succ) q
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

end Logarithm.ScaledArithmetic
end
end OAI

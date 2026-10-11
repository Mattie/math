import Positive
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Real intervalIntegral Set
namespace OAI.PositiveIntegrals

/-- Cross-ratio of the two real roots, expressed without dividing by the leading coefficient. -/
def crossRatio (A B C a b : ℝ) : ℝ :=
  ((2*A*b+B-sqrt (B^2-4*A*C))*(2*A*a+B+sqrt (B^2-4*A*C))) /
  ((2*A*b+B+sqrt (B^2-4*A*C))*(2*A*a+B-sqrt (B^2-4*A*C)))

private theorem ratio_pos_of_nonzero (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hn : ∀ x ∈ Icc a b, f x ≠ 0) :
    0 < f b / f a := by
  have ha := hn a (left_mem_Icc.mpr hab)
  have hb := hn b (right_mem_Icc.mpr hab)
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hb' : f b < 0 := by
      by_contra h
      have hz := intermediate_value_Icc hab hc ⟨ha.le, le_of_not_gt h⟩
      obtain ⟨x, hx, he⟩ := hz
      exact hn x hx he
    exact div_pos_of_neg_of_neg hb' ha
  · have hb' : 0 < f b := by
      by_contra h
      have hz := intermediate_value_Icc' hab hc ⟨le_of_not_gt h, ha.le⟩
      obtain ⟨x, hx, he⟩ := hz
      exact hn x hx he
    exact div_pos hb' ha

/-- The cross-ratio is positive and nontrivial, and gives the actual interval integral. -/
theorem crossRatio_spec (A B C a b : ℝ) (hA : A ≠ 0)
    (hΔ : 0 < B^2-4*A*C) (hab : a < b)
    (hQ : ∀ x ∈ Icc a b, A*x^2+B*x+C ≠ 0) :
    0 < crossRatio A B C a b ∧ crossRatio A B C a b ≠ 1 ∧
    (∫ x in a..b, 1/(A*x^2+B*x+C)) =
      log (crossRatio A B C a b) / sqrt (B^2-4*A*C) := by
  let s := sqrt (B^2-4*A*C)
  have hs : 0 < s := sqrt_pos.mpr hΔ
  have hs2 : s^2 = B^2-4*A*C := sq_sqrt hΔ.le
  have hpm (x : ℝ) (hx : x ∈ Icc a b) :
      2*A*x+B-s ≠ 0 ∧ 2*A*x+B+s ≠ 0 := by
    have hid : (2*A*x+B-s)*(2*A*x+B+s) = 4*A*(A*x^2+B*x+C) := by
      linear_combination -hs2
    have hn := mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hA) (hQ x hx)
    rw [← hid] at hn
    exact mul_ne_zero_iff.mp hn
  obtain ⟨ham, hap⟩ := hpm a (left_mem_Icc.mpr hab.le)
  obtain ⟨hbm, hbp⟩ := hpm b (right_mem_Icc.mpr hab.le)
  have hm : 0 < (2*A*b+B-s)/(2*A*a+B-s) :=
    ratio_pos_of_nonzero (fun x => 2*A*x+B-s) hab.le (by fun_prop)
      (fun x hx => (hpm x hx).1)
  have hp : 0 < (2*A*b+B+s)/(2*A*a+B+s) :=
    ratio_pos_of_nonzero (fun x => 2*A*x+B+s) hab.le (by fun_prop)
      (fun x hx => (hpm x hx).2)
  have hpos : 0 < crossRatio A B C a b := by
    have he : crossRatio A B C a b =
        ((2*A*b+B-s)/(2*A*a+B-s))/((2*A*b+B+s)/(2*A*a+B+s)) := by
      change ((2*A*b+B-s)*(2*A*a+B+s)) / ((2*A*b+B+s)*(2*A*a+B-s)) = _
      field_simp [ham, hap, hbp]
    rw [he]
    exact div_pos hm hp
  refine ⟨hpos, ?_, ?_⟩
  · intro he
    change ((2*A*b+B-s)*(2*A*a+B+s)) /
      ((2*A*b+B+s)*(2*A*a+B-s)) = 1 at he
    have he' := (div_eq_one_iff_eq (mul_ne_zero hbp ham)).mp he
    have hz : 4*A*s*(b-a) = 0 := by linear_combination he'
    have : 4*A*s*(b-a) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) hs.ne') (sub_pos.mpr hab).ne'
    exact this hz
  · rw [OAI.Integrals.positive_evaluation A B C a b hA hΔ hab.le hQ]
    change _ = log (((2*A*b+B-s)*(2*A*a+B+s)) /
      ((2*A*b+B+s)*(2*A*a+B-s))) / s
    rw [log_div (mul_ne_zero hbm hap) (mul_ne_zero hbp ham),
      log_mul hbm hap, log_mul hbp ham]
    dsimp [s]
    ring

#print axioms crossRatio_spec
end OAI.PositiveIntegrals

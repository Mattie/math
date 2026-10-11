import PairedAffine.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace OAI.PairedAffine.Concrete
noncomputable section
open OAI.PairedAffine.Field

def realBase : ℝ := 3 + 2 * Real.sqrt 2
def target : ℝ := Real.log realBase / Real.sqrt 2 + Real.sqrt 3

theorem realBase_gt_one : 1 < realBase := by
  dsimp [realBase]
  linarith [Real.sqrt_nonneg (2 : ℝ)]

theorem target_pos : 0 < target := by
  have hlog := Real.log_pos realBase_gt_one
  dsimp [target]
  positivity

theorem scaled_target : Real.sqrt 2 * (target - Real.sqrt 3) = Real.log realBase := by
  have h : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  dsimp [target]
  field_simp
  ring

theorem reciprocal : realBase⁻¹ = 3 - 2 * Real.sqrt 2 := by
  have hb : realBase ≠ 0 := ne_of_gt (lt_trans zero_lt_one realBase_gt_one)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  dsimp [realBase]
  nlinarith

theorem omega_eq (e : Bool) :
    sigma e true sqrtTwo * ((target : ℂ) - sigma e true sqrtThree) =
      if e then (Real.log realBase : ℂ) else -(Real.log realBase : ℂ) := by
  have h : (Real.sqrt 2 : ℂ) * ((target : ℂ) - (Real.sqrt 3 : ℂ)) =
      (Real.log realBase : ℂ) := by exact_mod_cast scaled_target
  cases e <;> simp only [sigma_sqrtTwo, sigma_sqrtThree, signedRoot,
    Bool.false_eq_true, ↓reduceIte, neg_mul, h]

theorem compatible (e : Bool) :
    Complex.exp (sigma e true sqrtTwo * ((target : ℂ) - sigma e true sqrtThree)) =
      sigma e true base := by
  have he : Complex.exp (Real.log realBase : ℂ) = (realBase : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (lt_trans zero_lt_one realBase_gt_one)]
  rw [omega_eq]
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte, Complex.exp_neg, he, sigma_base,
      signedRoot]
    have hr : (realBase : ℂ)⁻¹ = 3 - 2 * (Real.sqrt 2 : ℂ) := by
      exact_mod_cast reciprocal
    rw [hr]
    ring
  · simpa [he, signedRoot, realBase] using he

theorem scale_norm_le (e : Bool) : ‖sigma e true sqrtTwo‖ ≤ 2 := by
  cases e <;> simp [signedRoot, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))]

theorem embeddings_distinct : sigma true true ≠ sigma false true := by
  intro h
  have hval := congrArg (fun f : F →ₐ[ℚ] ℂ => f sqrtTwo) h
  simp only [sigma_sqrtTwo, signedRoot, Bool.false_eq_true, ↓reduceIte] at hval
  have hr := congrArg Complex.re hval
  simp at hr
  have hp := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  linarith

def good : Finset (F →ₐ[ℚ] ℂ) := by
  classical
  exact {sigma true true, sigma false true}

theorem good_card : good.card = 2 := by
  classical
  simp [good, embeddings_distinct]

end
end OAI.PairedAffine.Concrete

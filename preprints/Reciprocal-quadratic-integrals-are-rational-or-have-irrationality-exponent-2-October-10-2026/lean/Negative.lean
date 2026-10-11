import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
noncomputable section
open Real intervalIntegral
namespace OAI.Integrals

theorem quadratic_no_zero (A B C : ℝ) (h : 0 < 4*A*C-B^2) (x : ℝ) :
    A*x^2+B*x+C ≠ 0 := by
  intro hz
  have hs := sq_nonneg (2*A*x+B)
  have hid : (2*A*x+B)^2 + (4*A*C-B^2) = 4*A*(A*x^2+B*x+C) := by ring
  rw [hz] at hid
  nlinarith

theorem negative_evaluation (A B C a b : ℝ) (hA : A ≠ 0)
    (hr : 0 < 4*A*C-B^2) :
    (∫ x in a..b, 1/(A*x^2+B*x+C)) =
      2 / sqrt (4*A*C-B^2) *
       (arctan ((2*A*b+B)/sqrt (4*A*C-B^2)) -
        arctan ((2*A*a+B)/sqrt (4*A*C-B^2))) := by
  let k := sqrt (4*A*C-B^2)
  have hk : k ≠ 0 := (sqrt_pos.mpr hr).ne'
  have hk2 : k^2 = 4*A*C-B^2 := sq_sqrt hr.le
  have hd (x : ℝ) : HasDerivAt
      (fun t => 2/k * arctan ((2*A*t+B)/k)) (1/(A*x^2+B*x+C)) x := by
    have hh := ((((hasDerivAt_id x).const_mul (2*A)).add_const B).div_const k).arctan
    have hh := hh.const_mul (2/k)
    simp only [id_eq] at hh
    convert hh using 1
    have hq := quadratic_no_zero A B C hr x
    have hp : 1+((2*A*x+B)/k)^2 ≠ 0 := by positivity
    field_simp [hk, hq, hp]
    rw [hk2]
    ring_nf
    field_simp [show A*x^2+C+B*x ≠ 0 by convert hq using 1 <;> ring]
    convert mul_inv_cancel₀ hq using 1 <;> ring
  have hc : Continuous (fun x : ℝ => 1/(A*x^2+B*x+C)) :=
    continuous_const.div (by fun_prop) (quadratic_no_zero A B C hr)
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable a b)]
  dsimp [k]
  ring

#print axioms quadratic_no_zero
#print axioms negative_evaluation
end OAI.Integrals

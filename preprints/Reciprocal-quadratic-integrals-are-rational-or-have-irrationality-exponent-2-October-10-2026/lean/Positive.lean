import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
noncomputable section
open Real intervalIntegral Set
namespace OAI.Integrals

theorem positive_evaluation (A B C a b : ℝ) (hA : A ≠ 0)
    (hr : 0 < B^2-4*A*C) (hab : a ≤ b)
    (hp : ∀ x ∈ Icc a b, A*x^2+B*x+C ≠ 0) :
    (∫ x in a..b, 1/(A*x^2+B*x+C)) =
      ((log (2*A*b+B-sqrt (B^2-4*A*C)) - log (2*A*b+B+sqrt (B^2-4*A*C))) -
       (log (2*A*a+B-sqrt (B^2-4*A*C)) - log (2*A*a+B+sqrt (B^2-4*A*C)))) /
      sqrt (B^2-4*A*C) := by
  let k := sqrt (B^2-4*A*C)
  have hk : k ≠ 0 := (sqrt_pos.mpr hr).ne'
  have hk2 : k^2 = B^2-4*A*C := sq_sqrt hr.le
  have hpm (x : ℝ) (hx : x ∈ Icc a b) :
      2*A*x+B-k ≠ 0 ∧ 2*A*x+B+k ≠ 0 := by
    have hid : (2*A*x+B-k)*(2*A*x+B+k) = 4*A*(A*x^2+B*x+C) := by
      linear_combination -hk2
    have hn := mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hA) (hp x hx)
    rw [← hid] at hn
    exact mul_ne_zero_iff.mp hn
  have hd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt
      (fun t => (log (2*A*t+B-k)-log (2*A*t+B+k))/k)
      (1/(A*x^2+B*x+C)) x := by
    obtain ⟨hm,hp'⟩ := hpm x hx
    have hbase := ((hasDerivAt_id x).const_mul (2*A)).add_const B
    have hh := (((hbase.sub_const k).log hm).sub ((hbase.add_const k).log hp')).div_const k
    simp only [id_eq] at hh
    convert hh using 1
    have hq := hp x hx
    have hq' : x*B+x^2*A+C ≠ 0 := by convert hq using 1 <;> ring
    have hm' : -k+x*A*2+B ≠ 0 := by convert hm using 1 <;> ring
    have hp'' : k+x*A*2+B ≠ 0 := by convert hp' using 1 <;> ring
    field_simp [hk, hq, hm, hp', hq', hm', hp'']
    ring_nf
    field_simp [hk, hq, hm, hp', hq', hm', hp'']
    have hcancel := mul_inv_cancel₀ hq
    linear_combination -(k/(A*x^2+B*x+C))*hk2 + 4*A*k*hcancel
  have hc : ContinuousOn (fun x : ℝ => 1/(A*x^2+B*x+C)) (Icc a b) :=
    continuousOn_const.div (by fun_prop) hp
  rw [integral_eq_sub_of_hasDerivAt (fun x hx => hd x (by simpa [uIcc_of_le hab] using hx))
      (hc.intervalIntegrable_of_Icc hab)]
  dsimp [k]
  ring

#print axioms positive_evaluation
end OAI.Integrals

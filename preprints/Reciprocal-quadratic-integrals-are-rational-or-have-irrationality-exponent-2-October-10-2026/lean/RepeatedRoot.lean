import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Real intervalIntegral Set
namespace OAI.IntegralClassification

/-- A repeated-root quadratic has a rational antiderivative on any pole-free interval. -/
theorem repeated_root_evaluation_real (A B C a b : ℝ) (hA : A ≠ 0)
    (hD : B^2-4*A*C=0) (hab : a ≤ b)
    (hp : ∀ x ∈ Icc a b, A*x^2+B*x+C ≠ 0) :
    (∫ x in a..b, 1/(A*x^2+B*x+C)) =
      2/(2*A*a+B)-2/(2*A*b+B) := by
  have hident (x : ℝ) : (2*A*x+B)^2 = 4*A*(A*x^2+B*x+C) := by
    nlinarith only [hD]
  have hu (x : ℝ) (hx : x ∈ Icc a b) : 2*A*x+B ≠ 0 := by
    intro hz
    have hn := mul_ne_zero (mul_ne_zero (by norm_num : (4:ℝ)≠0) hA) (hp x hx)
    apply hn
    rw [← hident x, hz]
    norm_num
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun t => -2/(2*A*t+B)) (1/(A*x^2+B*x+C)) x := by
    have hbase := ((hasDerivAt_id x).const_mul (2*A)).add_const B
    have hh := (hasDerivAt_const x (-2:ℝ)).div hbase (hu x hx)
    simp only [id_eq] at hh
    have hfrac : (0*(2*A*x+B)- -2*(2*A*1))/(2*A*x+B)^2 =
        1/(A*x^2+B*x+C) := by
      apply (div_eq_div_iff (pow_ne_zero 2 (hu x hx)) (hp x hx)).mpr
      nlinarith only [hident x]
    rw [hfrac] at hh
    exact hh
  have hc : ContinuousOn (fun x : ℝ => 1/(A*x^2+B*x+C)) (Icc a b) :=
    continuousOn_const.div (by fun_prop) hp
  rw [integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa [uIcc_of_le hab] using hx))
    (hc.intervalIntegrable_of_Icc hab)]
  ring

/-- With rational input, the repeated-root evaluation is a rational number. -/
theorem repeated_root_rational (A B C a b : ℚ) (hA : A ≠ 0)
    (hD : B^2-4*A*C=0) (hab : a < b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ) ≠ 0) :
    ∃ r : ℚ, (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) = (r:ℝ) := by
  refine ⟨2/(2*A*a+B)-2/(2*A*b+B), ?_⟩
  have hA' : (A:ℝ)≠0 := by exact_mod_cast hA
  have hD' : (B:ℝ)^2-4*(A:ℝ)*(C:ℝ)=0 := by exact_mod_cast hD
  have hab' : (a:ℝ)≤b := by exact_mod_cast hab.le
  simpa using repeated_root_evaluation_real (A:ℝ) B C a b hA' hD' hab' hp

end OAI.IntegralClassification

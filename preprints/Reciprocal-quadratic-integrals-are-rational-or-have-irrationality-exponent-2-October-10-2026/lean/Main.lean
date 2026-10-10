import Negative
import Coefficients
import Combined
noncomputable section
open Real intervalIntegral
namespace OAI.Integrals

theorem negative_integral_ne_zero (A B C a b : ℝ) (hA : A ≠ 0)
    (hr : 0 < 4*A*C-B^2) (hab : a < b) :
    (∫ x in a..b, 1/(A*x^2+B*x+C)) ≠ 0 := by
  rw [negative_evaluation A B C a b hA hr]
  apply mul_ne_zero (div_ne_zero (by norm_num) (sqrt_pos.mpr hr).ne')
  rw [sub_ne_zero, ne_eq, arctan_inj]
  intro h
  have he := (div_left_inj' (sqrt_pos.mpr hr).ne').mp h
  have : 2*A*(b-a)=0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hA ((mul_eq_zero.mp h).resolve_left (by norm_num))
  · linarith

theorem negative_discriminant_bound (A B C a b : ℚ)
    (hA : A ≠ 0) (hr : 0 < 4*A*C-B^2) (hab : a < b) :
    OAI.PiExponent.EventualLowerBound
      (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) := by
  let r : ℚ := 4*A*C-B^2
  let v : ℚ := 2*A*b+B
  let u : ℚ := 2*A*a+B
  let Ival : ℝ := ∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hA' : (A:ℝ) ≠ 0 := by exact_mod_cast hA
  have hdisc : 0 < 4*(A:ℝ)*(C:ℝ)-(B:ℝ)^2 := by exact_mod_cast hr
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  have hI : Ival ≠ 0 := negative_integral_ne_zero _ _ _ _ _ hA' hdisc hab'
  have hev : Ival = 2/sqrt (r:ℝ)*(arctan ((v:ℝ)/sqrt (r:ℝ))-
      arctan ((u:ℝ)/sqrt (r:ℝ))) := by
    simpa [Ival,r,v,u] using negative_evaluation (A:ℝ) (B:ℝ) (C:ℝ) a b hA' hdisc
  let P := ratCos r v*ratCos r u+r*ratSin r v*ratSin r u
  let S := ratSin r v*ratCos r u-ratCos r v*ratSin r u
  let d := OAI.PeriodicFamily.rationalRadicand r
  have hn : (r.den:ℂ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hk : (sqrt (r:ℝ):ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos.mpr hrR).ne'
  have hsq : (sqrt d:ℂ) = (r.den:ℂ)*(sqrt (r:ℝ):ℂ) := by
    exact_mod_cast OAI.PeriodicFamily.rationalRadicand_sqrt r hr
  have hbase : Complex.exp ((Complex.I*(sqrt (r:ℝ):ℂ))*(Ival:ℂ)) =
      (P:ℂ)+(S:ℂ)*(Complex.I*(sqrt (r:ℝ):ℂ)) := by
    rw [hev]
    have halg : Complex.I*(sqrt (r:ℝ):ℂ)*
        ((2/sqrt (r:ℝ)*(arctan ((v:ℝ)/sqrt (r:ℝ))-
        arctan ((u:ℝ)/sqrt (r:ℝ))):ℝ):ℂ) =
        Complex.I*((2*(arctan ((v:ℝ)/sqrt (r:ℝ))-
        arctan ((u:ℝ)/sqrt (r:ℝ))):ℝ):ℂ) := by
      push_cast
      field_simp
    rw [halg]
    exact exp_angle_difference r v u hr
  obtain ⟨U,V,hpow⟩ := rational_rotation_power d P (S/(r.den:ℚ)) r.den
  apply OAI.Applications.imaginary_quadratic_all_eventualLowerBound d
    (OAI.PeriodicFamily.rationalRadicand_pos r hr) Ival hI U V
  have hz : Complex.I*(sqrt d:ℂ)*(Ival:ℂ) =
      (r.den:ℂ)*((Complex.I*(sqrt (r:ℝ):ℂ))*(Ival:ℂ)) := by rw [hsq]; ring
  rw [hz, Complex.exp_nat_mul, hbase]
  convert hpow using 1
  rw [hsq]
  push_cast
  field_simp

theorem negative_discriminant_exponent (A B C a b : ℚ)
    (hA : A ≠ 0) (hr : 0 < 4*A*C-B^2) (hab : a < b) :
    OAI.PiExponent.irrationalityExponent
      (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) = 2 :=
  OAI.LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (negative_discriminant_bound A B C a b hA hr hab)

#print axioms negative_integral_ne_zero
#print axioms negative_discriminant_bound
#print axioms negative_discriminant_exponent
end OAI.Integrals

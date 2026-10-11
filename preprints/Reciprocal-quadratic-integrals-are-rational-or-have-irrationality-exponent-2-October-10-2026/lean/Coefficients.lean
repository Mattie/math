import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
noncomputable section
open Real intervalIntegral
namespace OAI.Integrals

theorem cos_two_arctan (x : ℝ) :
    cos (2*arctan x) = (1-x^2)/(1+x^2) := by
  rw [cos_two_mul, cos_sq_arctan]
  have hd : 1+x^2 ≠ 0 := by positivity
  field_simp
  ring

theorem sin_two_arctan (x : ℝ) :
    sin (2*arctan x) = 2*x/(1+x^2) := by
  have ht := tan_arctan x
  rw [tan_eq_sin_div_cos] at ht
  have hs := (div_eq_iff (cos_arctan_pos x).ne').mp ht
  calc
    _ = 2*x*cos (arctan x)^2 := by rw [sin_two_mul, hs]; ring
    _ = _ := by rw [cos_sq_arctan]; ring

theorem arctan_coefficients (r u : ℝ) (hr : 0 < r) :
    cos (2*arctan (u/sqrt r)) = (r-u^2)/(r+u^2) ∧
    sin (2*arctan (u/sqrt r)) = (2*u/(r+u^2))*sqrt r := by
  have hk : sqrt r ≠ 0 := (sqrt_pos.mpr hr).ne'
  have hk2 := sq_sqrt hr.le
  have hd : r+u^2 ≠ 0 := by positivity
  have hp : 1+(u/sqrt r)^2 ≠ 0 := by positivity
  rw [cos_two_arctan, sin_two_arctan]
  constructor <;> field_simp <;> rw [hk2] <;> ring

def ratCos (r u : ℚ) : ℚ := (r-u^2)/(r+u^2)
def ratSin (r u : ℚ) : ℚ := 2*u/(r+u^2)

theorem exp_angle_difference (r v u : ℚ) (hr : 0 < r) :
    Complex.exp (Complex.I * ((2*(arctan ((v:ℝ)/sqrt (r:ℝ)) -
      arctan ((u:ℝ)/sqrt (r:ℝ))) : ℝ) : ℂ)) =
      ((ratCos r v * ratCos r u + r*ratSin r v*ratSin r u : ℚ) : ℂ) +
      ((ratSin r v*ratCos r u-ratCos r v*ratSin r u : ℚ) : ℂ) *
        (Complex.I * (sqrt (r:ℝ) : ℂ)) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  obtain ⟨hvc, hvs⟩ := arctan_coefficients (r:ℝ) (v:ℝ) hrR
  obtain ⟨huc, hus⟩ := arctan_coefficients (r:ℝ) (u:ℝ) hrR
  have hk2 := sq_sqrt hrR.le
  have hc : cos (2*(arctan ((v:ℝ)/sqrt (r:ℝ)) - arctan ((u:ℝ)/sqrt (r:ℝ)))) =
      ((ratCos r v*ratCos r u+r*ratSin r v*ratSin r u : ℚ):ℝ) := by
    rw [mul_sub, cos_sub, hvc, hvs, huc, hus]
    simp only [ratCos,ratSin]
    push_cast
    linear_combination (2*(v:ℝ)/((r:ℝ)+(v:ℝ)^2))*(2*(u:ℝ)/((r:ℝ)+(u:ℝ)^2))*hk2
  have hs : sin (2*(arctan ((v:ℝ)/sqrt (r:ℝ)) - arctan ((u:ℝ)/sqrt (r:ℝ)))) =
      ((ratSin r v*ratCos r u-ratCos r v*ratSin r u : ℚ):ℝ)*sqrt (r:ℝ) := by
    rw [mul_sub, sin_sub, hvc, hvs, huc, hus]
    simp only [ratCos,ratSin]
    push_cast
    ring
  rw [mul_comm Complex.I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  push_cast
  ring
theorem rational_rotation_power (d : ℕ) (P S : ℚ) (n : ℕ) :
    ∃ U V : ℚ, ((P:ℂ)+(S:ℂ)*(Complex.I*(sqrt d:ℂ)))^n =
      (U:ℂ)+(V:ℂ)*(Complex.I*(sqrt d:ℂ)) := by
  have hrot : (Complex.I*(sqrt d:ℂ))^2 = -(d:ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, sq_sqrt (Nat.cast_nonneg d)]
    simp
  induction n with
  | zero => exact ⟨1,0,by simp⟩
  | succ n ih =>
    obtain ⟨U,V,h⟩ := ih
    refine ⟨U*P-V*S*d, U*S+V*P, ?_⟩
    rw [pow_succ, h]
    push_cast
    linear_combination (V:ℂ)*(S:ℂ)*hrot

end OAI.Integrals

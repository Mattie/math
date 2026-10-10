import PositiveLogBridge
import PositiveNormCoefficients
import Main
noncomputable section
open Real intervalIntegral Set OAI.PiExponent
namespace OAI.Integrals

/-- Every pole-free rational quadratic with positive discriminant has the explicit bound. -/
theorem positive_discriminant_bound (A B C a b : ℚ) (hA : A≠0)
    (hD : 0<B^2-4*A*C) (hab : a<b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)≠0) :
    EventualLowerBound
      (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) := by
  let r : ℚ := B^2-4*A*C
  let u : ℚ := 2*A*a+B
  let v : ℚ := 2*A*b+B
  have hr : 0<r := hD
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have habR : (a:ℝ)<b := by exact_mod_cast hab
  have hqa : A*a^2+B*a+C≠0 := by
    exact_mod_cast hp (a:ℝ) (left_mem_Icc.mpr habR.le)
  have hqb : A*b^2+B*b+C≠0 := by
    exact_mod_cast hp (b:ℝ) (right_mem_Icc.mpr habR.le)
  have hu : u^2-r≠0 := by
    have he : u^2-r=4*A*(A*a^2+B*a+C) := by dsimp [u,r]; ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hA) hqa
  have hv : v^2-r≠0 := by
    have he : v^2-r=4*A*(A*b^2+B*b+C) := by dsimp [v,r]; ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hA) hqb
  obtain ⟨c,d,hc,hsf,hd,hs⟩ := PositiveIntegrals.positive_rat_squareclass r hr
  have hrc : r=c^2*(d:ℚ) := by
    have hh : (r:ℝ)=(c:ℝ)^2*(d:ℝ) := by
      rw [← sq_sqrt hrR.le,hs,mul_pow,sq_sqrt (Nat.cast_nonneg d)]
    exact_mod_cast hh
  obtain ⟨P,S,hN,he⟩ := PositiveIntegrals.crossratio_norm_coefficients r u v hu hv
    (sqrt (r:ℝ)) (sq_sqrt hrR.le)
  have hNT : P^2-(d:ℚ)*(S*c)^2=1 := by rw [hrc] at hN; nlinarith only [hN]
  have hA' : (A:ℝ)≠0 := by exact_mod_cast hA
  have hD' : 0<(B:ℝ)^2-4*(A:ℝ)*(C:ℝ) := by exact_mod_cast hD
  obtain ⟨hpos,hne,hev⟩ := OAI.PositiveIntegrals.crossRatio_spec
    (A:ℝ) B C a b hA' hD' habR hp
  have hcross : OAI.PositiveIntegrals.crossRatio (A:ℝ) B C a b =
      (P:ℝ)+((S*c:ℚ):ℝ)*sqrt d := by
    have hcross0 : OAI.PositiveIntegrals.crossRatio (A:ℝ) B C a b =
        ((v:ℝ)-sqrt (r:ℝ))*((u:ℝ)+sqrt (r:ℝ)) /
        (((v:ℝ)+sqrt (r:ℝ))*((u:ℝ)-sqrt (r:ℝ))) := by
      simp [OAI.PositiveIntegrals.crossRatio,r,u,v]
    rw [hcross0,he,hs]
    push_cast
    ring
  rw [hcross] at hpos hne hev
  rw [hev]
  have hs' : sqrt ((B:ℝ)^2-4*(A:ℝ)*(C:ℝ)) = (c:ℝ)*sqrt d := by simpa [r] using hs
  rw [hs']
  exact norm_one_log_bound c d hc hd hsf P (S*c) hNT hpos hne

theorem positive_discriminant_exponent (A B C a b : ℚ) (hA : A≠0)
    (hD : 0<B^2-4*A*C) (hab : a<b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)≠0) :
    irrationalityExponent
      (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)))=2 :=
  OAI.LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (positive_discriminant_bound A B C a b hA hD hab hp)

theorem nonzero_discriminant_bound (A B C a b : ℚ) (hA : A≠0)
    (hD : B^2-4*A*C≠0) (hab : a<b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)≠0) :
    EventualLowerBound
      (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) := by
  rcases lt_or_gt_of_ne hD with hneg|hpos
  · exact negative_discriminant_bound A B C a b hA (by linarith) hab
  · exact positive_discriminant_bound A B C a b hA hpos hab hp

theorem nonzero_discriminant_exponent (A B C a b : ℚ) (hA : A≠0)
    (hD : B^2-4*A*C≠0) (hab : a<b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)≠0) :
    irrationalityExponent
      (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)))=2 :=
  OAI.LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (nonzero_discriminant_bound A B C a b hA hD hab hp)
end OAI.Integrals

import Imaginary.Scaling
noncomputable section
open Filter Real OAI.PiExponent
namespace OAI.Integrals

theorem eventualLowerBound_mul_nat {x : ℝ} (hx : EventualLowerBound x)
    (n : ℕ) (hn : 0 < n) : EventualLowerBound ((n:ℝ)*x) := by
  intro nu hnu
  let mu : ℝ := (nu+2)/2
  have hmu : 2 < mu := by dsimp [mu]; linarith
  have hgap : 0 < nu-mu := by dsimp [mu]; linarith
  obtain ⟨Q,hQ,hb⟩ := hx mu hmu
  have hgrowth : Tendsto (fun q : ℕ => (q:ℝ)^(nu-mu)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hgrowth.eventually (eventually_ge_atTop ((n:ℝ)^mu)))
  refine ⟨max Q N, hQ.trans (le_max_left _ _), ?_⟩
  intro p q hq
  have hqQ : Q ≤ q := (le_max_left _ _).trans hq
  have hqN : N ≤ q := (le_max_right _ _).trans hq
  have hqp : (0:ℝ)<q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0<Q) hqQ)
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hqq : Q ≤ n*q := hqQ.trans (by simpa using Nat.mul_le_mul_right q hn)
  have hb' := hb p (n*q) hqq
  have hpower : (q:ℝ)^(-nu) ≤ ((n:ℝ)*(q:ℝ))^(-mu) := by
    have hh := mul_le_mul_of_nonneg_right (hN q hqN) (rpow_nonneg hqp.le (-nu))
    rw [← rpow_add hqp] at hh
    have hh' : (n:ℝ)^mu*(q:ℝ)^(-nu) ≤ (q:ℝ)^(-mu) := by
      simpa only [show nu-mu+-nu = -mu by ring] using hh
    rw [mul_rpow hnp.le hqp.le, rpow_neg hnp.le]
    calc
      _ ≤ (q:ℝ)^(-mu)/(n:ℝ)^mu := (le_div_iff₀ (rpow_pos_of_pos hnp mu)).mpr (by simpa [mul_comm] using hh')
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have he : (n:ℝ)*x-(p:ℝ)/(q:ℝ) =
      (n:ℝ)*(x-(p:ℝ)/((n:ℝ)*(q:ℝ))) := by field_simp
  rw [he, abs_mul, abs_of_pos hnp]
  have hb'' : ((n:ℝ)*(q:ℝ))^(-mu) ≤ |x-(p:ℝ)/((n:ℝ)*(q:ℝ))| := by
    simpa only [Nat.cast_mul] using hb'
  exact hpower.trans (hb''.trans (le_mul_of_one_le_left (abs_nonneg _) hn1))

theorem eventualLowerBound_div_pos_rat {x : ℝ} (hx : EventualLowerBound x)
    (c : ℚ) (hc : 0<c) : EventualLowerBound (x/(c:ℝ)) := by
  have hnum : 0 < c.num := Rat.num_pos.mpr hc
  have hna : 0 < c.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum)
  have he : (c:ℝ) = (c.num.natAbs:ℝ)/(c.den:ℝ) := by
    have hh := c.num_div_den
    have hh' : (c.num:ℝ)/(c.den:ℝ) = (c:ℝ) := by exact_mod_cast hh
    have hncast : (c.num.natAbs:ℝ) = (c.num:ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) (Int.natAbs_of_nonneg hnum.le)
    simpa only [hncast] using hh'.symm
  have h := OAI.Imaginary.eventualLowerBound_div_nat
    (eventualLowerBound_mul_nat hx c.den c.pos) c.num.natAbs hna
  convert h using 1
  rw [he, div_div_eq_mul_div]
  ring
end OAI.Integrals

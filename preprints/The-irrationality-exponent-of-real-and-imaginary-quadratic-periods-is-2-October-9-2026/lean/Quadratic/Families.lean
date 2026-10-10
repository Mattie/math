import Quadratic.Main

namespace OAI.Quadratic
open PiExponent
noncomputable section

def realValue (d : ℕ) (a b : ℤ) (c : ℕ) : ℝ :=
  ((a : ℝ) + (b : ℝ) * Real.sqrt d) / (c : ℝ)

theorem real_exp_powers_injective {y : ℝ} (hy : y ≠ 0) :
    Function.Injective (fun n : ℕ => (Complex.exp (y : ℂ)) ^ n) := by
  intro j k h
  have he : Real.exp ((j : ℝ) * y) = Real.exp ((k : ℝ) * y) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.exp_nat_mul] using h
  have hn : (j : ℝ) = k := mul_right_cancel₀ hy (Real.exp_injective he)
  exact_mod_cast hn

def realNormOnePeriod (d : ℕ) (hd : 0 < d)
    (hn : ∀ n : ℤ, n * n ≠ (d : ℤ)) (a b : ℤ) (c : ℕ) (hc : 0 < c)
    (hN : a * a - (d : ℤ) * b * b = (c : ℤ) ^ 2)
    (hpos : 0 < realValue d a b c) (hne : realValue d a b c ≠ 1) :
    PeriodData (realContext d hn) := by
  let f := realContext d hn
  let z : RealInt f := ⟨a, b⟩
  let x := Real.log (realValue d a b c) / Real.sqrt d
  have hsR : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hsC : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hlog : Real.log (realValue d a b c) ≠ 0 := by
    intro he
    have hh := congrArg Real.exp he
    rw [Real.exp_log hpos, Real.exp_zero] at hh
    exact hne hh
  have hx : x ≠ 0 := div_ne_zero hlog hsR
  have hproduct : (RealInt.embedding false z / (c : ℂ)) *
      (RealInt.embedding true z / (c : ℂ)) = 1 := by
    have hz : (z.norm : ℂ) = (c : ℂ) ^ 2 := by
      change (((a * a - (d : ℤ) * b * b : ℤ)) : ℂ) = _
      exact_mod_cast hN
    have hp : RealInt.embedding false z * RealInt.embedding true z = (z.norm : ℂ) := by
      simpa using (RealInt.norm_eq_product false z).symm
    rw [div_mul_div_comm, hp, hz,
      ← pow_two, div_self (pow_ne_zero 2 hcC)]
  have hepos : Complex.exp (rotation f false * (x : ℂ)) =
      RealInt.embedding false z / (c : ℂ) := by
    have he : rotation f false * (x : ℂ) = (Real.log (realValue d a b c) : ℂ) := by
      simp only [rotation, Bool.false_eq_true, ite_false, f, realContext, x, Complex.ofReal_div]
      field_simp
    rw [he, ← Complex.ofReal_exp, Real.exp_log hpos]
    rw [RealInt.embedding_def]
    simp [realValue, z, f, rotation, realContext]
  have hexp : ∀ s : Bool, Complex.exp (rotation f s * (x : ℂ)) =
      RealInt.embedding s z / (c : ℂ) := by
    intro s
    cases s
    · exact hepos
    · have he : rotation f true * (x : ℂ) = -(rotation f false * (x : ℂ)) := by
        simp [rotation]
      rw [he, Complex.exp_neg, hepos]
      have hv : RealInt.embedding false z / (c : ℂ) ≠ 0 := by
        rw [← hepos]
        exact Complex.exp_ne_zero _
      apply mul_left_cancel₀ hv
      rw [mul_inv_cancel₀ hv]
      exact hproduct.symm
  have hpowers : ∀ s : Bool, Function.Injective
      (fun n : ℕ => (RealInt.embedding s z / (c : ℂ)) ^ n) := by
    intro s
    rw [← hexp s]
    cases s
    · have he : rotation f false * (x : ℂ) = ((Real.sqrt d * x : ℝ) : ℂ) := by
        simp [rotation, f, realContext]
      rw [he]
      exact real_exp_powers_injective (mul_ne_zero hsR hx)
    · have he : rotation f true * (x : ℂ) = ((-Real.sqrt d * x : ℝ) : ℂ) := by
        simp [rotation, f, realContext]
      rw [he]
      exact real_exp_powers_injective (mul_ne_zero (neg_ne_zero.mpr hsR) hx)
  exact ⟨z, c, hc, x, hx, hexp, hpowers, false⟩

/-- An unconditional approximation endpoint for an explicitly represented norm-one element. -/
theorem real_norm_one_eventualLowerBound (d : ℕ) (hd : 0 < d)
    (hn : ∀ n : ℤ, n * n ≠ (d : ℤ)) (a b : ℤ) (c : ℕ) (hc : 0 < c)
    (hN : a * a - (d : ℤ) * b * b = (c : ℤ) ^ 2)
    (hpos : 0 < realValue d a b c) (hne : realValue d a b c ≠ 1) :
    EventualLowerBound (Real.log (realValue d a b c) / Real.sqrt d) :=
  DeterminantContradiction.period_eventualLowerBound (realNormOnePeriod d hd hn a b c hc hN hpos hne)

theorem real_norm_one_exponent (d : ℕ) (hd : 0 < d)
    (hn : ∀ n : ℤ, n * n ≠ (d : ℤ)) (a b : ℤ) (c : ℕ) (hc : 0 < c)
    (hN : a * a - (d : ℤ) * b * b = (c : ℤ) ^ 2)
    (hpos : 0 < realValue d a b c) (hne : realValue d a b c ≠ 1) :
    irrationalityExponent (Real.log (realValue d a b c) / Real.sqrt d) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (real_norm_one_eventualLowerBound d hd hn a b c hc hN hpos hne)

def imaginaryValue (d : ℕ) (a b : ℤ) (c : ℕ) : ℂ :=
  ((a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) / (c : ℂ)

theorem powers_injective_of_no_root {z : ℂ} (hz : z ≠ 0)
    (hn : ∀ n : ℕ, 0 < n → z ^ n ≠ 1) : Function.Injective (fun n : ℕ => z ^ n) := by
  intro j k h
  change z ^ j = z ^ k at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · apply hn (k-j) (Nat.sub_pos_of_lt hjk)
    rw [pow_sub₀ z hz hjk.le, h, mul_inv_cancel₀ (pow_ne_zero _ hz)]
  · apply hn (j-k) (Nat.sub_pos_of_lt hkj)
    rw [pow_sub₀ z hz hkj.le, h, mul_inv_cancel₀ (pow_ne_zero _ hz)]

def imaginaryNonTorsionPeriod (d : ℕ) (hd : 0 < d) (x : ℝ)
    (a b : ℤ) (c : ℕ) (hc : 0 < c)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) = imaginaryValue d a b c)
    (hn : ∀ n : ℕ, 0 < n → (imaginaryValue d a b c) ^ n ≠ 1) :
    PeriodData (imaginaryContext d hd) := by
  let f := imaginaryContext d hd
  let z : RealInt f := ⟨a, b⟩
  have hp : Complex.exp (rotation f false * (x : ℂ)) = RealInt.embedding false z / (c : ℂ) := by
    rw [RealInt.embedding_def]
    simpa [f, imaginaryContext, rotation, z, imaginaryValue] using he
  have hx : x ≠ 0 := by
    intro h
    have hv : imaginaryValue d a b c = 1 := by simpa [h] using he.symm
    exact hn 1 (by norm_num) (by simp [hv])
  have hneg : Complex.exp (rotation f true * (x : ℂ)) = RealInt.embedding true z / (c : ℂ) := by
    rw [RealInt.embedding_def]
    have hh := congrArg (starRingEnd ℂ) he
    simpa [← Complex.exp_conj, f, imaginaryContext, rotation, z,
      imaginaryValue, map_div₀, map_add, map_mul] using hh
  have hplus : Function.Injective (fun n : ℕ => (RealInt.embedding false z / (c : ℂ)) ^ n) := by
    rw [RealInt.embedding_def]
    have hz : imaginaryValue d a b c ≠ 0 := by rw [← he]; exact Complex.exp_ne_zero _
    simpa [f, imaginaryContext, rotation, z, imaginaryValue] using
      powers_injective_of_no_root hz hn
  have hminus : Function.Injective (fun n : ℕ => (RealInt.embedding true z / (c : ℂ)) ^ n) := by
    intro j k h
    apply hplus
    simp only [RealInt.embedding_def (f := f) true z] at h
    simp only [RealInt.embedding_def (f := f) false z]
    have hh := congrArg (starRingEnd ℂ) h
    simpa [f, imaginaryContext, rotation, z, map_pow, map_div₀, map_add, map_mul] using hh
  exact ⟨z, c, hc, x, hx, (by intro s; cases s; exact hp; exact hneg),
    (by intro s; cases s; exact hplus; exact hminus), false⟩

/-- Every real branch is retained; there is no principal-argument hypothesis. -/
theorem imaginary_non_torsion_eventualLowerBound (d : ℕ) (hd : 0 < d) (x : ℝ)
    (a b : ℤ) (c : ℕ) (hc : 0 < c)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) = imaginaryValue d a b c)
    (hn : ∀ n : ℕ, 0 < n → (imaginaryValue d a b c) ^ n ≠ 1) : EventualLowerBound x :=
  DeterminantContradiction.period_eventualLowerBound (imaginaryNonTorsionPeriod d hd x a b c hc he hn)

theorem imaginary_non_torsion_exponent (d : ℕ) (hd : 0 < d) (x : ℝ)
    (a b : ℤ) (c : ℕ) (hc : 0 < c)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) = imaginaryValue d a b c)
    (hn : ∀ n : ℕ, 0 < n → (imaginaryValue d a b c) ^ n ≠ 1) : irrationalityExponent x = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (imaginary_non_torsion_eventualLowerBound d hd x a b c hc he hn)

end
end OAI.Quadratic

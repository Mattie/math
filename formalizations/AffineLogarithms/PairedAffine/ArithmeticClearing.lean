import AlgebraicLog.IntegerClearing
import AlgebraicLog.MatrixArithmetic

namespace OAI.PairedAffine.Arithmetic

noncomputable section
open scoped BigOperators NumberField
open PiExponent PiExponent.InterpolationMatrix

variable {F : Type*} [Field F] [NumberField F]

def logTrunc (F : Type*) [Field F] [NumberField F] (T : ℕ) : Polynomial F :=
  PowerSeries.trunc T (PowerSeries.log F)

theorem map_logTrunc (T : ℕ) (σ : F →ₐ[ℚ] ℂ) :
    (logTrunc F T).map σ.toRingHom = truncatedLog T := by
  ext k
  by_cases hk : k < T <;> by_cases hk0 : k = 0 <;>
    simp [logTrunc, truncatedLog, Polynomial.coeff_map, PowerSeries.coeff_trunc,
      PowerSeries.coeff_log, hk, hk0, map_div₀]

theorem lcm_mul_log_coeff_int (T k : ℕ) (hk : k ≤ T) :
    (Nat.lcmUpto T : F) * PowerSeries.coeff k (PowerSeries.log F) ∈
      (Int.castRingHom F).range := by
  by_cases hk0 : k = 0
  · simp [hk0]
  obtain ⟨n, hn⟩ := PiExponent.Arithmetic.dvd_lcmUpto_of_pos_le (Nat.pos_of_ne_zero hk0) hk
  refine ⟨(-1 : ℤ) ^ (k + 1) * (n : ℤ), ?_⟩
  rw [PowerSeries.coeff_log, ite_eq_right hk0, hn]
  have hkF : (k : F) ≠ 0 := by exact_mod_cast hk0
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀, Nat.cast_mul]
  field_simp

def integralPolynomials (F : Type*) [Field F] [NumberField F] : Subring (Polynomial F) :=
  (Polynomial.mapRingHom (algebraMap (integralClosure ℤ F) F)).range

theorem integral_C_mem (z : F) (hz : IsIntegral ℤ z) :
    Polynomial.C z ∈ integralPolynomials F := by
  have hmem : z ∈ integralClosure ℤ F := hz
  refine ⟨Polynomial.C (⟨z, hmem⟩ : integralClosure ℤ F), ?_⟩
  change Polynomial.map (algebraMap (integralClosure ℤ F) F)
    (Polynomial.C (⟨z, hmem⟩ : integralClosure ℤ F)) = _
  rw [Polynomial.map_C]
  rfl

theorem integral_logTrunc_mem (T : ℕ) :
    Polynomial.C (Nat.lcmUpto T : F) * logTrunc F T ∈ integralPolynomials F := by
  apply (Polynomial.mem_map_range (algebraMap (integralClosure ℤ F) F)).mpr
  intro k
  rw [Polynomial.coeff_C_mul]
  change (Nat.lcmUpto T : F) *
    (PowerSeries.trunc T (PowerSeries.log F)).coeff k ∈ _
  rw [PowerSeries.coeff_trunc]
  split_ifs with hk
  · obtain ⟨z, hz⟩ := lcm_mul_log_coeff_int (F := F) T k hk.le
    refine ⟨(z : integralClosure ℤ F), ?_⟩
    simpa using hz
  · simp

theorem integral_shifted_logTrunc_mem (T q : ℕ) (z : F) (hz : IsIntegral ℤ z) :
    Polynomial.C (Nat.lcmUpto T : F) *
      (Polynomial.C z + Polynomial.C (q : F) * logTrunc F T) ∈
        integralPolynomials F := by
  let S := integralPolynomials F
  have hL : Polynomial.C (Nat.lcmUpto T : F) ∈ S :=
    integral_C_mem _ (isIntegral_natCast _)
  have hq : Polynomial.C (q : F) ∈ S := integral_C_mem _ (isIntegral_natCast _)
  have h := S.add_mem (S.mul_mem hL (integral_C_mem z hz))
    (S.mul_mem hq (integral_logTrunc_mem T))
  convert h using 1
  ring

theorem cleared_polynomial_power_mem (L e d : ℕ) (f : Polynomial F) (hd : d ≤ e)
    (hf : Polynomial.C (L : F) * f ∈ integralPolynomials F) :
    Polynomial.C ((L : F) ^ e) * f ^ d ∈ integralPolynomials F := by
  let S := integralPolynomials F
  have hL : Polynomial.C (L : F) ∈ S := integral_C_mem _ (isIntegral_natCast _)
  have h := S.mul_mem (S.pow_mem hL (e - d)) (S.pow_mem hf d)
  have he : e = (e - d) + d := (Nat.sub_add_cancel hd).symm
  rw [he, map_pow, pow_add]
  simpa only [mul_pow, mul_assoc] using h

theorem cleared_polynomial_product_mem {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial F) (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : F) * f i ∈ integralPolynomials F) :
    Polynomial.C (∏ i ∈ s, (L i : F) ^ e i) *
      (∏ i ∈ s, f i ^ d i) ∈ integralPolynomials F := by
  have h := (integralPolynomials F).prod_mem (fun i hi =>
    cleared_polynomial_power_mem (L i) (e i) (d i) (f i) (hd i hi) (hf i hi))
  simpa only [← Finset.prod_mul_distrib, map_prod] using h

theorem integral_coeff_of_mem (P : Polynomial F) (hP : P ∈ integralPolynomials F)
    (k : ℕ) : IsIntegral ℤ (P.coeff k) := by
  obtain ⟨Q, hQ⟩ := hP
  change Q.map (algebraMap (integralClosure ℤ F) F) = P at hQ
  rw [← hQ, Polynomial.coeff_map]
  exact (Q.coeff k).property

theorem common_denominator_coeff_integral {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → Polynomial F) (P : Polynomial F)
    (hP : P ∈ integralPolynomials F)
    (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, Polynomial.C (L i : F) * f i ∈ integralPolynomials F) (k : ℕ) :
    IsIntegral ℤ ((∏ i ∈ s, (L i : F) ^ e i) *
      (P * ∏ i ∈ s, f i ^ d i).coeff k) := by
  have h := (integralPolynomials F).mul_mem hP
    (cleared_polynomial_product_mem s L e d f hd hf)
  have he : P * (Polynomial.C (∏ i ∈ s, (L i : F) ^ e i) *
      ∏ i ∈ s, f i ^ d i) =
      Polynomial.C (∏ i ∈ s, (L i : F) ^ e i) * (P * ∏ i ∈ s, f i ^ d i) := by ring
  rw [he] at h
  simpa only [Polynomial.coeff_C_mul] using integral_coeff_of_mem _ h k

/-- Algebraic-integral numerators replace the integer numerators in the
original clearing lemma. All embeddings evaluate one field element. -/
theorem exists_integral_entry_lift {m : ℕ}
    (a : F) (ha : IsIntegral ℤ a)
    (T q e : Fin m → ℕ) (z : Fin m → F) (hz : ∀ i, IsIntegral ℤ (z i))
    (hq : ∀ i, q i ≠ 0) (j s h : ℕ) (β γ : Fin m → ℕ)
    (hγ : ∀ i, γ i ≤ e i) :
    ∃ b : F, IsIntegral ℤ b ∧ ∀ σ : F →ₐ[ℚ] ℂ,
      σ b =
        ((∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) /
          (∏ i, (q i : ℂ) ^ β i)) *
        (∏ i, (q i : ℂ) ^ γ i) *
        ((σ a) ^ (j * h) * entry (fun i => σ (z i) / (q i : ℂ))
          (fun i => truncatedLog (T i)) j s β h γ) := by
  classical
  by_cases hβγ : ∀ i, β i ≤ γ i
  swap
  · refine ⟨0, isIntegral_zero, fun σ => ?_⟩
    rw [entry_eq_zero_of_not_le _ _ _ _ _ _ _ hβγ]
    simp
  let f : Fin m → Polynomial F := fun i =>
    Polynomial.C ((j : F) * z i) + Polynomial.C (q i : F) * logTrunc F (T i)
  let P : Polynomial F := (1 + Polynomial.X) ^ h
  let n : F := (∏ i, (Nat.lcmUpto (T i) : F) ^ e i) *
    (P * ∏ i, f i ^ (γ i - β i)).coeff s
  have hP : P ∈ integralPolynomials F := by
    exact ⟨((1 + Polynomial.X) ^ h : Polynomial (integralClosure ℤ F)), by simp [P]⟩
  have hn : IsIntegral ℤ n :=
    common_denominator_coeff_integral Finset.univ
      (fun i => Nat.lcmUpto (T i)) e (fun i => γ i - β i) f P hP
      (fun i _ => (Nat.sub_le _ _).trans (hγ i))
      (fun i _ => integral_shifted_logTrunc_mem (T i) (q i) _
        ((isIntegral_natCast j).mul (hz i))) s
  let chooseFactor : F := ∏ i, ((γ i).choose (β i) : F)
  have hchoose : IsIntegral ℤ chooseFactor :=
    IsIntegral.prod _ (fun i _ => isIntegral_natCast _)
  refine ⟨a ^ (j * h) * chooseFactor * n, ((ha.pow _).mul hchoose).mul hn, ?_⟩
  intro σ
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ γ i) / (∏ i, (q i : ℂ) ^ β i) =
      ∏ i, (q i : ℂ) ^ (γ i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hβγ i)).symm
  have hzmap (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * (σ (z i) / (q i : ℂ))) + truncatedLog (T i)) =
      Polynomial.C ((j : ℂ) * σ (z i)) +
        Polynomial.C (q i : ℂ) * truncatedLog (T i) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    field_simp [hqC i]
  have hfmap (i : Fin m) : (f i).map σ.toRingHom =
      Polynomial.C ((j : ℂ) * σ (z i)) +
        Polynomial.C (q i : ℂ) * truncatedLog (T i) := by
    simp only [f, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    rw [map_logTrunc]
    simp
  have hnmap : σ n = (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      ((1 + Polynomial.X) ^ h * ∏ i,
        (Polynomial.C ((j : ℂ) * σ (z i)) +
          Polynomial.C (q i : ℂ) * truncatedLog (T i)) ^ (γ i - β i)).coeff s := by
    simp only [n, map_mul, map_prod, map_pow, map_natCast]
    congr 1
    change σ.toRingHom ((P * ∏ i, f i ^ (γ i - β i)).coeff s) = _
    rw [← Polynomial.coeff_map]
    simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow, hfmap,
      P, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X, map_mul, map_natCast]
  have hscalar := scalar_product_mul_coeff (fun i => (q i : ℂ))
    (fun i => γ i - β i) ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * (σ (z i) / (q i : ℂ))) + truncatedLog (T i)) s
  simp_rw [hzmap] at hscalar
  rw [map_mul, map_mul, map_pow, hnmap, ← hscalar]
  simp only [chooseFactor, map_prod, map_natCast]
  rw [entry_eq_binomial_product]
  have he := hratio
  rw [div_eq_mul_inv] at he
  simp only [div_eq_mul_inv]
  rw [show (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ β i)⁻¹ * (∏ i, (q i : ℂ) ^ γ i) =
      (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
        (∏ i, (q i : ℂ) ^ (γ i - β i)) by rw [← he]; ring]
  ring

end
end OAI.PairedAffine.Arithmetic

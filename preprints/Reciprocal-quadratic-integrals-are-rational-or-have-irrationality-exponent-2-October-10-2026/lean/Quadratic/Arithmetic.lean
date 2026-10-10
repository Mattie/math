import Quadratic.Order
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

namespace OAI.Quadratic.Arithmetic
variable {f : Context}
noncomputable section
open scoped BigOperators
open PiExponent PiExponent.InterpolationMatrix

abbrev lcmConstant := PiExponent.Arithmetic.lcmConstant
abbrev lcmConstant_pos := PiExponent.Arithmetic.lcmConstant_pos

/-- The logarithm truncation is cleared over the ordinary integers. This one
polynomial is subsequently evaluated at both quadratic embeddings. -/
theorem exists_integer_log (T : ℕ) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℂ) =
        Polynomial.C (Nat.lcmUpto T : ℂ) * truncatedLog T := by
  apply (Polynomial.mem_map_range (Int.castRingHom ℂ)).mpr
  intro k
  rw [Polynomial.coeff_C_mul, truncatedLog_coeff]
  split_ifs with hk hk0
  · simp
  · obtain ⟨m, hm⟩ := PiExponent.Arithmetic.dvd_lcmUpto_of_pos_le
      (Nat.pos_of_ne_zero hk0) hk.le
    refine ⟨((-1 : ℤ) ^ (k + 1)) * (m : ℤ), ?_⟩
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    simp only [hm, map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀, Nat.cast_mul]
    field_simp
  · simp

def clearedLog (T : ℕ) : Polynomial (RealInt f) :=
  (exists_integer_log T).choose.map (Int.castRingHom (RealInt f))

theorem map_clearedLog (φ : (RealInt f) →+* ℂ) (T : ℕ) :
    (clearedLog T).map φ = Polynomial.C (Nat.lcmUpto T : ℂ) * truncatedLog T := by
  rw [clearedLog, Polynomial.map_map]
  have h : φ.comp (Int.castRingHom (RealInt f)) = Int.castRingHom ℂ := by ext; simp
  rw [h]
  exact (exists_integer_log T).choose_spec

def clearedPolynomial {m : ℕ} (T q e a : Fin m → ℕ)
    (z : Fin m → (RealInt f)) (h : ℕ) : Polynomial (RealInt f) :=
  (1 + Polynomial.X) ^ h * ∏ i,
    Polynomial.C ((Nat.lcmUpto (T i) : (RealInt f)) ^ (e i - a i)) *
      (Polynomial.C ((Nat.lcmUpto (T i) : (RealInt f)) * z i) +
        Polynomial.C (q i : (RealInt f)) * clearedLog (T i)) ^ a i

theorem map_clearedPolynomial {m : ℕ} (φ : (RealInt f) →+* ℂ)
    (T q e a : Fin m → ℕ) (z : Fin m → (RealInt f)) (h : ℕ)
    (ha : ∀ i, a i ≤ e i) :
    (clearedPolynomial T q e a z h).map φ =
      Polynomial.C (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
        ((1 + Polynomial.X) ^ h * ∏ i,
          (Polynomial.C (φ (z i)) + Polynomial.C (q i : ℂ) * truncatedLog (T i)) ^ a i) := by
  have he (i : Fin m) :
      Polynomial.C ((Nat.lcmUpto (T i) : ℂ) ^ (e i - a i)) *
        (Polynomial.C ((Nat.lcmUpto (T i) : ℂ) * φ (z i)) +
          Polynomial.C (q i : ℂ) *
            (Polynomial.C (Nat.lcmUpto (T i) : ℂ) * truncatedLog (T i))) ^ a i =
      Polynomial.C ((Nat.lcmUpto (T i) : ℂ) ^ e i) *
        (Polynomial.C (φ (z i)) + Polynomial.C (q i : ℂ) * truncatedLog (T i)) ^ a i := by
    rw [map_mul]
    rw [show Polynomial.C (Nat.lcmUpto (T i) : ℂ) * Polynomial.C (φ (z i)) +
        Polynomial.C (q i : ℂ) *
          (Polynomial.C (Nat.lcmUpto (T i) : ℂ) * truncatedLog (T i)) =
        Polynomial.C (Nat.lcmUpto (T i) : ℂ) *
          (Polynomial.C (φ (z i)) + Polynomial.C (q i : ℂ) * truncatedLog (T i)) by ring]
    rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel (ha i)]
  simp only [clearedPolynomial, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_one, Polynomial.map_X, Polynomial.map_prod,
    Polynomial.map_C, Polynomial.map_natCast, map_pow, map_natCast, RingHom.map_mul, map_clearedLog]
  simp only [map_pow, map_mul, map_natCast] at he
  simp_rw [he]
  rw [Finset.prod_mul_distrib, map_prod]
  simp only [map_pow, map_natCast]
  ring

def clearedEntry {m : ℕ} (T q e : Fin m → ℕ) (p : Fin m → ℤ)
    (j s h : ℕ) (b a : Fin m → ℕ) : (RealInt f) :=
  if ∀ i, b i ≤ a i then
    (∏ i, ((a i).choose (b i) : (RealInt f))) *
      (clearedPolynomial T q e (fun i => a i - b i)
        (fun i => ⟨0, (j : ℤ) * p i⟩) h).coeff s
  else 0

theorem map_clearedEntry {m : ℕ} (slopeSign : Bool)
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (b a : Fin m → ℕ) (ha : ∀ i, a i ≤ e i) :
    RealInt.embedding (f := f) slopeSign (clearedEntry T q e p j s h b a) =
      (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
        (∏ i, (q i : ℂ) ^ a i) / (∏ i, (q i : ℂ) ^ b i) *
          entry (fun i => (rotation f) slopeSign * (p i : ℂ) / (q i : ℂ))
            (fun i => truncatedLog (T i)) j s b h a := by
  classical
  by_cases hba : ∀ i, b i ≤ a i
  swap
  · simp [clearedEntry, hba, entry_eq_zero_of_not_le _ _ _ _ _ _ _ hba]
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by intro i; exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ a i) / (∏ i, (q i : ℂ) ^ b i) =
      ∏ i, (q i : ℂ) ^ (a i - b i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hba i)).symm
  have hz (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * ((rotation f) slopeSign * (p i : ℂ) / (q i : ℂ))) +
        truncatedLog (T i)) =
      Polynomial.C (RealInt.embedding slopeSign (⟨0, (j : ℤ) * p i⟩ : (RealInt f))) +
        Polynomial.C (q i : ℂ) * truncatedLog (T i) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    simp only [RealInt.embedding_def, Int.cast_zero, Int.cast_mul, Int.cast_natCast, zero_add]
    field_simp [hqC i]
  have hscalar := scalar_product_mul_coeff (fun i => (q i : ℂ)) (fun i => a i - b i)
    ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * ((rotation f) slopeSign * (p i : ℂ) / (q i : ℂ))) +
      truncatedLog (T i)) s
  simp_rw [hz] at hscalar
  rw [clearedEntry, ite_eq_left hba, map_mul, map_prod]
  simp only [map_natCast]
  rw [← Polynomial.coeff_map, map_clearedPolynomial _ _ _ _ _ _ _
    (fun i => (Nat.sub_le _ _).trans (ha i)), Polynomial.coeff_C_mul, ← hscalar]
  rw [mul_div_assoc, hratio, entry_eq_binomial_product]
  ring

/-- One order matrix supplies both selected determinants. The second determinant
is forced nonzero by the integral norm, not by a separately chosen minor. -/
theorem cleared_det_pair_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sgn : Bool) (A A' : Matrix ι ι ℂ) (B : Matrix ι ι (RealInt f))
    (r c : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hB : B.map (RealInt.embedding sgn) = fun i j => (r i : ℂ) * ((c j : ℂ) * A i j))
    (hB' : B.map (RealInt.embedding (!sgn)) = fun i j => (r i : ℂ) * ((c j : ℂ) * A' i j)) :
    A'.det ≠ 0 ∧
      -(∑ i, Real.log (r i)) - ∑ j, Real.log (c j) ≤
        (Real.log ‖A.det‖ + Real.log ‖A'.det‖) / 2 := by
  have hdet : RealInt.embedding sgn B.det =
      (∏ i, (r i : ℂ)) * (∏ j, (c j : ℂ)) * A.det := by
    rw [RingHom.map_det]
    change (B.map (RealInt.embedding sgn)).det = _
    rw [hB, PiExponent.Arithmetic.det_row_column_scale]
  have hdet' : RealInt.embedding (!sgn) B.det =
      (∏ i, (r i : ℂ)) * (∏ j, (c j : ℂ)) * A'.det := by
    rw [RingHom.map_det]
    change (B.map (RealInt.embedding (!sgn))).det = _
    rw [hB', PiExponent.Arithmetic.det_row_column_scale]
  have hrp : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => hr i)
  have hcp : 0 < ∏ i, c i := Finset.prod_pos (fun i _ => hc i)
  have hrC : (∏ i, (r i : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_prod]; exact_mod_cast hrp.ne'
  have hcC : (∏ i, (c i : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_prod]; exact_mod_cast hcp.ne'
  have hne : B.det ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hdet
    exact (mul_ne_zero (mul_ne_zero hrC hcC) hA) hdet.symm
  have hne' : A'.det ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdet'
    exact hne (RealInt.embedding_injective (!sgn) (by simpa using hdet'))
  refine ⟨hne', ?_⟩
  have hn := RealInt.one_le_norm_product sgn hne
  rw [hdet, hdet', norm_mul, norm_mul, norm_mul, norm_mul, norm_prod, norm_prod] at hn
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr _), abs_of_pos (hc _)] at hn
  have hl := Real.log_nonneg hn
  rw [Real.log_mul (mul_pos (mul_pos hrp hcp) (norm_pos_iff.mpr hA)).ne'
    (mul_pos (mul_pos hrp hcp) (norm_pos_iff.mpr hne')).ne'] at hl
  simp only [Real.log_mul (mul_pos hrp hcp).ne' (norm_pos_iff.mpr hA).ne',
    Real.log_mul (mul_pos hrp hcp).ne' (norm_pos_iff.mpr hne').ne',
    Real.log_mul hrp.ne' hcp.ne', Real.log_prod (fun i _ => (hr i).ne'),
    Real.log_prod (fun i _ => (hc i).ne')] at hl
  linarith

theorem cleared_det_pair_bound_with_denominator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sgn : Bool) (A A' : Matrix ι ι ℂ) (B : Matrix ι ι (RealInt f))
    (r c : ι → ℝ) (D : ℝ) (hD : 0 < D)
    (hr : ∀ i, 0 < r i) (hc : ∀ i, 0 < c i) (hA : A.det ≠ 0)
    (hB : B.map (RealInt.embedding sgn) = fun i j =>
      (D : ℂ) * (r i : ℂ) * ((c j : ℂ) * A i j))
    (hB' : B.map (RealInt.embedding (!sgn)) = fun i j =>
      (D : ℂ) * (r i : ℂ) * ((c j : ℂ) * A' i j)) :
    A'.det ≠ 0 ∧
      -(Fintype.card ι : ℝ) * Real.log D - (∑ i, Real.log (r i)) -
        ∑ j, Real.log (c j) ≤ (Real.log ‖A.det‖ + Real.log ‖A'.det‖) / 2 := by
  obtain ⟨hne, h⟩ := cleared_det_pair_bound sgn A A' B (fun i => D * r i) c
    (fun i => mul_pos hD (hr i)) hc hA (by simpa using hB) (by simpa using hB')
  refine ⟨hne, ?_⟩
  simp_rw [Real.log_mul hD.ne' (hr _).ne'] at h
  rw [Finset.sum_add_distrib, Finset.sum_const] at h
  simp only [Finset.card_univ, nsmul_eq_mul] at h
  linarith

end
end OAI.Quadratic.Arithmetic

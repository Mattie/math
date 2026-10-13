import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Mathlib.Algebra.Algebra.Hom.Rat

namespace OAI.PairedAffine.Field

noncomputable section

private theorem nonsquare_three : ¬ IsSquare (3 : ℚ) := by
  change ¬ IsSquare ((3 : ℕ) : ℚ)
  rw [Rat.isSquare_natCast_iff]
  norm_num [IsSquare]

private theorem nonsquare_two : ¬ IsSquare (2 : ℚ) := by
  change ¬ IsSquare ((2 : ℕ) : ℚ)
  rw [Rat.isSquare_natCast_iff]
  norm_num [IsSquare]

private theorem nonsquare_six : ¬ IsSquare (6 : ℚ) := by
  change ¬ IsSquare ((6 : ℕ) : ℚ)
  rw [Rat.isSquare_natCast_iff]
  norm_num [IsSquare]

abbrev K := QuadraticAlgebra ℚ 3 0
instance : Fact (¬ IsSquare (3 : ℚ)) := ⟨nonsquare_three⟩

private theorem nonsquare_two_K : ¬ IsSquare (2 : K) := by
  rintro ⟨x, hx⟩
  have hre := congrArg QuadraticAlgebra.re hx
  have him := congrArg QuadraticAlgebra.im hx
  change (2 : ℚ) = (x * x).re at hre
  change (0 : ℚ) = (x * x).im at him
  simp at hre him
  have hzero : x.re = 0 ∨ x.im = 0 := by
    have : x.re * x.im = 0 := by nlinarith [him]
    exact mul_eq_zero.mp this
  rcases hzero with h | h
  · apply nonsquare_six
    refine ⟨3 * x.im, ?_⟩
    simp [h] at hre
    nlinarith
  · apply nonsquare_two
    refine ⟨x.re, ?_⟩
    simpa [h] using hre

instance : Fact (¬ IsSquare (2 : K)) := ⟨nonsquare_two_K⟩
abbrev F := QuadraticAlgebra K 2 0

instance : NumberField K := NumberField.of_module_finite ℚ K
instance : NumberField F := NumberField.of_module_finite K F

theorem degree : Module.finrank ℚ F = 4 := by
  rw [← Module.finrank_mul_finrank ℚ K F]
  norm_num [QuadraticAlgebra.finrank_eq_two]

def sqrtTwo : F := QuadraticAlgebra.omega
def sqrtThree : F := algebraMap K F QuadraticAlgebra.omega
def base : F := 3 + 2 * sqrtTwo

theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  rw [pow_two]
  ext <;> norm_num [sqrtTwo, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  change algebraMap K F (QuadraticAlgebra.omega : K) ^ 2 = 3
  rw [← map_pow]
  have h : (QuadraticAlgebra.omega : K) ^ 2 = 3 := by
    ext <;> norm_num [pow_two, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [h, map_ofNat]

def embeddingK (v : ℂ) (hv : v ^ 2 = 3) : K →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨v, by simpa [pow_two] using hv⟩

def embedding (u v : ℂ) (hu : u ^ 2 = 2) (hv : v ^ 2 = 3) : F →ₐ[ℚ] ℂ := by
  letI : Algebra K ℂ := (embeddingK v hv).toAlgebra
  let f : F →ₐ[K] ℂ := QuadraticAlgebra.lift ⟨u, by
    simpa [pow_two, Algebra.smul_def, map_ofNat] using hu⟩
  exact f.toRingHom.toRatAlgHom

@[simp] theorem embedding_sqrtTwo (u v : ℂ) (hu : u ^ 2 = 2) (hv : v ^ 2 = 3) :
    embedding u v hu hv sqrtTwo = u := by
  change (embeddingK v hv) 0 * 1 + (embeddingK v hv) 1 * u = u
  simp

@[simp] theorem embedding_sqrtThree (u v : ℂ) (hu : u ^ 2 = 2) (hv : v ^ 2 = 3) :
    embedding u v hu hv sqrtThree = v := by
  change (embeddingK v hv) QuadraticAlgebra.omega * 1 + (embeddingK v hv) 0 * u = v
  simp only [map_zero, zero_mul, add_zero, mul_one]
  change (0 : ℚ) • (1 : ℂ) + (1 : ℚ) • v = v
  simp

@[simp] theorem embedding_base (u v : ℂ) (hu : u ^ 2 = 2) (hv : v ^ 2 = 3) :
    embedding u v hu hv base = 3 + 2 * u := by
  simp [base, map_ofNat]

theorem sqrtTwo_integral : IsIntegral ℤ sqrtTwo := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [sqrtTwo_sq]
  exact isIntegral_algebraMap

theorem sqrtThree_integral : IsIntegral ℤ sqrtThree := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [sqrtThree_sq]
  exact isIntegral_algebraMap

theorem base_integral : IsIntegral ℤ base := by
  exact (isIntegral_algebraMap (x := (3 : ℤ))).add
    ((isIntegral_algebraMap (x := (2 : ℤ))).mul sqrtTwo_integral)

def signedRoot (positive : Bool) (n : ℝ) : ℂ :=
  if positive then (Real.sqrt n : ℂ) else -(Real.sqrt n : ℂ)

theorem signedRoot_sq (positive : Bool) (n : ℝ) (hn : 0 ≤ n) :
    signedRoot positive n ^ 2 = (n : ℂ) := by
  have h : (Real.sqrt n : ℂ) ^ 2 = (n : ℂ) := by
    exact_mod_cast Real.sq_sqrt hn
  cases positive <;> simp [signedRoot, h]

def sigma (e t : Bool) : F →ₐ[ℚ] ℂ :=
  embedding (signedRoot e 2) (signedRoot t 3)
    (by simpa using signedRoot_sq e 2 (by norm_num))
    (by simpa using signedRoot_sq t 3 (by norm_num))

@[simp] theorem sigma_sqrtTwo (e t : Bool) : sigma e t sqrtTwo = signedRoot e 2 := by
  simp [sigma]

@[simp] theorem sigma_sqrtThree (e t : Bool) : sigma e t sqrtThree = signedRoot t 3 := by
  simp [sigma]

@[simp] theorem sigma_base (e t : Bool) : sigma e t base = 3 + 2 * signedRoot e 2 := by
  simp [sigma]


end
end OAI.PairedAffine.Field

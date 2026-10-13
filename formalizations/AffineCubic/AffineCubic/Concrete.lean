import AffineCubic.Field

namespace OAI.AffineCubic.Concrete
open OAI.AffineCubic.Field
noncomputable section

/-- The explicit real target: the logarithm of two plus the positive cube root of two. -/
def x : ℝ := Real.log 2 + root

theorem x_pos : 0 < x := add_pos (Real.log_pos (by norm_num)) root_pos

/-- The affine exponential relation at the distinguished complex embedding. -/
theorem exponential_identity :
    Complex.exp ((x : ℂ) - sigma0 r) = sigma0 (2 : F) := by
  rw [sigma0_r]
  have h : (x : ℂ) - (root : ℂ) = (Real.log 2 : ℂ) := by
    simp [x, Complex.ofReal_add]
  rw [h, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  simp [map_ofNat]

theorem two_integral : IsIntegral ℤ (2 : F) := isIntegral_algebraMap

theorem one_integral : IsIntegral ℤ (1 : F) := isIntegral_one

theorem all_embeddings_one_norm (σ : F →ₐ[ℚ] ℂ) : ‖σ (1 : F)‖ ≤ 1 := by simp

end
end OAI.AffineCubic.Concrete


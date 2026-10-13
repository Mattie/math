import AffineCubic.Endpoint
import AffineCubic.Concrete

namespace OAI.AffineCubic.Pilot

noncomputable section

/-- The literal eventual rational approximation bound for the affine cubic target. -/
theorem eventualLowerBound : EventualLowerBoundSix Concrete.x := by
  classical
  apply Endpoint.cubic_eventualLowerBound (2 : Field.F) 1 Field.r
    Concrete.two_integral Concrete.one_integral Field.r_integral Field.degree
    Field.sigma0 2 (by norm_num) (by norm_num) (by exact_mod_cast map_ofNat Field.sigma0 2)
    Concrete.x Concrete.x_pos.ne' {Field.sigma0} (by simp)
  · intro σ hσ
    have heq : σ = Field.sigma0 := by simpa only [Finset.mem_singleton] using hσ
    subst σ
    simpa only [map_one, one_mul] using Concrete.exponential_identity
  · intro σ _
    exact Concrete.all_embeddings_one_norm σ

/-- Irrationality follows from the eventual bound, without a separate transcendence input. -/
theorem irrational : Irrational Concrete.x :=
  irrational_of_eventualLowerBoundSix eventualLowerBound

/-- The conventional supremum-based irrationality exponent is at most six. -/
theorem irrationalityExponent_le_six :
    PiExponent.irrationalityExponent Concrete.x ≤ 6 :=
  irrationalityExponent_le_six_of_eventualLowerBoundSix eventualLowerBound

/-- The standard Mathlib approximation predicate is excluded above six. -/
theorem not_liouvilleWith : ∀ nu : ℝ, 6 < nu → ¬ LiouvilleWith nu Concrete.x :=
  not_liouvilleWith_of_eventual_bound Concrete.x eventualLowerBound

end
end OAI.AffineCubic.Pilot

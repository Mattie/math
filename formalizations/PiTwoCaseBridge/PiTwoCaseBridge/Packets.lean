import PiTwoCaseBridge.Triangular
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Polynomial packets with a common source bound

The triangular correction is performed inside the same degree-bounded
submodule, so taking linear combinations does not spend further degree.
-/

namespace PiTwoCaseBridge

open scoped Classical

open MvPolynomial

variable {K σ J : Type*} [Field K] [Fintype σ] [Fintype J]

/-- Exponents of weight strictly below the packet cutoff. -/
def PacketExponent (V : σ → ℕ) (T : ℕ) := {a : σ →₀ ℕ // Finsupp.weight V a < T}

@[instance_reducible]
noncomputable def packetExponentFintype (V : σ → ℕ) (hV : ∀ i, 0 < V i) (T : ℕ) :
    Fintype (PacketExponent V T) := by
  classical
  let encode (a : PacketExponent V T) (i : σ) : Fin T :=
    ⟨a.1 i, (Finsupp.le_weight V (hV i).ne' a.1).trans_lt a.2⟩
  exact Fintype.ofInjective encode (fun a b h => Subtype.ext
    (Finsupp.ext fun i => congrArg Fin.val (congrFun h i)))

/-- Bound on the source degree, written without division. -/
def sourceBudget (W : σ → ℕ) (L C : ℕ) : Submodule K (MvPolynomial σ K) where
  carrier := {p | ∀ a ∈ p.support, L * Finsupp.weight W a ≤ C}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro f g hf hg a ha
    rcases Finset.mem_union.mp (support_add ha) with ha | ha
    · exact hf a ha
    · exact hg a ha
  smul_mem' := by
    intro s f hf a ha
    apply hf a
    rw [mem_support_iff] at ha ⊢
    intro h
    exact ha (by simp [h])

/-- Simultaneous coefficient extraction into the one vector indexed by all centers. -/
noncomputable def polynomialPacket (chart : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (W V : σ → ℕ) (L C T : ℕ) :
    sourceBudget (K := K) W L C →ₗ[K] (J × PacketExponent V T → K) :=
  LinearMap.pi fun r => ((lcoeff K r.2.1).comp (chart r.1).toLinearMap).comp
    (sourceBudget W L C).subtype

theorem surjective_polynomialPacket_of_initial_monomials
    (chart : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (W V : σ → ℕ) (hV : ∀ i, 0 < V i) (L d B T : ℕ)
    (hLift : ∀ (j : J) (a : σ →₀ ℕ), Finsupp.weight V a < T →
      ∃ Q : MvPolynomial σ K,
        L * weightedTotalDegree W Q ≤ d * Finsupp.weight V a + L * B ∧
        ∀ (i : J) (b : σ →₀ ℕ), Finsupp.weight V b ≤ Finsupp.weight V a →
          (chart i Q).coeff b = if i = j ∧ b = a then 1 else 0) :
    Function.Surjective (polynomialPacket chart W V L (d * T + L * B) T) := by
  classical
  let := packetExponentFintype V hV T
  have hex (r : J × PacketExponent V T) :
      ∃ Q : sourceBudget (K := K) W L (d * T + L * B),
        ∀ s : J × PacketExponent V T, Finsupp.weight V s.2.1 ≤ Finsupp.weight V r.2.1 →
          polynomialPacket chart W V L (d * T + L * B) T Q s =
            if s = r then 1 else 0 := by
    obtain ⟨Q, hQ, hcoeff⟩ := hLift r.1 r.2.1 r.2.2
    let Q' : sourceBudget (K := K) W L (d * T + L * B) :=
      ⟨Q, fun a ha => (Nat.mul_le_mul_left L (le_weightedTotalDegree W ha)).trans
        (hQ.trans (Nat.add_le_add_right (Nat.mul_le_mul_left d r.2.2.le) _))⟩
    refine ⟨Q', fun s hs => ?_⟩
    change (chart s.1 Q).coeff s.2.1 = _
    rw [hcoeff s.1 s.2.1 hs]
    by_cases h : s = r
    · subst s
      simp
    · have hn : ¬ (s.1 = r.1 ∧ s.2.1 = r.2.1) :=
        fun e => h (Prod.ext e.1 (Subtype.ext e.2))
      simp [h, hn]
  choose lift hlift using hex
  apply surjective_of_weight_triangular_lifts (fun r => Finsupp.weight V r.2.1)
    _ T (fun r => r.2.2) lift
  intro r s hs
  by_cases h : s = r <;> simpa [h] using hlift r s hs

end PiTwoCaseBridge

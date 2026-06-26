import Mathlib.GroupTheory.Perm.Closure

/-!
# Milne, Chapter 8, Remark 8.28

A subgroup of a symmetric group of prime degree that contains a full cycle
and a transposition is the whole symmetric group.
-/

namespace Submission.NumberTheory.Milne

open Equiv Function Finset

variable {alpha : Type*} [DecidableEq alpha] [Fintype alpha]

/-- Milne, Remark 8.28: in prime degree, a full cycle and a transposition
generate the symmetric group. -/
theorem perm_cycle_swap
    (H : Subgroup (Equiv.Perm alpha)) {sigma tau : Equiv.Perm alpha}
    (hprime : (Fintype.card alpha).Prime)
    (hsigmaCycle : Equiv.Perm.IsCycle sigma)
    (hsigmaSupport : sigma.support = Finset.univ)
    (htauSwap : Equiv.Perm.IsSwap tau)
    (hsigma : sigma ∈ H) (htau : tau ∈ H) :
    H = ⊤ := by
  apply top_unique
  rw [← Equiv.Perm.closure_prime_cycle_swap hprime hsigmaCycle hsigmaSupport htauSwap]
  exact (Subgroup.closure_le H).2 (by
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hsigma, htau⟩)

/-- A permutation with a cycle partition of lengths two and three has a
transposition as its cube.  This is the permutation-theoretic conversion used
for the mod-`2` factorization in Example 8.25. -/
theorem swap_cycle_partition
    (rho : Equiv.Perm alpha) (s₂ s₃ : Finset alpha)
    (hcover : s₂ ∪ s₃ = Finset.univ)
    (hcard₂ : s₂.card = 2) (hcard₃ : s₃.card = 3)
    (hcycle₂ : rho.IsCycleOn (s₂ : Set alpha))
    (hcycle₃ : rho.IsCycleOn (s₃ : Set alpha)) :
    (rho ^ 3).IsSwap := by
  rw [← Equiv.Perm.card_support_eq_two]
  have hsupp : (rho ^ 3).support = s₂ := by
    ext x
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hx
      have hxuniv : x ∈ s₂ ∪ s₃ := by rw [hcover]; simp
      rw [Finset.mem_union] at hxuniv
      rcases hxuniv with hx₂ | hx₃
      · exact hx₂
      · exact False.elim (hx ((hcycle₃.pow_apply_eq hx₃).2 (by
          rw [hcard₃])))
    · intro hx₂ hfix
      have hdvd : s₂.card ∣ 3 := (hcycle₂.pow_apply_eq hx₂).1 hfix
      rw [hcard₂] at hdvd
      norm_num at hdvd
  rw [hsupp, hcard₂]

/-- A permutation which is cyclic on a finite type of cardinality at least
two is a full cycle. -/
theorem cycle_support_univ
    (sigma : Equiv.Perm alpha) (hcard : 2 ≤ Fintype.card alpha)
    (hcycle : sigma.IsCycleOn (Set.univ : Set alpha)) :
    sigma.IsCycle ∧ sigma.support = Finset.univ := by
  letI : Nontrivial alpha := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnontrivial : (Set.univ : Set alpha).Nontrivial := Set.nontrivial_univ
  have hsigma : sigma.IsCycle :=
    Equiv.Perm.isCycle_iff_exists_isCycleOn.mpr
      ⟨Set.univ, hnontrivial, hcycle, by simp⟩
  refine ⟨hsigma, ?_⟩
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
  exact hcycle.apply_ne hnontrivial (Set.mem_univ x)

end Submission.NumberTheory.Milne

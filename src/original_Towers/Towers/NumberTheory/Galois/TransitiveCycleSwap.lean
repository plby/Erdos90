import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Milne, Chapter 8, Lemma 8.26

A transitive subgroup of a finite symmetric group that contains a cycle on all but one point and
a transposition is the whole symmetric group.
-/

namespace Towers.NumberTheory.Milne

open Equiv Finset MulAction Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Milne, Lemma 8.26: a transitive permutation subgroup containing an `(n - 1)`-cycle and a
transposition is the full symmetric group. -/
theorem perm_pretransitive_cycle
    (H : Subgroup (Equiv.Perm α)) [MulAction.IsPretransitive H α]
    {σ τ : Equiv.Perm α} (hσ_cycle : σ.IsCycle)
    (hσ_card : σ.support.card + 1 = Fintype.card α) (hτ_swap : τ.IsSwap)
    (hσ_mem : σ ∈ H) (hτ_mem : τ ∈ H) :
    H = ⊤ := by
  obtain ⟨z, hz⟩ : ∃ z : α, z ∉ σ.support := by
    by_contra h
    push Not at h
    have hsupport : σ.support = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    have := hσ_card
    rw [hsupport, Finset.card_univ] at this
    omega
  obtain ⟨a, b, hab, rfl⟩ := hτ_swap
  obtain ⟨g, hg⟩ := exists_smul_eq H a z
  change (g : Equiv.Perm α) a = z at hg
  let c : α := (g : Equiv.Perm α) b
  have hzc : z ≠ c := by
    rw [← hg]
    exact (g : Equiv.Perm α).injective.ne hab
  have hstar : Equiv.swap z c ∈ H := by
    have hconj : (g : Equiv.Perm α) * Equiv.swap a b * (g : Equiv.Perm α)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem g.property hτ_mem) (H.inv_mem g.property)
    rw [← Equiv.swap_apply_apply] at hconj
    simpa [c, hg] using hconj
  have hsupport : σ.support = {z}ᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact fun hxz => hz (hxz ▸ hx)
    · rw [Finset.card_compl, Finset.card_singleton]
      omega
  have hstar_all : ∀ x : α, Equiv.swap z x ∈ H := by
    intro x
    by_cases hxz : x = z
    · subst x
      rw [Equiv.swap_self]
      exact H.one_mem
    have hc_support : c ∈ σ.support := by
      rw [hsupport]
      simp [hzc.symm]
    have hx_support : x ∈ σ.support := by
      rw [hsupport]
      simp [hxz]
    obtain ⟨i, hi⟩ := hσ_cycle.exists_pow_eq
      (Equiv.Perm.mem_support.mp hc_support) (Equiv.Perm.mem_support.mp hx_support)
    have hσpow : σ ^ i ∈ H := H.pow_mem hσ_mem i
    have hconj : σ ^ i * Equiv.swap z c * (σ ^ i)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hσpow hstar) (H.inv_mem hσpow)
    have hz_fixed : (σ ^ i) z = z := by
      apply Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
      simpa only [Equiv.Perm.mem_support, not_ne_iff] using hz
    rw [← Equiv.swap_apply_apply] at hconj
    simpa [hz_fixed, hi] using hconj
  apply top_unique
  rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  intro π hπ
  obtain ⟨x, y, hxy, rfl⟩ := hπ
  exact SubmonoidClass.swap_mem_trans H (by simpa [Equiv.swap_comm] using hstar_all x) (hstar_all y)

end Towers.NumberTheory.Milne

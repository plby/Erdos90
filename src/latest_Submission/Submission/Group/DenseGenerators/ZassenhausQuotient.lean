import Mathlib
import Submission.Algebra.DenseGenerators.FiniteGroupAlgebra


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

/-- Surjective homomorphisms map `D_n` onto `D_n`.

This is the reverse inclusion to `filtration_map_le`, and it is the algebraic exactness
input needed when the eventual Nikolov-Segal quotient is chosen. -/
lemma zassenhaus_filtration_surjective
    {G H : Type u} [Group G] [Group H]
    (p : ℕ)
    (n : ℕ)
    (f : G →* H)
    (hf : Function.Surjective f) :
    zassenhausFiltration p H n ≤
      Subgroup.map f (zassenhausFiltration p G n) := by
  rw [zassenhausFiltration]
  apply (Subgroup.closure_le _).mpr
  intro y hy
  have hy_lift :
      y ∈ (fun x : G => f x) '' zassenhausGeneratorSet p G n :=
    set_subset_surjective
      (p := p) (n := n) f hf hy
  rcases hy_lift with ⟨x, hx, rfl⟩
  exact Subgroup.mem_map_of_mem f (Subgroup.subset_closure hx)
/-- If a normal subgroup contains `D_n(G)`, then the quotient has trivial target `D_n`. -/
lemma filtration_quotient_bot
    {p : ℕ}
    {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {n : ℕ}
    (hDH : zassenhausFiltration p G n ≤ H) :
    zassenhausFiltration p (G ⧸ H) n = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  have hsurj : Function.Surjective (QuotientGroup.mk' H) :=
    QuotientGroup.mk'_surjective H
  have hqmap :
      q ∈ Subgroup.map (QuotientGroup.mk' H) (zassenhausFiltration p G n) :=
    zassenhaus_filtration_surjective
      (p := p) (n := n) (f := QuotientGroup.mk' H) hsurj hq
  rcases hqmap with ⟨x, hxD, rfl⟩
  have hxH : x ∈ H := hDH hxD
  have hxone : QuotientGroup.mk' H x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hxH
  simpa using hxone
end Submission

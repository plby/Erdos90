import Towers.ClassField.LocalExistence.CompactNormFibers

/-!
# Milne, Class Field Theory, Section III.5, Step 3

At the end of Step 3, Milne has a downward-directed family of nonempty finite
sets `E(L)` of possible `n`th roots.  He concludes that their total
intersection is nonempty.  This is the finite-set analogue of the compact
intersection argument in Step 2.
-/

namespace Towers.CField.LExist

universe u v

/-- A downward-directed family of nonempty finite sets has nonempty total
intersection. -/
theorem i_inter_directed
    {X : Type u} {ι : Type v} [Nonempty ι]
    (S : ι → Set X)
    (hdir : ∀ i j, ∃ k, S k ⊆ S i ∩ S j)
    (hnonempty : ∀ i, (S i).Nonempty)
    (hfinite : ∀ i, (S i).Finite) :
    (⋂ i, S i).Nonempty := by
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := discreteTopology_bot X
  exact inter_directed_compact
    S hdir hnonempty fun i ↦ (hfinite i).isCompact

/-- If every member of each finite set is an `n`th root of `a`, their common
point is an `n`th root of `a`.  This is the final finite-intersection step in
Milne's proof that `D_K` is divisible. -/
theorem common_directed_nonempty
    {M : Type u} [Monoid M] {ι : Type v} [Nonempty ι]
    (S : ι → Set M) (n : ℕ) (a : M)
    (hdir : ∀ i j, ∃ k, S k ⊆ S i ∩ S j)
    (hnonempty : ∀ i, (S i).Nonempty)
    (hfinite : ∀ i, (S i).Finite)
    (hroot : ∀ i x, x ∈ S i → x ^ n = a) :
    ∃ x, x ∈ ⋂ i, S i ∧ x ^ n = a := by
  obtain ⟨x, hx⟩ :=
    i_inter_directed S hdir hnonempty hfinite
  let i : ι := Classical.choice inferInstance
  exact ⟨x, hx, hroot i x (Set.mem_iInter.mp hx i)⟩

/-- The norm calculation in Step 3: applying a multiplicative map to an
`n`th-power identity again gives an `n`th-power identity. -/
theorem map_eq_eq
    {M : Type u} {N : Type v} [Monoid M] [Monoid N]
    (f : M →* N) {c a : M} {n : ℕ} (h : c ^ n = a) :
    (f c) ^ n = f a := by
  rw [← f.map_pow, h]

end Towers.CField.LExist

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Milne, Class Field Theory, Section III.5, Step 2

The point-set heart of Step 2 is Cantor's intersection argument.  Milne
considers compact nonempty subsets of one norm fibre, indexed by finite field
extensions, and observes that any two contain a third.  Their total
intersection is therefore nonempty.
-/

namespace Towers.CField.LExist

universe u v w

/-- A downward-directed family of nonempty compact subsets of a Hausdorff
space has nonempty intersection.  This is the point-set theorem used in Step
III.5.2. -/
theorem inter_directed_compact
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {ι : Type v} [Nonempty ι]
    (S : ι → Set X)
    (hdir : ∀ i j, ∃ k, S k ⊆ S i ∩ S j)
    (hnonempty : ∀ i, (S i).Nonempty)
    (hcompact : ∀ i, IsCompact (S i)) :
    (⋂ i, S i).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S
  · intro i j
    obtain ⟨k, hk⟩ := hdir i j
    exact ⟨k, fun _ hx ↦ (hk hx).1, fun _ hx ↦ (hk hx).2⟩
  · exact hnonempty
  · exact hcompact
  · exact fun i ↦ (hcompact i).isClosed

/-- If the compact sets in the preceding theorem all lie in one fibre, the
common point lies in that fibre.  In Milne's application `S i` is
`Nm_{L/K'}(Lˣ) ∩ Nm_{K'/K}^{-1}(a)`. -/
theorem inter_directed_fibers
    {X : Type u} {Y : Type w} [TopologicalSpace X] [T2Space X]
    {ι : Type v} [Nonempty ι]
    (f : X → Y) (a : Y) (S : ι → Set X)
    (hdir : ∀ i j, ∃ k, S k ⊆ S i ∩ S j)
    (hnonempty : ∀ i, (S i).Nonempty)
    (hcompact : ∀ i, IsCompact (S i))
    (hfiber : ∀ i, S i ⊆ f ⁻¹' {a}) :
    ∃ x, x ∈ ⋂ i, S i ∧ f x = a := by
  obtain ⟨x, hx⟩ :=
    inter_directed_compact S hdir hnonempty hcompact
  refine ⟨x, hx, ?_⟩
  let i : ι := Classical.choice inferInstance
  exact Set.mem_singleton_iff.mp (hfiber i (Set.mem_iInter.mp hx i))

/-- The set-theoretic form of the equality in Step III.5.2.  If the easy
inclusion `f(⋂ N_i) ⊆ D` is known and, over every point of `D`, the sets
`N_i ∩ f⁻¹(a)` are nonempty compact sets, then directedness gives the reverse
inclusion and hence equality. -/
theorem inter_compact_fibers
    {X : Type u} {Y : Type w} [TopologicalSpace X] [T2Space X]
    {ι : Type v} [Nonempty ι]
    (f : X → Y) (D : Set Y) (N : ι → Set X)
    (hforward : f '' (⋂ i, N i) ⊆ D)
    (hdir : ∀ i j, ∃ k, N k ⊆ N i ∩ N j)
    (hnonempty : ∀ a ∈ D, ∀ i, (N i ∩ f ⁻¹' {a}).Nonempty)
    (hcompact : ∀ a ∈ D, ∀ i, IsCompact (N i ∩ f ⁻¹' {a})) :
    f '' (⋂ i, N i) = D := by
  apply Set.Subset.antisymm hforward
  intro a ha
  let S : ι → Set X := fun i ↦ N i ∩ f ⁻¹' {a}
  have hSdir : ∀ i j, ∃ k, S k ⊆ S i ∩ S j := by
    intro i j
    obtain ⟨k, hk⟩ := hdir i j
    refine ⟨k, ?_⟩
    rintro x ⟨hxN, hxf⟩
    exact ⟨⟨(hk hxN).1, hxf⟩, ⟨(hk hxN).2, hxf⟩⟩
  obtain ⟨x, hx, hfx⟩ :=
    inter_directed_fibers
      f a S hSdir (hnonempty a ha) (hcompact a ha) (fun _ _ hx ↦ hx.2)
  refine ⟨x, ?_, hfx⟩
  exact Set.mem_iInter.mpr fun i ↦ (Set.mem_iInter.mp hx i).1

end Towers.CField.LExist

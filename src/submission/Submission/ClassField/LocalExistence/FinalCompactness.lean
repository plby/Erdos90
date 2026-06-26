import Submission.ClassField.LocalExistence.IsDivisibleSubgroup
import Submission.ClassField.LocalExistence.CompactNormFibers

/-!
# Milne, Class Field Theory, Section III.5: final compactness argument

After proving Steps 1--5, Milne intersects the candidate norm groups with the
compact unit group.  Since their total intersection lies in the target
finite-index subgroup, compactness and directedness show that one candidate
already has this property.
-/

namespace Submission.CField.LExist

universe u v

/-- Let `C i` be a downward-directed family of closed sets.  If their common
part inside a compact set `U` lies in an open set `I`, then already
`U ∩ C i ⊆ I` for one index `i`. -/
theorem inter_compact_directed
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {ι : Type v} [Nonempty ι]
    (U I : Set X) (C : ι → Set X)
    (hU : IsCompact U) (hI : IsOpen I)
    (hC : ∀ i, IsClosed (C i))
    (hdir : ∀ i j, ∃ k, C k ⊆ C i ∩ C j)
    (hcore : U ∩ ⋂ i, C i ⊆ I) :
    ∃ i, U ∩ C i ⊆ I := by
  by_contra h
  have hnot : ∀ i, ¬U ∩ C i ⊆ I := by
    simpa only [not_exists] using h
  let S : ι → Set X := fun i ↦ (U ∩ C i) ∩ Iᶜ
  have hnonempty : ∀ i, (S i).Nonempty := by
    intro i
    obtain ⟨x, hx, hxI⟩ := Set.not_subset.mp (hnot i)
    exact ⟨x, hx, hxI⟩
  have hcompact : ∀ i, IsCompact (S i) := fun i ↦
    (hU.inter_right (hC i)).inter_right hI.isClosed_compl
  have hSdir : ∀ i j, ∃ k, S k ⊆ S i ∩ S j := by
    intro i j
    obtain ⟨k, hk⟩ := hdir i j
    refine ⟨k, ?_⟩
    rintro x ⟨⟨hxU, hxC⟩, hxI⟩
    exact ⟨⟨⟨hxU, (hk hxC).1⟩, hxI⟩, ⟨⟨hxU, (hk hxC).2⟩, hxI⟩⟩
  obtain ⟨x, hx⟩ :=
    inter_directed_compact S hSdir hnonempty hcompact
  have hxall : x ∈ ⋂ i, C i :=
    Set.mem_iInter.mpr fun i ↦ (Set.mem_iInter.mp hx i).1.2
  have hxnotI : x ∉ I := (Set.mem_iInter.mp hx (Classical.choice inferInstance)).2
  exact hxnotI (hcore ⟨(Set.mem_iInter.mp hx (Classical.choice inferInstance)).1.1, hxall⟩)

variable {Z : Type u} [CommGroup Z]

/-- Subgroup form of the compactness argument used in the proof of Theorem
III.5.1. -/
theorem inf_directed_core
    [TopologicalSpace Z] [T2Space Z]
    {ι : Type v} [Nonempty ι]
    (U I : Subgroup Z) (N : ι → Subgroup Z)
    (hU : IsCompact (U : Set Z)) (hI : IsOpen (I : Set Z))
    (hN : ∀ i, IsClosed (N i : Set Z))
    (hdir : ∀ i j, ∃ k, N k ≤ N i ⊓ N j)
    (hcore : familyCore N ≤ I) :
    ∃ i, N i ⊓ U ≤ I := by
  obtain ⟨i, hi⟩ := inter_compact_directed
    (U : Set Z) (I : Set Z) (fun i ↦ (N i : Set Z)) hU hI hN
    (fun i j ↦ by
      obtain ⟨k, hk⟩ := hdir i j
      exact ⟨k, fun _ hx ↦ ⟨(hk hx).1, (hk hx).2⟩⟩)
    (by
      rintro x ⟨hxU, hxN⟩
      apply hcore
      rw [familyCore, Subgroup.mem_iInf]
      exact Set.mem_iInter.mp hxN)
  exact ⟨i, fun _ hx ↦ hi ⟨hx.2, hx.1⟩⟩

end Submission.CField.LExist

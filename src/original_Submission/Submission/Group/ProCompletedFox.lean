import Submission.Group.HilbertJenningsFox
import Submission.Group.ProPPresentation
import Submission.Group.CompletedRelationModule

/-!
# Completed group-algebra Fox inequality for free pro-p presentations

This file isolates the direct completed-group-algebra input needed by the HMR
cutting argument.  The theorem below is the topological analogue of the
ordinary filtered Fox relation-module estimate: closed normal generation by
relators of specified Zassenhaus depths gives the corresponding
prefix-rank Vinberg inequality in every degree.
-/

open scoped BigOperators

noncomputable section

namespace Submission
namespace ProP

universe u

/-- The cumulative augmentation-layer rank through degree `n` for a finite
group algebra.  This is the coefficient sequence in the filtered Vinberg
recurrence. -/
def completedPrefixRank
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    GroupAlgebra.augmentationLayerRank (ZMod p) Q k

/-- The completed group-algebra prefix-rank sequence starts at one. -/
@[simp] theorem completed_prefix_rank
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] :
    completedPrefixRank p Q 0 = 1 := by
  simp [completedPrefixRank,
    GroupAlgebra.augmentation_rank_zero]

/-- In particular, the completed group-algebra prefix-rank sequence starts
positively. -/
theorem completed_rank_pos
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] :
    0 < completedPrefixRank p Q 0 := by
  simp

/-- For a finite group, every augmentation-layer prefix rank is bounded by the
cardinality of the group. -/
theorem completed_rank_upper
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] [Finite Q] :
    FPres.SUBound
      (completedPrefixRank p Q) (Nat.card Q) := by
  letI := Fintype.ofFinite Q
  intro n
  simpa [completedPrefixRank,
    Nat.card_eq_fintype_card] using
    (GroupAlgebra.sum_layer_card (K := ZMod p) (G := Q) (n + 1))

/--
The completed-group-algebra Fox/Hilbert Vinberg inequality for a finite quotient
of a free pro-`p` group.

The proof should pass from closed normal generation to the completed relation
ideal, reduce modulo the next augmentation power, and apply continuous Fox
derivatives.  The filtered form uses cumulative augmentation-layer ranks.  The
finite target makes each finite layer discrete, so topological closure does not
enlarge its image.
-/
theorem completed_fox_inequality
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (_quotientMap_continuous : Continuous quotientMap)
    (_quotientMap_surjective : Function.Surjective quotientMap)
    {ι : Type u} [Fintype ι]
    (relator : ι → F.Carrier)
    (_kernel_eq :
      MonoidHom.ker quotientMap =
        (Subgroup.normalClosure (Set.range relator)).topologicalClosure)
    (depth : ι → ℕ)
    (_relator_depth :
      ∀ r, relator r ∈
        (zassenhausFiltration p F.Carrier (depth r)).topologicalClosure)
    (n : ℕ) :
    d *
        (if 1 ≤ n then
          completedPrefixRank p Q (n - 1)
        else 0) ≤
      completedPrefixRank p Q n +
        ∑ r : ι,
          if depth r ≤ n then
            completedPrefixRank p Q (n - depth r)
          else 0 := by
  by_cases hn : 1 ≤ n
  · let D : CFDatum
        F quotientMap relator depth n :=
      Classical.choice
        (nonempty_datum_generation
          F quotientMap _quotientMap_continuous _quotientMap_surjective
          relator _kernel_eq depth _relator_depth n)
    have h :=
      completed_guarded_relator
        D
    have hprefix :
        ∀ m,
          completedPrefixRank p Q m =
            Module.finrank (ZMod p)
              (completedFoxTruncation p Q (m + 1)) := by
      intro m
      exact
        GroupAlgebra.rank_truncation_finrank
          (K := ZMod p) (G := Q) (m + 1)
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [if_pos hn, hprefix (n - 1), hprefix n]
    simp_rw [hprefix]
    rw [hnsub]
    exact h
  · simp [if_neg hn]

end ProP
end Submission

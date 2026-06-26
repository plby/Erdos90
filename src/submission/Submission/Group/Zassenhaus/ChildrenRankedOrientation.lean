import Submission.Group.Zassenhaus.ChildrenJacobiOrientation
import Submission.Group.Zassenhaus.Jacobi


/-!
# Ranked Hall orientation for power Jacobi frontiers with basic children

The ordinary two-basic-child orientation layer remembers only which child is
an exposed commutator. Ranked descendant scheduling needs the inequalities
proved at the same time: after choosing the left-normed orientation
`[[a, b], v]`, one has `v < b < a`.

This file preserves that stronger Hall certificate and compiles either
orientation into the ranked expanded-Jacobi decomposition consumed by
reachable descendant scheduling.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u

/--
A two-basic-child Jacobi frontier oriented as `[[a, b], v]`, retaining the
strict inequalities needed by ranked descendant recursion.
-/
inductive RankedJacobiOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d)) where
  | left
      (left₁ left₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : left = .commutator left₁ left₂)
      (right_lt_left₂ : right < left₂)
      (left₂_lt_left₁ : left₂ < left₁)
      (left₁_isBasic : left₁.IsBasic)
      (left₂_isBasic : left₂.IsBasic)
  | right
      (right₁ right₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : right = .commutator right₁ right₂)
      (left_lt_right₂ : left < right₂)
      (right₂_lt_right₁ : right₂ < right₁)
      (right₁_isBasic : right₁.IsBasic)
      (right₂_isBasic : right₂.IsBasic)

/--
Hall admissibility orients every two-basic-child frontier while preserving
the inequalities discarded by the earlier shape-only dispatcher.
-/
theorem nonempty_children_orientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    Nonempty (RankedJacobiOrientation left right) := by
  rcases
      HallTree.inadmissible_orientation_children
        left right hleftBasic hrightBasic hchildrenNe hforwardNonbasic
          hreverseNonbasic with
    hleft | hright
  · rcases hleft with ⟨left₁, left₂, hleft, _hrightLeft, hbad⟩
    have hleftBasic' : (HallTree.commutator left₁ left₂).IsBasic := by
      simpa only [hleft] using hleftBasic
    rcases (HallTree.isBasic_commutator left₁ left₂).mp hleftBasic' with
      ⟨hleft₁Basic, hleft₂Basic, hleft₂Left₁, _hadmissible⟩
    exact
      ⟨.left left₁ left₂ hleft (lt_of_not_ge hbad) hleft₂Left₁
        hleft₁Basic hleft₂Basic⟩
  · rcases hright with ⟨right₁, right₂, hright, _hleftRight, hbad⟩
    have hrightBasic' : (HallTree.commutator right₁ right₂).IsBasic := by
      simpa only [hright] using hrightBasic
    rcases (HallTree.isBasic_commutator right₁ right₂).mp hrightBasic' with
      ⟨hright₁Basic, hright₂Basic, hright₂Right₁, _hadmissible⟩
    exact
      ⟨.right right₁ right₂ hright (lt_of_not_ge hbad) hright₂Right₁
        hright₁Basic hright₂Basic⟩

/-- Choose the ranked Hall orientation of a two-basic-child frontier. -/
noncomputable def childrenRankedOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    RankedJacobiOrientation left right :=
  Classical.choice
    (nonempty_children_orientation left right hleftBasic
      hrightBasic hchildrenNe hforwardNonbasic hreverseNonbasic)

/--
Ranked expanded-Jacobi data after orienting a two-basic-child frontier.
The reversed case carries the sign-corrected swapped factor.
-/
inductive CRDispat
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) where
  | forward
      (ranked :
        TRDecomp
          factor)
  | swapped
      (ranked :
        TRDecomp
          (childrenSwapFactor factor left right hleftBasic hrightBasic
            htree))

namespace CRDispat

/-- Forward dispatch retains the incoming symmetric bracket-rank defect. -/
theorem forward_rank_defect
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (_hleftBasic : left.IsBasic)
    (_hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (ranked :
      TRDecomp
        factor) :
    expandedParentDefect ranked.decomposition =
      HallTree.bracketRankDefect
        (left.weight + right.weight) left right := by
  have hroot :
      HallTree.commutator left right =
        .commutator
          (.commutator
            (tree ranked.decomposition.left)
            (tree ranked.decomposition.middle))
          (tree ranked.decomposition.right) := by
    rw [← htree, ranked.decomposition.tree_eq]
  injection hroot with hleft hright
  simp only [expandedParentDefect]
  rw [← hleft, ← hright]
  simp only [tree_commutator, ← hleft]

/-- Swapped dispatch retains the incoming symmetric bracket-rank defect. -/
theorem swapped_rank_defect
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (ranked :
      TRDecomp
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree)) :
    expandedParentDefect ranked.decomposition =
      HallTree.bracketRankDefect
        (left.weight + right.weight) left right := by
  have hroot :
      HallTree.commutator right left =
        .commutator
          (.commutator
            (tree ranked.decomposition.left)
            (tree ranked.decomposition.middle))
          (tree ranked.decomposition.right) := by
    rw [← tree_children_swap factor left right hleftBasic
      hrightBasic htree, ranked.decomposition.tree_eq]
  injection hroot with hright hleft
  simp only [expandedParentDefect]
  rw [← hright, ← hleft]
  simp only [tree_commutator, ← hright,
    HallTree.bracketRankDefect, min_comm, add_comm]

end CRDispat

open TRDecomp

/--
Compile the ranked Hall orientation into forward or sign-corrected swapped
expanded-Jacobi data.
-/
noncomputable def childrenJacobiDispatch
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    CRDispat factor left right hleftBasic hrightBasic
      htree := by
  let orientation :=
    childrenRankedOrientation left right hleftBasic hrightBasic
      hchildrenNe hforwardNonbasic hreverseNonbasic
  cases orientation with
  | left left₁ left₂ hleft hrightLeft₂ hleft₂Left₁ hleft₁Basic
      hleft₂Basic =>
      exact
        .forward
          (nonbasic_commutator_tree
            factor left₁ left₂ right
              (by simpa only [hleft] using htree)
              (by simpa only [hleft] using hforwardNonbasic)
              hrightLeft₂ hleft₂Left₁ hleft₁Basic hleft₂Basic)
  | right right₁ right₂ hright hleftRight₂ hright₂Right₁ hright₁Basic
      hright₂Basic =>
      exact
        .swapped
          (nonbasic_commutator_tree
            (childrenSwapFactor factor left right hleftBasic hrightBasic
              htree)
            right₁ right₂ left
              (by simp only [tree_children_swap, hright])
              (by simpa only [hright] using hreverseNonbasic)
              hleftRight₂ hright₂Right₁ hright₁Basic hright₂Basic)

end TCTex
end Submission

import Towers.Group.HallBasic.Word
import Towers.Group.HallBasic.LowerLieBridge


noncomputable section

namespace Towers
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The canonical indexed form of the recursive decomposition of a non-atomic
basic Hall tree.  The two children are again canonically indexed basic trees
of strictly smaller positive weights.
-/
structure IBDecomp
    {r : ℕ}
    (i : BasicIndex (α := α) r) where
  leftWeight : ℕ
  rightWeight : ℕ
  leftIndex : BasicIndex (α := α) leftWeight
  rightIndex : BasicIndex (α := α) rightWeight
  leftWeight_pos : 0 < leftWeight
  rightWeight_pos : 0 < rightWeight
  weight_add : leftWeight + rightWeight = r
  tree_eq :
    indexedBasicTree i =
      commutator (indexedBasicTree leftIndex) (indexedBasicTree rightIndex)
  right_lt_left : indexedBasicTree rightIndex < indexedBasicTree leftIndex
  admissible :
    match indexedBasicTree leftIndex with
    | atom _ => True
    | commutator _ leftRight => leftRight ≤ indexedBasicTree rightIndex

/-- The left child in an indexed Hall decomposition has smaller weight. -/
theorem IBDecomp.leftWeight_lt
    {r : ℕ}
    {i : BasicIndex (α := α) r}
    (D : IBDecomp i) :
    D.leftWeight < r := by
  have := D.weight_add
  have := D.rightWeight_pos
  omega

/-- The right child in an indexed Hall decomposition has smaller weight. -/
theorem IBDecomp.rightWeight_lt
    {r : ℕ}
    {i : BasicIndex (α := α) r}
    (D : IBDecomp i) :
    D.rightWeight < r := by
  have := D.weight_add
  have := D.leftWeight_pos
  omega

/-- Every canonical Hall index has positive weight. -/
theorem basic_index_pos
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    0 < r := by
  simpa only [← indexed_tree_weight i] using (indexedBasicTree i).weight_pos

/-- Every canonical Hall index has weight one or weight strictly above one. -/
theorem basic_index_or
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    r = 1 ∨ 1 < r := by
  have := basic_index_pos i
  omega

/--
Every canonical basic Hall tree of weight above one decomposes into canonical
basic Hall trees of smaller weights, retaining the Hall inequalities.
-/
theorem nonempty_indexed_decomposition
    {r : ℕ}
    (i : BasicIndex (α := α) r)
    (hr : 1 < r) :
    Nonempty (IBDecomp i) := by
  have hbasic := indexed_tree i
  have hweight := indexed_tree_weight i
  cases htree : indexedBasicTree i with
  | atom a =>
      rw [htree, weight_atom] at hweight
      omega
  | commutator u v =>
      rw [htree] at hbasic hweight
      rcases (isBasic_commutator u v).mp hbasic with
        ⟨huBasic, hvBasic, hvu, hadmissible⟩
      obtain ⟨leftIndex, hleft⟩ :=
        indexed_basic_tree huBasic rfl
      obtain ⟨rightIndex, hright⟩ :=
        indexed_basic_tree hvBasic rfl
      refine ⟨{
        leftWeight := u.weight
        rightWeight := v.weight
        leftIndex := leftIndex
        rightIndex := rightIndex
        leftWeight_pos := u.weight_pos
        rightWeight_pos := v.weight_pos
        weight_add := ?_
        tree_eq := ?_
        right_lt_left := ?_
        admissible := ?_ }⟩
      · simpa only [weight_commutator] using hweight
      · simpa only [hleft, hright] using htree
      · simpa only [hleft, hright] using hvu
      · simpa only [hleft, hright] using hadmissible

/--
A chosen recursive decomposition for a canonical basic Hall tree of weight
above one.
-/
noncomputable def indexedBasicDecomposition
    {r : ℕ}
    (i : BasicIndex (α := α) r)
    (hr : 1 < r) :
    IBDecomp i :=
  Classical.choice (nonempty_indexed_decomposition i hr)

/--
Strong induction over canonical basic Hall trees.  The commutator step receives
the indexed recursive decomposition and induction hypotheses for both children.
-/
theorem indexed_strong_induction
    (P : ∀ r : ℕ, BasicIndex (α := α) r → Prop)
    (hatom : ∀ i : BasicIndex (α := α) 1, P 1 i)
    (hcommutator :
      ∀ {r : ℕ} (i : BasicIndex (α := α) r) (_hr : 1 < r)
        (D : IBDecomp i),
        P D.leftWeight D.leftIndex →
        P D.rightWeight D.rightIndex →
        P r i) :
    ∀ {r : ℕ} (i : BasicIndex (α := α) r), P r i := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro i
      rcases basic_index_or i with rfl | hr
      · exact hatom i
      · let D := indexedBasicDecomposition i hr
        exact hcommutator i hr D
          (ih D.leftWeight D.leftWeight_lt D.leftIndex)
          (ih D.rightWeight D.rightWeight_lt D.rightIndex)

end HallTree
end Towers


/-!
# Recursive graded evaluation of indexed Hall trees

The canonical indexed Hall decomposition has strictly smaller indexed
children.  This file records that its evaluation in the free-group
lower-central associated graded is the bracket of the evaluations of those
children.  It is intentionally not imported by the existing collection
proof.
-/

noncomputable section

namespace Towers
namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/-- Fixed-weight Hall classes are insensitive to a proof-preserving tree equality. -/
theorem free_lower_tree
    {w v : HallTree α}
    {n : ℕ}
    (h : w = v)
    (hw : w.weight = n)
    (hv : v.weight = n) :
    w.freeLowerWeight hw =
      v.freeLowerWeight hv := by
  subst v
  rfl

variable [Fintype α] [DecidableEq α] [Encodable α]

/-- The child degrees of an indexed Hall decomposition add to the parent degree. -/
theorem IBDecomp.lower_bracket_degree
    {r : ℕ}
    {i : BasicIndex (α := α) r}
    (D : IBDecomp i) :
    (D.leftWeight - 1) + (D.rightWeight - 1) + 1 = r - 1 := by
  have := D.leftWeight_pos
  have := D.rightWeight_pos
  have := D.weight_add
  omega

/--
The two indexed children in a canonical decomposition bracket to the parent's
weight.
-/
theorem IBDecomp.commutator_weight_eq
    {r : ℕ}
    {i : BasicIndex (α := α) r}
    (D : IBDecomp i) :
    (commutator
      (indexedBasicTree D.leftIndex)
      (indexedBasicTree D.rightIndex)).weight = r := by
  simpa only [weight_commutator, indexed_tree_weight] using D.weight_add

/--
The fixed-weight lower-central class of an indexed Hall tree is the graded
bracket of the classes of the two indexed children in any canonical
decomposition.
-/
theorem indexed_free_bracket
    {r : ℕ}
    {i : BasicIndex (α := α) r}
    (D : IBDecomp i) :
    (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) =
      lowerBracketClass
        ((indexedBasicTree D.leftIndex).weight - 1)
        ((indexedBasicTree D.rightIndex).weight - 1)
        (r - 1)
        (by
          simpa only [indexed_tree_weight] using
            D.lower_bracket_degree)
        (indexedBasicTree D.leftIndex).freeCentralLayer
        (indexedBasicTree D.rightIndex).freeCentralLayer := by
  calc
    _ = (commutator
          (indexedBasicTree D.leftIndex)
          (indexedBasicTree D.rightIndex)).freeLowerWeight
          D.commutator_weight_eq :=
      free_lower_tree
        D.tree_eq (indexed_tree_weight i) D.commutator_weight_eq
    _ = _ :=
      free_central_commutator
        (indexedBasicTree D.leftIndex)
        (indexedBasicTree D.rightIndex)
        D.commutator_weight_eq

/--
Every indexed Hall class above weight one is a bracket of indexed Hall classes
of strictly smaller positive weights.
-/
theorem indexed_tree_bracket
    {r : ℕ}
    (i : BasicIndex (α := α) r)
    (hr : 1 < r) :
    let D := indexedBasicDecomposition i hr
    (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) =
      lowerBracketClass
        ((indexedBasicTree D.leftIndex).weight - 1)
        ((indexedBasicTree D.rightIndex).weight - 1)
        (r - 1)
        (by
          simpa only [indexed_tree_weight] using
            D.lower_bracket_degree)
        (indexedBasicTree D.leftIndex).freeCentralLayer
        (indexedBasicTree D.rightIndex).freeCentralLayer := by
  exact indexed_free_bracket
    (indexedBasicDecomposition i hr)

end HallTree
end Towers


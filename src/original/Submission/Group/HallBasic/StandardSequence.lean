import Submission.Group.HallBasic.RecursiveCoefficientSplitting
import Mathlib.Data.List.Shortlex
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Set.Finite.List
import Submission.Group.HallBasic.Word
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Submission.Group.HallBasic.AssociatedGradedSpanning
import Submission.Group.HallBasic.ConcreteBasisBridge
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.List.Infix
import Mathlib.LinearAlgebra.Finsupp.Supported


open Submission.TCTex
open scoped IsMulCommutative

/-!
# Standard sequences for Hall collection

The classical Hall basis argument collects lists of basic trees.  A standard
sequence records the right-factor inequalities that make every legal adjacent
drop into another basic Hall tree.  The associative polynomial identity for a
drop is the PBW-style collection step.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/--
A Hall standard sequence: every entry is basic, and the right child of each
composite entry is bounded above by every later entry.
-/
def ISSequen : List (HallTree α) → Prop
  | [] => True
  | w :: tail =>
      w.IsBasic ∧
        (match w with
        | atom _ => True
        | commutator _ right => ∀ x ∈ tail, right ≤ x) ∧
        ISSequen tail

@[simp] theorem standard_nil :
    ISSequen ([] : List (HallTree α)) :=
  trivial

@[simp] theorem standard_atom_cons
    (a : α)
    (tail : List (HallTree α)) :
    ISSequen (atom a :: tail) ↔ ISSequen tail := by
  simp [ISSequen]

@[simp] theorem standard_sequence_cons
    (left right : HallTree α)
    (tail : List (HallTree α)) :
    ISSequen (commutator left right :: tail) ↔
      (commutator left right).IsBasic ∧
        (∀ x ∈ tail, right ≤ x) ∧
        ISSequen tail := by
  rfl

theorem ISSequen.head_isBasic
    {w : HallTree α}
    {tail : List (HallTree α)}
    (h : ISSequen (w :: tail)) :
    w.IsBasic :=
  h.1

theorem ISSequen.tail
    {w : HallTree α}
    {tail : List (HallTree α)}
    (h : ISSequen (w :: tail)) :
    ISSequen tail :=
  h.2.2

theorem ISSequen.mem_isBasic
    {sequence : List (HallTree α)}
    (h : ISSequen sequence)
    {w : HallTree α}
    (hw : w ∈ sequence) :
    w.IsBasic := by
  induction sequence with
  | nil => simp at hw
  | cons head tail ih =>
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h.head_isBasic
      · exact ih h.tail hw

/-- Each child is strictly smaller than its composite Hall tree. -/
theorem lt_commutator_left
    (u v : HallTree α) :
    u < commutator u v := by
  apply lt_weight_lt
  simp only [weight_commutator]
  exact Nat.lt_add_of_pos_right v.weight_pos

/-- Each child is strictly smaller than its composite Hall tree. -/
theorem lt_commutator_right
    (u v : HallTree α) :
    v < commutator u v := by
  apply lt_weight_lt
  simp only [weight_commutator]
  exact Nat.lt_add_of_pos_left u.weight_pos

/--
In a standard sequence, a descending first pair has a basic Hall commutator.
-/
theorem ISSequen.comm_head_basicdrop
    {u v : HallTree α}
    {tail : List (HallTree α)}
    (h : ISSequen (u :: v :: tail))
    (hvu : v < u) :
    (commutator u v).IsBasic := by
  refine basic_commutator_admissible
    (u := u) (v := v) h.head_isBasic h.tail.head_isBasic hvu ?_
  cases u with
  | atom a => trivial
  | commutator left right =>
      exact h.2.1 v (by simp)

/--
Swapping a descending first pair preserves the standard-sequence invariant.
-/
theorem ISSequen.swap_head_drop
    {u v : HallTree α}
    {tail : List (HallTree α)}
    (h : ISSequen (u :: v :: tail))
    (hvu : v < u) :
    ISSequen (v :: u :: tail) := by
  refine ⟨h.tail.head_isBasic, ?_, ?_⟩
  · cases v with
    | atom a => trivial
    | commutator left right =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (lt_commutator_right left right).trans hvu |>.le
        · exact h.tail.2.1 x hx
  · refine ⟨h.head_isBasic, ?_, h.tail.tail⟩
    cases u with
    | atom a => trivial
    | commutator left right =>
        intro x hx
        exact h.2.1 x (by simp [hx])

/--
Merging a descending first pair preserves standardness when the smaller entry
is bounded above by the untouched tail.
-/
theorem ISSequen.merge_head_drop
    {u v : HallTree α}
    {tail : List (HallTree α)}
    (h : ISSequen (u :: v :: tail))
    (hvu : v < u)
    (hvTail : ∀ x ∈ tail, v ≤ x) :
    ISSequen (commutator u v :: tail) := by
  exact
    ⟨h.comm_head_basicdrop hvu,
      hvTail,
      h.tail.tail⟩

/-- Product of the associative Hall polynomials along a tree sequence. -/
noncomputable def associativeWordProduct
    (R : Type*) [CommRing R] :
    List (HallTree α) → AssociativeWordPolynomial R α
  | [] => 1
  | w :: tail =>
      w.associativeWordPolynomial R *
        associativeWordProduct R tail

omit [Encodable α] in
@[simp] theorem associative_product_nil
    (R : Type*) [CommRing R] :
    associativeWordProduct (α := α) R [] = 1 :=
  rfl

omit [Encodable α] in
@[simp] theorem associative_product_cons
    (R : Type*) [CommRing R]
    (w : HallTree α)
    (tail : List (HallTree α)) :
    associativeWordProduct R (w :: tail) =
      w.associativeWordPolynomial R *
        associativeWordProduct R tail :=
  rfl

omit [Encodable α] in
@[simp] theorem associative_product_append
    (R : Type*) [CommRing R]
    (xs ys : List (HallTree α)) :
    associativeWordProduct R (xs ++ ys) =
      associativeWordProduct R xs *
        associativeWordProduct R ys := by
  induction xs with
  | nil => simp
  | cons w xs ih =>
      simp only [List.cons_append, associative_product_cons, ih]
      rw [mul_assoc]

omit [Encodable α] in
/--
The associative collection identity for one adjacent drop:
`uv = vu + [u,v]`.
-/
theorem associative_product_drop
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (tail : List (HallTree α)) :
    associativeWordProduct R (u :: v :: tail) =
      associativeWordProduct R (v :: u :: tail) +
        associativeWordProduct R (commutator u v :: tail) := by
  simp only [associative_product_cons,
    associative_word_commutator]
  noncomm_ring

omit [Encodable α] in
/-- The same collection identity inside an arbitrary left context. -/
theorem associative_drop_context
    (R : Type*) [CommRing R]
    (xs : List (HallTree α))
    (u v : HallTree α)
    (tail : List (HallTree α)) :
    associativeWordProduct R (xs ++ u :: v :: tail) =
      associativeWordProduct R (xs ++ v :: u :: tail) +
        associativeWordProduct R
          (xs ++ commutator u v :: tail) := by
  simp only [associative_product_append]
  rw [associative_product_drop]
  noncomm_ring

end HallTree
end Submission


/-!
# Collection steps for Hall standard sequences

This file isolates the list-ordering layer of the classical Hall collection
argument.  Ordered basic sequences are standard, and every non-ordered
sequence has a rightmost adjacent drop.  Swapping or merging that drop
preserves standardness even inside an arbitrary left context.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/-- A sequence is ordered when its Hall trees occur in nondecreasing order. -/
def IsOrderedSequence (sequence : List (HallTree α)) : Prop :=
  sequence.Pairwise (· ≤ ·)

/-- An ordered sequence of basic Hall trees is a standard sequence. -/
theorem standard_sequence_forall
    {sequence : List (HallTree α)}
    (hbasic : ∀ w ∈ sequence, w.IsBasic)
    (hordered : IsOrderedSequence sequence) :
    ISSequen sequence := by
  induction sequence with
  | nil => simp
  | cons w tail ih =>
      rw [IsOrderedSequence, List.pairwise_cons] at hordered
      refine ⟨hbasic w (by simp), ?_, ih ?_ hordered.2⟩
      · cases w with
        | atom a => trivial
        | commutator left right =>
            intro x hx
            exact (lt_commutator_right left right).le.trans
              (hordered.1 x hx)
      · intro x hx
        exact hbasic x (by simp [hx])

/--
Swapping a descending adjacent pair preserves standardness inside an
arbitrary left context.
-/
theorem ISSequen.swap_drop_incontext
    {xs : List (HallTree α)}
    {u v : HallTree α}
    {tail : List (HallTree α)}
    (h : ISSequen (xs ++ u :: v :: tail))
    (hvu : v < u) :
    ISSequen (xs ++ v :: u :: tail) := by
  induction xs with
  | nil =>
      simpa using h.swap_head_drop hvu
  | cons head xs ih =>
      refine ⟨h.head_isBasic, ?_, ih h.tail⟩
      cases head with
      | atom a => trivial
      | commutator left right =>
          intro x hx
          apply h.2.1 x
          apply List.mem_append.mpr
          rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (by
              simp only [List.mem_cons] at hx ⊢
              tauto)

/--
Merging a descending adjacent pair preserves standardness inside an
arbitrary left context when the smaller entry is bounded by the untouched
suffix.
-/
theorem ISSequen.merge_drop_incontext
    {xs : List (HallTree α)}
    {u v : HallTree α}
    {tail : List (HallTree α)}
    (h : ISSequen (xs ++ u :: v :: tail))
    (hvu : v < u)
    (hvTail : ∀ x ∈ tail, v ≤ x) :
    ISSequen (xs ++ commutator u v :: tail) := by
  induction xs with
  | nil =>
      simpa using h.merge_head_drop hvu hvTail
  | cons head xs ih =>
      refine ⟨h.head_isBasic, ?_, ih h.tail⟩
      cases head with
      | atom a => trivial
      | commutator left right =>
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact h.2.1 x (List.mem_append.mpr (Or.inl hx))
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact
                (h.2.1 u
                    (List.mem_append.mpr (Or.inr (by simp)))).trans
                  (lt_commutator_left u v).le
            · exact h.2.1 x
                (List.mem_append.mpr (Or.inr (by simp [hx])))

/--
Every non-ordered sequence contains a rightmost adjacent drop.  The suffix
to the right of that drop is ordered, so the smaller entry is bounded above
by each untouched suffix entry.
-/
theorem rightmost_drop_not
    {sequence : List (HallTree α)}
    (h : ¬ IsOrderedSequence sequence) :
    ∃ xs u v tail,
      sequence = xs ++ u :: v :: tail ∧
        v < u ∧
        IsOrderedSequence (v :: tail) := by
  induction sequence with
  | nil => simp [IsOrderedSequence] at h
  | cons u sequence ih =>
      cases sequence with
      | nil => simp [IsOrderedSequence] at h
      | cons v tail =>
          by_cases htail : IsOrderedSequence (v :: tail)
          · have hvu : v < u := by
              have htail' := htail
              rw [IsOrderedSequence, List.pairwise_cons] at htail'
              apply lt_of_not_ge
              intro huv
              apply h
              rw [IsOrderedSequence, List.pairwise_cons]
              refine ⟨?_, htail⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact huv
              · exact huv.trans (htail'.1 x hx)
            exact ⟨[], u, v, tail, by simp, hvu, htail⟩
          · rcases ih htail with ⟨xs, left, right, suffix, heq, hdrop, hsuffix⟩
            exact ⟨u :: xs, left, right, suffix, by simp [heq], hdrop, hsuffix⟩

/--
The rightmost drop decomposition supplies the tail inequality needed by the
merge collection step.
-/
theorem rightmost_drop_bound
    {sequence : List (HallTree α)}
    (h : ¬ IsOrderedSequence sequence) :
    ∃ xs u v tail,
      sequence = xs ++ u :: v :: tail ∧
        v < u ∧
        (∀ x ∈ tail, v ≤ x) := by
  rcases rightmost_drop_not h with
    ⟨xs, u, v, tail, rfl, hvu, hordered⟩
  rw [IsOrderedSequence, List.pairwise_cons] at hordered
  exact ⟨xs, u, v, tail, rfl, hvu, hordered.1⟩

/--
The Hall order is well-founded: it is the order induced by the lexicographic
natural-number key `(weight, encoding)`.
-/
theorem lt_wellFounded :
    WellFounded (· < · : HallTree α → HallTree α → Prop) := by
  exact InvImage.wf orderKey wellFounded_lt

/--
Shortlex order is the collection recursion order.  A merge decreases length,
while a swap at the chosen drop preserves length and decreases lexicographic
order.
-/
def CollectionBefore :
    List (HallTree α) → List (HallTree α) → Prop :=
  List.Shortlex (· < ·)

/-- Hall collection shortlex order is well-founded. -/
theorem before_well_founded :
    WellFounded (CollectionBefore (α := α)) :=
  List.Shortlex.wf lt_wellFounded

/-- Swapping a descending adjacent pair strictly decreases collection order. -/
theorem collection_before_drop
    (xs : List (HallTree α))
    (u v : HallTree α)
    (tail : List (HallTree α))
    (hvu : v < u) :
    CollectionBefore (xs ++ v :: u :: tail) (xs ++ u :: v :: tail) := by
  apply List.Shortlex.append_left
  apply List.Shortlex.of_lex
  · simp
  · exact List.Lex.rel hvu

/-- Merging an adjacent pair strictly decreases collection order. -/
theorem before_merge_drop
    (xs : List (HallTree α))
    (u v : HallTree α)
    (tail : List (HallTree α)) :
    CollectionBefore
      (xs ++ commutator u v :: tail)
      (xs ++ u :: v :: tail) := by
  apply List.Shortlex.of_length_lt
  simp

end HallTree
end Submission


/-!
# A terminating measure for Hall standard-sequence collection

A rightmost Hall drop expands by the PBW identity into a swapped branch and a
merged branch.  The swapped branch has one fewer inversion, while the merged
branch has one fewer list entry.  This file packages those two decreases into
one lexicographic measure, together with the standardness and polynomial
identities needed by a recursive collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/-- Number of descending pairs in a Hall-tree sequence. -/
def standardInversionCount : List (HallTree α) → ℕ
  | [] => 0
  | w :: tail =>
      (tail.filter fun x => x < w).length +
        standardInversionCount tail

/--
Swapping one adjacent descending pair removes exactly one inversion.  Prefix
entries see a permutation of the same suffix, so their contributions are
unchanged.
-/
theorem standard_inversion_drop
    (xs : List (HallTree α))
    (u v : HallTree α)
    (tail : List (HallTree α))
    (hvu : v < u) :
    standardInversionCount (xs ++ v :: u :: tail) + 1 =
      standardInversionCount (xs ++ u :: v :: tail) := by
  induction xs with
  | nil =>
      simp [standardInversionCount, hvu, not_lt_of_ge hvu.le]
      omega
  | cons head xs ih =>
      have hperm :
          (xs ++ v :: u :: tail).Perm (xs ++ u :: v :: tail) :=
        List.Perm.append_left xs (List.Perm.swap u v tail)
      have hfilter :
          ((xs ++ v :: u :: tail).filter fun x => x < head).length =
            ((xs ++ u :: v :: tail).filter fun x => x < head).length :=
        (hperm.filter fun x => x < head).length_eq
      simp only [List.cons_append, standardInversionCount]
      omega

/-- The lexicographic termination measure for Hall standard-sequence collection. -/
def standardSequenceMeasure
    (sequence : List (HallTree α)) :
    ℕ × ℕ :=
  (sequence.length, standardInversionCount sequence)

/-- Swapping a descending pair strictly decreases the collection measure. -/
theorem standard_measure_drop
    (xs : List (HallTree α))
    (u v : HallTree α)
    (tail : List (HallTree α))
    (hvu : v < u) :
    Prod.Lex (· < ·) (· < ·)
      (standardSequenceMeasure (xs ++ v :: u :: tail))
      (standardSequenceMeasure (xs ++ u :: v :: tail)) := by
  have hcount :
      standardInversionCount (xs ++ v :: u :: tail) <
        standardInversionCount (xs ++ u :: v :: tail) := by
    have hcount :=
      standard_inversion_drop xs u v tail hvu
    omega
  simpa [standardSequenceMeasure] using
    (Prod.Lex.right (xs ++ v :: u :: tail).length hcount)

/-- Merging a descending pair strictly decreases the collection measure. -/
theorem measure_merge_drop
    (xs : List (HallTree α))
    (u v : HallTree α)
    (tail : List (HallTree α)) :
    Prod.Lex (· < ·) (· < ·)
      (standardSequenceMeasure
        (xs ++ commutator u v :: tail))
      (standardSequenceMeasure (xs ++ u :: v :: tail)) := by
  have hlength :
      (xs ++ commutator u v :: tail).length <
        (xs ++ u :: v :: tail).length := by
    simp
  exact Prod.Lex.left _ _ hlength

/--
The two smaller standard sequences produced by collecting one rightmost PBW
drop.
-/
structure RDExp
    (sequence : List (HallTree α)) where
  context : List (HallTree α)
  left : HallTree α
  right : HallTree α
  suffix : List (HallTree α)
  source_eq : sequence = context ++ left :: right :: suffix
  drop : right < left
  orderedSuffix : IsOrderedSequence (right :: suffix)

namespace RDExp

/-- The branch obtained by swapping the selected drop. -/
def swapped
    {sequence : List (HallTree α)}
    (drop : RDExp sequence) :
    List (HallTree α) :=
  drop.context ++ drop.right :: drop.left :: drop.suffix

/-- The branch obtained by merging the selected drop into its Hall bracket. -/
def merged
    {sequence : List (HallTree α)}
    (drop : RDExp sequence) :
    List (HallTree α) :=
  drop.context ++ commutator drop.left drop.right :: drop.suffix

/-- The ordered suffix supplies the inequality required by the merge branch. -/
theorem right_suffix
    {sequence : List (HallTree α)}
    (drop : RDExp sequence)
    {x : HallTree α}
    (hx : x ∈ drop.suffix) :
    drop.right ≤ x := by
  have hordered :
      (drop.right :: drop.suffix).Pairwise (· ≤ ·) :=
    drop.orderedSuffix
  rw [List.pairwise_cons] at hordered
  exact hordered.1 x hx

/-- The swapped PBW branch remains a standard sequence. -/
theorem swapped_standard_sequence
    {sequence : List (HallTree α)}
    (drop : RDExp sequence)
    (hstandard : ISSequen sequence) :
    ISSequen drop.swapped := by
  rw [drop.source_eq] at hstandard
  exact hstandard.swap_drop_incontext drop.drop

/-- The merged PBW branch remains a standard sequence. -/
theorem merged_standard_sequence
    {sequence : List (HallTree α)}
    (drop : RDExp sequence)
    (hstandard : ISSequen sequence) :
    ISSequen drop.merged := by
  rw [drop.source_eq] at hstandard
  exact hstandard.merge_drop_incontext drop.drop fun x hx =>
    drop.right_suffix hx

/-- The swapped PBW branch is smaller in the collection measure. -/
theorem swapped_measure_lt
    {sequence : List (HallTree α)}
    (drop : RDExp sequence) :
    Prod.Lex (· < ·) (· < ·)
      (standardSequenceMeasure drop.swapped)
      (standardSequenceMeasure sequence) := by
  obtain ⟨context, left, right, suffix, rfl, hdrop, _⟩ := drop
  exact standard_measure_drop
    context left right suffix hdrop

/-- The merged PBW branch is smaller in the collection measure. -/
theorem merged_measure_lt
    {sequence : List (HallTree α)}
    (drop : RDExp sequence) :
    Prod.Lex (· < ·) (· < ·)
      (standardSequenceMeasure drop.merged)
      (standardSequenceMeasure sequence) := by
  obtain ⟨context, left, right, suffix, rfl, _, _⟩ := drop
  exact measure_merge_drop
    context left right suffix

/-- The source polynomial is the sum of its two smaller PBW branches. -/
theorem associative_word_product
    {sequence : List (HallTree α)}
    (drop : RDExp sequence)
    (R : Type*) [CommRing R] :
    associativeWordProduct R sequence =
      associativeWordProduct R drop.swapped +
        associativeWordProduct R drop.merged := by
  obtain ⟨context, left, right, suffix, rfl, _, _⟩ := drop
  exact associative_drop_context
    R context left right suffix

end RDExp

/-- Every unordered sequence supplies one terminating rightmost PBW expansion. -/
theorem rightmost_drop_sequence
    {sequence : List (HallTree α)}
    (h : ¬ IsOrderedSequence sequence) :
    Nonempty (RDExp sequence) := by
  rcases rightmost_drop_not h with
    ⟨context, left, right, suffix, source_eq, drop, orderedSuffix⟩
  exact ⟨{
    context := context
    left := left
    right := right
    suffix := suffix
    source_eq := source_eq
    drop := drop
    orderedSuffix := orderedSuffix }⟩

end HallTree
end Submission


/-!
# Finite ordered PBW expansions of Hall standard sequences

The rightmost-drop measure gives an executable Hall collection recursion.
Each unordered sequence expands into its swapped branch and its merged branch;
both are smaller.  The resulting finite list consists of ordered sequences,
and the sum of their associative Hall-polynomial products is the original
sequence product.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

attribute [local instance] Classical.propDecidable

/--
Collect one Hall-tree sequence into finitely many ordered PBW monomials,
retaining repetitions as their natural positive coefficients.
-/
noncomputable def standardSequenceExpansion
    (sequence : List (HallTree α)) :
    List (List (HallTree α)) := by
  classical
  exact
    if hordered : IsOrderedSequence sequence then
      [sequence]
    else
      let drop :=
        Classical.choice
          (rightmost_drop_sequence hordered)
      standardSequenceExpansion drop.swapped ++
        standardSequenceExpansion drop.merged
termination_by standardSequenceMeasure sequence
decreasing_by
  · exact drop.swapped_measure_lt
  · exact drop.merged_measure_lt

/-- Sum of associative Hall-polynomial products over a finite PBW expansion. -/
noncomputable def associativeProductSum
    (R : Type*) [CommRing R] :
    List (List (HallTree α)) → AssociativeWordPolynomial R α
  | [] => 0
  | sequence :: sequences =>
      associativeWordProduct R sequence +
        associativeProductSum R sequences

omit [Encodable α] in
@[simp]
theorem associative_sum_nil
    (R : Type*) [CommRing R] :
    associativeProductSum (α := α) R [] = 0 :=
  rfl

omit [Encodable α] in
@[simp]
theorem associative_sum_cons
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α))
    (sequences : List (List (HallTree α))) :
    associativeProductSum R (sequence :: sequences) =
      associativeWordProduct R sequence +
        associativeProductSum R sequences :=
  rfl

omit [Encodable α] in
@[simp]
theorem associative_sum_append
    (R : Type*) [CommRing R]
    (left right : List (List (HallTree α))) :
    associativeProductSum R (left ++ right) =
      associativeProductSum R left +
        associativeProductSum R right := by
  induction left with
  | nil =>
      simp
  | cons sequence left ih =>
      simp only [List.cons_append, associative_sum_cons, ih]
      abel

/-- Every sequence emitted by Hall PBW collection is ordered. -/
theorem sequence_standard_expansion
    (sequence : List (HallTree α))
    {ordered : List (HallTree α)}
    (hordered : ordered ∈ standardSequenceExpansion sequence) :
    IsOrderedSequence ordered := by
  rw [standardSequenceExpansion] at hordered
  split at hordered
  next hsequence =>
    have heq : ordered = sequence := by
      simpa only [List.mem_singleton] using hordered
    simpa [heq] using hsequence
  next hsequence =>
    let drop :=
      Classical.choice
        (rightmost_drop_sequence hsequence)
    change
      ordered ∈
        standardSequenceExpansion drop.swapped ++
          standardSequenceExpansion drop.merged at hordered
    rcases List.mem_append.mp hordered with hswapped | hmerged
    · exact
        sequence_standard_expansion
          drop.swapped hswapped
    · exact
        sequence_standard_expansion
          drop.merged hmerged
termination_by standardSequenceMeasure sequence
decreasing_by
  · exact drop.swapped_measure_lt
  · exact drop.merged_measure_lt

/-- Standard input sequences expand only into standard ordered sequences. -/
theorem standard_sequence_ordered
    {sequence : List (HallTree α)}
    (hstandard : ISSequen sequence)
    {ordered : List (HallTree α)}
    (hordered : ordered ∈ standardSequenceExpansion sequence) :
    ISSequen ordered := by
  rw [standardSequenceExpansion] at hordered
  split at hordered
  next =>
    have heq : ordered = sequence := by
      simpa only [List.mem_singleton] using hordered
    simpa [heq] using hstandard
  next hsequence =>
    let drop :=
      Classical.choice
        (rightmost_drop_sequence hsequence)
    change
      ordered ∈
        standardSequenceExpansion drop.swapped ++
          standardSequenceExpansion drop.merged at hordered
    rcases List.mem_append.mp hordered with hswapped | hmerged
    · exact
        standard_sequence_ordered
          (drop.swapped_standard_sequence hstandard) hswapped
    · exact
        standard_sequence_ordered
          (drop.merged_standard_sequence hstandard) hmerged
termination_by standardSequenceMeasure sequence
decreasing_by
  · exact drop.swapped_measure_lt
  · exact drop.merged_measure_lt

/--
Hall PBW collection preserves the associative polynomial represented by the
input sequence.
-/
theorem associative_ordered_expansion
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α)) :
    associativeWordProduct R sequence =
      associativeProductSum R
        (standardSequenceExpansion sequence) := by
  rw [standardSequenceExpansion]
  split
  next =>
    simp
  next hsequence =>
    let drop :=
      Classical.choice
        (rightmost_drop_sequence hsequence)
    simp only [associative_sum_append]
    rw [← associative_ordered_expansion R
        drop.swapped,
      ← associative_ordered_expansion R
        drop.merged]
    exact drop.associative_word_product R
termination_by standardSequenceMeasure sequence
decreasing_by
  · exact drop.swapped_measure_lt
  · exact drop.merged_measure_lt

end HallTree
end Submission


/-!
# Spanning by ordered Hall standard sequences

The PBW-style Hall collection identity recursively rewrites the polynomial
product of any standard sequence into a linear combination of products of
ordered standard sequences.  The recursion is justified by collection
shortlex order: swaps decrease lexicographic order and merges shorten the
sequence.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/-- Polynomial products indexed by ordered Hall standard sequences. -/
def standardSequenceSet
    (R : Type*) [CommRing R] :
    Set (AssociativeWordPolynomial R α) :=
  Set.range fun sequence :
      { sequence : List (HallTree α) //
        ISSequen sequence ∧ IsOrderedSequence sequence } =>
    associativeWordProduct R sequence.1

/--
Every Hall standard-sequence polynomial product belongs to the span of
ordered Hall standard-sequence products.
-/
theorem associative_standard_sequence
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α))
    (hstandard : ISSequen sequence) :
    associativeWordProduct R sequence ∈
      Submodule.span R (standardSequenceSet (α := α) R) := by
  refine before_well_founded.induction
    (C := fun sequence =>
      ISSequen sequence →
        associativeWordProduct R sequence ∈
          Submodule.span R
            (standardSequenceSet (α := α) R))
    sequence ?_ hstandard
  intro sequence ih hstandard
  by_cases hordered : IsOrderedSequence sequence
  · apply Submodule.subset_span
    exact ⟨⟨sequence, hstandard, hordered⟩, rfl⟩
  · rcases
      rightmost_drop_bound hordered
      with ⟨xs, u, v, tail, rfl, hvu, hvTail⟩
    rw [associative_drop_context]
    exact
      (Submodule.span R
          (standardSequenceSet (α := α) R)).add_mem
        (ih (xs ++ v :: u :: tail)
          (collection_before_drop xs u v tail hvu)
          (hstandard.swap_drop_incontext hvu))
        (ih (xs ++ commutator u v :: tail)
          (before_merge_drop xs u v tail)
          (hstandard.merge_drop_incontext hvu hvTail))

/-- A sequence of atoms is a Hall standard sequence. -/
theorem standard_atom
    (letters : List α) :
    ISSequen (letters.map atom) := by
  induction letters with
  | nil => simp
  | cons a letters ih => simp [ih]

omit [Encodable α] in
/-- The polynomial product along an atom sequence is its monomial word. -/
theorem associative_product_atom
    (R : Type*) [CommRing R]
    (letters : List α) :
    associativeWordProduct R (letters.map atom) =
      MonoidAlgebra.single (FreeMonoid.ofList letters) 1 := by
  induction letters with
  | nil => simp [MonoidAlgebra.one_def]
  | cons a letters ih =>
      simp [ih, MonoidAlgebra.single_mul_single]

/-- Every monomial word belongs to the span of ordered standard products. -/
theorem single_standard_sequence
    (R : Type*) [CommRing R]
    (word : FreeMonoid α) :
    MonoidAlgebra.single word 1 ∈
      Submodule.span R (standardSequenceSet (α := α) R) := by
  rw [← FreeMonoid.ofList_toList word,
    ← associative_product_atom R word.toList]
  exact
    associative_standard_sequence
      R (word.toList.map atom) (standard_atom word.toList)

/--
Ordered Hall standard-sequence products span the whole free associative
algebra.
-/
theorem standard_sequence_top
    (R : Type*) [CommRing R] :
    Submodule.span R (standardSequenceSet (α := α) R) =
      ⊤ := by
  apply top_unique
  intro polynomial htop
  clear htop
  induction polynomial using Finsupp.induction_linear with
  | zero =>
      exact Submodule.zero_mem _
  | add left right hleft hright =>
      exact Submodule.add_mem _ hleft hright
  | single word coefficient =>
      rw [← Finsupp.smul_single_one]
      exact Submodule.smul_mem _
        coefficient
        (single_standard_sequence R word)

end HallTree
end Submission


/-!
# Coordinates supplied by Hall standard-sequence collection

The executable Hall collector gives finite coordinates on ordered Hall-tree
sequences.  Evaluating those coordinates recovers the input product.  Applied
to the atom sequence of each associative word, this produces an explicit
linear section of evaluation from Hall-sequence coordinates to the free
associative algebra.

This is the spanning half of the Hall PBW argument in coordinate form.  The
remaining PBW uniqueness theorem is exactly injectivity after restricting
evaluation to standard ordered sequences.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/-- The coordinate predicate for Hall PBW normal forms. -/
def OrderedSequence (sequence : List (HallTree α)) : Prop :=
  ISSequen sequence ∧ IsOrderedSequence sequence

/-- Evaluate a finitely supported combination of Hall-tree sequences. -/
noncomputable def hallSequenceLinear
    (R : Type*) [CommRing R] :
    (List (HallTree α) →₀ R) →ₗ[R] AssociativeWordPolynomial R α :=
  Finsupp.linearCombination R (associativeWordProduct R)

/--
Finite Hall-PBW coordinates of one sequence.  Repetitions in the expansion
list become their natural coefficients.
-/
noncomputable def standardSequenceCoordinates
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α)) :
    List (HallTree α) →₀ R :=
  ((standardSequenceExpansion sequence).map fun ordered =>
    Finsupp.single ordered 1).sum

omit [Encodable α] in
/-- Evaluating list-sum coordinates is the corresponding polynomial sum. -/
theorem sequence_linear_single
    (R : Type*) [CommRing R]
    (sequences : List (List (HallTree α))) :
    hallSequenceLinear R
        ((sequences.map fun sequence => Finsupp.single sequence 1).sum) =
      associativeProductSum R sequences := by
  induction sequences with
  | nil =>
      simp [hallSequenceLinear]
  | cons sequence sequences ih =>
      simp only [List.map_cons, List.sum_cons,
        associative_sum_cons, map_add, ih]
      simp [hallSequenceLinear]

/-- Hall-PBW coordinates evaluate to the original sequence product. -/
theorem sequence_standard_coordinates
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α)) :
    hallSequenceLinear R
        (standardSequenceCoordinates R sequence) =
      associativeWordProduct R sequence := by
  rw [standardSequenceCoordinates,
    sequence_linear_single,
    ← associative_ordered_expansion]

/-- Coordinates obtained by collecting the atom sequence of one word. -/
noncomputable def associativeExpansionCoordinates
    (R : Type*) [CommRing R]
    (word : FreeMonoid α) :
    List (HallTree α) →₀ R :=
  standardSequenceCoordinates R (word.toList.map atom)

/--
Linearly collect every associative word into Hall standard-sequence
coordinates.
-/
noncomputable def associativeOrderedLinear
    (R : Type*) [CommRing R] :
    AssociativeWordPolynomial R α →ₗ[R] (List (HallTree α) →₀ R) :=
  Finsupp.linearCombination R (associativeExpansionCoordinates R)

/-- The collector's linear extension on one monomial word. -/
theorem associative_expansion_single
    (R : Type*) [CommRing R]
    (word : FreeMonoid α)
    (coefficient : R) :
    associativeOrderedLinear R
        (MonoidAlgebra.single word coefficient) =
      coefficient • associativeExpansionCoordinates R word := by
  exact Finsupp.linearCombination_single R coefficient word

/--
Evaluating the collected coordinates of a polynomial recovers the polynomial.
Thus Hall standard-sequence evaluation has an explicit linear section.
-/
theorem sequence_associative_expansion
    (R : Type*) [CommRing R]
    (polynomial : AssociativeWordPolynomial R α) :
    hallSequenceLinear R
        (associativeOrderedLinear R polynomial) =
      polynomial := by
  induction polynomial using Finsupp.induction_linear with
  | zero =>
      calc
        hallSequenceLinear R
            (associativeOrderedLinear R 0) =
          hallSequenceLinear R 0 :=
            congrArg (hallSequenceLinear R)
              (associativeOrderedLinear R).map_zero
        _ = 0 := (hallSequenceLinear R).map_zero
  | add left right hleft hright =>
      calc
        hallSequenceLinear R
            (associativeOrderedLinear R (left + right)) =
          hallSequenceLinear R
            (associativeOrderedLinear R left +
              associativeOrderedLinear R right) :=
            congrArg (hallSequenceLinear R)
              ((associativeOrderedLinear R).map_add left right)
        _ =
            hallSequenceLinear R
                (associativeOrderedLinear R left) +
              hallSequenceLinear R
                (associativeOrderedLinear R right) :=
            (hallSequenceLinear R).map_add _ _
        _ = left + right := congrArg₂ (· + ·) hleft hright
  | single word coefficient =>
      rw [associative_expansion_single, map_smul,
        associativeExpansionCoordinates,
        sequence_standard_coordinates,
        associative_product_atom]
      simp

/-- Sequence-polynomial evaluation is surjective. -/
theorem sequence_linear_surjective
    (R : Type*) [CommRing R] :
    Function.Surjective (hallSequenceLinear (α := α) R) := by
  intro polynomial
  exact
    ⟨associativeOrderedLinear R polynomial,
      sequence_associative_expansion
        R polynomial⟩

/--
Every sequence occurring in the collected coordinates of a standard input is
itself standard and ordered.
-/
theorem standard_sequence_expansion
    {sequence ordered : List (HallTree α)}
    (hstandard : ISSequen sequence)
    (hordered : ordered ∈ standardSequenceExpansion sequence) :
    OrderedSequence ordered :=
  ⟨standard_sequence_ordered
      hstandard hordered,
    sequence_standard_expansion
      sequence hordered⟩

/-- Finitely supported coordinates whose indices are Hall PBW normal forms. -/
def orderedStandardSubmodule
    (R : Type*) [CommRing R] :
    Submodule R (List (HallTree α) →₀ R) :=
  Finsupp.supported R R { sequence | OrderedSequence sequence }

omit [Encodable α] in
/-- A list-sum coordinate outside its indexing list vanishes. -/
theorem sum_single_not
    (R : Type*) [CommRing R]
    (sequences : List (List (HallTree α)))
    (ordered : List (HallTree α))
    (hordered : ordered ∉ sequences) :
    ((sequences.map fun sequence => Finsupp.single sequence (1 : R)).sum) ordered = 0 := by
  induction sequences with
  | nil =>
      simp
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at hordered
      simp [hordered.1, ih hordered.2]

/-- A coordinate outside the finite collected expansion vanishes. -/
theorem standard_sequence_coordinates
    (R : Type*) [CommRing R]
    (sequence ordered : List (HallTree α))
    (hordered : ordered ∉ standardSequenceExpansion sequence) :
    standardSequenceCoordinates R sequence ordered = 0 := by
  simpa [standardSequenceCoordinates] using
    sum_single_not
      R (standardSequenceExpansion sequence) ordered hordered

/-- Coordinates obtained by collecting a standard sequence are normal-form supported. -/
theorem standard_coordinates_submodule
    (R : Type*) [CommRing R]
    {sequence : List (HallTree α)}
    (hstandard : ISSequen sequence) :
    standardSequenceCoordinates R sequence ∈
      orderedStandardSubmodule (α := α) R := by
  rw [orderedStandardSubmodule, Finsupp.mem_supported']
  intro ordered hordered
  apply
    standard_sequence_coordinates
      R sequence ordered
  intro hmem
  exact
    hordered
      (standard_sequence_expansion
        hstandard hmem)

/-- Collected coordinates of an associative word are normal-form supported. -/
theorem associative_coordinates_submodule
    (R : Type*) [CommRing R]
    (word : FreeMonoid α) :
    associativeExpansionCoordinates R word ∈
      orderedStandardSubmodule (α := α) R := by
  exact
    standard_coordinates_submodule
      R (standard_atom word.toList)

/-- The ambient linear collector takes values in normal-form coordinates. -/
theorem associative_standard_submodule
    (R : Type*) [CommRing R]
    (polynomial : AssociativeWordPolynomial R α) :
    associativeOrderedLinear (α := α) R polynomial ∈
      orderedStandardSubmodule (α := α) R := by
  induction polynomial using Finsupp.induction_linear with
  | zero =>
      exact
        (associativeOrderedLinear (α := α) R).map_zero ▸
          Submodule.zero_mem _
  | add left right hleft hright =>
      exact
        (associativeOrderedLinear (α := α) R).map_add left right ▸
          Submodule.add_mem _ hleft hright
  | single word coefficient =>
      rw [associative_expansion_single]
      exact
        Submodule.smul_mem _
          coefficient
          (associative_coordinates_submodule
            R word)

/-- Evaluate a finitely supported combination of Hall PBW normal forms. -/
noncomputable def standardSequenceLinear
    (R : Type*) [CommRing R] :
    orderedStandardSubmodule (α := α) R →ₗ[R]
      AssociativeWordPolynomial R α :=
  (hallSequenceLinear R).comp
    (Submodule.subtype
      (orderedStandardSubmodule (α := α) R))

/-- Collect an associative polynomial into Hall PBW normal-form coordinates. -/
noncomputable def associativeRestrictedLinear
    (R : Type*) [CommRing R] :
    AssociativeWordPolynomial R α →ₗ[R]
      orderedStandardSubmodule (α := α) R :=
  LinearMap.codRestrict
    (orderedStandardSubmodule (α := α) R)
    (associativeOrderedLinear (α := α) R)
    (associative_standard_submodule
      (α := α) R)

/-- Restricted evaluation after Hall collection is the identity. -/
theorem
  sequence_associative_restricted
    (R : Type*) [CommRing R]
    (polynomial : AssociativeWordPolynomial R α) :
    standardSequenceLinear R
        (associativeRestrictedLinear R polynomial) =
      polynomial := by
  exact
    sequence_associative_expansion
      R polynomial

/-- Hall PBW normal-form products span the free associative algebra. -/
theorem ordered_sequence_surjective
    (R : Type*) [CommRing R] :
    Function.Surjective
      (standardSequenceLinear (α := α) R) := by
  intro polynomial
  exact
    ⟨associativeRestrictedLinear R polynomial,
      sequence_associative_restricted
        R polynomial⟩

end HallTree
end Submission


/-!
# Homogeneous Hall standard-sequence coordinates

Hall collection preserves the sum of the weights of the trees in a sequence.
Consequently the ordered standard-sequence coordinates and their associative
polynomials split degree by degree.  Over a finite alphabet, there are only
finitely many normal forms in each degree.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Encodable α]

/-- Total Hall weight of a sequence of bracket trees. -/
def standardSequenceWeight (sequence : List (HallTree α)) : ℕ :=
  (sequence.map weight).sum

omit [Encodable α] in
@[simp]
theorem standard_weight_nil :
    standardSequenceWeight ([] : List (HallTree α)) = 0 :=
  rfl

omit [Encodable α] in
@[simp]
theorem standard_weight_cons
    (w : HallTree α)
    (sequence : List (HallTree α)) :
    standardSequenceWeight (w :: sequence) =
      w.weight + standardSequenceWeight sequence :=
  rfl

omit [Encodable α] in
@[simp]
theorem standard_sequence_append
    (left right : List (HallTree α)) :
    standardSequenceWeight (left ++ right) =
      standardSequenceWeight left + standardSequenceWeight right := by
  simp [standardSequenceWeight]

omit [Encodable α] in
@[simp]
theorem standard_sequence_atom
    (letters : List α) :
    standardSequenceWeight (letters.map atom) = letters.length := by
  induction letters with
  | nil => simp
  | cons letter letters ih => simp [ih, Nat.add_comm]

omit [Encodable α] in
/-- Swapping an adjacent pair does not change total Hall weight. -/
theorem standard_sequence_drop
    (context : List (HallTree α))
    (left right : HallTree α)
    (suffix : List (HallTree α)) :
    standardSequenceWeight (context ++ right :: left :: suffix) =
      standardSequenceWeight (context ++ left :: right :: suffix) := by
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

omit [Encodable α] in
/-- Replacing an adjacent pair by its bracket does not change total Hall weight. -/
theorem standard_merge_drop
    (context : List (HallTree α))
    (left right : HallTree α)
    (suffix : List (HallTree α)) :
    standardSequenceWeight
        (context ++ commutator left right :: suffix) =
      standardSequenceWeight (context ++ left :: right :: suffix) := by
  simp [Nat.add_assoc]

namespace RDExp

/-- The swapped branch of one collection step has the source degree. -/
theorem swapped_weight_eq
    {sequence : List (HallTree α)}
    (drop : RDExp sequence) :
    standardSequenceWeight drop.swapped =
      standardSequenceWeight sequence := by
  obtain ⟨context, left, right, suffix, rfl, _, _⟩ := drop
  exact
    standard_sequence_drop
      context left right suffix

/-- The merged branch of one collection step has the source degree. -/
theorem merged_weight_eq
    {sequence : List (HallTree α)}
    (drop : RDExp sequence) :
    standardSequenceWeight drop.merged =
      standardSequenceWeight sequence := by
  obtain ⟨context, left, right, suffix, rfl, _, _⟩ := drop
  exact
    standard_merge_drop
      context left right suffix

end RDExp

/-- Every normal form emitted by Hall collection has the source degree. -/
theorem standard_ordered_expansion
    (sequence : List (HallTree α))
    {ordered : List (HallTree α)}
    (hordered : ordered ∈ standardSequenceExpansion sequence) :
    standardSequenceWeight ordered = standardSequenceWeight sequence := by
  rw [standardSequenceExpansion] at hordered
  split at hordered
  next =>
    have heq : ordered = sequence := by
      simpa only [List.mem_singleton] using hordered
    exact congrArg standardSequenceWeight heq
  next hsequence =>
    let drop :=
      Classical.choice
        (rightmost_drop_sequence hsequence)
    change
      ordered ∈
        standardSequenceExpansion drop.swapped ++
          standardSequenceExpansion drop.merged at hordered
    rcases List.mem_append.mp hordered with hswapped | hmerged
    · exact
        (standard_ordered_expansion
          drop.swapped hswapped).trans drop.swapped_weight_eq
    · exact
        (standard_ordered_expansion
          drop.merged hmerged).trans drop.merged_weight_eq
termination_by standardSequenceMeasure sequence
decreasing_by
  · exact drop.swapped_measure_lt
  · exact drop.merged_measure_lt

omit [Encodable α] in
/-- Every word occurring in a sequence product has the sequence's total weight. -/
theorem associative_support_length
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α))
    {word : FreeMonoid α}
    (hword : word ∈ (associativeWordProduct R sequence).support) :
    word.length = standardSequenceWeight sequence := by
  classical
  induction sequence generalizing word with
  | nil =>
      have hsingleton :
          word ∈ ({1} : Finset (FreeMonoid α)) :=
        Finsupp.support_single_subset hword
      have hwordEq : word = 1 := Finset.mem_singleton.mp hsingleton
      simp [hwordEq]
  | cons tree sequence ih =>
      have hmul :=
        MonoidAlgebra.support_mul
          (tree.associativeWordPolynomial R)
          (associativeWordProduct R sequence) hword
      obtain ⟨treeWord, htreeWord, sequenceWord, hsequenceWord, rfl⟩ :=
        Finset.mem_mul.mp hmul
      simp [associative_word_length R tree htreeWord,
        ih hsequenceWord]

/-- A sequence product, packaged in its homogeneous word submodule. -/
def associativeProductRep
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α)) :
    AssociativeHomogeneousWords R α (standardSequenceWeight sequence) :=
  ⟨associativeWordProduct R sequence, by
    intro word hword
    exact associative_support_length R sequence hword⟩

/-- Reindex a sequence product into an explicitly equal total weight. -/
def associativeHomogeneousRep
    (R : Type*) [CommRing R]
    {n : ℕ}
    (sequence : List (HallTree α))
    (hweight : standardSequenceWeight sequence = n) :
    AssociativeHomogeneousWords R α n :=
  ⟨associativeWordProduct R sequence, by
    intro word hword
    simpa [hweight] using
      associative_support_length R sequence hword⟩

/-- The degree-`n` Hall PBW normal-form predicate. -/
def OrderedStandardSequence
    (n : ℕ)
    (sequence : List (HallTree α)) : Prop :=
  OrderedSequence sequence ∧ standardSequenceWeight sequence = n

/-- Normal-form coordinates supported in one Hall degree. -/
def orderedSequenceSubmodule
    (R : Type*) [CommRing R]
    (n : ℕ) :
    Submodule R (List (HallTree α) →₀ R) :=
  Finsupp.supported R R
    { sequence | OrderedStandardSequence n sequence }

/-- Collecting a standard sequence produces coordinates in its own degree. -/
theorem standardSequenceSubmodule
    (R : Type*) [CommRing R]
    {sequence : List (HallTree α)}
    (hstandard : ISSequen sequence) :
    standardSequenceCoordinates R sequence ∈
      orderedSequenceSubmodule
        (α := α) R (standardSequenceWeight sequence) := by
  rw [orderedSequenceSubmodule, Finsupp.mem_supported']
  intro ordered hordered
  apply
    standard_sequence_coordinates
      R sequence ordered
  intro hmem
  exact
    hordered
      ⟨standard_sequence_expansion
          hstandard hmem,
        standard_ordered_expansion
          sequence hmem⟩

/-- The collected coordinates of an associative word have its word length. -/
theorem associativeCoordSubmodule
    (R : Type*) [CommRing R]
    (word : FreeMonoid α) :
    associativeExpansionCoordinates R word ∈
      orderedSequenceSubmodule
        (α := α) R word.length := by
  simpa [associativeExpansionCoordinates, FreeMonoid.length] using
    standardSequenceSubmodule
      R (standard_atom word.toList)

omit [Encodable α] in
/-- Sequence length is bounded above by total Hall weight. -/
theorem length_standard_sequence
    (sequence : List (HallTree α)) :
    sequence.length ≤ standardSequenceWeight sequence := by
  induction sequence with
  | nil => simp
  | cons tree sequence ih =>
      have htree := tree.weight_pos
      simp only [List.length_cons, standard_weight_cons]
      omega

omit [Encodable α] in
/-- Every entry in a sequence has weight at most the sequence's total weight. -/
theorem weight_standard_sequence
    {sequence : List (HallTree α)}
    {tree : HallTree α}
    (htree : tree ∈ sequence) :
    tree.weight ≤ standardSequenceWeight sequence := by
  induction sequence with
  | nil => simp at htree
  | cons head sequence ih =>
      rcases List.mem_cons.mp htree with rfl | htree
      · simp
      · exact (ih htree).trans (Nat.le_add_left _ _)

section FiniteAlphabet

variable [Finite α]

noncomputable local instance : Fintype α := Fintype.ofFinite α

omit [Encodable α] in
/-- A tree of weight at most `n` occurs in the finite height-`n` enumeration. -/
theorem all_trees_up
    {n : ℕ}
    (tree : HallTree α)
    (htree : tree.weight ≤ n) :
    tree ∈ allTreesHeight n :=
  trees_height Finset.univ.toList htree
    (all_trees_height tree)

/-- There are finitely many Hall trees of weight at most `n`. -/
theorem finite_set_weight
    (n : ℕ) :
    { tree : HallTree α | tree.weight ≤ n }.Finite := by
  refine ((allTreesHeight n).toFinset.finite_toSet).subset ?_
  intro tree htree
  simpa using all_trees_up tree htree

/--
Encode a degree-`n` tree sequence as a bounded-length list of trees individually
bounded by `n`.
-/
def boundedSequenceWeight
    (n : ℕ)
    (sequence :
      { sequence : List (HallTree α) |
        standardSequenceWeight sequence = n }) :
    List { tree : HallTree α | tree.weight ≤ n } :=
  sequence.1.attach.map fun tree =>
    ⟨tree.1, by
      exact
        (weight_standard_sequence tree.2).trans_eq
          sequence.2⟩

omit [Encodable α] [Finite α] in
@[simp]
theorem bounded_sequence_length
    (n : ℕ)
    (sequence :
      { sequence : List (HallTree α) |
        standardSequenceWeight sequence = n }) :
    (boundedSequenceWeight n sequence).length = sequence.1.length := by
  simp [boundedSequenceWeight]

/-- Add the total-length bound to the finite sequence encoding. -/
def boundedSequenceCode
    (n : ℕ)
    (sequence :
      { sequence : List (HallTree α) |
        standardSequenceWeight sequence = n }) :
    { sequence : List { tree : HallTree α | tree.weight ≤ n } |
      sequence.length ≤ n } :=
  ⟨boundedSequenceWeight n sequence, by
    change (boundedSequenceWeight n sequence).length ≤ n
    rw [bounded_sequence_length]
    exact
      (length_standard_sequence sequence.1).trans_eq
        sequence.2⟩

omit [Encodable α] [Finite α] in
/-- The finite sequence encoding is injective. -/
theorem sequence_code_injective
    (n : ℕ) :
    Function.Injective (boundedSequenceCode (α := α) n) := by
  intro left right heq
  apply Subtype.ext
  have heq :=
    congrArg
      (List.map fun tree : { tree : HallTree α | tree.weight ≤ n } => tree.1)
      (congrArg Subtype.val heq)
  simpa [boundedSequenceCode, boundedSequenceWeight] using heq

/-- There are finitely many tree sequences in each total Hall degree. -/
theorem set_sequence_weight
    (n : ℕ) :
    { sequence : List (HallTree α) |
      standardSequenceWeight sequence = n }.Finite := by
  rw [← Set.finite_coe_iff]
  letI : Finite { tree : HallTree α | tree.weight ≤ n } :=
    Set.finite_coe_iff.mpr (finite_set_weight n)
  letI :
      Finite
        { sequence : List { tree : HallTree α | tree.weight ≤ n } |
          sequence.length ≤ n } :=
    Set.finite_coe_iff.mpr
      (List.finite_length_le { tree : HallTree α | tree.weight ≤ n } n)
  exact
    Finite.of_injective
      (boundedSequenceCode (α := α) n)
      (sequence_code_injective (α := α) n)

/-- In particular, the Hall PBW normal forms of each degree form a finite set. -/
theorem set_standard_sequence
    (n : ℕ) :
    { sequence : List (HallTree α) |
      OrderedStandardSequence n sequence }.Finite :=
  (set_sequence_weight n).subset fun _ hsequence =>
    hsequence.2

end FiniteAlphabet

end HallTree
end Submission


/-!
# Degreewise evaluation of Hall standard-sequence coordinates

The Hall collector respects the homogeneous grading.  This file restricts both
normal-form evaluation and associative-word collection to one degree and proves
that collection is an explicit linear section.  Thus the remaining PBW
uniqueness theorem can be attacked degree by degree.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Encodable α]

omit [Encodable α] in
/-- A sequence product vanishes on words outside its homogeneous degree. -/
theorem associative_length_ne
    (R : Type*) [CommRing R]
    (sequence : List (HallTree α))
    (word : FreeMonoid α)
    (hlength : word.length ≠ standardSequenceWeight sequence) :
    associativeWordProduct R sequence word = 0 := by
  rw [← Finsupp.notMem_support_iff]
  intro hword
  exact
    hlength
      (associative_support_length R sequence hword)

/--
Evaluating degree-`n` Hall normal-form coordinates produces a homogeneous
associative polynomial of word length `n`.
-/
noncomputable def orderedStandardSequence
    (R : Type*) [CommRing R]
    (n : ℕ) :
    orderedSequenceSubmodule (α := α) R n →ₗ[R]
      AssociativeHomogeneousWords R α n :=
  LinearMap.codRestrict
    (AssociativeHomogeneousWords R α n)
    ((hallSequenceLinear R).comp
      (Submodule.subtype
        (orderedSequenceSubmodule (α := α) R n)))
    fun coordinate => by
      change
        coordinate.1.sum
            (fun sequence coefficient =>
              coefficient • associativeWordProduct R sequence) ∈
          AssociativeHomogeneousWords R α n
      apply Submodule.sum_mem
      intro sequence hsequence
      have hsequenceDegree :
          OrderedStandardSequence n sequence :=
        coordinate.2 hsequence
      exact
        Submodule.smul_mem _ _
          (associativeHomogeneousRep
            R sequence hsequenceDegree.2).2

/--
The ambient linear collector maps homogeneous polynomials into normal-form
coordinates of the same degree.
-/
theorem
  associative_sequence_submodule
    (R : Type*) [CommRing R]
    (n : ℕ)
    (polynomial : AssociativeHomogeneousWords R α n) :
    associativeOrderedLinear (α := α) R polynomial.1 ∈
      orderedSequenceSubmodule (α := α) R n := by
  change
    polynomial.1.sum
        (fun word coefficient =>
          coefficient • associativeExpansionCoordinates R word) ∈
      orderedSequenceSubmodule (α := α) R n
  apply Submodule.sum_mem
  intro word hword
  apply Submodule.smul_mem
  have hlength : word.length = n :=
    polynomial.2 hword
  simpa [hlength] using
    associativeCoordSubmodule
      R word

/-- Restrict associative-word collection to homogeneous word polynomials. -/
noncomputable def associativeExpansionLinear
    (R : Type*) [CommRing R]
    (n : ℕ) :
    AssociativeHomogeneousWords R α n →ₗ[R]
      orderedSequenceSubmodule (α := α) R n :=
  LinearMap.codRestrict
    (orderedSequenceSubmodule (α := α) R n)
    ((associativeOrderedLinear (α := α) R).comp
      (Submodule.subtype (AssociativeHomogeneousWords R α n)))
    (associative_sequence_submodule
      (α := α) R n)

/-- Degreewise evaluation after Hall collection is the identity. -/
theorem standardSequencePoly
    (R : Type*) [CommRing R]
    (n : ℕ)
    (polynomial : AssociativeHomogeneousWords R α n) :
    orderedStandardSequence R n
        (associativeExpansionLinear R n polynomial) =
      polynomial := by
  apply Subtype.ext
  exact
    sequence_associative_expansion
      R polynomial.1

/-- Degreewise Hall normal-form evaluation is surjective. -/
theorem standard_sequence_surjective
    (R : Type*) [CommRing R]
    (n : ℕ) :
    Function.Surjective
      (orderedStandardSequence (α := α) R n) := by
  intro polynomial
  exact
    ⟨associativeExpansionLinear R n polynomial,
      standardSequencePoly
        R n polynomial⟩

/--
Degree-`n` coordinates are, in particular, unrestricted ordered-standard
coordinates.
-/
theorem ordered_sequence_submodule
    (R : Type*) [CommRing R]
    (n : ℕ) :
    orderedSequenceSubmodule (α := α) R n ≤
      orderedStandardSubmodule (α := α) R := by
  intro coordinate hcoordinate
  rw [orderedStandardSubmodule, Finsupp.mem_supported']
  intro sequence hsequence
  apply (Finsupp.mem_supported' R coordinate).mp hcoordinate
  intro hsequenceDegree
  exact hsequence hsequenceDegree.1

/-- Forget the degree bound on homogeneous normal-form coordinates. -/
def standardSequenceInclusion
    (R : Type*) [CommRing R]
    (n : ℕ) :
    orderedSequenceSubmodule (α := α) R n →ₗ[R]
      orderedStandardSubmodule (α := α) R :=
  Submodule.inclusion (ordered_sequence_submodule R n)

/-- Degreewise evaluation agrees with unrestricted evaluation after inclusion. -/
theorem standard_sequence_inclusion
    (R : Type*) [CommRing R]
    (n : ℕ)
    (coordinate :
      orderedSequenceSubmodule (α := α) R n) :
    (standardSequenceLinear R)
        (standardSequenceInclusion R n coordinate) =
      (orderedStandardSequence R n coordinate).1 :=
  rfl

end HallTree
end Submission


/-!
# Degreewise rank reduction for Hall standard-sequence coordinates

Over a finite alphabet, both the degree-`n` Hall normal-form coordinates and
the degree-`n` associative words have finite bases.  Since Hall collection
already gives a section of evaluation, equality of the two finite cardinalities
upgrades degreewise surjectivity to injectivity.

The remaining combinatorial input is isolated in two forms:

* `PCInput` asks only for equality of cardinalities.
* `PFInput` asks for the classical factorization
  equivalence between ordered standard sequences and associative words.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Encodable α]

/-- The single-sequence basis of homogeneous Hall normal-form coordinates. -/
noncomputable def standardSequenceBasis
    (R : Type*) [CommRing R]
    (n : ℕ) :
    Module.Basis
      { sequence : List (HallTree α) //
        OrderedStandardSequence n sequence }
      R
      (orderedSequenceSubmodule (α := α) R n) :=
  Finsupp.basisSingleOne.map
    (Finsupp.supportedEquivFinsupp
      (R := R)
      { sequence : List (HallTree α) |
        OrderedStandardSequence n sequence }).symm

section FiniteAlphabet

variable [Finite α]

noncomputable local instance : Fintype α := Fintype.ofFinite α

/-- Degree-`n` ordered standard Hall sequences form a finite type. -/
instance standard_sequence_weight
    (n : ℕ) :
    Finite
      { sequence : List (HallTree α) //
        OrderedStandardSequence n sequence } :=
  Set.finite_coe_iff.mpr
    (set_standard_sequence (α := α) n)

/-- Fixed-length associative words over a finite alphabet form a finite type. -/
instance associative_words_length
    (n : ℕ) :
    Finite (AssociativeWordsLength α n) :=
  Finite.of_equiv
    (List.Vector α n)
    (associativeVectorEquiv α n).symm

omit [Finite α] in
/-- The rank of homogeneous Hall coordinates is their number of normal forms. -/
theorem standard_sequence_submodule
    (K : Type*) [Field K]
    (n : ℕ) :
    Module.finrank K
        (orderedSequenceSubmodule (α := α) K n) =
      Nat.card
        { sequence : List (HallTree α) //
          OrderedStandardSequence n sequence } :=
  Module.finrank_eq_nat_card_basis
    (standardSequenceBasis (α := α) K n)

omit [Encodable α] [Finite α] in
/-- The rank of homogeneous associative polynomials is the number of words. -/
theorem finrank_homogeneous_words
    (K : Type*) [Field K]
    (n : ℕ) :
    Module.finrank K (AssociativeHomogeneousWords K α n) =
      Nat.card (AssociativeWordsLength α n) :=
  Module.finrank_eq_nat_card_basis
    (associativeHomogeneousWords K α n)

/--
The weak numerical input needed by the degreewise rank argument: Hall normal
forms and associative words have the same cardinality in every degree.
-/
structure PCInput : Prop where
  card_eq :
    ∀ n : ℕ,
      Nat.card
          { sequence : List (HallTree α) //
            OrderedStandardSequence n sequence } =
        Nat.card (AssociativeWordsLength α n)

/--
The classical combinatorial form of the missing PBW input: every word admits a
unique ordered-standard Hall factorization in each degree.
-/
structure PFInput : Prop where
  equivWords :
    ∀ n : ℕ,
      Nonempty
        ({ sequence : List (HallTree α) //
            OrderedStandardSequence n sequence } ≃
          AssociativeWordsLength α n)

namespace PFInput

omit [Finite α] in
/-- A Hall factorization equivalence supplies the numerical rank input. -/
theorem cardinalityInput
    (input : PFInput (α := α)) :
    PCInput (α := α) where
  card_eq n := by
    exact Nat.card_congr (Classical.choice (input.equivWords n))

end PFInput

namespace PCInput

omit [Finite α] in
/-- Equality of normal-form counts gives equality of the two degreewise ranks. -/
theorem finrank_eq
    (input : PCInput (α := α))
    (K : Type*) [Field K]
    (n : ℕ) :
    Module.finrank K
        (orderedSequenceSubmodule (α := α) K n) =
      Module.finrank K (AssociativeHomogeneousWords K α n) := by
  rw [standard_sequence_submodule,
    finrank_homogeneous_words]
  exact input.card_eq n

/--
Equality of normal-form counts upgrades the already-proved degreewise
surjectivity of Hall evaluation to injectivity.
-/
theorem evaluation_injective
    (input : PCInput (α := α))
    (K : Type*) [Field K]
    (n : ℕ) :
    Function.Injective
      (orderedStandardSequence (α := α) K n) := by
  letI :
      FiniteDimensional K
        (orderedSequenceSubmodule (α := α) K n) :=
    (standardSequenceBasis (α := α) K n).finiteDimensional_of_finite
  letI :
      FiniteDimensional K (AssociativeHomogeneousWords K α n) :=
    (associativeHomogeneousWords K α n).finiteDimensional_of_finite
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (input.finrank_eq K n)).mpr
        (standard_sequence_surjective
          (α := α) K n)

end PCInput

namespace PFInput

/-- Hall factorization implies injectivity of evaluation in each degree. -/
theorem evaluation_injective
    (input : PFInput (α := α))
    (K : Type*) [Field K]
    (n : ℕ) :
    Function.Injective
      (orderedStandardSequence (α := α) K n) :=
  input.cardinalityInput.evaluation_injective K n

end PFInput

end FiniteAlphabet

end HallTree
end Submission


/-!
# Hall basis theorem reduced to PBW uniqueness

Hall standard-sequence collection already supplies an explicit linear section
of evaluation from ordered standard Hall sequences to the free associative
algebra.  Thus evaluation is surjective.  The remaining classical PBW input is
exactly injectivity of that restricted evaluation map.

This file records the consequences of that injectivity statement.  Each
indexed Hall basic tree gives the normal-form singleton sequence containing
that tree.  These singleton coordinates are independent, so PBW uniqueness
implies independence of Hall word polynomials.  The existing Magnus transport
and all-weight spanning theorem then produce the concrete free-group
associated-graded basis predicate consumed by collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

open TBluepr

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The remaining Hall PBW uniqueness input: ordered standard Hall-sequence
polynomials have unique coordinates in the free associative algebra.
-/
structure HPUniq
    (R : Type*) [CommRing R] : Prop where
  eval_injective :
    Function.Injective
      (standardSequenceLinear (α := α) R)

omit [Fintype α] [DecidableEq α] in
/-- Collection existence plus PBW uniqueness makes normal-form evaluation bijective. -/
theorem HPUniq.eval_bijective
    (R : Type*) [CommRing R]
    (P : HPUniq (α := α) R) :
    Function.Bijective
      (standardSequenceLinear (α := α) R) :=
  ⟨P.eval_injective,
    ordered_sequence_surjective R⟩

/-- The singleton sequence containing an indexed basic Hall tree is a PBW normal form. -/
theorem indexed_tree_sequence
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    OrderedSequence [indexedBasicTree i] := by
  constructor
  · refine ⟨indexed_tree i, ?_, trivial⟩
    cases indexedBasicTree i with
    | atom a =>
        trivial
    | commutator left right =>
        intro x hx
        simp at hx
  · simp [IsOrderedSequence]

/-- The normal-form coordinate indexed by the singleton sequence of one basic Hall tree. -/
noncomputable def indexedTreeSingleton
    (R : Type*) [CommRing R]
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    orderedStandardSubmodule (α := α) R :=
  ⟨Finsupp.single [indexedBasicTree i] 1,
    Finsupp.single_mem_supported R 1
      (indexed_tree_sequence i)⟩

/-- Indexed basic trees remain injectively indexed after taking singleton sequences. -/
theorem indexed_singleton_injective
    {r : ℕ} :
    Function.Injective
      (fun i : BasicIndex (α := α) r => [indexedBasicTree i]) :=
  List.singleton_injective.comp indexed_tree_injective

/-- The singleton PBW coordinates of indexed basic trees are linearly independent. -/
theorem indexed_singleton_independent
    (R : Type*) [CommRing R]
    {r : ℕ} :
    LinearIndependent R
      (fun i : BasicIndex (α := α) r =>
        indexedTreeSingleton R i) := by
  apply LinearIndependent.of_comp
    (Submodule.subtype
      (orderedStandardSubmodule (α := α) R))
  simpa [indexedTreeSingleton,
    Function.comp_def] using
      (Finsupp.linearIndependent_single_one R (List (HallTree α))).comp
        (fun i : BasicIndex (α := α) r => [indexedBasicTree i])
        indexed_singleton_injective

/-- Evaluating a basic-tree singleton normal form is its Hall word polynomial. -/
@[simp]
theorem
  indexed_tree_singleton
    (R : Type*) [CommRing R]
    {r : ℕ}
    (i : BasicIndex (α := α) r) :
    standardSequenceLinear R
        (indexedTreeSingleton R i) =
      (indexedBasicTree i).associativeWordPolynomial R := by
  simp [standardSequenceLinear,
    indexedTreeSingleton,
    hallSequenceLinear]

/-- PBW uniqueness implies polynomial independence of indexed Hall basic trees. -/
theorem HPUniq.indexe_treea_polyl
    (R : Type*) [CommRing R]
    (P : HPUniq (α := α) R)
    {r : ℕ} :
    LinearIndependent R
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).associativeWordPolynomial R) := by
  have hcoordinates :=
    indexed_singleton_independent
      (α := α) R (r := r)
  have hevaluated :=
    hcoordinates.map'
      (standardSequenceLinear (α := α) R)
      (LinearMap.ker_eq_bot_of_injective P.eval_injective)
  simpa [Function.comp_def] using hevaluated

/--
PBW uniqueness implies homogeneous polynomial independence in the exact form
used by the Magnus transport.
-/
theorem HPUniq.indexedbasic_treeword_polylinindep
    (R : Type*) [CommRing R]
    (P : HPUniq (α := α) R)
    {r : ℕ} :
    LinearIndependent R
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).associativeRepWeight R
          (indexed_tree_weight i)) := by
  apply LinearIndependent.of_comp
    (Finsupp.supported R R {word : FreeMonoid α | word.length = r}).subtype
  exact P.indexe_treea_polyl R

/-- PBW uniqueness transfers through Magnus to lower-central independence. -/
theorem HPUniq.indeba_fregr_laywe
    (P : HPUniq (α := α) ℤ)
    {r : ℕ}
    (hr : 0 < r) :
    LinearIndependent ℤ
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).freeLowerWeight
          (indexed_tree_weight i)) :=
  free_independent_associative
    hr
    (indexedBasicTree (α := α) (r := r))
    indexed_tree_weight
    (P.indexedbasic_treeword_polylinindep ℤ)

/--
PBW uniqueness and Hall collection construct a basis of every positive
free-group lower-central layer.
-/
noncomputable def freePBWUniqueness
    (P : HPUniq (α := α) ℤ)
    {r : ℕ}
    (hr : 0 < r) :
    Module.Basis (BasicIndex (α := α) r) ℤ
      (Additive
        (LowerGradedLayer (FreeGroup α) (r - 1))) :=
  Module.Basis.mk
    (P.indeba_fregr_laywe hr)
    (by
      rw [indexed_basic_top hr])

end HallTree

namespace TCTex

universe u

/--
Map the PBW-uniqueness Hall basis to the one-based collection layer and
reindex it by the universe-lifted concrete Hall-family index.
-/
noncomputable def concretePBWUniqueness
    {d r : ℕ}
    (P : HallTree.HPUniq
      (α := FreeGenerator.{u} d) ℤ)
    (hr : 0 < r) :
    Module.Basis (concreteCommutatorsWeight.{u} d r).index ℤ
      (Additive
        (AssociatedGradedLayer
          (FreeGroup (FreeGenerator.{u} d)) r)) :=
  ((HallTree.freePBWUniqueness P hr).map
    (lowerGradedLinear
      (FreeGroup (FreeGenerator.{u} d)) r hr)).reindex Equiv.ulift.symm

/--
Hall PBW uniqueness supplies the classical fixed-weight free-group basis
predicate consumed by the collection development.
-/
theorem forms_associated_uniqueness
    {d r : ℕ}
    (P : HallTree.HPUniq
      (α := FreeGenerator.{u} d) ℤ)
    (hr : 0 < r) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis := by
  refine ⟨concretePBWUniqueness P hr, ?_⟩
  intro i
  rw [concretePBWUniqueness,
    Module.Basis.reindex_apply, Module.Basis.map_apply]
  simpa [HallTree.freePBWUniqueness,
    Module.Basis.mk_apply] using
      graded_indexed_tree
        hr i.down

/--
A single all-degree Hall PBW uniqueness proof supplies concrete free-group
graded Hall bases in every positive ordinary weight.
-/
theorem forms_pbw_uniqueness
    (d : ℕ)
    (P : HallTree.HPUniq
      (α := FreeGenerator.{u} d) ℤ) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  fun _r hr =>
    forms_associated_uniqueness P hr

end TCTex
end Submission


/-!
# Hall PBW uniqueness reduced to homogeneous degrees

The standard-sequence evaluation map respects total Hall weight.  Filtering a
normal-form coordinate vector by weight therefore lets degreewise injectivity
recover every unrestricted coefficient.

This file packages the reduction from injectivity in each homogeneous degree
to the all-degree Hall PBW uniqueness input used by the free-group basis bridge.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Encodable α]

/-- Extract the homogeneous degree-`n` part of ordered Hall normal-form coordinates. -/
noncomputable def standardSequenceProjection
    (R : Type*) [CommRing R]
    (n : ℕ) :
    orderedStandardSubmodule (α := α) R →ₗ[R]
      orderedSequenceSubmodule (α := α) R n := by
  classical
  refine
    { toFun := fun coordinate =>
        ⟨coordinate.1.filter fun sequence =>
            standardSequenceWeight sequence = n, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · rw [orderedSequenceSubmodule,
      Finsupp.mem_supported']
    intro sequence hsequence
    rw [Finsupp.filter_apply]
    split
    next hweight =>
      apply
        (Finsupp.mem_supported' R coordinate.1).mp
          (show coordinate.1 ∈
              Finsupp.supported R R
                { sequence : List (HallTree α) |
                  OrderedSequence sequence } by
            simp [orderedStandardSubmodule])
      intro hordered
      exact hsequence ⟨hordered, hweight⟩
    next => rfl
  · intro left right
    apply Subtype.ext
    exact Finsupp.filter_add
  · intro coefficient coordinate
    apply Subtype.ext
    ext sequence
    by_cases hweight : standardSequenceWeight sequence = n
    · simp [hweight]
    · simp [hweight]

@[simp]
theorem ordered_sequence_projection
    (R : Type*) [CommRing R]
    (n : ℕ)
    (coordinate : orderedStandardSubmodule (α := α) R)
    (sequence : List (HallTree α)) :
    (standardSequenceProjection R n coordinate).1
        sequence =
      if standardSequenceWeight sequence = n then coordinate.1 sequence else 0 :=
  rfl

omit [Encodable α] in
/-- A homogeneous associative polynomial vanishes away from its word length. -/
theorem associative_homogeneous_words
    (R : Type*) [CommRing R]
    (n : ℕ)
    (polynomial : AssociativeHomogeneousWords R α n)
    (word : FreeMonoid α)
    (hlength : word.length ≠ n) :
    polynomial.1 word = 0 := by
  rw [← Finsupp.notMem_support_iff]
  intro hword
  exact hlength (polynomial.2 hword)

omit [Encodable α] in
/--
Filtering Hall coordinates to degree `n` does not change the coefficient of a
word of length `n`.
-/
theorem sequence_filter_length
    (R : Type*) [CommRing R]
    (n : ℕ)
    (coordinate : List (HallTree α) →₀ R)
    (word : FreeMonoid α)
    (hlength : word.length = n) :
    hallSequenceLinear R
        (coordinate.filter fun sequence =>
          standardSequenceWeight sequence = n) word =
      hallSequenceLinear R coordinate word := by
  classical
  induction coordinate using Finsupp.induction_linear with
  | zero =>
      rw [Finsupp.filter_zero, map_zero]
  | add left right hleft hright =>
      rw [Finsupp.filter_add, map_add, map_add]
      change
        (hallSequenceLinear R
            (left.filter fun sequence =>
              standardSequenceWeight sequence = n)) word +
            (hallSequenceLinear R
              (right.filter fun sequence =>
                standardSequenceWeight sequence = n)) word =
          hallSequenceLinear R left word +
            hallSequenceLinear R right word
      rw [hleft, hright]
  | single sequence coefficient =>
      by_cases hweight : standardSequenceWeight sequence = n
      · simp [hallSequenceLinear, hweight]
      · have hzero :
            associativeWordProduct R sequence word = 0 :=
          associative_length_ne
            R sequence word fun hsequenceLength =>
              hweight (hsequenceLength.symm.trans hlength)
        simp [hallSequenceLinear, hweight, hzero]
        rfl

/--
Degreewise evaluation of a projected coordinate vector agrees with
unrestricted evaluation on words in that degree.
-/
theorem standard_sequence_projection
    (R : Type*) [CommRing R]
    (n : ℕ)
    (coordinate : orderedStandardSubmodule (α := α) R)
    (word : FreeMonoid α)
    (hlength : word.length = n) :
    (orderedStandardSequence R n
        (standardSequenceProjection R n coordinate)).1
          word =
      standardSequenceLinear R coordinate word := by
  exact
    sequence_filter_length
      R n coordinate.1 word hlength

/-- The remaining Hall PBW uniqueness input, split into homogeneous degrees. -/
structure PDUniq
    (R : Type*) [CommRing R] : Prop where
  eval_injective :
    ∀ n : ℕ,
      Function.Injective
        (orderedStandardSequence (α := α) R n)

namespace PDUniq

/-- Injectivity in every homogeneous degree implies unrestricted injectivity. -/
theorem global_evaluation_injective
    (R : Type*) [CommRing R]
    (input : PDUniq (α := α) R) :
    Function.Injective
      (standardSequenceLinear (α := α) R) := by
  intro left right hevaluation
  apply Subtype.ext
  ext sequence
  let n := standardSequenceWeight sequence
  have hprojection :
      standardSequenceProjection R n left =
        standardSequenceProjection R n right := by
    apply input.eval_injective n
    apply Subtype.ext
    ext word
    by_cases hlength : word.length = n
    · rw [
        standard_sequence_projection
          R n left word hlength,
        standard_sequence_projection
          R n right word hlength,
        hevaluation]
    · rw [
        associative_homogeneous_words
          R n _ word hlength,
        associative_homogeneous_words
          R n _ word hlength]
  have hcoefficient :=
    congrArg (fun coordinate => coordinate.1 sequence) hprojection
  simpa [n] using hcoefficient

/-- Degreewise Hall PBW uniqueness supplies the all-degree input. -/
def hallPBWInput
    (R : Type*) [CommRing R]
    (input : PDUniq (α := α) R) :
    HPUniq (α := α) R where
  eval_injective := input.global_evaluation_injective R

end PDUniq

section FiniteAlphabet

variable [Fintype α]

namespace PCInput

/-- Equal degreewise counts imply degreewise Hall PBW uniqueness over a field. -/
def degreewiseUniquenessInput
    (input : PCInput (α := α))
    (K : Type*) [Field K] :
    PDUniq (α := α) K where
  eval_injective n := input.evaluation_injective K n

/-- Equal degreewise counts imply unrestricted Hall PBW uniqueness over a field. -/
def hallPBWInput
    (input : PCInput (α := α))
    (K : Type*) [Field K] :
    HPUniq (α := α) K :=
  (input.degreewiseUniquenessInput K).hallPBWInput K

end PCInput

namespace PFInput

/-- Classical Hall factorization implies unrestricted PBW uniqueness over a field. -/
def hallPBWInput
    (input : PFInput (α := α))
    (K : Type*) [Field K] :
    HPUniq (α := α) K :=
  input.cardinalityInput.hallPBWInput K

end PFInput

end FiniteAlphabet

end HallTree
end Submission


/-!
# Integral descent for Hall PBW uniqueness

Finite-dimensional rank comparison naturally proves Hall PBW uniqueness over
`ℚ`.  The lower-central basis bridge needs integer coefficients.  This file
casts Hall normal-form coordinates and associative word polynomials from `ℤ`
to `ℚ`, proves that evaluation commutes with the cast, and descends rational
injectivity back to integral injectivity.

Combined with the degreewise factorization reduction, this turns the remaining
classical Hall factorization theorem directly into the concrete free-group
associated-graded basis predicate consumed by collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Encodable α]

/-- Cast coefficients of an associative word polynomial from `ℤ` to `ℚ`. -/
noncomputable def associativeIntRat :
    AssociativeWordPolynomial ℤ α →+*
      AssociativeWordPolynomial ℚ α :=
  MonoidAlgebra.mapRingHom (FreeMonoid α) (Int.castRingHom ℚ)

omit [Encodable α] in
/-- Recursive Hall word polynomials commute with coefficient cast to `ℚ`. -/
theorem associative_word_rat
    (tree : HallTree α) :
    associativeIntRat
        (tree.associativeWordPolynomial ℤ) =
      tree.associativeWordPolynomial ℚ := by
  induction tree with
  | atom letter =>
      simp [associativeIntRat]
  | commutator left right hleft hright =>
      change
        associativeIntRat
            (left.associativeWordPolynomial ℤ *
              right.associativeWordPolynomial ℤ -
              right.associativeWordPolynomial ℤ *
                left.associativeWordPolynomial ℤ) =
          left.associativeWordPolynomial ℚ *
              right.associativeWordPolynomial ℚ -
            right.associativeWordPolynomial ℚ *
              left.associativeWordPolynomial ℚ
      rw [map_sub, map_mul, map_mul, hleft, hright]

omit [Encodable α] in
/-- Products along Hall-tree sequences commute with coefficient cast to `ℚ`. -/
theorem associative_int_rat
    (sequence : List (HallTree α)) :
    associativeIntRat
        (associativeWordProduct ℤ sequence) =
      associativeWordProduct ℚ sequence := by
  induction sequence with
  | nil =>
      simp [associativeIntRat]
  | cons tree sequence ih =>
      change
        associativeIntRat
            (tree.associativeWordPolynomial ℤ *
              associativeWordProduct ℤ sequence) =
          tree.associativeWordPolynomial ℚ *
            associativeWordProduct ℚ sequence
      rw [map_mul,
        associative_word_rat,
        ih]

/-- Cast finitely supported Hall-sequence coefficients from `ℤ` to `ℚ`. -/
noncomputable def sequenceIntRat
    (coordinate : List (HallTree α) →₀ ℤ) :
    List (HallTree α) →₀ ℚ :=
  Finsupp.mapRange (fun coefficient : ℤ => (coefficient : ℚ))
    (by simp) coordinate

omit [Encodable α] in
/-- Casting arbitrary Hall-sequence coordinates to `ℚ` is injective. -/
theorem int_rat_injective :
    Function.Injective (sequenceIntRat (α := α)) :=
  Finsupp.mapRange_injective
    (fun coefficient : ℤ => (coefficient : ℚ))
    (by simp)
    Int.cast_injective

omit [Encodable α] in
/-- Hall-sequence polynomial evaluation commutes with coefficient cast to `ℚ`. -/
theorem sequence_int_rat
    (coordinate : List (HallTree α) →₀ ℤ) :
    hallSequenceLinear ℚ
        (sequenceIntRat coordinate) =
      associativeIntRat
        (hallSequenceLinear ℤ coordinate) := by
  induction coordinate using Finsupp.induction_linear with
  | zero =>
      simp [sequenceIntRat, associativeIntRat]
  | add left right hleft hright =>
      change
        hallSequenceLinear ℚ
            (sequenceIntRat (left + right)) =
          associativeIntRat
            (hallSequenceLinear ℤ (left + right))
      rw [show
        sequenceIntRat (left + right) =
            sequenceIntRat left +
              sequenceIntRat right by
          ext sequence
          simp [sequenceIntRat]]
      rw [map_add, hleft, hright]
      rw [map_add (hallSequenceLinear ℤ)]
      exact
        (map_add associativeIntRat
          (hallSequenceLinear ℤ left)
          (hallSequenceLinear ℤ right)).symm
  | single sequence coefficient =>
      simp only [sequenceIntRat,
        Finsupp.mapRange_single, hallSequenceLinear,
        Finsupp.linearCombination_single]
      calc
        (coefficient : ℚ) •
              associativeWordProduct ℚ sequence =
            coefficient •
              associativeWordProduct ℚ sequence := by
          rw [Int.cast_smul_eq_zsmul]
        _ =
            coefficient •
              associativeIntRat
                (associativeWordProduct ℤ sequence) := by
          rw [
            associative_int_rat]
        _ =
            associativeIntRat
              (coefficient •
                associativeWordProduct ℤ sequence) := by
          rw [map_zsmul]

/-- Cast ordered Hall normal-form coordinates from `ℤ` to `ℚ`. -/
noncomputable def standardSequenceRat
    (coordinate :
      orderedStandardSubmodule (α := α) ℤ) :
    orderedStandardSubmodule (α := α) ℚ :=
  ⟨sequenceIntRat coordinate.1, by
    rw [orderedStandardSubmodule,
      Finsupp.mem_supported']
    intro sequence hsequence
    rw [sequenceIntRat, Finsupp.mapRange_apply]
    have hzero : coordinate.1 sequence = 0 := by
      apply
        (Finsupp.mem_supported' ℤ coordinate.1).mp
          (show coordinate.1 ∈
              Finsupp.supported ℤ ℤ
                { sequence : List (HallTree α) |
                  OrderedSequence sequence } by
            simp [orderedStandardSubmodule])
      exact hsequence
    simp [hzero]⟩

/-- Casting ordered Hall normal-form coordinates to `ℚ` is injective. -/
theorem sequence_rat_injective :
    Function.Injective
      (standardSequenceRat (α := α)) := by
  intro left right heq
  apply Subtype.ext
  exact
    int_rat_injective
      (congrArg Subtype.val heq)

/-- Restricted ordered-normal-form evaluation commutes with cast to `ℚ`. -/
theorem standard_sequence_rat
    (coordinate :
      orderedStandardSubmodule (α := α) ℤ) :
    standardSequenceLinear ℚ
        (standardSequenceRat coordinate) =
      associativeIntRat
        (standardSequenceLinear ℤ coordinate) :=
  sequence_int_rat coordinate.1

/-- Rational Hall PBW uniqueness descends to integer coefficients. -/
theorem pbw_uniqueness_rat
    (input : HPUniq (α := α) ℚ) :
    HPUniq (α := α) ℤ where
  eval_injective := by
    intro left right hevaluation
    apply sequence_rat_injective
    apply input.eval_injective
    rw [standard_sequence_rat,
      standard_sequence_rat,
      hevaluation]

section FiniteAlphabet

variable [Fintype α]

namespace PCInput

/-- Equal normal-form counts imply integral Hall PBW uniqueness. -/
def pbwUniquenessInt
    (input : PCInput (α := α)) :
    HPUniq (α := α) ℤ :=
  pbw_uniqueness_rat
    (input.hallPBWInput ℚ)

end PCInput

namespace PFInput

/-- Classical Hall factorization implies integral Hall PBW uniqueness. -/
def pbwUniquenessInt
    (input : PFInput (α := α)) :
    HPUniq (α := α) ℤ :=
  input.cardinalityInput.pbwUniquenessInt

end PFInput

end FiniteAlphabet

end HallTree

namespace TCTex

universe u

/--
The classical degreewise Hall-factorization theorem supplies concrete
free-group associated-graded Hall bases in every positive weight.
-/
theorem forms_associated_factorization
    (d : ℕ)
    (input :
      HallTree.PFInput
        (α := FreeGenerator.{u} d)) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_pbw_uniqueness
    d input.pbwUniquenessInt

end TCTex
end Submission


/-!
# Hall PBW reduced to an injective normal-form code

Degreewise Hall collection already gives a linear section from homogeneous
associative polynomials to ordered Hall normal-form coordinates.  Consequently
there are at least as many normal forms as words in every degree.

This file packages the converse combinatorial input in a particularly concrete
form: an injective code from ordered Hall normal forms to words of the same
degree.  Such a code forces equality of the finite cardinalities, hence supplies
the Hall PBW uniqueness input and the concrete free-group associated-graded
basis predicate needed by collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Encodable α] [Finite α]

noncomputable local instance : Fintype α := Fintype.ofFinite α

/--
There are at most as many degree-`n` words as degree-`n` ordered Hall normal
forms.  This direction is already a consequence of executable Hall collection:
the homogeneous collector is injective because evaluation is its left inverse.
-/
theorem associative_words_sequence
    (n : ℕ) :
    Nat.card (AssociativeWordsLength α n) ≤
      Nat.card
        { sequence : List (HallTree α) //
          OrderedStandardSequence n sequence } := by
  rw [← finrank_homogeneous_words ℚ n,
    ← standard_sequence_submodule ℚ n]
  letI :
      FiniteDimensional ℚ
        (orderedSequenceSubmodule (α := α) ℚ n) :=
    (standardSequenceBasis (α := α) ℚ n).finiteDimensional_of_finite
  refine LinearMap.finrank_le_finrank_of_injective
    (f := associativeExpansionLinear (α := α) ℚ n) ?_
  intro left right heq
  calc
    left =
        orderedStandardSequence ℚ n
          (associativeExpansionLinear ℚ n left) :=
      (standardSequencePoly
        ℚ n left).symm
    _ =
        orderedStandardSequence ℚ n
          (associativeExpansionLinear ℚ n right) :=
      congrArg
        (orderedStandardSequence ℚ n)
        heq
    _ = right :=
      standardSequencePoly
        ℚ n right

/--
The remaining classical combinatorial input, reduced to a coding theorem:
ordered Hall normal forms of degree `n` inject into words of length `n`.
-/
structure PCInputa where
  code :
    ∀ n : ℕ,
      { sequence : List (HallTree α) //
        OrderedStandardSequence n sequence } →
        AssociativeWordsLength α n
  code_injective :
    ∀ n : ℕ, Function.Injective (code n)

namespace PCInputa

/-- An injective normal-form code supplies equality of the degreewise counts. -/
theorem cardinalityInput
    (input : PCInputa (α := α)) :
    PCInput (α := α) where
  card_eq n :=
    le_antisymm
      (Nat.card_le_card_of_injective
        (input.code n) (input.code_injective n))
      (associative_words_sequence
        (α := α) n)

/--
An injective normal-form code is automa a degreewise Hall
factorization equivalence: collection supplies the opposite finite-cardinality
inequality.
-/
noncomputable def factorizationInput
    (input : PCInputa (α := α)) :
    PFInput (α := α) where
  equivWords n :=
    ⟨Equiv.ofBijective
      (input.code n)
      ⟨input.code_injective n,
        (input.code_injective n).bijective_of_nat_card_le
          (associative_words_sequence
            (α := α) n) |>.2⟩⟩

/-- An injective normal-form code supplies integral Hall PBW uniqueness. -/
noncomputable def pbwUniquenessInt
    (input : PCInputa (α := α)) :
    HPUniq (α := α) ℤ :=
  input.cardinalityInput.pbwUniquenessInt

end PCInputa

end HallTree

namespace TCTex

universe u

/--
An injective degreewise code for ordered Hall normal forms supplies concrete
free-group associated-graded Hall bases in every positive weight.
-/
theorem forms_associated_coding
    (d : ℕ)
    (input :
      HallTree.PCInputa
        (α := FreeGenerator.{u} d)) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_pbw_uniqueness
    d input.pbwUniquenessInt

end TCTex
end Submission


/-!
# Foliage coding for ordered Hall normal forms

The classical Hall-word factorization theorem uses the word of leaves of each
basic Hall tree.  The code of an ordered normal form is the concatenation of
those foliage words.

This file defines that concrete code and isolates a recursive proof interface.
It is enough to recover the head Hall factor from an equality of two nonempty
ordered-normal-form codes: free-monoid cancellation then recovers the tails.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Encodable α]

/-- Concatenate the foliage words of a Hall-tree sequence. -/
def standardFoliageWord : List (HallTree α) → FreeMonoid α
  | [] => 1
  | tree :: sequence =>
      tree.foliageWord * standardFoliageWord sequence

omit [Encodable α] in
@[simp]
theorem standard_sequence_nil :
    standardFoliageWord ([] : List (HallTree α)) = 1 :=
  rfl

omit [Encodable α] in
@[simp]
theorem sequence_foliage_cons
    (tree : HallTree α)
    (sequence : List (HallTree α)) :
    standardFoliageWord (tree :: sequence) =
      tree.foliageWord * standardFoliageWord sequence :=
  rfl

omit [Encodable α] in
@[simp]
theorem sequence_foliage_append
    (left right : List (HallTree α)) :
    standardFoliageWord (left ++ right) =
      standardFoliageWord left *
        standardFoliageWord right := by
  induction left with
  | nil =>
      simp
  | cons tree left ih =>
      simp only [List.cons_append, sequence_foliage_cons, ih]
      rw [mul_assoc]

omit [Encodable α] in
/-- The concatenated foliage code has the total Hall weight of its sequence. -/
@[simp]
theorem sequence_foliage_length
    (sequence : List (HallTree α)) :
    (standardFoliageWord sequence).length =
      standardSequenceWeight sequence := by
  induction sequence with
  | nil =>
      simp
  | cons tree sequence ih =>
      simp [ih]

omit [Encodable α] in
/-- Atom sequences code the corresponding free-monoid word. -/
@[simp]
theorem sequence_foliage_atom
    (letters : List α) :
    standardFoliageWord (letters.map atom) =
      FreeMonoid.ofList letters := by
  induction letters with
  | nil =>
      simp
  | cons letter letters ih =>
      simp [ih]

omit [Encodable α] in
/-- A nonempty sequence has a nontrivial foliage code. -/
theorem standard_foliage_nil
    {sequence : List (HallTree α)}
    (hsequence : sequence ≠ []) :
    standardFoliageWord sequence ≠ 1 := by
  cases sequence with
  | nil =>
      exact (hsequence rfl).elim
  | cons tree sequence =>
      intro hcode
      have hlength := congrArg FreeMonoid.length hcode
      simp only [sequence_foliage_length,
        standard_weight_cons, FreeMonoid.length_one] at hlength
      have htree := tree.weight_pos
      omega

/-- The concrete foliage code in one total Hall degree. -/
def sequenceFoliageCode
    (n : ℕ)
    (sequence :
      { sequence : List (HallTree α) //
        OrderedStandardSequence n sequence }) :
    AssociativeWordsLength α n :=
  ⟨standardFoliageWord sequence.1, by
    rw [sequence_foliage_length]
    exact sequence.2.2⟩

/--
The classical Hall-word factorization theorem in its direct global form:
concatenated foliage words distinguish ordered standard sequences.
-/
structure FFInput : Prop where
  foliage_injective :
    Function.Injective
      (fun sequence :
        { sequence : List (HallTree α) //
          OrderedSequence sequence } =>
        standardFoliageWord sequence.1)

/--
A smaller recursive interface for Hall factorization: equality of two
nonempty ordered-normal-form foliage codes forces equality of their head Hall
factors.
-/
structure FUInput : Prop where
  head_code :
    ∀ {leftHead rightHead : HallTree α}
      {leftTail rightTail : List (HallTree α)},
      OrderedSequence (leftHead :: leftTail) →
      OrderedSequence (rightHead :: rightTail) →
      standardFoliageWord (leftHead :: leftTail) =
        standardFoliageWord (rightHead :: rightTail) →
      leftHead = rightHead

namespace FUInput

/--
Recovering the first Hall factor recursively recovers the entire ordered
normal form.
-/
theorem standard_foliage_injective
    (input : FUInput (α := α)) :
    ∀ {left right : List (HallTree α)},
      OrderedSequence left →
      OrderedSequence right →
      standardFoliageWord left =
        standardFoliageWord right →
      left = right := by
  intro left
  induction left with
  | nil =>
      intro right _ hright heq
      cases right with
      | nil =>
          rfl
      | cons rightHead rightTail =>
          exfalso
          exact standard_foliage_nil
            (show rightHead :: rightTail ≠ [] by simp)
            (by simpa using heq.symm)
  | cons leftHead leftTail ih =>
      intro right hleft hright heq
      cases right with
      | nil =>
          exfalso
          exact standard_foliage_nil
            (show leftHead :: leftTail ≠ [] by simp)
            (by simpa using heq)
      | cons rightHead rightTail =>
          have hhead : leftHead = rightHead :=
            input.head_code hleft hright heq
          subst rightHead
          have htailCode :
              standardFoliageWord leftTail =
                standardFoliageWord rightTail := by
            apply mul_left_cancel
            simpa only [sequence_foliage_cons] using heq
          have htail :
              leftTail = rightTail :=
            ih
              ⟨hleft.1.tail, hleft.2.tail⟩
              ⟨hright.1.tail, hright.2.tail⟩
              htailCode
          exact congrArg (List.cons leftHead) htail

/-- Head recovery makes the subtype foliage-code function injective. -/
theorem foliage_injective
    (input : FUInput (α := α)) :
    Function.Injective
      (fun sequence :
        { sequence : List (HallTree α) //
          OrderedSequence sequence } =>
        standardFoliageWord sequence.1) := by
  intro left right heq
  exact
    Subtype.ext
      (input.standard_foliage_injective
        left.2 right.2 heq)

/-- Head uniqueness supplies the global foliage-factorization predicate. -/
theorem factorizationInput
    (input : FUInput (α := α)) :
    FFInput (α := α) :=
  ⟨input.foliage_injective⟩

end FUInput

namespace FFInput

/-- Global foliage factorization restricts to an injective degreewise code. -/
theorem code_weight_injective
    (input : FFInput (α := α))
    (n : ℕ) :
    Function.Injective
      (sequenceFoliageCode (α := α) n) := by
  intro left right heq
  apply Subtype.ext
  have hglobal :
      (⟨left.1, left.2.1⟩ :
        { sequence : List (HallTree α) //
          OrderedSequence sequence }) =
        ⟨right.1, right.2.1⟩ := by
    apply input.foliage_injective
    exact congrArg Subtype.val heq
  exact congrArg
    (fun sequence :
      { sequence : List (HallTree α) //
        OrderedSequence sequence } =>
      sequence.1)
    hglobal

section FiniteAlphabet

variable [Fintype α]

/-- Global foliage factorization supplies the degreewise normal-form code. -/
noncomputable def formCodingInput
    (input : FFInput (α := α)) :
    PCInputa (α := α) where
  code := sequenceFoliageCode
  code_injective := input.code_weight_injective

/-- Global foliage factorization supplies integral Hall PBW uniqueness. -/
noncomputable def pbwUniquenessInt
    (input : FFInput (α := α)) :
    HPUniq (α := α) ℤ :=
  input.formCodingInput.pbwUniquenessInt

end FiniteAlphabet

end FFInput

end HallTree

namespace TCTex

universe u

/--
The classical ordered Hall foliage-factorization theorem supplies concrete
free-group associated-graded Hall bases in every positive weight.
-/
theorem forms_associated_foliage
    (d : ℕ)
    (input :
      HallTree.FFInput
        (α := FreeGenerator.{u} d)) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_pbw_uniqueness
    d input.pbwUniquenessInt

end TCTex
end Submission


/-!
# List-level parsing lemmas for ordered Hall foliage words

The Hall foliage-factorization problem is a word-parsing problem.  This file
passes from free-monoid values to their underlying lists, records the exact
prefix and suffix identities needed by a recursive parser, and isolates a
parser-correctness interface which supplies the head-uniqueness input used by
the foliage-code reduction.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/-- The list of leaves of a Hall tree, read from left to right. -/
def foliageList (tree : HallTree α) : List α :=
  tree.foliageWord.toList

omit [Encodable α] in
@[simp]
theorem foliageList_atom
    (letter : α) :
    foliageList (atom letter) = [letter] :=
  rfl

omit [Encodable α] in
@[simp]
theorem foliageList_commutator
    (left right : HallTree α) :
    foliageList (commutator left right) =
      foliageList left ++ foliageList right :=
  rfl

omit [Encodable α] in
/-- The leaf-list length is the Hall weight. -/
@[simp]
theorem foliageList_length
    (tree : HallTree α) :
    tree.foliageList.length = tree.weight := by
  exact tree.foliageWord_length

omit [Encodable α] in
/-- Every Hall tree has at least one leaf. -/
theorem foliage_ne_nil
    (tree : HallTree α) :
    tree.foliageList ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp only [foliageList_length, List.length_nil] at hlength
  exact (Nat.ne_of_gt tree.weight_pos) hlength

omit [Encodable α] in
/-- The leaf list of a Hall tree is nonempty. -/
theorem foliage_length_pos
    (tree : HallTree α) :
    0 < tree.foliageList.length := by
  rw [foliageList_length]
  exact tree.weight_pos

/-- The list underlying the concatenated foliage code of a tree sequence. -/
def standardSequenceFoliage
    (sequence : List (HallTree α)) :
    List α :=
  (standardFoliageWord sequence).toList

omit [Encodable α] in
@[simp]
theorem sequence_foliage_nil :
    standardSequenceFoliage ([] : List (HallTree α)) = [] :=
  rfl

omit [Encodable α] in
@[simp]
theorem standard_foliage_cons
    (tree : HallTree α)
    (sequence : List (HallTree α)) :
    standardSequenceFoliage (tree :: sequence) =
      tree.foliageList ++ standardSequenceFoliage sequence :=
  rfl

omit [Encodable α] in
@[simp]
theorem standard_foliage_append
    (left right : List (HallTree α)) :
    standardSequenceFoliage (left ++ right) =
      standardSequenceFoliage left ++
        standardSequenceFoliage right := by
  simp only [standardSequenceFoliage,
    sequence_foliage_append, FreeMonoid.toList_mul]

omit [Encodable α] in
/-- The list-level foliage code has total Hall weight as its length. -/
@[simp]
theorem standard_foliage_length
    (sequence : List (HallTree α)) :
    (standardSequenceFoliage sequence).length =
      standardSequenceWeight sequence := by
  exact sequence_foliage_length sequence

omit [Encodable α] in
/-- The list-level code of an atom sequence is the original letter list. -/
@[simp]
theorem standard_foliage_atom
    (letters : List α) :
    standardSequenceFoliage (letters.map atom) = letters := by
  simp only [standardSequenceFoliage,
    sequence_foliage_atom, FreeMonoid.toList_ofList]

omit [Encodable α] in
/-- Equality of foliage codes can be checked on their underlying lists. -/
theorem standard_foliage_list
    {left right : List (HallTree α)} :
    standardFoliageWord left =
        standardFoliageWord right ↔
      standardSequenceFoliage left =
        standardSequenceFoliage right := by
  constructor
  · exact congrArg FreeMonoid.toList
  · intro heq
    exact FreeMonoid.toList.injective heq

omit [Encodable α] in
/-- The first Hall factor contributes a concrete prefix of a sequence code. -/
theorem foliage_sequence_cons
    (tree : HallTree α)
    (sequence : List (HallTree α)) :
    tree.foliageList <+:
      standardSequenceFoliage (tree :: sequence) := by
  rw [standard_foliage_cons]
  exact List.prefix_append _ _

omit [Encodable α] in
/-- Taking the first factor's weight recovers its full foliage list. -/
@[simp]
theorem take_foliage_cons
    (tree : HallTree α)
    (sequence : List (HallTree α)) :
    (standardSequenceFoliage (tree :: sequence)).take tree.weight =
      tree.foliageList := by
  rw [standard_foliage_cons, ← foliageList_length]
  exact List.take_left

omit [Encodable α] in
/-- Dropping the first factor's weight recovers the tail foliage code. -/
@[simp]
theorem drop_foliage_cons
    (tree : HallTree α)
    (sequence : List (HallTree α)) :
    (standardSequenceFoliage (tree :: sequence)).drop tree.weight =
      standardSequenceFoliage sequence := by
  rw [standard_foliage_cons, ← foliageList_length]
  exact List.drop_left

omit [Encodable α] in
/-- The left child contributes the prefix of a composite Hall foliage list. -/
theorem foliage_prefix_commutator
    (left right : HallTree α) :
    left.foliageList <+: (commutator left right).foliageList := by
  rw [foliageList_commutator]
  exact List.prefix_append _ _

omit [Encodable α] in
/-- Taking the left child's weight recovers the left foliage block. -/
@[simp]
theorem take_foliage_commutator
    (left right : HallTree α) :
    (commutator left right).foliageList.take left.weight =
      left.foliageList := by
  rw [foliageList_commutator, ← foliageList_length]
  exact List.take_left

omit [Encodable α] in
/-- Dropping the left child's weight recovers the right foliage block. -/
@[simp]
theorem drop_foliage_commutator
    (left right : HallTree α) :
    (commutator left right).foliageList.drop left.weight =
      right.foliageList := by
  rw [foliageList_commutator, ← foliageList_length]
  exact List.drop_left

/--
A concrete recursive Hall parser: on every nonempty ordered normal form, it
recovers the first Hall factor from the list of leaves.
-/
structure FPInput where
  parser : List α → Option (HallTree α)
  parser_some_head :
    ∀ {head : HallTree α}
      {tail : List (HallTree α)},
      OrderedSequence (head :: tail) →
      parser (standardSequenceFoliage (head :: tail)) = some head

namespace FPInput

/-- A correct list-level Hall parser gives equality of heads of equal codes. -/
theorem head_list
    (input : FPInput (α := α))
    {leftHead rightHead : HallTree α}
    {leftTail rightTail : List (HallTree α)}
    (hleft : OrderedSequence (leftHead :: leftTail))
    (hright : OrderedSequence (rightHead :: rightTail))
    (heq :
      standardSequenceFoliage (leftHead :: leftTail) =
        standardSequenceFoliage (rightHead :: rightTail)) :
    leftHead = rightHead := by
  apply Option.some.inj
  rw [← input.parser_some_head hleft,
    heq, input.parser_some_head hright]

/-- A correct list-level parser supplies the recursive head-uniqueness input. -/
def headUniquenessInput
    (input : FPInput (α := α)) :
    FUInput (α := α) where
  head_code hleft hright heq :=
    input.head_list hleft hright
      (standard_foliage_list.mp heq)

/-- A correct list-level parser supplies global ordered foliage factorization. -/
def factorizationInput
    (input : FPInput (α := α)) :
    FFInput (α := α) :=
  input.headUniquenessInput.factorizationInput

end FPInput

end HallTree
end Submission


/-!
# Right-to-left contraction of Hall foliage words

Reading a foliage word from right to left gives a direct parser for its
ordered Hall factors.  When a newly read factor is larger than the first
already-parsed factor, contract that descending pair into its Hall
commutator and continue.  The recursive Hall admissibility inequality is
exactly what reconstructs a basic commutator from the foliage of its two
children.

This proves the classical ordered foliage-factorization theorem needed by the
Hall PBW reduction, and therefore supplies the concrete free-group
associated-graded Hall basis theorem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/--
Insert one parsed Hall factor on the left of an already-parsed suffix.  A
descending boundary contracts and is tested against the shorter suffix.
-/
def contractLeft :
    HallTree α → List (HallTree α) → List (HallTree α)
  | tree, [] => [tree]
  | tree, right :: suffix =>
      if right < tree then
        contractLeft (commutator tree right) suffix
      else
        tree :: right :: suffix

/-- An ordered boundary is left unchanged by left contraction. -/
theorem contract_cons_forall
    (tree : HallTree α)
    (suffix : List (HallTree α))
    (hle : ∀ right ∈ suffix, tree ≤ right) :
    contractLeft tree suffix = tree :: suffix := by
  cases suffix with
  | nil =>
      rfl
  | cons right suffix =>
      simp only [contractLeft]
      rw [if_neg]
      exact not_lt_of_ge (hle right (by simp))

/--
Prepending a basic tree to a standard suffix remains standard when the tree
is bounded above by every suffix factor.
-/
theorem standard_cons_forall
    {tree : HallTree α}
    {suffix : List (HallTree α)}
    (hbasic : tree.IsBasic)
    (hsuffix : ISSequen suffix)
    (hle : ∀ right ∈ suffix, tree ≤ right) :
    ISSequen (tree :: suffix) := by
  refine ⟨hbasic, ?_, hsuffix⟩
  cases tree with
  | atom letter =>
      trivial
  | commutator left right =>
      intro x hx
      exact (lt_commutator_right left right).le.trans (hle x hx)

/--
Contracting the atomic foliage of one standard-sequence head is the same as
contracting the head itself.  This is the recursive core of the Hall parser.
-/
theorem foliage_foldr_contract :
    ∀ (tree : HallTree α)
      (suffix : List (HallTree α)),
      ISSequen (tree :: suffix) →
      tree.foliageList.foldr
          (fun letter parsed => contractLeft (atom letter) parsed)
          suffix =
        contractLeft tree suffix
  | atom letter, suffix, _ => by
      rfl
  | commutator left right, suffix, hstandard => by
      have hrootBasic : (commutator left right).IsBasic :=
        hstandard.head_isBasic
      rcases (isBasic_commutator left right).mp hrootBasic with
        ⟨hleftBasic, hrightBasic, hrightLeft, hadmissible⟩
      have hrightLe :
          ∀ x ∈ suffix, right ≤ x :=
        hstandard.2.1
      have hsuffixStandard :
          ISSequen suffix :=
        hstandard.tail
      have hrightStandard :
          ISSequen (right :: suffix) :=
        standard_cons_forall
          hrightBasic hsuffixStandard hrightLe
      have hleftStandard :
          ISSequen (left :: right :: suffix) := by
        refine ⟨hleftBasic, ?_, hrightStandard⟩
        cases left with
        | atom letter =>
            trivial
        | commutator leftLeft leftRight =>
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hadmissible
            · exact hadmissible.trans (hrightLe x hx)
      rw [foliageList_commutator, List.foldr_append,
        foliage_foldr_contract
          right suffix hrightStandard,
        contract_cons_forall right suffix hrightLe,
        foliage_foldr_contract
          left (right :: suffix) hleftStandard]
      simp only [contractLeft, if_pos hrightLeft]

/-- Parse a leaf list into Hall factors by right-to-left contraction. -/
def contractFoliageList
    (letters : List α) :
    List (HallTree α) :=
  letters.foldr
    (fun letter parsed => contractLeft (atom letter) parsed)
    []

/--
Right-to-left foliage contraction recovers every ordered standard Hall
sequence exactly.
-/
theorem contract_foliage_sequence
    {sequence : List (HallTree α)}
    (hsequence : OrderedSequence sequence) :
    contractFoliageList (standardSequenceFoliage sequence) =
      sequence := by
  induction sequence with
  | nil =>
      rfl
  | cons tree suffix ih =>
      have hsuffix :
          OrderedSequence suffix :=
        ⟨hsequence.1.tail, hsequence.2.tail⟩
      have htreeLe :
          ∀ right ∈ suffix, tree ≤ right := by
        have hordered := hsequence.2
        rw [IsOrderedSequence, List.pairwise_cons] at hordered
        exact hordered.1
      rw [standard_foliage_cons]
      rw [contractFoliageList, List.foldr_append]
      change
        tree.foliageList.foldr
            (fun letter parsed => contractLeft (atom letter) parsed)
            (contractFoliageList (standardSequenceFoliage suffix)) =
          tree :: suffix
      rw [ih hsuffix]
      rw [foliage_foldr_contract
        tree suffix hsequence.1]
      exact contract_cons_forall tree suffix htreeLe

/--
Concatenated foliage lists distinguish ordered standard Hall sequences.
-/
theorem standard_sequence_foliage :
    ∀ {left right : List (HallTree α)},
      OrderedSequence left →
      OrderedSequence right →
      standardSequenceFoliage left =
        standardSequenceFoliage right →
      left = right := by
  intro left right hleft hright heq
  calc
    left =
        contractFoliageList (standardSequenceFoliage left) :=
      (contract_foliage_sequence hleft).symm
    _ =
        contractFoliageList (standardSequenceFoliage right) :=
      congrArg contractFoliageList heq
    _ = right :=
      contract_foliage_sequence hright

/--
Concatenated foliage words distinguish ordered standard Hall sequences.
-/
theorem standard_foliage_ordered :
    ∀ {left right : List (HallTree α)},
      OrderedSequence left →
      OrderedSequence right →
      standardFoliageWord left =
        standardFoliageWord right →
      left = right := by
  intro left right hleft hright heq
  exact
    standard_sequence_foliage
      hleft hright
      (standard_foliage_list.mp heq)

/-- The concrete list parser returning only the recovered head factor. -/
def contractFoliageHead
    (letters : List α) :
    Option (HallTree α) :=
  (contractFoliageList letters).head?

/-- On a nonempty ordered standard sequence, the concrete parser finds its head. -/
theorem contract_foliage_cons
    {head : HallTree α}
    {tail : List (HallTree α)}
    (hsequence : OrderedSequence (head :: tail)) :
    contractFoliageHead
        (standardSequenceFoliage (head :: tail)) =
      some head := by
  rw [contractFoliageHead,
    contract_foliage_sequence hsequence]
  rfl

/-- The right-to-left contraction parser realizes the parser interface. -/
def foliageParserInput :
    FPInput (α := α) where
  parser := contractFoliageHead
  parser_some_head := contract_foliage_cons

/-- The classical ordered Hall foliage-factorization theorem. -/
def foliageFactorizationInput :
    FFInput (α := α) :=
  foliageParserInput.factorizationInput

end HallTree

namespace TCTex

universe u

/--
The images of the concrete Hall basic commutators form a basis in every
positive free-group lower-central associated-graded weight.
-/
theorem commutators_forms_basis
    (d : ℕ) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_associated_foliage
    d HallTree.foliageFactorizationInput

/--
Below the truncation class, the concrete Hall basic commutators also form a
basis in the lower-central associated graded of the free nilpotent truncation.
-/
theorem concrete_forms_associated
    (d n r : ℕ)
    (hr : 0 < r)
    (hrn : r < n) :
    (concreteCommutatorsWeight.{u} d r).FormsAssocGradedbasis
      (n := n) :=
  BCWta.formassograd_basisformsfree_groassgrabas
    (concreteCommutatorsWeight.{u} d r) hr hrn
    (commutators_forms_basis d r hr)

end TCTex
end Submission


/-!
# Hall PBW basis reduced to normal-form uniqueness

Executable Hall collection gives a surjective evaluation map from coordinates
supported on ordered Hall standard sequences to the free associative algebra.
This file isolates the remaining PBW uniqueness input and packages the linear
equivalence and basis that follow from it.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Encodable α]

/--
The remaining uniqueness input for the Hall PBW theorem: evaluation of ordered
Hall standard-sequence coordinates is injective.
-/
structure PUInput
    (R : Type*) [CommRing R] : Prop where
  injective :
    Function.Injective
      (standardSequenceLinear (α := α) R)

namespace PUInput

/--
PBW uniqueness and executable Hall collection identify ordered normal-form
coordinates with the free associative algebra.
-/
noncomputable def linearEquiv
    (R : Type*) [CommRing R]
    (P : PUInput (α := α) R) :
    orderedStandardSubmodule (α := α) R ≃ₗ[R]
      AssociativeWordPolynomial R α :=
  LinearEquiv.ofBijective
    (standardSequenceLinear R)
    ⟨P.injective, ordered_sequence_surjective R⟩

/--
Under PBW uniqueness, ordered Hall standard sequences form a basis of the free
associative algebra.
-/
noncomputable def basis
    (R : Type*) [CommRing R]
    (P : PUInput (α := α) R) :
    Module.Basis
      { sequence : List (HallTree α) // OrderedSequence sequence }
      R
      (AssociativeWordPolynomial R α) :=
  Module.Basis.ofRepr <|
    P.linearEquiv R |>.symm |>.trans <|
      Finsupp.supportedEquivFinsupp
        { sequence : List (HallTree α) | OrderedSequence sequence }

/-- The PBW basis vector indexed by a normal form is its polynomial product. -/
theorem basis_apply
    (R : Type*) [CommRing R]
    (P : PUInput (α := α) R)
    (sequence :
      { sequence : List (HallTree α) // OrderedSequence sequence }) :
    P.basis R sequence =
      associativeWordProduct R sequence := by
  rw [basis, Module.Basis.coe_ofRepr]
  change
    P.linearEquiv R
        ((Finsupp.supportedEquivFinsupp
          { sequence : List (HallTree α) |
            OrderedSequence sequence }).symm
          (Finsupp.single sequence 1)) =
      associativeWordProduct R sequence
  have hsingle :
      (Finsupp.supportedEquivFinsupp
          { sequence : List (HallTree α) |
            OrderedSequence sequence }).symm
          (Finsupp.single sequence (1 : R)) =
        ⟨Finsupp.single (sequence : List (HallTree α)) 1,
          Finsupp.single_mem_supported R 1 sequence.property⟩ := by
    apply Subtype.ext
    exact
      Finsupp.supportedEquivFinsupp_symm_single
        { sequence : List (HallTree α) |
          OrderedSequence sequence }
        sequence 1
  rw [hsingle]
  simp [linearEquiv, standardSequenceLinear,
    hallSequenceLinear]

/--
PBW uniqueness therefore supplies linear independence of all ordered Hall
standard-sequence polynomial products.
-/
theorem polynomial_linear_independent
    (R : Type*) [CommRing R]
    (P : PUInput (α := α) R) :
    LinearIndependent R fun sequence :
        { sequence : List (HallTree α) // OrderedSequence sequence } =>
      associativeWordProduct R (sequence : List (HallTree α)) := by
  rw [show
    (fun sequence :
        { sequence : List (HallTree α) // OrderedSequence sequence } =>
      associativeWordProduct R (sequence : List (HallTree α))) =
      P.basis R by
        funext sequence
        exact (P.basis_apply R sequence).symm]
  exact (P.basis R).linearIndependent

end PUInput

end HallTree
end Submission


noncomputable section

namespace Submission

namespace HallTree

universe u

open TBluepr

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
A sequence-level signed leading-word certificate for Hall PBW normal forms.
-/
structure SSPivotsa
    (R : Type*) [CommRing R] where
  standardWord :
    { sequence : List (HallTree α) // OrderedSequence sequence } →
      FreeMonoid α
  diagonal :
    ∀ sequence :
        { sequence : List (HallTree α) // OrderedSequence sequence },
      associativeWordProduct R (sequence : List (HallTree α))
          (standardWord sequence) = 1 ∨
        associativeWordProduct R (sequence : List (HallTree α))
          (standardWord sequence) = -1
  offDiagonal :
    ∀ sequence other :
        { sequence : List (HallTree α) // OrderedSequence sequence },
      sequence ≠ other →
        associativeWordProduct R (other : List (HallTree α))
          (standardWord sequence) = 0

namespace SSPivotsa

omit [Fintype α] [DecidableEq α] in
theorem polynomial_linear_independent
    (R : Type*) [CommRing R]
    (P : SSPivotsa (α := α) R) :
    LinearIndependent R fun sequence :
        { sequence : List (HallTree α) // OrderedSequence sequence } =>
      associativeWordProduct R (sequence : List (HallTree α)) :=
  finsupp_linear_pivot
    R
    (fun sequence :
      { sequence : List (HallTree α) // OrderedSequence sequence } =>
      associativeWordProduct R (sequence : List (HallTree α)))
    P.standardWord P.diagonal P.offDiagonal

omit [Fintype α] [DecidableEq α] in
theorem combination_supported_finsupp
    (R : Type*) [CommRing R]
    (coordinates : orderedStandardSubmodule (α := α) R) :
    standardSequenceLinear R coordinates =
      Finsupp.linearCombination R (fun sequence :
          { sequence : List (HallTree α) // OrderedSequence sequence } =>
        associativeWordProduct R (sequence : List (HallTree α)))
        ((Finsupp.supportedEquivFinsupp
          { sequence : List (HallTree α) |
            OrderedSequence sequence }) coordinates) := by
  rw [standardSequenceLinear,
    LinearMap.comp_apply, hallSequenceLinear,
    Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply]
  change
    coordinates.1.sum (fun i a => a • associativeWordProduct R i) =
      (coordinates.1.subtypeDomain fun sequence =>
        OrderedSequence sequence).sum
          (fun i a => a • associativeWordProduct R i.1)
  exact (Finsupp.sum_subtypeDomain_index coordinates.property).symm

noncomputable def hallPBWUniqueness
    (R : Type*) [CommRing R]
    (P : SSPivotsa (α := α) R) :
    HPUniq (α := α) R where
  eval_injective := by
    intro left right heval
    apply (Finsupp.supportedEquivFinsupp
      { sequence : List (HallTree α) |
        OrderedSequence sequence }).injective
    apply (P.polynomial_linear_independent R).finsuppLinearCombination_injective
    exact
      (combination_supported_finsupp
          R left).symm.trans
        (heval.trans
          (combination_supported_finsupp
            R right))

noncomputable def pbwUniquenessInput
    (R : Type*) [CommRing R]
    (P : SSPivotsa (α := α) R) :
    PUInput (α := α) R where
  injective := (P.hallPBWUniqueness R).eval_injective

end SSPivotsa

end HallTree

namespace TCTex

universe u

theorem commutators_forms_pivots
    (d : ℕ)
    (P : HallTree.SSPivotsa
      (α := FreeGenerator.{u} d) ℤ) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_pbw_uniqueness
    d (P.hallPBWUniqueness ℤ)

end TCTex

end Submission

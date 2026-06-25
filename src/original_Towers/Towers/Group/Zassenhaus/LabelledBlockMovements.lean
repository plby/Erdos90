import Towers.Group.Zassenhaus.LabelledWordMovements

/-!
# Exact movements of finite labelled Hall-Petresco blocks

The row movement layer bubbles one labelled word rightward across a finite
list.  This file records two corresponding finite block movements.

The first recursively bubbles each head across the full row produced by its
tail.  The second is the packet-preserving transposition used by product and
inverse collection: process the left block from the right, bubble across only
the active row, and retain already moved parent words as a settled suffix.

Both are literal finite Hall rewrite schedules.  They deliberately retain
every generated correction word.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace HLMoveme

open BBSched
open PLMoveme

/--
Concrete endpoint after recursively bubbling every left word across the full
row produced by its tail.  Earlier left words also cross corrections and parent
words retained while later left words move.
-/
def movedRightBlock
    {M N : ℕ} :
    List (BatchLabelledWord M N) →
      List (BatchLabelledWord M N) →
        List (BatchLabelledWord M N)
  | [], right =>
      right
  | B :: left, right =>
      movedRightAcross B (movedRightBlock left right)

@[simp]
lemma moved_block_nil
    {M N : ℕ}
    (right : List (BatchLabelledWord M N)) :
    movedRightBlock [] right = right :=
  rfl

@[simp]
lemma moved_block_cons
    {M N : ℕ}
    (B : BatchLabelledWord M N)
    (left right : List (BatchLabelledWord M N)) :
    movedRightBlock (B :: left) right =
      movedRightAcross B (movedRightBlock left right) :=
  rfl

@[simp]
lemma moved_block_singleton
    {M N : ℕ}
    (B : BatchLabelledWord M N)
    (right : List (BatchLabelledWord M N)) :
    movedRightBlock [B] right = movedRightAcross B right :=
  rfl

/--
Bubble a complete finite left block rightward across a finite right block by
an explicit finite run of primitive adjacent Hall rewrites.
-/
lemma rewrites_moved_block
    {M N : ℕ} :
    ∀ (left right : List (BatchLabelledWord M N)),
      LWRw
        (left ++ right)
        (movedRightBlock left right)
  | [], _right =>
      Relation.ReflTransGen.refl
  | B :: left, right => by
      have htail :
          LWRw
            (B :: (left ++ right))
            (B :: movedRightBlock left right) := by
        simpa using
          (rewrites_moved_block left right).context [B] []
      exact htail.trans
        (rewrites_moved_right B (movedRightBlock left right))

/-- Bubble a complete finite block inside an arbitrary concrete list context. -/
lemma rewrites_moved_context
    {M N : ℕ}
    (P S left right : List (BatchLabelledWord M N)) :
    LWRw
      (P ++ (left ++ right) ++ S)
      (P ++ movedRightBlock left right ++ S) :=
  (rewrites_moved_block left right).context P S

/-- Finite block bubbling preserves the ordered labelled-word evaluation. -/
lemma labelled_moved_block
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    HACoeff.labelledListEval
        (movedRightBlock left right) =
      HACoeff.labelledListEval (left ++ right) :=
  (rewrites_moved_block left right).listEval_eq

/--
The emitted active prefix of one row movement.  Appending the moved word
recovers `movedRightAcross`.
-/
def movedRightPrefix
    {M N : ℕ}
    (B : BatchLabelledWord M N) :
    List (BatchLabelledWord M N) →
      List (BatchLabelledWord M N)
  | [] =>
      []
  | A :: row =>
      batchCorrection B A :: A :: movedRightPrefix B row

@[simp]
lemma moved_prefix_append
    {M N : ℕ}
    (B : BatchLabelledWord M N) :
    ∀ row : List (BatchLabelledWord M N),
      movedRightAcross B row =
        movedRightPrefix B row ++ [B]
  | [] =>
      rfl
  | A :: row => by
      rw [moved_right_cons, moved_prefix_append]
      rfl

/--
The active row prefix consists, up to permutation, of the newly emitted
Cartesian correction row followed by the original active row.
-/
lemma moved_row_append
    {M N : ℕ}
    (B : BatchLabelledWord M N) :
    ∀ row : List (BatchLabelledWord M N),
      List.Perm (movedRightPrefix B row)
        (rowCorrections B row ++ row)
  | [] =>
      List.Perm.refl []
  | A :: row => by
      have ih := moved_row_append B row
      have hmiddle :
          List.Perm
            (A :: rowCorrections B row ++ row)
            (rowCorrections B row ++ A :: row) := by
        have hcomm :
            List.Perm
              (([A] : List (BatchLabelledWord M N)) ++ rowCorrections B row)
              (rowCorrections B row ++ [A]) :=
          List.perm_append_comm
        simpa [List.append_assoc] using hcomm.append_right row
      simpa [movedRightPrefix, rowCorrections] using
        (List.Perm.cons (batchCorrection B A)
          ((List.Perm.cons A ih).trans hmiddle))

/--
Packet-preserving block transposition helper.  `reverseLeft` stores the
unmoved left parents from right to left; `settled` stores the already moved
parent suffix in its original order.
-/
def transposedReverseBlock
    {M N : ℕ} :
    List (BatchLabelledWord M N) →
      List (BatchLabelledWord M N) →
        List (BatchLabelledWord M N) →
          List (BatchLabelledWord M N)
  | [], active, settled =>
      active ++ settled
  | B :: reverseLeft, active, settled =>
      transposedReverseBlock reverseLeft
        (movedRightPrefix B active) (B :: settled)

/--
Active prefix emitted by packet-preserving block transposition.  The moved
left-parent block is omitted: it survives unchanged as a settled suffix.
-/
def transposedReversePrefix
    {M N : ℕ} :
    List (BatchLabelledWord M N) →
      List (BatchLabelledWord M N) →
        List (BatchLabelledWord M N)
  | [], active =>
      active
  | B :: reverseLeft, active =>
      transposedReversePrefix reverseLeft
        (movedRightPrefix B active)

/--
Concrete corrections emitted while packet-preserving block transposition
processes a reversed left-parent block.  Deeper corrections appear first,
matching the final active-prefix decomposition.
-/
def transposedReverseCorrections
    {M N : ℕ} :
    List (BatchLabelledWord M N) →
      List (BatchLabelledWord M N) →
        List (BatchLabelledWord M N)
  | [], _active =>
      []
  | B :: reverseLeft, active =>
      transposedReverseCorrections reverseLeft
          (movedRightPrefix B active) ++
        rowCorrections B active

/--
The active prefix is, up to permutation, the recursively emitted correction
list followed by the original active row.
-/
lemma transposed_perm_append
    {M N : ℕ} :
    ∀ (reverseLeft active : List (BatchLabelledWord M N)),
      List.Perm
        (transposedReversePrefix reverseLeft active)
        (transposedReverseCorrections reverseLeft active ++
          active)
  | [], _active =>
      List.Perm.refl _
  | B :: reverseLeft, active => by
      have ih :=
        transposed_perm_append
          reverseLeft (movedRightPrefix B active)
      have hrow :=
        moved_row_append B active
      simpa [transposedReversePrefix,
        transposedReverseCorrections, List.append_assoc] using
          ih.trans
            (List.Perm.append_left
              (transposedReverseCorrections reverseLeft
                (movedRightPrefix B active))
              hrow)

/--
The packet-preserving helper splits into its emitted active prefix, unchanged
left-parent block, and pre-existing settled suffix.
-/
lemma transposed_reverse_append
    {M N : ℕ} :
    ∀ (reverseLeft active settled : List (BatchLabelledWord M N)),
      transposedReverseBlock reverseLeft active settled =
        transposedReversePrefix reverseLeft active ++
          reverseLeft.reverse ++ settled
  | [], _active, _settled => by
      simp [transposedReverseBlock,
        transposedReversePrefix]
  | B :: reverseLeft, active, settled => by
      rw [transposedReverseBlock,
        transposedReversePrefix,
        transposed_reverse_append]
      simp [List.append_assoc]

/--
The packet-preserving helper is reached by explicit Hall rewrites from the
unmoved left block, active row, and settled parent suffix.
-/
lemma rewrites_transposed_reverse
    {M N : ℕ} :
    ∀ (reverseLeft active settled : List (BatchLabelledWord M N)),
      LWRw
        (reverseLeft.reverse ++ active ++ settled)
        (transposedReverseBlock reverseLeft active settled)
  | [], _active, _settled =>
      Relation.ReflTransGen.refl
  | B :: reverseLeft, active, settled => by
      have hmove :
          LWRw
            ((B :: reverseLeft).reverse ++ active ++ settled)
            (reverseLeft.reverse ++
              movedRightPrefix B active ++ B :: settled) := by
        simpa [List.append_assoc] using
          (rewrites_moved_right B active).context
            reverseLeft.reverse settled
      exact hmove.trans
        (rewrites_transposed_reverse reverseLeft
          (movedRightPrefix B active) (B :: settled))

/--
Transpose one finite left parent block rightward across one active right row,
preserving the original order of the moved left parent suffix.
-/
def transposedRightBlock
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    List (BatchLabelledWord M N) :=
  transposedReverseBlock left.reverse right []

/-- Concrete correction list emitted by packet-preserving block transposition. -/
def transposedBlockCorrections
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    List (BatchLabelledWord M N) :=
  transposedReverseCorrections left.reverse right

/--
Packet-preserving transposition exposes one active prefix followed by the
unchanged moved left-parent block.
-/
lemma transposed_prefix_append
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    transposedRightBlock left right =
      transposedReversePrefix left.reverse right ++ left := by
  rw [transposedRightBlock,
    transposed_reverse_append]
  simp

/--
The concrete transposition endpoint consists, up to permutation, of its
recursively emitted corrections followed by the swapped parent blocks.
-/
lemma transposed_perm_parents
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    List.Perm (transposedRightBlock left right)
      (transposedBlockCorrections left right ++ right ++ left) := by
  rw [transposed_prefix_append]
  exact
    (transposed_perm_append
      left.reverse right).append_right left

/--
Packet-preserving block transposition is an explicit finite run of primitive
adjacent Hall rewrites.
-/
lemma rewrites_transposed_block
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    LWRw
      (left ++ right)
      (transposedRightBlock left right) := by
  simpa [transposedRightBlock] using
    rewrites_transposed_reverse left.reverse right []

/--
Packet-preserving transposition reaches the exposed active prefix followed by
the unchanged left-parent block.
-/
lemma rewrites_transposed_append
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    LWRw
      (left ++ right)
      (transposedReversePrefix left.reverse right ++ left) := by
  simpa [transposed_prefix_append] using
    rewrites_transposed_block left right

/-- Packet-preserving finite block transposition preserves ordered evaluation. -/
lemma labelled_transposed_block
    {M N : ℕ}
    (left right : List (BatchLabelledWord M N)) :
    HACoeff.labelledListEval
        (transposedRightBlock left right) =
      HACoeff.labelledListEval (left ++ right) :=
  (rewrites_transposed_block left right).listEval_eq

/--
The first nested left correction appears when two left parents move across one
right parent.  This is the operational orientation used by the recursive
packet layer.
-/
@[simp]
lemma transposed_right_block
    {M N : ℕ}
    (B0 B1 A : BatchLabelledWord M N) :
    transposedRightBlock [B0, B1] [A] =
      [batchCorrection B0 (batchCorrection B1 A),
        batchCorrection B1 A, batchCorrection B0 A, A, B0, B1] :=
  rfl

end HLMoveme
end TCTex
end Towers

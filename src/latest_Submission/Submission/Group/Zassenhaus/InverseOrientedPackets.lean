import Submission.Group.Zassenhaus.PermutedPacketWorklist
import Submission.Group.Zassenhaus.CompletePetrescoRecipe

/-!
# Inverse-oriented Hall-Petresco packets

Concrete Hall collection repeatedly conjugates an already emitted positive
commutator past earlier words.  The correction created by that move is
inverse-oriented: `[D^-1, a]`.  At the word level the existing collector
represents `D^-1` by `rootSwapWord D`; at the recipe level it is
`BFam.inverseCorrection`.

This file proves that root-swapping preserves closed collapsed packets and
constructs the corresponding permutation-aware work item.  It is
intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace HOPacket

open HACoeff
open HPWork
open BRSpec

/-- Root basic correction words in row-major order. -/
def basicWords
    (M N : ℕ) :
    List (CWord (LabelledAtom M N)) :=
  (labelledLeftAtoms M N).flatMap fun left =>
    (labelledRightAtoms M N).map fun right =>
      .commutator (.atom left) (.atom right)

/-- Counted family of all basic root corrections. -/
def basicFamily
    (M N : ℕ) :
    BFam M N where
  recipe := hallPair
  realizations := basicWords M N
  collapse_word := by
    intro w hw
    rcases List.mem_flatMap.mp hw with ⟨left, hleft, hw⟩
    rcases List.mem_map.mp hw with ⟨right, hright, rfl⟩
    simp [collapseWord, collapse_label_atoms hleft,
      collapse_labelled_atoms hright,
      erased_shape_pair, CWord.hallPairBase]
  length_eq := by
    change
      (basicWords M N).length =
        Fintype.card (BRecipe.OrderEmbeddings [1] M) *
          Fintype.card (BRecipe.OrderEmbeddings [1] N)
    rw [BRecipe.card_orderEmbeddings, BRecipe.card_orderEmbeddings]
    simp [basicWords, labelledLeftAtoms, labelledRightAtoms, List.sum_ofFn]

@[simp]
lemma recipe_basicFamily
    (M N : ℕ) :
    (basicFamily M N).recipe = hallPair :=
  rfl

@[simp]
lemma realizations_basicFamily
    (M N : ℕ) :
    (basicFamily M N).realizations = basicWords M N :=
  rfl

/-- Root-swap every concrete word in one collapsed packet. -/
def rootSwapWords
    {M N : ℕ}
    (words : List (CWord (LabelledAtom M N))) :
    List (CWord (LabelledAtom M N)) :=
  words.map rootSwapWord

@[simp]
lemma swap_words_realizations
    {M N : ℕ}
    (F : BFam M N) :
    rootSwapWords F.realizations = F.rootSwap.realizations :=
  rfl

/-- Root-swapping preserves a common collapsed Hall shape. -/
lemma same_collapsed_words
    {M N : ℕ}
    {F : BFam M N}
    {words : List (CWord (LabelledAtom M N))}
    (hshape :
      PCCounti.SCShape
        F.recipe.erasedShape words) :
    PCCounti.SCShape
      F.rootSwap.recipe.erasedShape (rootSwapWords words) := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨u, hu, rfl⟩
  rw [collapse_root_swap, hshape u hu, BFam.recipe_rootSwap,
    BRecipe.erased_shape_swap]

/-- Root-swapping preserves exact collapsed-packet closure. -/
lemma collapsed_swap_words
    {M N : ℕ}
    {F : BFam M N}
    {words : List (CWord (LabelledAtom M N))}
    (hpacket :
      PCCounti.CPFor F words) :
    PCCounti.CPFor
      F.rootSwap (rootSwapWords words) where
  same_shape := same_collapsed_words hpacket.same_shape
  length_eq := by
    calc
      (rootSwapWords words).length = words.length := by
        simp [rootSwapWords]
      _ = F.realizations.length := hpacket.length_eq
      _ = F.rootSwap.realizations.length := by
        simp [BFam.rootSwap]

/--
Pair each root-swapped right-parent word with each left-parent word.  This is
the concrete packet for the inverse-oriented recipe `[A^-1, B]`.
-/
def inverseCorrectionWords
    {M N : ℕ}
    (left right : List (CWord (LabelledAtom M N))) :
    List (CWord (LabelledAtom M N)) :=
  PCCounti.correctionWords
    (rootSwapWords right) left

@[simp]
lemma inverse_words_realizations
    {M N : ℕ}
    (B A : BFam M N) :
    inverseCorrectionWords B.realizations A.realizations =
      (B.inverseCorrection A).realizations := by
  rfl

/-- Closed parent packets produce a closed inverse-oriented correction packet. -/
lemma PCCounti.CPFor.inverseCorrectionWords
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft :
      PCCounti.CPFor B left)
    (hright :
      PCCounti.CPFor A right) :
    PCCounti.CPFor
      (B.inverseCorrection A) (inverseCorrectionWords left right) := by
  exact (collapsed_swap_words hright).correctionWords hleft

/--
Initial permutation-aware ledger for an inverse-oriented correction packet.
Its ordinary left family is `A.rootSwap`, so the emitted correction family is
definitionally `B.inverseCorrection A`.
-/
def inverseInitialLedger
    {M N : ℕ}
    (B A : BFam M N) :
    PSLedger
      A.rootSwap B A.rootSwap.realizations B.realizations :=
  PSLedger.initial
    A.rootSwap B A.rootSwap.realizations B.realizations

namespace PWItem

/--
Canonical work item for the inverse-oriented packet `[A^-1, B]` emitted while
conjugating a previously produced `A` packet past a `B` packet.
-/
def inverseOrientedInitial
    {M N : ℕ}
    (B A : BFam M N) :
    PWItem M N :=
  PWItem.initial A.rootSwap B

@[simp]
lemma inverse_oriented_family
    {M N : ℕ}
    (B A : BFam M N) :
    (inverseOrientedInitial B A).leftFamily.correction
        (inverseOrientedInitial B A).rightFamily =
      B.inverseCorrection A :=
  rfl

@[simp]
lemma inverse_oriented_pending
    {M N : ℕ}
    (B A : BFam M N) :
    (inverseOrientedInitial B A).ledger.pending =
      inverseCorrectionWords B.realizations A.realizations :=
  rfl

end PWItem

/--
Raw packet histories generated by Hall collection.  A leading transposition
emits a direct correction.  Moving an already emitted packet past an earlier
parent emits the inverse-oriented correction `[A^-1, B]`.
-/
inductive PHistor
    (M N : ℕ) where
  | hallPair :
      PHistor M N
  | direct
      (left right : BFam M N) :
      PHistor M N
  | conjugate
      (parent : BFam M N)
      (emitted : PHistor M N) :
      PHistor M N

namespace PHistor

/-- Complete counted family represented by one raw Hall-collection history. -/
def family
    {M N : ℕ} :
    PHistor M N → BFam M N
  | .hallPair =>
      basicFamily M N
  | .direct left right =>
      left.correction right
  | .conjugate parent emitted =>
      parent.inverseCorrection emitted.family

@[simp]
lemma family_hallPair
    {M N : ℕ} :
    (hallPair : PHistor M N).family = basicFamily M N :=
  rfl

@[simp]
lemma family_direct
    {M N : ℕ}
    (left right : BFam M N) :
    (direct left right).family = left.correction right :=
  rfl

@[simp]
lemma family_conjugate
    {M N : ℕ}
    (parent : BFam M N)
    (emitted : PHistor M N) :
    (conjugate parent emitted).family =
      parent.inverseCorrection emitted.family :=
  rfl

/-- Weighted Hall degree of the packet family represented by one history. -/
def weight
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (history : PHistor M N) :
    ℕ :=
  BRSpec.weightedWordWeight
    leftWeight rightWeight history.family.recipe

@[simp]
lemma weight_hallPair
    {M N leftWeight rightWeight : ℕ} :
    (hallPair : PHistor M N).weight leftWeight rightWeight =
      leftWeight + rightWeight := by
  simp [weight]

@[simp]
lemma weight_direct
    {M N leftWeight rightWeight : ℕ}
    (left right : BFam M N) :
    (direct left right).weight leftWeight rightWeight =
      BRSpec.weightedWordWeight
          leftWeight rightWeight left.recipe +
        BRSpec.weightedWordWeight
          leftWeight rightWeight right.recipe := by
  change
    BRSpec.weightedWordWeight
        leftWeight rightWeight (left.correction right).recipe =
      _
  rw [BFam.recipe_correction,
    BRSpec.weighted_weight_correction]

@[simp]
lemma weight_conjugate
    {M N leftWeight rightWeight : ℕ}
    (parent : BFam M N)
    (emitted : PHistor M N) :
    (conjugate parent emitted).weight leftWeight rightWeight =
      BRSpec.weightedWordWeight
          leftWeight rightWeight parent.recipe +
        emitted.weight leftWeight rightWeight := by
  change
    BRSpec.weightedWordWeight
        leftWeight rightWeight
          (emitted.family.rootSwap.correction parent).recipe =
      _
  rw [BFam.recipe_correction,
    BRSpec.weighted_weight_correction,
    BFam.recipe_rootSwap,
    BRSpec.weighted_root_swap,
    Nat.add_comm]
  rfl

/-- Every inverse-oriented conjugation correction strictly increases weight. -/
lemma weight_lt_conjugate
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parent : BFam M N)
    (emitted : PHistor M N) :
    emitted.weight leftWeight rightWeight <
      (conjugate parent emitted).weight leftWeight rightWeight := by
  rw [weight_conjugate]
  have hparent :
      0 <
        BRSpec.weightedWordWeight
          leftWeight rightWeight parent.recipe :=
    BRSpec.weighted_weight_pos
      hleftWeight hrightWeight parent.recipe
  omega

/-- Initial work item for one leading direct packet history. -/
def directInitial
    {M N : ℕ}
    (left right : BFam M N) :
    PWItem M N :=
  PWItem.initial left right

@[simp]
lemma direct_initial_family
    {M N : ℕ}
    (left right : BFam M N) :
    (directInitial left right).leftFamily.correction
        (directInitial left right).rightFamily =
      (direct left right).family :=
  rfl

/-- Initial work item for one inverse-oriented conjugation history. -/
def conjugateInitial
    {M N : ℕ}
    (parent : BFam M N)
    (emitted : PHistor M N) :
    PWItem M N :=
  PWItem.inverseOrientedInitial parent emitted.family

@[simp]
lemma conjugate_initial_family
    {M N : ℕ}
    (parent : BFam M N)
    (emitted : PHistor M N) :
    (conjugateInitial parent emitted).leftFamily.correction
        (conjugateInitial parent emitted).rightFamily =
      (conjugate parent emitted).family :=
  rfl

end PHistor

end HOPacket
end TCTex
end Submission

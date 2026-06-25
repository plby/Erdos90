import Submission.Group.Zassenhaus.TransientResidual
import Submission.Group.Zassenhaus.Polynomial

/-!
# Strict tails around the basic transient Hall-Petresco term

The transient powered-bridge residual contains one same-stratum basic term
and higher-weight correction terms.  The basic term need not sit at either
end of the ordered packet: at cutoff four the packet is
`[leftTriple, basic, rightTriple]`.

This file records an ordered `prefix ++ basic :: suffix` interface and proves
that both nonbasic sides become strictly heavier after rewording.  It does not
commute or cancel those terms prematurely.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff
open BRSpec

namespace PTSubsti

/-- Every recipe in a tail has bidegree different from `(1, 1)`. -/
def SOTail
    (recipes : List BRecipe) :
    Prop :=
  ∀ R ∈ recipes, R.leftDegree ≠ 1 ∨ R.rightDegree ≠ 1

namespace SOTail

/-- The empty recipe list is a strict outer tail. -/
lemma nil :
    SOTail [] := by
  intro R hR
  simp at hR

/-- Concatenating strict tails preserves strictness. -/
lemma append
    {left right : List BRecipe}
    (hleft : SOTail left)
    (hright : SOTail right) :
    SOTail (left ++ right) := by
  intro R hR
  rcases List.mem_append.mp hR with hR | hR
  · exact hleft R hR
  · exact hright R hR

end SOTail

/--
Every member of a strict temporary reworded tail is physically heavier than
the original outer bracket.
-/
theorem outer_expansions_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    {recipes : List BRecipe}
    (htail : SOTail recipes)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        wordExpansions hinputWeight recipes (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)) :
    outerExpansion.word.weight PEAddres.weight <
      nextExpansion.word.weight PEAddres.weight := by
  rcases recipe_word_expansions hnext with ⟨R, hR, rfl⟩
  exact
    outer_reword_bidegree
      hinputWeight R outerExpansion innerWord rightWord hword (htail R hR)

/--
Reverse-negating a strict temporary tail preserves its strict physical
support bound.
-/
theorem
    expansions_reword_tail
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    {recipes : List BRecipe}
    (htail : SOTail recipes)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        TWExp.inverseList
          (wordExpansions hinputWeight recipes (outerExpansion.reword innerWord)
            (TWExp.wordUnit rightWord))) :
    outerExpansion.word.weight PEAddres.weight <
      nextExpansion.word.weight PEAddres.weight := by
  rw [TWExp.inverseList] at hnext
  rcases List.mem_map.mp hnext with ⟨sourceExpansion, hsource, rfl⟩
  rw [TWExp.word_neg]
  apply
    outer_expansions_reword
      hinputWeight htail outerExpansion innerWord rightWord hword
  simpa using hsource

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/--
An ordered packet decomposition around its same-stratum basic recipe.

Both sides are retained separately because inversion reverses the complete
temporary packet, so their relative position matters to later contextual
recollection.
-/
structure OBSplit
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) where
  beforeBasic :
    List BRecipe
  afterBasic :
    List BRecipe
  recipes_eq :
    packet.recipes = beforeBasic ++ hallPair :: afterBasic
  before_strict_tail :
    SOTail beforeBasic
  after_strict_tail :
    SOTail afterBasic

namespace OBSplit

/-- The nonbasic recipes on both sides form a strict outer tail. -/
def strictRecipes
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet) :
    List BRecipe :=
  split.beforeBasic ++ split.afterBasic

/-- Every recipe retained away from the basic term has nonbasic bidegree. -/
lemma strict_recipes_tail
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet) :
    SOTail split.strictRecipes :=
  split.before_strict_tail.append split.after_strict_tail

/-- Transient substitution preserves the ordered split around the basic term. -/
lemma expans_prefi_suffi
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    wordExpansions hinputWeight packet.recipes B A =
      wordExpansions hinputWeight split.beforeBasic B A ++
        [wordExpansion hinputWeight hallPair B A] ++
          wordExpansions hinputWeight split.afterBasic B A := by
  rw [split.recipes_eq]
  simp [wordExpansions]

/--
After inversion, the suffix moves before the basic inverse and the prefix
moves after it.  This is the ordered shape needed for contextual cancellation.
-/
lemma expans_suffi_prefi
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    TWExp.inverseList
        (wordExpansions hinputWeight packet.recipes B A) =
      TWExp.inverseList
          (wordExpansions hinputWeight split.afterBasic B A) ++
        [(wordExpansion hinputWeight hallPair B A).neg] ++
          TWExp.inverseList
            (wordExpansions hinputWeight split.beforeBasic B A) := by
  rw [split.expans_prefi_suffi]
  simp [TWExp.inverseList]

/--
The full residual source exposes both strict inverse tails around the basic
inverse, followed by the original outer carrier.
-/
lemma inner_after_before
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    packet.transientInnerReduction hinputWeight
        outerExpansion innerWord rightWord =
      TWExp.inverseList
          (wordExpansions hinputWeight split.afterBasic
            (outerExpansion.reword innerWord)
            (TWExp.wordUnit rightWord)) ++
        [(wordExpansion hinputWeight hallPair (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)).neg] ++
        TWExp.inverseList
            (wordExpansions hinputWeight split.beforeBasic
              (outerExpansion.reword innerWord)
              (TWExp.wordUnit rightWord)) ++
          [outerExpansion] := by
  rw [transientInnerReduction, transientWordExpansions,
    split.expans_suffi_prefi]

end OBSplit

/-- The cutoff-three singleton packet has an empty strict prefix and suffix. -/
def split_n_three
    {d n : ℕ}
    (hn : n ≤ 3) :
    OBSplit
      (n_three hn :
        PFSubsti.TAPkt.{u}
          d n) where
  beforeBasic := []
  afterBasic := []
  recipes_eq := by rfl
  before_strict_tail := SOTail.nil
  after_strict_tail := SOTail.nil

/--
The cutoff-four packet keeps the left triple before the basic term and the
right triple after it.
-/
def split_n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    OBSplit
      (n_four hn :
        PFSubsti.TAPkt.{u}
          d n) where
  beforeBasic := [leftTriple]
  afterBasic := [rightTriple]
  recipes_eq := by rfl
  before_strict_tail := by
    intro R hR
    simp only [List.mem_singleton] at hR
    subst R
    left
    simp [leftTriple, BRecipe.leftDegree]
  after_strict_tail := by
    intro R hR
    simp only [List.mem_singleton] at hR
    subst R
    right
    simp [rightTriple, BRecipe.rightDegree]

end PFSubsti.TAPkt

end TCTex
end Submission

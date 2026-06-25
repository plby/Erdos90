import Towers.Group.Zassenhaus.TransientExponentCarriers

/-!
# Transient Hall-Petresco packet substitution

Transient exponent carriers separate their arithmetic bound from the physical
weight of an attached Hall word.  This file lifts that separation over a
complete Hall-Petresco packet.  In particular, rewording a parent exponent
onto an inner Hall word always yields a finite ordered symbolic expansion of
`[inner ^ e, right]`, even when the parent recipe cannot be bounded by the
smaller inner word.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace TWExp

/-- Evaluate one transiently powered Hall word. -/
def value
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansion : TWExp H inputWeight) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  wordExpansion.word.eval
      PEAddres.freeLowerTruncation ^
    wordExpansion.exponent q

/-- Evaluate a finite ordered list of transiently powered Hall words. -/
def listValue
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansions :
      List (TWExp H inputWeight)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (wordExpansions.map fun wordExpansion => wordExpansion.value q).prod

end TWExp

namespace PTSubsti

@[simp]
lemma word_wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    (wordExpansion hinputWeight R B A).word = boundWord R B A :=
  rfl

@[simp]
lemma word_eval_expansion
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    (wordExpansion hinputWeight R B A).word.eval
        PEAddres.freeLowerTruncation =
      R.erasedShape.eval
        (HPAtom.eval
          (B.word.eval
            (PEAddres.freeLowerTruncation
              (n := n)))
          (A.word.eval
            (PEAddres.freeLowerTruncation
              (n := n)))) := by
  simp [wordExpansion, boundWord, CWord.eval_pair_bind]

/-- Attach a finite ordered recipe list to two transiently powered parents. -/
def wordExpansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : TWExp H inputWeight) :
    List (TWExp H inputWeight) :=
  recipes.map fun R => wordExpansion hinputWeight R B A

/-- Evaluate a finite ordered list of transiently substituted block recipes. -/
lemma list_value_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : TWExp H inputWeight)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (wordExpansions hinputWeight recipes B A) =
      (recipes.map fun R =>
        R.erasedShape.eval
            (HPAtom.eval
              (B.word.eval
                (PEAddres.freeLowerTruncation
                  (n := n)))
              (A.word.eval
                (PEAddres.freeLowerTruncation
                  (n := n)))) ^
          BRSpec.coefficientValue R
            (B.exponent q) (A.exponent q)).prod := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (wordExpansion hinputWeight R B A).word.eval
              PEAddres.freeLowerTruncation ^
            (wordExpansion hinputWeight R B A).exponent q *
          TWExp.listValue q
            (wordExpansions hinputWeight recipes B A) =
        _ * _
      rw [word_eval_expansion, exponent_wordExpansion, ih]
      rfl

/-- Every transient substituted word remembers its source block recipe. -/
lemma recipe_word_expansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hinputWeight : 0 < inputWeight}
    {recipes : List BRecipe}
    {B A : TWExp H inputWeight}
    {expansion : TWExp H inputWeight}
    (hexpansion :
      expansion ∈ wordExpansions hinputWeight recipes B A) :
    ∃ R ∈ recipes, expansion = wordExpansion hinputWeight R B A := by
  rcases List.mem_map.mp hexpansion with ⟨R, hR, rfl⟩
  exact ⟨R, hR, rfl⟩

/-- Transient recipe words are physically strictly above their left parent. -/
lemma left_weight_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    B.word.weight PEAddres.weight <
      (wordExpansion hinputWeight R B A).word.weight
        PEAddres.weight := by
  rw [word_wordExpansion, weight_boundWord]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R)) ?_
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.rightDegree_pos R)
      (CWord.weight_pos
        PEAddres.weight PEAddres.weight_pos
        A.word))

/-- Transient recipe words are physically strictly above their right parent. -/
lemma right_weight_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    A.word.weight PEAddres.weight <
      (wordExpansion hinputWeight R B A).word.weight
        PEAddres.weight := by
  rw [word_wordExpansion, weight_boundWord]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R)) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.leftDegree_pos R)
      (CWord.weight_pos
        PEAddres.weight PEAddres.weight_pos
        B.word))

@[simp]
lemma exponent_outer_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerReductionExpansion hinputWeight R factor innerWord
      rightWord).exponentWeight =
        R.leftDegree *
          factor.word.weight PEAddres.weight := by
  simp [innerReductionExpansion, wordExpansion,
    TWExp.rewordFactor,
    TWExp.wordUnit]

@[simp]
lemma inner_reduction_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerReductionExpansion hinputWeight R factor innerWord
      rightWord).word.weight PEAddres.weight =
        R.leftDegree *
            innerWord.weight PEAddres.weight +
          R.rightDegree *
            rightWord.weight PEAddres.weight := by
  exact weight_boundWord R
    (TWExp.rewordFactor factor innerWord)
    (TWExp.wordUnit rightWord)

end PTSubsti

namespace PFSubsti.TAPkt

/-- Unconditionally substitute two transiently powered parents into a packet. -/
def transientWordExpansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    List (TWExp H inputWeight) :=
  PTSubsti.wordExpansions
    hinputWeight packet.recipes B A

/-- The transient packet expansion evaluates to the parent commutator. -/
lemma transient_word_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (packet.transientWordExpansions hinputWeight B A) =
      ⁅B.value (n := n) q, A.value (n := n) q⁆ := by
  rw [transientWordExpansions,
    PTSubsti.list_value_expansions]
  let Bvalue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    B.word.eval
      (PEAddres.freeLowerTruncation
        (H := H) (n := n))
  let Avalue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    A.word.eval
      (PEAddres.freeLowerTruncation
        (H := H) (n := n))
  simpa [TWExp.value] using
    packet.listEval_eq Bvalue Avalue (B.exponent q) (A.exponent q)

/--
Unconditional transient expansion of `[inner ^ e, right]` for an arbitrary
ordinary parent factor reworded onto `inner`.
-/
def innerReductionExpansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (TWExp H inputWeight) :=
  packet.transientWordExpansions hinputWeight
    (TWExp.rewordFactor factor innerWord)
    (TWExp.wordUnit rightWord)

/--
The unconditional inner-reduction packet evaluates exactly to
`[inner ^ factor.exponent, right]`.
-/
lemma outer_transient_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (packet.innerReductionExpansions hinputWeight factor
          innerWord rightWord) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  simpa [innerReductionExpansions,
    TWExp.value] using
      packet.transient_word_expansions hinputWeight
        (TWExp.rewordFactor factor innerWord)
        (TWExp.wordUnit rightWord) q

end PFSubsti.TAPkt

end TCTex
end Towers

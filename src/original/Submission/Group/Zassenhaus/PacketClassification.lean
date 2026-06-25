import Submission.Group.Zassenhaus.Attachment

/-!
# Classifying transient inner-reduction packets

An inner-reduction Hall-Petresco packet contains two kinds of terms.  Terms
with `leftDegree ≤ rightDegree` can immediately return to the ordinary
bounded symbolic language.  Terms with excess left degree remain transient
and form the genuine post-cancellation frontier.

This file classifies packet terms without changing their order and proves
that the resulting mixed packet still evaluates to the original outer
commutator.  Keeping the order is essential: no commutation of attached terms
past frontier terms is assumed.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

/--
One ordered inner-reduction output is either back in the ordinary bounded
symbolic language or still on the transient excess-left frontier.
-/
inductive SOTerm
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight : ℕ) where
  | attached (wordExpansion : SWExp H inputWeight)
  | frontier
      (wordExpansion : TWExp H inputWeight)

namespace SOTerm

/-- Evaluate one mixed attached-or-frontier output. -/
def value
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ) :
    SOTerm H inputWeight →
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  | .attached wordExpansion =>
      wordExpansion.word.eval
            PEAddres.freeLowerTruncation ^
        wordExpansion.exponent q
  | .frontier wordExpansion => wordExpansion.value q

/-- Evaluate a finite mixed packet in its original order. -/
def listValue
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (terms : List (SOTerm H inputWeight)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (terms.map fun term => term.value q).prod

end SOTerm

namespace PTSubsti

/--
Classify one inner-reduction recipe term, attaching exactly the balanced-side
terms and preserving excess-left terms as transient outputs.
-/
def classifiedOuterTerm
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    SOTerm H inputWeight :=
  if hbalanced : R.leftDegree ≤ R.rightDegree then
    .attached
      (attachedInnerExpansion hinputWeight R factor
        innerWord rightWord hword hbalanced)
  else
    .frontier
      (innerReductionExpansion hinputWeight R factor innerWord
        rightWord)

/-- A balanced recipe is classified as an attached ordinary expansion. -/
lemma classified_outer_degree
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : R.leftDegree ≤ R.rightDegree) :
    classifiedOuterTerm hinputWeight R factor innerWord
        rightWord hword =
      .attached
        (attachedInnerExpansion hinputWeight R factor
          innerWord rightWord hword hbalanced) := by
  simp [classifiedOuterTerm, hbalanced]

/-- An excess-left recipe is classified as a transient frontier expansion. -/
lemma classified_inner_degree
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree) :
    classifiedOuterTerm hinputWeight R factor innerWord
        rightWord hword =
      .frontier
        (innerReductionExpansion hinputWeight R factor innerWord
          rightWord) := by
  simp [classifiedOuterTerm, Nat.not_le_of_lt hfrontier]

/-- Every classified recipe lies on exactly one of the two arithmetic sides. -/
lemma classified_attached_frontier
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (∃ hbalanced : R.leftDegree ≤ R.rightDegree,
      classifiedOuterTerm hinputWeight R factor innerWord
          rightWord hword =
        .attached
          (attachedInnerExpansion hinputWeight R factor
            innerWord rightWord hword hbalanced)) ∨
      (∃ _hfrontier : R.rightDegree < R.leftDegree,
        classifiedOuterTerm hinputWeight R factor innerWord
            rightWord hword =
          .frontier
            (innerReductionExpansion hinputWeight R factor innerWord
              rightWord)) := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · exact Or.inl
      ⟨hbalanced,
        classified_outer_degree
          hinputWeight R factor innerWord rightWord hword hbalanced⟩
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    exact Or.inr
      ⟨hfrontier,
        classified_inner_degree
          hinputWeight R factor innerWord rightWord hword hfrontier⟩

/-- Excess-left terms are precisely terms whose transient bound does not fit. -/
lemma not_inner_degree
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree) :
    ¬ (innerReductionExpansion hinputWeight R factor innerWord
        rightWord).exponentWeight ≤
      (innerReductionExpansion hinputWeight R factor innerWord
        rightWord).word.weight PEAddres.weight := by
  rw [exponent_inner_expansion
    hinputWeight R factor innerWord rightWord hword]
  exact Nat.not_le_of_lt hfrontier

/-- Classifying one recipe leaves its represented transient value unchanged. -/
lemma value_classified_term
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    (classifiedOuterTerm hinputWeight R factor innerWord
        rightWord hword).value (n := n) q =
      (innerReductionExpansion hinputWeight R factor innerWord
        rightWord).value q := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · simp [classifiedOuterTerm, hbalanced,
      SOTerm.value,
      TWExp.value]
  · simp [classifiedOuterTerm, hbalanced,
      SOTerm.value]

/-- Classifying a finite ordered recipe list preserves its transient product. -/
lemma classifiedInnerTerm
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (recipes.map fun R =>
          classifiedOuterTerm hinputWeight R factor innerWord
            rightWord hword) =
      TWExp.listValue (n := n) q
        (recipes.map fun R =>
          innerReductionExpansion hinputWeight R factor innerWord
            rightWord) := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (classifiedOuterTerm hinputWeight R factor innerWord
              rightWord hword).value q *
            SOTerm.listValue q
              (recipes.map fun nextR =>
                classifiedOuterTerm hinputWeight nextR factor
                  innerWord rightWord hword) =
          (innerReductionExpansion hinputWeight R factor innerWord
                rightWord).value q *
            TWExp.listValue q
              (recipes.map fun nextR =>
                innerReductionExpansion hinputWeight nextR factor
                  innerWord rightWord)
      rw [value_classified_term, ih]

end PTSubsti

namespace PFSubsti.TAPkt

/-- Packet recipes that immediately return to the ordinary bounded API. -/
def innerBalancedRecipes
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt d n) :
    List BRecipe :=
  packet.recipes.filter fun R => decide (R.leftDegree ≤ R.rightDegree)

/-- Packet recipes that remain on the transient excess-left frontier. -/
def innerReductionRecipes
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt d n) :
    List BRecipe :=
  packet.recipes.filter fun R => decide (R.rightDegree < R.leftDegree)

@[simp]
lemma inner_balanced_recipes
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt d n)
    (R : BRecipe) :
    R ∈ packet.innerBalancedRecipes ↔
      R ∈ packet.recipes ∧ R.leftDegree ≤ R.rightDegree := by
  simp [innerBalancedRecipes]

@[simp]
lemma inner_reduction_recipes
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt d n)
    (R : BRecipe) :
    R ∈ packet.innerReductionRecipes ↔
      R ∈ packet.recipes ∧ R.rightDegree < R.leftDegree := by
  simp [innerReductionRecipes]

/-- Every packet recipe belongs to the balanced side or the excess-left side. -/
lemma balanced_or_frontier
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt d n)
    {R : BRecipe}
    (hR : R ∈ packet.recipes) :
    R ∈ packet.innerBalancedRecipes ∨
      R ∈ packet.innerReductionRecipes := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · exact Or.inl (by simp [hR, hbalanced])
  · exact Or.inr (by simp [hR, Nat.lt_of_not_ge hbalanced])

/-- Classify every packet term while preserving the original recipe order. -/
def innerOuterTerms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SOTerm H inputWeight) :=
  packet.recipes.map fun R =>
    PTSubsti.classifiedOuterTerm
      hinputWeight R factor innerWord rightWord hword

/--
The order-preserving mixed packet still evaluates exactly to the original
inner-reduction outer commutator.
-/
lemma inner_reduction_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (packet.innerOuterTerms hinputWeight factor
          innerWord rightWord hword) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [innerOuterTerms,
    PTSubsti.classifiedInnerTerm]
  simpa [innerReductionExpansions, transientWordExpansions,
    PTSubsti.wordExpansions] using
      packet.outer_transient_expansions (H := H)
        hinputWeight factor innerWord rightWord q

end PFSubsti.TAPkt

end TCTex
end Submission

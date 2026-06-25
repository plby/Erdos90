import Submission.Group.Zassenhaus.TransientResidual
import Submission.Group.Zassenhaus.Polynomial

/-!
# Principal-recipe inventory for transient rewording residuals

The raw transient powered-bridge residual contains the inverse temporary
Hall-Petresco packet followed by its original outer carrier.  At the physical
weight of the outer carrier, only recipes of bidegree `(1, 1)` can occur.

The generic packet interface intentionally does not state that `basic` is its
unique recipe of bidegree `(1, 1)`.  This file records that extra collector
invariant explicitly, proves the resulting residual inventory, and verifies
the invariant for the cutoff-four packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open HACoeff
open BRSpec
open PTSubsti

/--
A packet has a principal basic recipe when it emits `basic` and no other
recipe has bidegree `(1, 1)`.
-/
structure PBRecipea
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) : Prop where
  basic_mem :
    hallPair ∈ packet.recipes
  basic_bidegree_one :
    ∀ R ∈ packet.recipes,
      R.leftDegree = 1 →
        R.rightDegree = 1 →
          R = hallPair

/--
Every nonprincipal recipe in a packet with a principal basic recipe becomes
strictly heavier when it is substituted into a reworded transient outer
bracket.
-/
lemma outer_reword_pair
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hprincipal : packet.PBRecipea)
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (hR : R ∈ packet.recipes)
    (hne : R ≠ hallPair)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    outerExpansion.word.weight PEAddres.weight <
      (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord)).word.weight
          PEAddres.weight := by
  apply
    outer_reword_bidegree
      hinputWeight R outerExpansion innerWord rightWord hword
  by_cases hleft : R.leftDegree = 1
  · by_cases hright : R.rightDegree = 1
    · exact False.elim <|
        hne (hprincipal.basic_bidegree_one R hR hleft hright)
    · exact Or.inr hright
  · exact Or.inl hleft

/--
Every member of a raw transient rewording residual is either the negation of
one emitted recipe term or the appended original outer carrier.
-/
theorem
    recipe_or_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) :
    (∃ R ∈ packet.recipes,
      nextExpansion =
        (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)).neg) ∨
      nextExpansion = outerExpansion := by
  rw [transientInnerReduction] at hnext
  rcases List.mem_append.mp hnext with hnext | hnext
  · left
    rw [TWExp.inverseList] at hnext
    rcases List.mem_map.mp hnext with ⟨sourceExpansion, hsource, rfl⟩
    have hsource' :
        sourceExpansion ∈
          packet.transientWordExpansions hinputWeight
            (outerExpansion.reword innerWord)
            (TWExp.wordUnit rightWord) := by
      simpa using hsource
    rw [transientWordExpansions] at hsource'
    rcases recipe_word_expansions hsource' with ⟨R, hR, rfl⟩
    exact ⟨R, hR, rfl⟩
  · right
    simpa only [List.mem_singleton] using hnext

/--
Without any principal-recipe hypothesis, the only obstruction to strict
physical growth in a raw residual is an emitted recipe of bidegree `(1, 1)`,
together with the deliberately appended parent carrier.
-/
theorem
    bidegree_outer_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) :
    (∃ R ∈ packet.recipes,
      R.leftDegree = 1 ∧
        R.rightDegree = 1 ∧
          nextExpansion =
            (wordExpansion hinputWeight R (outerExpansion.reword innerWord)
              (TWExp.wordUnit
                rightWord)).neg) ∨
      outerExpansion.word.weight PEAddres.weight <
        nextExpansion.word.weight PEAddres.weight ∨
      nextExpansion = outerExpansion := by
  rcases
      packet
        |>.recipe_or_transient
          hinputWeight outerExpansion innerWord rightWord nextExpansion hnext with
    ⟨R, hR, rfl⟩ | rfl
  · by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · exact Or.inl ⟨R, hR, hleft, hright, rfl⟩
      · exact Or.inr <| Or.inl <| by
          rw [TWExp.word_neg]
          exact
            outer_reword_bidegree
              hinputWeight R outerExpansion innerWord rightWord hword
                (Or.inr hright)
    · exact Or.inr <| Or.inl <| by
        rw [TWExp.word_neg]
        exact
          outer_reword_bidegree
            hinputWeight R outerExpansion innerWord rightWord hword
              (Or.inl hleft)
  · exact Or.inr <| Or.inr rfl

/--
For a packet with a principal basic recipe, every raw residual member is the
negated basic output, a strictly heavier output, or the appended parent.
-/
theorem
    neg_outer_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hprincipal : packet.PBRecipea)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) :
    nextExpansion =
        (wordExpansion hinputWeight hallPair (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)).neg ∨
      outerExpansion.word.weight PEAddres.weight <
        nextExpansion.word.weight PEAddres.weight ∨
      nextExpansion = outerExpansion := by
  rcases
      packet
        |>.bidegree_outer_source
          hinputWeight outerExpansion innerWord rightWord hword nextExpansion
            hnext with
    ⟨R, hR, hleft, hright, hnext⟩ | hnext
  · left
    rw [hprincipal.basic_bidegree_one R hR hleft hright] at hnext
    exact hnext
  · exact Or.inr hnext

/-- The cutoff-four packet has `basic` as its principal recipe. -/
def principal_n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    (n_four (d := d) hn).PBRecipea where
  basic_mem := by
    simp [n_four]
  basic_bidegree_one := by
    intro R hR hleft hright
    simp only [n_four, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · simp [leftTriple, BRecipe.leftDegree] at hleft
    · rfl
    · simp [rightTriple, BRecipe.rightDegree] at hright

end PFSubsti.TAPkt

end TCTex
end Submission

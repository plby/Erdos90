import Mathlib.Data.Multiset.DershowitzManna
import Submission.Group.Zassenhaus.FrontierWeightDescent

/-!
# Defect descent for classified transient packets

A classified inner-reduction packet must remain in its original Hall-Petresco
order: attached terms cannot be commuted past transient frontier terms.  For
termination, however, only the frontier entries remain recursive obligations.

This file measures those entries inside the original interleaved packet.  Every
frontier defect is strictly smaller than the parent defect, so replacing one
parent by the complete classified packet decreases the Dershowitz-Manna
multiset order.  The statement keeps the packet context intact and does not
split transient entries into independent recollection obligations.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff

namespace SOTerm

/--
The multiset of cutoff defects carried by transient frontier entries of an
ordered classified packet.  Attached entries contribute no recursive task.
-/
def frontierDefectMultiset
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ) :
    List (SOTerm H inputWeight) →
      Multiset ℕ
  | [] => ∅
  | .attached _ :: terms => frontierDefectMultiset n terms
  | .frontier wordExpansion :: terms =>
      {n - wordExpansion.word.weight PEAddres.weight} +
        frontierDefectMultiset n terms

@[simp]
lemma frontier_multiset_nil
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    frontierDefectMultiset (H := H) n
        ([] : List (SOTerm H inputWeight)) =
      ∅ :=
  rfl

@[simp]
lemma multiset_cons_attached
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight)
    (terms : List (SOTerm H inputWeight)) :
    frontierDefectMultiset n (.attached wordExpansion :: terms) =
      frontierDefectMultiset n terms :=
  rfl

@[simp]
lemma frontierMultisetCons
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (terms : List (SOTerm H inputWeight)) :
    frontierDefectMultiset n (.frontier wordExpansion :: terms) =
      {n - wordExpansion.word.weight PEAddres.weight} +
        frontierDefectMultiset n terms :=
  rfl

/-- Dershowitz-Manna descent induced by transient defects in mixed packets. -/
def FrontierDefectMultiset
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (left right :
      List (SOTerm H inputWeight)) :
    Prop :=
  Multiset.IsDershowitzMannaLT
    (frontierDefectMultiset n left)
    (frontierDefectMultiset n right)

/-- Frontier-defect descent on complete mixed packets is well founded. -/
lemma well_founded_multiset
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    WellFounded
      (FrontierDefectMultiset
        (H := H) (inputWeight := inputWeight) n) :=
  InvImage.wf
    (frontierDefectMultiset
      (H := H) (inputWeight := inputWeight) n)
    Multiset.wellFounded_isDershowitzMannaLT

end SOTerm

namespace PTSubsti

/--
Every recursive defect in an ordered classified recipe list is strictly
smaller than the defect of the parent factor.
-/
lemma forall_frontier_classified
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∀ defect ∈
        SOTerm.frontierDefectMultiset n
          (recipes.map fun R =>
            classifiedOuterTerm hinputWeight R factor innerWord
              rightWord hword),
      defect < SPFactora.cutoffDefect n factor := by
  induction recipes with
  | nil =>
      simp
  | cons R recipes ih =>
      simp only [List.map_cons]
      by_cases hbalanced : R.leftDegree ≤ R.rightDegree
      · rw [classified_outer_degree
          hinputWeight R factor innerWord rightWord hword hbalanced]
        simpa using ih
      · have hfrontier : R.rightDegree < R.leftDegree :=
          Nat.lt_of_not_ge hbalanced
        rw [classified_inner_degree
          hinputWeight R factor innerWord rightWord hword hfrontier]
        intro defect hdefect
        simp only [
          SOTerm.frontierMultisetCons,
          Multiset.mem_add, Multiset.mem_singleton] at hdefect
        rcases hdefect with rfl | hdefect
        · exact
            defect_inner_degree
              hinputWeight R factor innerWord rightWord hword hfrontier
                hfactorTruncated
        · exact ih defect hdefect

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/--
Every recursive defect retained by a complete interleaved classified packet is
strictly smaller than the parent defect.
-/
lemma forall_multiset_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∀ defect ∈
        SOTerm.frontierDefectMultiset n
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword),
      defect < SPFactora.cutoffDefect n factor := by
  rw [innerOuterTerms]
  exact forall_frontier_classified
    hinputWeight packet.recipes factor innerWord rightWord hword
      hfactorTruncated

/--
Inside an arbitrary multiset context, replacing one parent obligation by its
complete ordered classified packet strictly decreases the frontier-defect
measure.
-/
lemma multiset_classified_singleton
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (context : Multiset ℕ) :
    Multiset.IsDershowitzMannaLT
      (context +
        SOTerm.frontierDefectMultiset n
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword))
      (context + {SPFactora.cutoffDefect n factor}) := by
  refine ⟨context, _, _, by simp, rfl, rfl, ?_⟩
  intro defect hdefect
  exact
    ⟨SPFactora.cutoffDefect n factor, by simp,
      packet.forall_multiset_terms
        hinputWeight factor innerWord rightWord hword hfactorTruncated defect
          hdefect⟩

/--
Replacing one parent obligation by its complete ordered classified packet
strictly decreases the frontier-defect measure.
-/
lemma frontier_multiset_singleton
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    Multiset.IsDershowitzMannaLT
      (SOTerm.frontierDefectMultiset n
        (packet.innerOuterTerms hinputWeight factor
          innerWord rightWord hword))
      {SPFactora.cutoffDefect n factor} := by
  simpa using
    packet.multiset_classified_singleton
      hinputWeight factor innerWord rightWord hword hfactorTruncated ∅

/--
View an ordinary parent factor as one transient obligation on its own word.
The complete ordered classified packet strictly descends from that singleton
in the well-founded mixed-packet recursion relation.
-/
lemma inner_multiset_reword
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SOTerm.FrontierDefectMultiset n
      (packet.innerOuterTerms hinputWeight factor innerWord
        rightWord hword)
      [.frontier
        (TWExp.rewordFactor factor
          factor.word)] := by
  simpa [SOTerm.FrontierDefectMultiset,
    SPFactora.cutoffDefect,
    TWExp.rewordFactor] using
      packet.frontier_multiset_singleton
        hinputWeight factor innerWord rightWord hword hfactorTruncated

end PFSubsti.TAPkt

end TCTex
end Submission

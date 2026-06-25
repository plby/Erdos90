import Submission.Group.Zassenhaus.ClassifiedPacketDescent

/-!
# Classifying arbitrary transient Hall-Petresco packets

Recursive transient recollection must expand frontier tasks, not only the
first inner reduction of an ordinary factor.  This file classifies an
arbitrary Hall-Petresco substitution of two transiently powered words.

Each output is attached to the ordinary bounded symbolic language exactly
when its arithmetic bound fits its physical Hall word.  The remaining
frontier entries preserve their packet order and strictly decrease the
cutoff-defect measure from either transient parent.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace PTSubsti

/--
Classify one arbitrary transient recipe output by its exact attachability
condition.
-/
def classifiedTransientTerm
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    SOTerm H inputWeight :=
  let expansion := wordExpansion hinputWeight R B A
  if hweight :
      expansion.exponentWeight ≤
        expansion.word.weight PEAddres.weight then
    .attached (expansion.toWordExpansion hweight)
  else
    .frontier expansion

/-- An attachable transient output returns to the ordinary symbolic API. -/
lemma classified_attached_exponent
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight)
    (hweight :
      (wordExpansion hinputWeight R B A).exponentWeight ≤
        (wordExpansion hinputWeight R B A).word.weight
          PEAddres.weight) :
    classifiedTransientTerm hinputWeight R B A =
      .attached ((wordExpansion hinputWeight R B A).toWordExpansion hweight) := by
  unfold classifiedTransientTerm
  dsimp only
  rw [dif_pos hweight]

/-- A transient output whose bound does not fit remains on the frontier. -/
lemma classified_transient_exponent
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight)
    (hweight :
      ¬ (wordExpansion hinputWeight R B A).exponentWeight ≤
        (wordExpansion hinputWeight R B A).word.weight
          PEAddres.weight) :
    classifiedTransientTerm hinputWeight R B A =
      .frontier (wordExpansion hinputWeight R B A) := by
  unfold classifiedTransientTerm
  dsimp only
  rw [dif_neg hweight]

/-- Classifying one arbitrary transient recipe leaves its value unchanged. -/
lemma classified_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight)
    (q : ℕ) :
    (classifiedTransientTerm hinputWeight R B A).value (n := n) q =
      (wordExpansion hinputWeight R B A).value q := by
  by_cases hweight :
      (wordExpansion hinputWeight R B A).exponentWeight ≤
        (wordExpansion hinputWeight R B A).word.weight
          PEAddres.weight
  · rw [classified_attached_exponent
      hinputWeight R B A hweight]
    simp [
      SOTerm.value,
      TWExp.value]
    rfl
  · rw [classified_transient_exponent
      hinputWeight R B A hweight]
    rfl

/-- Classifying an ordered recipe list preserves its transient product. -/
lemma list_classified_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : TWExp H inputWeight)
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (recipes.map fun R => classifiedTransientTerm hinputWeight R B A) =
      TWExp.listValue (n := n) q
        (recipes.map fun R => wordExpansion hinputWeight R B A) := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (classifiedTransientTerm hinputWeight R B A).value q *
            SOTerm.listValue q
              (recipes.map fun nextR =>
                classifiedTransientTerm hinputWeight nextR B A) =
          (wordExpansion hinputWeight R B A).value q *
            TWExp.listValue q
              (recipes.map fun nextR => wordExpansion hinputWeight nextR B A)
      rw [classified_transient, ih]

/-- One arbitrary transient output strictly decreases left-parent defect. -/
lemma cutoff_defect_left
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight)
    (hB :
      B.word.weight PEAddres.weight < n) :
    n - (wordExpansion hinputWeight R B A).word.weight
          PEAddres.weight <
      n - B.word.weight PEAddres.weight := by
  have hweight :=
    left_weight_expansion hinputWeight R B A
  omega

/-- One arbitrary transient output strictly decreases right-parent defect. -/
lemma cutoff_defect_right
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight)
    (hA :
      A.word.weight PEAddres.weight < n) :
    n - (wordExpansion hinputWeight R B A).word.weight
          PEAddres.weight <
      n - A.word.weight PEAddres.weight := by
  have hweight :=
    right_weight_expansion hinputWeight R B A
  omega

/--
Every recursive defect in an arbitrary classified recipe list strictly
decreases from its left transient parent.
-/
lemma forall_frontier_left
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : TWExp H inputWeight)
    (hB :
      B.word.weight PEAddres.weight < n) :
    ∀ defect ∈
        SOTerm.frontierDefectMultiset n
          (recipes.map fun R => classifiedTransientTerm hinputWeight R B A),
      defect < n - B.word.weight PEAddres.weight := by
  induction recipes with
  | nil =>
      simp
  | cons R recipes ih =>
      simp only [List.map_cons]
      by_cases hweight :
          (wordExpansion hinputWeight R B A).exponentWeight ≤
            (wordExpansion hinputWeight R B A).word.weight
              PEAddres.weight
      · rw [classified_attached_exponent
          hinputWeight R B A hweight]
        simpa using ih
      · rw [classified_transient_exponent
          hinputWeight R B A hweight]
        intro defect hdefect
        simp only [
          SOTerm.frontierMultisetCons,
          Multiset.mem_add, Multiset.mem_singleton] at hdefect
        rcases hdefect with rfl | hdefect
        · exact cutoff_defect_left hinputWeight R B A hB
        · exact ih defect hdefect

/--
Every recursive defect in an arbitrary classified recipe list strictly
decreases from its right transient parent.
-/
lemma forall_frontier_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : TWExp H inputWeight)
    (hA :
      A.word.weight PEAddres.weight < n) :
    ∀ defect ∈
        SOTerm.frontierDefectMultiset n
          (recipes.map fun R => classifiedTransientTerm hinputWeight R B A),
      defect < n - A.word.weight PEAddres.weight := by
  induction recipes with
  | nil =>
      simp
  | cons R recipes ih =>
      simp only [List.map_cons]
      by_cases hweight :
          (wordExpansion hinputWeight R B A).exponentWeight ≤
            (wordExpansion hinputWeight R B A).word.weight
              PEAddres.weight
      · rw [classified_attached_exponent
          hinputWeight R B A hweight]
        simpa using ih
      · rw [classified_transient_exponent
          hinputWeight R B A hweight]
        intro defect hdefect
        simp only [
          SOTerm.frontierMultisetCons,
          Multiset.mem_add, Multiset.mem_singleton] at hdefect
        rcases hdefect with rfl | hdefect
        · exact cutoff_defect_right hinputWeight R B A hA
        · exact ih defect hdefect

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/-- Classify an arbitrary transient packet without changing recipe order. -/
def transientClassifiedTerms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    List (SOTerm H inputWeight) :=
  packet.recipes.map fun R => classifiedTransientTerm hinputWeight R B A

/-- The classified arbitrary packet evaluates to its parent commutator. -/
lemma value_transient_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (packet.transientClassifiedTerms hinputWeight B A) =
      ⁅B.value (n := n) q, A.value (n := n) q⁆ := by
  rw [transientClassifiedTerms, list_classified_transient]
  simpa [transientWordExpansions,
    PTSubsti.wordExpansions] using
      packet.transient_word_expansions hinputWeight B A q

/--
Every recursive defect retained by an arbitrary classified packet strictly
decreases from its left transient parent.
-/
lemma forall_frontier_multiset
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hB :
      B.word.weight PEAddres.weight < n) :
    ∀ defect ∈
        SOTerm.frontierDefectMultiset n
          (packet.transientClassifiedTerms hinputWeight B A),
      defect < n - B.word.weight PEAddres.weight := by
  rw [transientClassifiedTerms]
  exact
    forall_frontier_left
      hinputWeight packet.recipes B A hB

/--
Every recursive defect retained by an arbitrary classified packet strictly
decreases from its right transient parent.
-/
lemma forall_multiset_transient
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hA :
      A.word.weight PEAddres.weight < n) :
    ∀ defect ∈
        SOTerm.frontierDefectMultiset n
          (packet.transientClassifiedTerms hinputWeight B A),
      defect < n - A.word.weight PEAddres.weight := by
  rw [transientClassifiedTerms]
  exact
    forall_frontier_transient
      hinputWeight packet.recipes B A hA

/--
The arbitrary classified packet descends from the singleton left-parent
frontier obligation.
-/
lemma transient_multiset_singleton
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hB :
      B.word.weight PEAddres.weight < n) :
    SOTerm.FrontierDefectMultiset n
      (packet.transientClassifiedTerms hinputWeight B A)
      [.frontier B] := by
  refine ⟨∅,
    SOTerm.frontierDefectMultiset n
      (packet.transientClassifiedTerms hinputWeight B A),
    {n - B.word.weight PEAddres.weight},
    by simp, by simp, by simp, ?_⟩
  intro defect hdefect
  exact
    ⟨n - B.word.weight PEAddres.weight, by simp,
      packet.forall_frontier_multiset
        hinputWeight B A hB defect hdefect⟩

/--
The arbitrary classified packet descends from the singleton right-parent
frontier obligation.
-/
lemma transient_classified_multiset
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hA :
      A.word.weight PEAddres.weight < n) :
    SOTerm.FrontierDefectMultiset n
      (packet.transientClassifiedTerms hinputWeight B A)
      [.frontier A] := by
  refine ⟨∅,
    SOTerm.frontierDefectMultiset n
      (packet.transientClassifiedTerms hinputWeight B A),
    {n - A.word.weight PEAddres.weight},
    by simp, by simp, by simp, ?_⟩
  intro defect hdefect
  exact
    ⟨n - A.word.weight PEAddres.weight, by simp,
      packet.forall_multiset_transient
        hinputWeight B A hA defect hdefect⟩

end PFSubsti.TAPkt

end TCTex
end Submission

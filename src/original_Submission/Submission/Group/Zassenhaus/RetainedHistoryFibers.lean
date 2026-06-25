import Submission.Group.Zassenhaus.TruncatedRecipeInventories
import Submission.Group.Zassenhaus.FamilyOperationalSupport
import Submission.Group.Zassenhaus.CompatiblePacketRouting
import Submission.Group.Zassenhaus.AtomParentHistories
import Submission.Group.Zassenhaus.TruncatedTraceEvaluation
import Submission.Group.Zassenhaus.CorrectionClosureVocabulary
import Mathlib.Data.Prod.Lex
import Submission.Group.Zassenhaus.CompletePetrescoRecipe
import Submission.Group.Zassenhaus.Inverse
import Submission.Group.Zassenhaus.InverseUniversalClosure


/-!
# Retained raw-history shape fibers at arbitrary cutoff

The initially retained source packet of the cutoff-full collector has two
exact presentations: indexed decorated family terms and inverse raw histories.
The recipe-truncation boundary identifies their labelled word lists.  This
file records the corresponding erased-shape identity and its shape-fiber
cardinality consequence at arbitrary cutoff and arbitrary source weights.

This is the raw-source half of a later symbolic endpoint-profile construction.
It is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  RHFiber

open HACoeff
open RHRecipe
open HHTrunc
open RRTrunc

/--
Forgetting indexed family provenance from the retained raw packet recovers the
collapsed Hall-pair words of the exact retained inverse histories, in order.
-/
lemma erased_collapse_histories
    (M N n leftWeight rightWeight : ℕ) :
    (retainedRawTerms M N n leftWeight rightWeight).map
        DFTerm.erasedShape =
      (retainedHistories n leftWeight rightWeight
        (inverseRawHistories M N)).map fun history =>
          collapseWord history.word := by
  have hwords :=
    congrArg
      (List.map collapseWord)
      (history_words_histories
        M N n leftWeight rightWeight)
  simpa [historyWords, decoratedFamilyList, List.map_map,
    Function.comp_def, DFTerm.erasedShape,
    DTerm.erasedShape] using hwords.symm

/--
Filtering retained raw terms by erased Hall shape is exactly filtering retained
inverse histories by collapsed Hall word.
-/
lemma
    length_collapse_histories
    (M N n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    ((retainedRawTerms M N n leftWeight rightWeight).filter fun term =>
      decide (term.erasedShape = word)).length =
        ((retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N)).filter fun history =>
            decide (collapseWord history.word = word)).length := by
  have hwords :=
    congrArg
      (fun words =>
        (words.filter fun next => decide (collapseWord next = word)).length)
      (history_words_histories
        M N n leftWeight rightWeight)
  simpa [historyWords, decoratedFamilyList, List.filter_map,
    DFTerm.erasedShape, DTerm.erasedShape] using hwords.symm

end
  RHFiber
end TCTex
end Submission

/-!
# Cutoff-aware full collection of recipe-certified family terms

Unrestricted full Hall collection need not terminate: interchanging histories
with overlapping support can recursively create corrections of ever higher
weight.  In a nilpotent quotient there is a finite replacement.  Retain a
generated correction while its weighted Hall degree is below the cutoff, and
discard it only after proving that it evaluates trivially at or above the
cutoff.

This file defines that term-level relation.  It proves semantic preservation
in every matching nilpotent target and proves that the retained endpoint is
sorted by the complete decorated collector key.  Termination is isolated for
the following file.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CFCollec

open scoped commutatorElement

open HACoeff
open BFTrunc
open CCAggreg
open OCPartit

namespace DFTerm

/-- Evaluate one selected recipe-certified term at an arbitrary Hall pair. -/
def collapsedEvalAt
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (term : DFTerm M N K) :
    G :=
  (collapseWord term.decorated.word).eval (HPAtom.eval x y)

/-- Evaluate a selected family-term list in its current noncommutative order. -/
def collapsedList
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (terms : List (DFTerm M N K)) :
    G :=
  (terms.map fun term => collapsedEvalAt x y term).prod

@[simp]
lemma collapsed_list_nil
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G) :
    collapsedList
      (M := M) (N := N) (K := K) x y [] = 1 :=
  rfl

@[simp]
lemma collapsed_list_append
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (left right : List (DFTerm M N K)) :
    collapsedList x y (left ++ right) =
      collapsedList x y left *
        collapsedList x y right := by
  simp [collapsedList, List.prod_append]

@[simp]
lemma collapsed_append_singleton
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (terms : List (DFTerm M N K))
    (term : DFTerm M N K) :
    collapsedList x y (terms ++ [term]) =
      collapsedList x y terms *
        collapsedEvalAt x y term := by
  simp [collapsedList]

/-- The selected correction term implements the exact adjacent swap. -/
lemma collapsed_correction_mul
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (left right : DFTerm M N K) :
    collapsedEvalAt x y (left.correction right) *
          collapsedEvalAt x y right *
          collapsedEvalAt x y left =
      collapsedEvalAt x y left * collapsedEvalAt x y right := by
  simp [collapsedEvalAt,
    DFTerm.correction, DTerm.correction,
    collapseWord, CWord.eval_commutator,
    commutatorElement_def]

/-- A selected term at or above the cutoff evaluates trivially. -/
lemma collapsed_eval_weight
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (term : DFTerm M N K)
    (hweight :
      n ≤ decoratedFamilyWeight leftWeight rightWeight term) :
    collapsedEvalAt x y term = 1 :=
  OCPartit.collapsed_one_weight
    hleftWeight hrightWeight hx hy hbot term hweight

/--
Insert one retained term into a complete-key-sorted prefix.  Below-cutoff
corrections recurse.  Above-cutoff corrections disappear only semantically.
-/
inductive CInsert
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    List (DFTerm M N K) →
      DFTerm M N K →
        List (DFTerm M N K) →
          Prop where
  | nil
      (A : DFTerm M N K) :
      CInsert n leftWeight rightWeight [] A [A]
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hBA : B.decorated.collectorLe A.decorated) :
      CInsert n leftWeight rightWeight
        (P ++ [B]) A (P ++ [B, A])
  | retained
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.collectorBefore B.decorated)
      (hweight :
        decoratedFamilyWeight leftWeight rightWeight (B.correction A) < n)
      {Q R : List (DFTerm M N K)}
      (hcorrection :
        CInsert n leftWeight rightWeight P (B.correction A) Q)
      (hinsert :
        CInsert n leftWeight rightWeight Q A R) :
      CInsert n leftWeight rightWeight (P ++ [B]) A (R ++ [B])
  | residual
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.collectorBefore B.decorated)
      (hweight :
        n ≤ decoratedFamilyWeight leftWeight rightWeight (B.correction A))
      {R : List (DFTerm M N K)}
      (hinsert :
        CInsert n leftWeight rightWeight P A R) :
      CInsert n leftWeight rightWeight (P ++ [B]) A (R ++ [B])

/--
Cutoff-aware insertion preserves collapsed evaluation in every matching
nilpotent target.
-/
lemma collapsed_cutoff_inserts
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R) :
    collapsedList x y R =
      collapsedList x y L *
        collapsedEvalAt x y A := by
  induction hinsert with
  | nil A =>
      simp [collapsedList]
  | append P B A _hBA =>
      simp [collapsedList, mul_assoc]
  | retained P B A _hAB _hweight hcorrection hinsert
      ihcorrection ihinsert =>
      rw [collapsed_append_singleton, ihinsert, ihcorrection,
        collapsed_append_singleton]
      calc
        (collapsedList x y P *
              collapsedEvalAt x y (B.correction A)) *
              collapsedEvalAt x y A * collapsedEvalAt x y B =
            collapsedList x y P *
              (collapsedEvalAt x y (B.correction A) *
                collapsedEvalAt x y A * collapsedEvalAt x y B) := by
                  group
        _ = collapsedList x y P *
              (collapsedEvalAt x y B * collapsedEvalAt x y A) := by
                rw [collapsed_correction_mul]
        _ = (collapsedList x y P *
              collapsedEvalAt x y B) * collapsedEvalAt x y A := by
                group
  | residual P B A _hAB hweight hinsert ihinsert =>
      have hcorrection :
          collapsedEvalAt x y (B.correction A) = 1 :=
        collapsed_eval_weight
          hleftWeight hrightWeight hx hy hbot (B.correction A) hweight
      have hcommute :
          collapsedEvalAt x y A * collapsedEvalAt x y B =
            collapsedEvalAt x y B * collapsedEvalAt x y A := by
        have hswap := collapsed_correction_mul x y B A
        rw [hcorrection, one_mul] at hswap
        exact hswap
      rw [collapsed_append_singleton, ihinsert,
        collapsed_append_singleton]
      simp only [mul_assoc]
      rw [hcommute]

/--
Cutoff insertion preserves any common upper bound in the complete collector
order.
-/
lemma collector_cutoff_inserts
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    {A U : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R)
    (hLU : ∀ term ∈ L, term.decorated.collectorLe U.decorated)
    (hAU : A.decorated.collectorLe U.decorated) :
    ∀ term ∈ R, term.decorated.collectorLe U.decorated := by
  induction hinsert with
  | nil A =>
      intro term hterm
      rcases List.mem_singleton.mp hterm with rfl
      exact hAU
  | append P B A _hBA =>
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hLU term (List.mem_append_left [B] hterm)
      · rcases List.mem_cons.mp hterm with hterm | hterm
        · subst term
          exact hLU B (by simp)
        · rcases List.mem_singleton.mp hterm with rfl
          exact hAU
  | retained P B A _hAB _hweight hcorrection hinsert
      ihcorrection ihinsert =>
      have hP :
          ∀ term ∈ P, term.decorated.collectorLe U.decorated := by
        intro term hterm
        exact hLU term (List.mem_append_left [B] hterm)
      have hcorrectionU :
          (B.correction A).decorated.collectorLe U.decorated := by
        apply collector_le_of
        exact DTerm.collector_before
          (DTerm.collector_before_right B.positive) hAU
      have hQ := ihcorrection hP hcorrectionU
      have hR := ihinsert hQ hAU
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hR term hterm
      · rcases List.mem_singleton.mp hterm with rfl
        exact hLU _ (by simp)
  | residual P B A _hAB _hweight hinsert ihinsert =>
      have hP :
          ∀ term ∈ P, term.decorated.collectorLe U.decorated := by
        intro term hterm
        exact hLU term (List.mem_append_left [B] hterm)
      have hR := ihinsert hP hAU
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hR term hterm
      · rcases List.mem_singleton.mp hterm with rfl
        exact hLU _ (by simp)

/-- Every cutoff insertion into a collected prefix returns a collected list. -/
lemma decorated_collected_inserts
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R)
    (hcollected :
      Collected (L.map DFTerm.decorated)) :
    Collected (R.map DFTerm.decorated) := by
  induction hinsert with
  | nil A =>
      simp [Collected]
  | append P B A hBA =>
      have hPB :
          Collected ((P ++ [B]).map DFTerm.decorated) :=
        hcollected
      have hPB' :
          Collected
            (P.map DFTerm.decorated ++ [B.decorated]) := by
        simpa [List.map_append] using hPB
      have hPBA :
          ∀ term ∈ (P ++ [B]).map DFTerm.decorated,
            term.collectorLe A.decorated := by
        intro term hterm
        rcases List.mem_map.mp hterm with ⟨familyTerm, hfamilyTerm, rfl⟩
        rcases List.mem_append.mp hfamilyTerm with hfamilyTerm | hfamilyTerm
        · exact DTerm.collectorLe_trans
            (collector_last_collected hPB' familyTerm.decorated
              (List.mem_map.mpr ⟨familyTerm, hfamilyTerm, rfl⟩)) hBA
        · rcases List.mem_singleton.mp hfamilyTerm with rfl
          exact hBA
      simpa [List.map_append, List.append_assoc] using
        collected_append_singleton hPB hPBA
  | retained P B A hAB _hweight hcorrection hinsert
      ihcorrection ihinsert =>
      have hP :
          Collected (P.map DFTerm.decorated) := by
        apply collected_append_left
        simpa [List.map_append] using hcollected
      have hQ :=
        ihcorrection hP
      have hR :=
        ihinsert hQ
      have hPB :
          ∀ term ∈ P,
            term.decorated.collectorLe B.decorated := by
        have hcollected' :
            Collected
              (P.map DFTerm.decorated ++ [B.decorated]) := by
          simpa [List.map_append] using hcollected
        intro term hterm
        exact collector_last_collected hcollected' term.decorated
          (List.mem_map.mpr ⟨term, hterm, rfl⟩)
      have hcorrectionB :
          (B.correction A).decorated.collectorLe B.decorated :=
        collector_le_of
          (DTerm.collector_before_left A.positive)
      have hQB :=
        collector_cutoff_inserts hcorrection hPB hcorrectionB
      have hABle : A.decorated.collectorLe B.decorated :=
        collector_le_of hAB
      have hRB :=
        collector_cutoff_inserts hinsert hQB hABle
      simpa [List.map_append] using
        collected_append_singleton hR (by
          intro term hterm
          rcases List.mem_map.mp hterm with ⟨familyTerm, hfamilyTerm, rfl⟩
          exact hRB familyTerm hfamilyTerm)
  | residual P B A hAB _hweight hinsert ihinsert =>
      have hP :
          Collected (P.map DFTerm.decorated) := by
        apply collected_append_left
        simpa [List.map_append] using hcollected
      have hR := ihinsert hP
      have hPB :
          ∀ term ∈ P,
            term.decorated.collectorLe B.decorated := by
        have hcollected' :
            Collected
              (P.map DFTerm.decorated ++ [B.decorated]) := by
          simpa [List.map_append] using hcollected
        intro term hterm
        exact collector_last_collected hcollected' term.decorated
          (List.mem_map.mpr ⟨term, hterm, rfl⟩)
      have hABle : A.decorated.collectorLe B.decorated :=
        collector_le_of hAB
      have hRB :=
        collector_cutoff_inserts hinsert hPB hABle
      simpa [List.map_append] using
        collected_append_singleton hR (by
          intro term hterm
          rcases List.mem_map.mp hterm with ⟨familyTerm, hfamilyTerm, rfl⟩
          exact hRB familyTerm hfamilyTerm)

/--
Collect an input list by cutoff-aware insertion.  Above-cutoff source terms
are discarded semantically before insertion.
-/
inductive CCollec
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    List (DFTerm M N K) →
      List (DFTerm M N K) →
        Prop where
  | nil :
      CCollec n leftWeight rightWeight [] []
  | retained
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hweight :
        decoratedFamilyWeight leftWeight rightWeight A < n)
      {C R : List (DFTerm M N K)}
      (hcollect :
        CCollec n leftWeight rightWeight P C)
      (hinsert :
        CInsert n leftWeight rightWeight C A R) :
      CCollec n leftWeight rightWeight (P ++ [A]) R
  | residual
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hweight :
        n ≤ decoratedFamilyWeight leftWeight rightWeight A)
      {C : List (DFTerm M N K)}
      (hcollect :
        CCollec n leftWeight rightWeight P C) :
      CCollec n leftWeight rightWeight (P ++ [A]) C

/--
Cutoff-aware collection preserves collapsed evaluation in every matching
nilpotent target.
-/
lemma collapsed_cutoff_collects
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    {L R : List (DFTerm M N K)}
    (hcollect : CCollec n leftWeight rightWeight L R) :
    collapsedList x y R =
      collapsedList x y L := by
  induction hcollect with
  | nil =>
      rfl
  | retained P A _hweight hcollect hinsert ihcollect =>
      rw [collapsed_cutoff_inserts
        hleftWeight hrightWeight hx hy hbot hinsert,
        ihcollect, collapsed_append_singleton]
  | residual P A hweight hcollect ihcollect =>
      have hA :
          collapsedEvalAt x y A = 1 :=
        collapsed_eval_weight
          hleftWeight hrightWeight hx hy hbot A hweight
      rw [collapsed_append_singleton, hA, mul_one]
      exact ihcollect

/-- Every cutoff-aware collection endpoint is complete-key sorted. -/
lemma decorated_collected_collects
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : CCollec n leftWeight rightWeight L R) :
    Collected (R.map DFTerm.decorated) := by
  induction hcollect with
  | nil =>
      simp [Collected]
  | retained P A _hweight hcollect hinsert ihcollect =>
      exact decorated_collected_inserts hinsert ihcollect
  | residual P A _hweight hcollect ihcollect =>
      exact ihcollect

end DFTerm

end CFCollec
end TCTex
end Submission

/-!
# Termination of cutoff-aware full family collection

The cutoff collector retains corrections only below a fixed weighted Hall
degree.  This makes unrestricted support overlap harmless: a retained
correction has strictly larger weight than the inserted term and therefore
strictly smaller cutoff defect.

The second recursive insertion keeps the same term but removes one complete
collector obstruction.  Together with list length this gives a lexicographic
well-founded measure and an unconditional finite scheduler for every finite
recipe-certified family-term list.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FCTermin

open HACoeff
open BRSpec
open CFCollec.DFTerm
open CCAggreg
open OCPartit

/-- One insertion state for the cutoff-aware full family collector. -/
abbrev CutoffInsertionState
    (M N K : ℕ) :=
  List (DFTerm M N K) × DFTerm M N K

/-- Lexicographic cutoff-defect, obstruction-count, and prefix-length measure. -/
def cutoffInsertionMeasure
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (state : CutoffInsertionState M N K) :
    ℕ × ℕ × ℕ :=
  (n - decoratedFamilyWeight leftWeight rightWeight state.2,
    obstructionCount
      (state.1.map DFTerm.decorated)
      state.2.decorated,
    state.1.length)

/-- Pull back the existing lexicographic natural-number relation. -/
def cutoffInsertionBefore
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    CutoffInsertionState M N K →
      CutoffInsertionState M N K →
        Prop :=
  InvImage insertionMeasureBefore
    (cutoffInsertionMeasure n leftWeight rightWeight)

lemma insertion_before_wf
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    WellFounded
      (@cutoffInsertionBefore M N K n leftWeight rightWeight) :=
  InvImage.wf
    (cutoffInsertionMeasure n leftWeight rightWeight)
    insertion_measure_wf

/-- A retained correction strictly reduces cutoff defect. -/
lemma insertion_before_correction
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (P : List (DFTerm M N K))
    (B A : DFTerm M N K)
    (hA :
      decoratedFamilyWeight leftWeight rightWeight A < n)
    (hcorrection :
      decoratedFamilyWeight leftWeight rightWeight
        (B.correction A) < n) :
    cutoffInsertionBefore n leftWeight rightWeight
      (P, B.correction A) (P ++ [B], A) := by
  unfold cutoffInsertionBefore cutoffInsertionMeasure
  apply Prod.Lex.left
  change
    n - decoratedFamilyWeight leftWeight rightWeight (B.correction A) <
      n - decoratedFamilyWeight leftWeight rightWeight A
  have hBpositive :
      0 < decoratedFamilyWeight leftWeight rightWeight B := by
    exact weighted_weight_pos hleftWeight hrightWeight B.family.recipe
  rw [decorated_family_correction] at hcorrection ⊢
  omega

/-- Removing the final obstructing term strictly decreases obstruction count. -/
lemma insertion_state_before
    {M N K n leftWeight rightWeight : ℕ}
    (P : List (DFTerm M N K))
    (B A : DFTerm M N K)
    (hAB : A.decorated.collectorBefore B.decorated) :
    cutoffInsertionBefore n leftWeight rightWeight
      (P, A) (P ++ [B], A) := by
  unfold cutoffInsertionBefore cutoffInsertionMeasure
  apply Prod.Lex.right
  apply Prod.Lex.left
  dsimp only [Prod.fst, Prod.snd]
  rw [List.map_append, List.map_singleton,
    obstruction_last_before
      (P.map DFTerm.decorated)
      B.decorated A.decorated hAB]
  omega

/--
Inserting a term already preceding `A` preserves the number of obstructions
seen by `A`, even when high-weight corrections disappear.
-/
lemma obstruction_inserts_before
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    {C A : DFTerm M N K}
    (hinsert :
      CInsert n leftWeight rightWeight L C R)
    (hCA : C.decorated.collectorBefore A.decorated) :
    obstructionCount
        (R.map DFTerm.decorated) A.decorated =
      obstructionCount
        (L.map DFTerm.decorated) A.decorated := by
  induction hinsert generalizing A with
  | nil C =>
      have hAC :
          ¬ A.decorated.collectorBefore C.decorated :=
        DTerm.collectorBefore_asymm hCA
      simp [obstructionCount, hAC]
  | append P B C _hBC =>
      have hAC :
          ¬ A.decorated.collectorBefore C.decorated :=
        DTerm.collectorBefore_asymm hCA
      simpa [List.map_append, List.append_assoc] using
        obstruction_append_before
          (P.map DFTerm.decorated ++ [B.decorated])
          C.decorated A.decorated hAC
  | retained P B C _hCB _hweight hcorrection hinsert
      ihcorrection ihinsert =>
      have hcorrectionBeforeC :
          (B.correction C).decorated.collectorBefore C.decorated :=
        DTerm.collector_before_right B.positive
      have hcorrectionBeforeA :
          (B.correction C).decorated.collectorBefore A.decorated :=
        DTerm.collectorBefore_trans hcorrectionBeforeC hCA
      rw [List.map_append, List.map_append,
        obstructionCount_append, obstructionCount_append,
        ihinsert hCA, ihcorrection hcorrectionBeforeA]
  | residual P B C _hCB _hweight hinsert ihinsert =>
      rw [List.map_append, List.map_append,
        obstructionCount_append, obstructionCount_append,
        ihinsert hCA]

/--
After inserting a retained correction, the second recursive insertion removes
the final obstruction to `A`.
-/
lemma insertion_before_after
    {M N K n leftWeight rightWeight : ℕ}
    (P : List (DFTerm M N K))
    {B A : DFTerm M N K}
    {Q : List (DFTerm M N K)}
    (hAB : A.decorated.collectorBefore B.decorated)
    (hcorrection :
      CInsert n leftWeight rightWeight P (B.correction A) Q) :
    cutoffInsertionBefore n leftWeight rightWeight
      (Q, A) (P ++ [B], A) := by
  unfold cutoffInsertionBefore cutoffInsertionMeasure
  apply Prod.Lex.right
  apply Prod.Lex.left
  dsimp only [Prod.fst, Prod.snd]
  rw [obstruction_inserts_before hcorrection
      (DTerm.collector_before_right B.positive),
    List.map_append, List.map_singleton,
    obstruction_last_before
      (P.map DFTerm.decorated)
      B.decorated A.decorated hAB]
  omega

/-- Every below-cutoff selected term admits one finite cutoff insertion. -/
lemma exists_cutoffInserts
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ∀ (L : List (DFTerm M N K))
      (A : DFTerm M N K),
      decoratedFamilyWeight leftWeight rightWeight A < n →
        ∃ R : List (DFTerm M N K),
          CInsert n leftWeight rightWeight L A R := by
  intro L A
  refine
    (insertion_before_wf
      (M := M) (N := N) (K := K) n leftWeight rightWeight).induction
        (C := fun state =>
          decoratedFamilyWeight leftWeight rightWeight state.2 < n →
            ∃ R : List (DFTerm M N K),
              CInsert n leftWeight rightWeight state.1 state.2 R)
        (L, A) ?_
  rintro ⟨L, A⟩ ih hA
  rcases List.eq_nil_or_concat' L with rfl | ⟨P, B, rfl⟩
  · exact ⟨[A], CInsert.nil A⟩
  · by_cases hBA : B.decorated.collectorLe A.decorated
    · exact ⟨P ++ [B, A], CInsert.append P B A hBA⟩
    · have hAB :
          A.decorated.collectorBefore B.decorated := by
        simpa [DTerm.collectorLe] using hBA
      by_cases hcorrectionWeight :
          decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) < n
      · rcases
          ih (P, B.correction A)
            (insertion_before_correction
              hleftWeight hrightWeight P B A hA hcorrectionWeight)
            hcorrectionWeight with
          ⟨Q, hcorrection⟩
        rcases
          ih (Q, A)
            (insertion_before_after
              P hAB hcorrection)
            hA with
          ⟨R, hinsert⟩
        exact
          ⟨R ++ [B],
            CInsert.retained
              P B A hAB hcorrectionWeight hcorrection hinsert⟩
      · have hcorrectionWeightGe :
            n ≤ decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) :=
          Nat.le_of_not_gt hcorrectionWeight
        rcases
          ih (P, A)
            (insertion_state_before P B A hAB)
            hA with
          ⟨R, hinsert⟩
        exact
          ⟨R ++ [B],
            CInsert.residual
              P B A hAB hcorrectionWeightGe hinsert⟩

/-- Every finite family-term list admits one finite cutoff-aware collection. -/
lemma exists_cutoffCollects
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ∀ L : List (DFTerm M N K),
      ∃ R : List (DFTerm M N K),
        CCollec n leftWeight rightWeight L R := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
      exact ⟨[], CCollec.nil⟩
  | append_singleton P A ih =>
      rcases ih with ⟨C, hcollect⟩
      by_cases hA :
          decoratedFamilyWeight leftWeight rightWeight A < n
      · rcases exists_cutoffInserts hleftWeight hrightWeight C A hA with
          ⟨R, hinsert⟩
        exact ⟨R, CCollec.retained P A hA hcollect hinsert⟩
      · exact
          ⟨C, CCollec.residual P A
            (Nat.le_of_not_gt hA) hcollect⟩

end FCTermin
end TCTex
end Submission

/-!
# Sorted cutoff-aware inverse-raw family endpoints

The cutoff-aware full collector has an unconditional finite scheduler.  This
file packages its output for the inverse-oriented raw trace.  The retained
endpoint is sorted by the complete decorated Hall key, consists entirely of
below-cutoff family terms, resolves every maximal same-shape block as one exact
recipe fiber, and evaluates to the powered commutator in every matching
nilpotent target.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FCEnd

open scoped commutatorElement

open HACoeff
open BFTrunc
open CFCollec.DFTerm
open FCTermin
open DSBridge
open OCPartit
open RSCovera
open ITEvalua

namespace DFTerm

/--
Cutoff insertion preserves the invariant that every retained family term lies
strictly below the cutoff.
-/
lemma weight_cutoff_inserts
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R)
    (hL :
      ∀ term ∈ L,
        decoratedFamilyWeight leftWeight rightWeight term < n)
    (hA : decoratedFamilyWeight leftWeight rightWeight A < n) :
    ∀ term ∈ R,
      decoratedFamilyWeight leftWeight rightWeight term < n := by
  induction hinsert with
  | nil A =>
      intro term hterm
      rcases List.mem_singleton.mp hterm with rfl
      exact hA
  | append P B A _hBA =>
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hL term (List.mem_append_left [B] hterm)
      · rcases List.mem_cons.mp hterm with hterm | hterm
        · subst term
          exact hL B (by simp)
        · rcases List.mem_singleton.mp hterm with rfl
          exact hA
  | retained P B A _hAB hcorrectionWeight hcorrection hinsert
      ihcorrection ihinsert =>
      have hP :
          ∀ term ∈ P,
            decoratedFamilyWeight leftWeight rightWeight term < n := by
        intro term hterm
        exact hL term (List.mem_append_left [B] hterm)
      have hQ := ihcorrection hP hcorrectionWeight
      have hR := ihinsert hQ hA
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hR term hterm
      · rcases List.mem_singleton.mp hterm with rfl
        exact hL _ (by simp)
  | residual P B A _hAB _hcorrectionWeight hinsert ihinsert =>
      have hP :
          ∀ term ∈ P,
            decoratedFamilyWeight leftWeight rightWeight term < n := by
        intro term hterm
        exact hL term (List.mem_append_left [B] hterm)
      have hR := ihinsert hP hA
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hR term hterm
      · rcases List.mem_singleton.mp hterm with rfl
        exact hL _ (by simp)

/-- Every retained cutoff-collection endpoint term lies below the cutoff. -/
lemma weight_cutoff_collects
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : CCollec n leftWeight rightWeight L R) :
    ∀ term ∈ R,
      decoratedFamilyWeight leftWeight rightWeight term < n := by
  induction hcollect with
  | nil =>
      simp
  | retained P A hweight hcollect hinsert ihcollect =>
      exact weight_cutoff_inserts hinsert ihcollect hweight
  | residual P A _hweight hcollect ihcollect =>
      exact ihcollect

/-- Family-term collapsed evaluation is word-list collapsed evaluation. -/
lemma collapsed_decorated_family
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (terms : List (DFTerm M N K)) :
    CFCollec.DFTerm.collapsedList
        x y terms =
      BFTrunc.collapsedList
        x y (decoratedFamilyList terms) := by
  simp [CFCollec.DFTerm.collapsedList,
    CFCollec.DFTerm.collapsedEvalAt,
    BFTrunc.collapsedList,
    decoratedFamilyList, Function.comp_def]

end DFTerm

/--
An unconditional sorted cutoff endpoint for the inverse-oriented raw labelled
trace, retaining the concrete finite scheduler derivation.
-/
structure IDTerms
    (M N n leftWeight rightWeight : ℕ) where
  factors :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  family_cutoff_collects :
    CCollec n leftWeight rightWeight
      (inverseDecoratedTerms M N) factors

namespace IDTerms

/-- The cutoff-aware inverse-raw endpoint exists for every positive weight pair. -/
lemma nonempty
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Nonempty
      (IDTerms
        M N n leftWeight rightWeight) := by
  rcases exists_cutoffCollects
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      (n := n) hleftWeight hrightWeight
      (inverseDecoratedTerms M N) with
    ⟨factors, hcollect⟩
  exact ⟨{
    factors := factors
    family_cutoff_collects := hcollect }⟩

/-- Every retained endpoint factor has weighted Hall degree below the cutoff. -/
lemma weight_lt
    {M N n leftWeight rightWeight : ℕ}
    (collected :
      IDTerms
        M N n leftWeight rightWeight) :
    ∀ term ∈ collected.factors,
      decoratedFamilyWeight leftWeight rightWeight term < n :=
  DFTerm.weight_cutoff_collects
    collected.family_cutoff_collects

/-- The retained endpoint is sorted by the complete decorated Hall key. -/
lemma decorated_collected
    {M N n leftWeight rightWeight : ℕ}
    (collected :
      IDTerms
        M N n leftWeight rightWeight) :
    Collected (collected.factors.map DFTerm.decorated) :=
  decorated_collected_collects collected.family_cutoff_collects

/-- Every maximal same-shape endpoint block is one complete recipe fiber. -/
lemma filter_eq
    {M N n leftWeight rightWeight : ℕ}
    (collected :
      IDTerms
        M N n leftWeight rightWeight)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks collected.factors) :
    ∃ shape : CWord HPAtom,
      collected.factors.filter
        (fun term => term.family.recipe.erasedShape = shape) =
          block :=
  same_blocks_decorated
    collected.decorated_collected hblock

/--
In every matching nilpotent target, the retained endpoint computes the
commutator of the corresponding natural powers.
-/
lemma collapsed_list_pow
    {M N n leftWeight rightWeight : ℕ}
    (collected :
      IDTerms
        M N n leftWeight rightWeight)
    {G : Type*}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    CFCollec.DFTerm.collapsedList
        x y collected.factors =
      ⁅x ^ M, y ^ N⁆ := by
  rw [collapsed_cutoff_collects
    hleftWeight hrightWeight hx hy hbot collected.family_cutoff_collects]
  rw [DFTerm.collapsed_decorated_family]
  rw [decorated_raw_terms]
  exact collapsed_commutator_pow x y

/--
The word-list evaluator exposes the same powered-commutator contract to the
existing symbolic recollection interfaces.
-/
lemma collapsed_decorated_pow
    {M N n leftWeight rightWeight : ℕ}
    (collected :
      IDTerms
        M N n leftWeight rightWeight)
    {G : Type*}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    BFTrunc.collapsedList
        x y (decoratedFamilyList collected.factors) =
      ⁅x ^ M, y ^ N⁆ := by
  rw [← DFTerm.collapsed_decorated_family]
  exact collected.collapsed_list_pow
    x y hleftWeight hrightWeight hx hy hbot

end IDTerms

end FCEnd
end TCTex
end Submission

/-!
# Global natural recollection from cutoff-aware full collection

The cutoff-aware full collector produces a finite sorted endpoint for every
pair of natural source multiplicities.  This file compresses each maximal
equal-shape run to one Hall word with a concrete natural multiplicity.  The
ordered run packet still computes the powered commutator in every matching
nilpotent target.

The resulting layer is deliberately natural and specialization-dependent.
Replacing its concrete run multiplicities by a fixed ordered family of
integer-valued polynomials is the remaining interpolation theorem.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CRLayer

open scoped commutatorElement

open HACoeff
open CFCollec.DFTerm
open FCEnd
open FCEnd.DFTerm
open
  FCEnd.IDTerms
open OCPartit

/-- One ordered equal-shape run compressed to a Hall word and its multiplicity. -/
structure NRFactor where
  word :
    CWord HPAtom
  multiplicity :
    ℕ

namespace NRFactor

/-- Evaluate one compressed natural run at an arbitrary Hall pair. -/
def evalAt
    {G : Type*}
    [Group G]
    (x y : G)
    (factor : NRFactor) :
    G :=
  factor.word.eval (HPAtom.eval x y) ^ factor.multiplicity

end NRFactor

/-- Shape of the first term of a run, with an irrelevant fallback for `[]`. -/
def firstErasedShape
    {M N K : ℕ} :
    List (DFTerm M N K) →
      CWord HPAtom
  | [] =>
      .atom .left
  | term :: _ =>
      term.erasedShape

/-- Compress one equal-shape run to one natural Hall factor. -/
def naturalRunFactor
    {M N K : ℕ}
    (block : List (DFTerm M N K)) :
    NRFactor where
  word :=
    firstErasedShape block
  multiplicity :=
    block.length

/-- Compress every maximal equal-shape run while preserving run order. -/
def naturalShapeFactors
    {M N K : ℕ}
    (blocks : List (List (DFTerm M N K))) :
    List NRFactor :=
  blocks.map naturalRunFactor

/-- Compress every maximal equal-shape run while preserving run order. -/
def naturalRunFactors
    {M N K : ℕ}
    (terms : List (DFTerm M N K)) :
    List NRFactor :=
  naturalShapeFactors (sameErasedBlocks terms)

namespace DFTerm

/-- A same-shape concrete term block evaluates as the corresponding power. -/
lemma collapsed_same_erased
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (block : List (DFTerm M N K))
    (shape : CWord HPAtom)
    (hsame : ∀ term ∈ block, term.erasedShape = shape) :
    CFCollec.DFTerm.collapsedList
        x y block =
      shape.eval (HPAtom.eval x y) ^ block.length := by
  induction block with
  | nil =>
      simp [CFCollec.DFTerm.collapsedList]
  | cons term terms ih =>
      rw [show
        CFCollec.DFTerm.collapsedList
            x y (term :: terms) =
          CFCollec.DFTerm.collapsedEvalAt
              x y term *
            CFCollec.DFTerm.collapsedList
              x y terms by
        rfl]
      rw [ih (fun next hnext => hsame next (by simp [hnext]))]
      change
        term.erasedShape.eval (HPAtom.eval x y) *
            shape.eval (HPAtom.eval x y) ^ terms.length =
          shape.eval (HPAtom.eval x y) ^ (terms.length + 1)
      rw [hsame term (by simp), pow_succ']

/-- Compressing one same-shape block preserves its collapsed evaluation. -/
lemma run_collapsed_list
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (block : List (DFTerm M N K))
    (hsame : SameErasedBlock block) :
    (naturalRunFactor block).evalAt x y =
      CFCollec.DFTerm.collapsedList
        x y block := by
  rcases hsame with ⟨shape, hshape⟩
  rw [collapsed_same_erased
    x y block shape hshape]
  cases block with
  | nil =>
      simp [NRFactor.evalAt, naturalRunFactor,
        firstErasedShape]
  | cons term terms =>
      simp [NRFactor.evalAt, naturalRunFactor,
        firstErasedShape, hshape term (by simp)]

/-- Ordered compression preserves the evaluation of any same-shape block list. -/
lemma natural_collapsed_flatten
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (blocks : List (List (DFTerm M N K)))
    (hblocks :
      ∀ block ∈ blocks,
        SameErasedBlock block) :
    ((naturalShapeFactors blocks).map fun factor =>
        factor.evalAt x y).prod =
      CFCollec.DFTerm.collapsedList
        x y blocks.flatten := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      rw [show
        naturalShapeFactors (block :: blocks) =
          naturalRunFactor block :: naturalShapeFactors blocks by
        rfl]
      rw [List.map_cons, List.prod_cons,
        run_collapsed_list
          x y block (hblocks block (by simp))]
      rw [show
        CFCollec.DFTerm.collapsedList
            x y (block :: blocks).flatten =
          CFCollec.DFTerm.collapsedList
              x y block *
            CFCollec.DFTerm.collapsedList
              x y blocks.flatten by
        simp [
          CFCollec.DFTerm.collapsed_list_append]]
      rw [ih (fun next hnext => hblocks next (by simp [hnext]))]

/-- Ordered run compression preserves collapsed evaluation of every term list. -/
lemma natural_run_collapsed
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (terms : List (DFTerm M N K)) :
    ((naturalRunFactors terms).map fun factor =>
        factor.evalAt x y).prod =
      CFCollec.DFTerm.collapsedList
        x y terms := by
  rw [naturalRunFactors,
    natural_collapsed_flatten
      x y (sameErasedBlocks terms)
        (same_erased_blocks terms)]
  rw [flatten_same_blocks]

end DFTerm

/--
A globally selected finite cutoff-aware endpoint for every natural
multiplicity pair.
-/
structure NRLayer
    (n leftWeight rightWeight : ℕ) where
  endpoint :
    ∀ M N : ℕ,
      IDTerms
        M N n leftWeight rightWeight

/-- Positive input weights construct the global natural recollection layer. -/
noncomputable def naturalRecollectionLayer
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    NRLayer n leftWeight rightWeight where
  endpoint M N :=
    Classical.choice
      (IDTerms.nonempty
        M N n leftWeight rightWeight hleftWeight hrightWeight)

namespace NRLayer

/-- Concrete ordered Hall-shape run factors at one natural specialization. -/
def factors
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    List NRFactor :=
  naturalRunFactors (layer.endpoint M N).factors

/-- Every retained concrete family term lies below the nilpotent cutoff. -/
lemma endpoint_weight_lt
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ∀ term ∈ (layer.endpoint M N).factors,
      decoratedFamilyWeight leftWeight rightWeight term < n :=
  (layer.endpoint M N).weight_lt

/-- Every selected endpoint is sorted by the complete decorated Hall key. -/
lemma endpoint_decorated_collected
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    Collected
      ((layer.endpoint M N).factors.map DFTerm.decorated) :=
  (layer.endpoint M N).decorated_collected

/-- Every maximal equal-shape run is one complete retained recipe-shape fiber. -/
lemma endpoint_filter_eq
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks (layer.endpoint M N).factors) :
    ∃ shape : CWord HPAtom,
      (layer.endpoint M N).factors.filter
        (fun term => term.family.recipe.erasedShape = shape) =
          block :=
  (layer.endpoint M N).filter_eq block hblock

/--
At every matching nilpotent target, the global natural run packet computes the
powered commutator.
-/
lemma factors_commutator_pow
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    ((layer.factors M N).map fun factor => factor.evalAt x y).prod =
      ⁅x ^ M, y ^ N⁆ := by
  rw [factors,
    DFTerm.natural_run_collapsed]
  exact
    (layer.endpoint M N).collapsed_list_pow
      x y hleftWeight hrightWeight hx hy hbot

end NRLayer

end CRLayer
end TCTex
end Submission

/-!
# Fixed signed-profile stabilization for cutoff-aware full collection

The cutoff-aware full collector gives one finite ordered Hall-shape run packet
at every natural specialization.  This file isolates the remaining
interpolation theorem: one fixed ordered signed-profile packet agrees with all
of those concrete run packets in the free lower-central truncation.

That stabilization hypothesis is exactly enough to recover the existing
cutoff-specific natural signed-block packet interface.  A universal
all-integral signed-block packet supplies the stabilization witness
automa.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CFStab

universe u

open scoped commutatorElement

open CRLayer
open CFSubsti
open CFExp
open UNPkt
open SCFactor

/--
One fixed ordered signed-profile packet interpolates every concrete natural
shape-run packet selected by the cutoff-aware full collector.
-/
structure NRStab
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (d : ℕ)
    (fixedPackets : List RFPkt) :
    Prop where
  leftWeight_pos :
    0 < leftWeight
  rightWeight_pos :
    0 < rightWeight
  packet_prod_factors :
    ∀ (M N : ℕ)
      (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      left ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (leftWeight - 1) →
        right ∈ Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (rightWeight - 1) →
          (fixedPackets.map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value (M : ℤ) (N : ℤ)).prod =
            ((layer.factors M N).map fun factor =>
              factor.evalAt left right).prod

namespace NRStab

/--
Fixed packet stabilization gives the natural powered-commutator law on the
prescribed lower-central layers.
-/
lemma nat_cast_pow
    {n leftWeight rightWeight d : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {fixedPackets : List RFPkt}
    (stabilization :
      NRStab.{u}
        layer d fixedPackets)
    (M N : ℕ)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (leftWeight - 1))
    (hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (rightWeight - 1)) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ :=
  (stabilization.packet_prod_factors M N left right hleft hright).trans
    (layer.factors_commutator_pow
      M N left right stabilization.leftWeight_pos
        stabilization.rightWeight_pos hleft hright
          trunc_last_bot)

/--
Root-layer stabilization supplies the existing cutoff-specific natural packet
interface.
-/
def truncNaturalPacket
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {fixedPackets : List RFPkt}
    (stabilization :
      NRStab.{u}
        layer d fixedPackets) :
    TBPkt.{u} d n where
  packets :=
    fixedPackets
  list_nat_cast left right M N :=
    stabilization.nat_cast_pow M N left right
      (by simp) (by simp)

end NRStab

/--
A universal all-integral signed-profile packet automa stabilizes every
cutoff-aware natural recollection layer.
-/
def runStabilizationUniversal
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (d : ℕ)
    (packet : UAPkt.{u})
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    NRStab.{u}
      layer d packet.packets where
  leftWeight_pos :=
    hleftWeight
  rightWeight_pos :=
    hrightWeight
  packet_prod_factors M N left right hleft hright := by
    have hpacket :
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value (M : ℤ) (N : ℤ)).prod =
          ⁅left ^ M, right ^ N⁆ := by
      simpa only [zpow_natCast] using
        packet.listEval_eq left right (M : ℤ) (N : ℤ)
    exact hpacket.trans
      (layer.factors_commutator_pow
        M N left right hleftWeight hrightWeight hleft hright
          trunc_last_bot).symm

end CFStab
end TCTex
end Submission

/-!
# Finite vocabulary support for cutoff-aware full collection

The cutoff-aware full collector terminates without appealing to the earlier
support-sensitive operational endpoint.  Its retained terms nevertheless lie
in the same conservative finite correction-closure vocabulary.

This file proves that connection directly.  Cutoff insertion and collection
preserve finite correction-tree provenance from their source list.  The
existing finite correction closure then covers every retained inverse-raw
endpoint term, and shape-run compression preserves that finite support.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FVSuppor

open HACoeff
open BRSpec
open CFCollec.DFTerm
open FCEnd
open
  FCEnd.IDTerms
open CRLayer
open OCClos
open OCClos.DFTerm
open OCPartit
open UCSuppor
open UCVocabu
open URVocabu
open USSuppor

namespace DFTerm

/--
Every term returned by cutoff insertion remains in the finite correction-tree
closure of any common source containing the prefix and inserted term.
-/
lemma correction_cutoff_inserts
    {M N K n leftWeight rightWeight : ℕ}
    {source L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R)
    (hL : ∀ term ∈ L, CGFrom source term)
    (hA : CGFrom source A) :
    ∀ term ∈ R, CGFrom source term := by
  induction hinsert with
  | nil A =>
      intro term hterm
      rcases List.mem_singleton.mp hterm with rfl
      exact hA
  | append P B A _hBA =>
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hL term (List.mem_append_left [B] hterm)
      · rcases List.mem_cons.mp hterm with hterm | hterm
        · subst term
          exact hL B (by simp)
        · rcases List.mem_singleton.mp hterm with rfl
          exact hA
  | retained P B A _hAB _hweight hcorrection hinsert
      ihcorrection ihinsert =>
      have hP :
          ∀ term ∈ P, CGFrom source term := by
        intro term hterm
        exact hL term (List.mem_append_left [B] hterm)
      have hBA :
          CGFrom source (B.correction A) :=
        CGFrom.correction
          (hL B (by simp)) hA
      have hQ := ihcorrection hP hBA
      have hR := ihinsert hQ hA
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hR term hterm
      · exact hL term (List.mem_append_right P hterm)
  | residual P B A _hAB _hweight hinsert ihinsert =>
      have hP :
          ∀ term ∈ P, CGFrom source term := by
        intro term hterm
        exact hL term (List.mem_append_left [B] hterm)
      have hR := ihinsert hP hA
      intro term hterm
      rcases List.mem_append.mp hterm with hterm | hterm
      · exact hR term hterm
      · exact hL term (List.mem_append_right P hterm)

/--
Every retained cutoff-collection endpoint term is generated from the original
input by finitely many pairwise corrections.
-/
lemma correction_cutoff_collects
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : CCollec n leftWeight rightWeight L R) :
    ∀ term ∈ R, CGFrom L term := by
  induction hcollect with
  | nil =>
      simp
  | retained P A _hweight hcollect hinsert ihcollect =>
      apply correction_cutoff_inserts hinsert
      · intro term hterm
        exact (ihcollect term hterm).mono fun next hnext =>
          List.mem_append_left [A] hnext
      · exact CGFrom.source (by simp)
  | residual P A _hweight hcollect ihcollect =>
      intro term hterm
      exact (ihcollect term hterm).mono fun next hnext =>
        List.mem_append_left [A] hnext

/--
Every below-cutoff inverse-raw collection endpoint term has an erased-shape
representative in the retained finite correction closure.
-/
lemma recipe_collects_raw
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {R : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)}
    (hcollect :
      CCollec n leftWeight rightWeight
        (inverseDecoratedTerms M N) R)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm : term ∈ R)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight term < n) :
    ∃ recipe ∈
        correctionClosureRecipes n leftWeight rightWeight,
      recipe.erasedShape = term.erasedShape := by
  have htermShapeWeight :
      term.erasedShape.weight
          (HPAtom.weight leftWeight rightWeight) < n := by
    simpa [decoratedFamilyWeight, weightedWordWeight,
      term.erased_shape_family] using hweight
  have hgenerated :
      CGFrom (inverseDecoratedTerms M N) term :=
    correction_cutoff_collects hcollect term hterm
  rcases
      recipe_generated_weight
        hleftWeight hrightWeight
        (sourceRecipes := sourceRecipes n leftWeight rightWeight)
        (fun sourceTerm hsourceTerm hsourceWeight => by
          apply raw_decorated_terms
            hleftWeight hrightWeight hsourceTerm
          simpa [decoratedFamilyWeight, weightedWordWeight,
            sourceTerm.erased_shape_family] using hsourceWeight)
        hgenerated hweight with
    ⟨recipe, hrecipe, hshape⟩
  refine ⟨recipe, retained_correction_closure.mpr ⟨?_, ?_⟩, hshape⟩
  · exact correction_closure hrecipe
      (Nat.le_of_lt hweight)
  · rw [weightedWordWeight, hshape]
    exact htermShapeWeight

end DFTerm

namespace IDTerms

/-- Every retained inverse-raw endpoint term is represented by the finite
correction closure. -/
lemma exists_of_mem
    {M N n leftWeight rightWeight : ℕ}
    (collected :
      IDTerms
        M N n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm : term ∈ collected.factors) :
    ∃ recipe ∈
        correctionClosureRecipes n leftWeight rightWeight,
      recipe.erasedShape = term.erasedShape :=
  DFTerm.recipe_collects_raw
    hleftWeight hrightWeight collected.family_cutoff_collects
      term hterm (collected.weight_lt term hterm)

/-- Every erased Hall shape retained by the cutoff collector lies in the
canonical finite correction-closure vocabulary. -/
lemma erased_vocab_factors
    {M N n leftWeight rightWeight : ℕ}
    (collected :
      IDTerms
        M N n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm : term ∈ collected.factors) :
    term.erasedShape ∈
      erasedShapeVocabulary n leftWeight rightWeight := by
  rcases exists_of_mem
      collected hleftWeight hrightWeight term hterm with
    ⟨recipe, hrecipe, hshape⟩
  rw [← hshape]
  exact shape_vocabulary_recipes hrecipe

end IDTerms

open IDTerms

namespace NRLayer

/-- Every compressed natural run factor lies in the fixed finite
correction-closure vocabulary. -/
lemma erased_vocabulary_factors
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (factor : NRFactor)
    (hfactor : factor ∈ layer.factors M N) :
    factor.word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  rw [
    CRLayer.NRLayer.factors,
    naturalRunFactors, naturalShapeFactors] at hfactor
  rcases List.mem_map.mp hfactor with ⟨block, hblock, rfl⟩
  cases block with
  | nil =>
      apply False.elim
      apply List.ne_nil_of_mem_splitBy
        (show
          [] ∈ (layer.endpoint M N).factors.splitBy
            fun left right => decide (left.erasedShape = right.erasedShape) by
          exact hblock)
      rfl
  | cons term terms =>
      change term.erasedShape ∈
        erasedShapeVocabulary n leftWeight rightWeight
      apply
        erased_vocab_factors
          (layer.endpoint M N) hleftWeight hrightWeight term
      rw [← flatten_same_blocks (layer.endpoint M N).factors]
      exact List.mem_flatten.mpr ⟨term :: terms, hblock, by simp⟩

/-- Every compressed natural run factor remains strictly below cutoff. -/
lemma word_cutoff_factors
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (factor : NRFactor)
    (hfactor : factor ∈ layer.factors M N) :
    factor.word.weight (HPAtom.weight leftWeight rightWeight) < n :=
  erased_shape_vocabulary
    (erased_vocabulary_factors layer
      hleftWeight hrightWeight M N factor hfactor)

/-- Every compressed natural run factor uses both Hall-pair atom directions. -/
lemma bidegree_positive_factors
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (factor : NRFactor)
    (hfactor : factor ∈ layer.factors M N) :
    factor.word.PBPos :=
  bidegree_positive_vocabulary
    (erased_vocabulary_factors layer
      hleftWeight hrightWeight M N factor hfactor)

end NRLayer

end FVSuppor
end TCTex
end Submission

/-!
# Duplicate-free finite subinventories for natural cutoff recollection

The terminating cutoff-aware collector compresses its sorted endpoint into
maximal equal-shape runs.  This file records the finite-inventory consequence:
the compressed run words are duplicate-free, every run word lies in the fixed
finite correction-closure vocabulary, and therefore every natural
specialization uses at most the vocabulary cardinality.

The statements remain deliberately natural and specialization-dependent.
They isolate the finite ordered support available before proving polynomial
stabilization of the run multiplicities.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CRSubinv

open HACoeff
open FVSuppor
open
  FVSuppor.NRLayer
open CRLayer
open DSBridge
open OCPartit
open FORed
open UCSuppor

/-- Primary More3 order on erased Hall-pair words: larger degree first, then
lexicographic shape code. -/
def erasedShapeBefore
    (left right : CWord HPAtom) :
    Prop :=
  right.weight (HPAtom.weight 1 1) <
      left.weight (HPAtom.weight 1 1) ∨
    (left.weight (HPAtom.weight 1 1) =
        right.weight (HPAtom.weight 1 1) ∧
      pairShapeCode left < pairShapeCode right)

/-- The primary erased-word order is transitive. -/
lemma erased_before_trans
    {left middle right : CWord HPAtom}
    (hleftMiddle : erasedShapeBefore left middle)
    (hmiddleRight : erasedShapeBefore middle right) :
    erasedShapeBefore left right := by
  unfold erasedShapeBefore at hleftMiddle hmiddleRight ⊢
  rcases hleftMiddle with hleftMiddle | ⟨hleftMiddleDegree, hleftMiddleCode⟩
  · rcases hmiddleRight with hmiddleRight | ⟨hmiddleRightDegree, _⟩
    · exact Or.inl (lt_trans hmiddleRight hleftMiddle)
    · exact Or.inl (by omega)
  · rcases hmiddleRight with hmiddleRight | ⟨hmiddleRightDegree, hmiddleRightCode⟩
    · exact Or.inl (by omega)
    · exact Or.inr
        ⟨hleftMiddleDegree.trans hmiddleRightDegree,
          lt_trans hleftMiddleCode hmiddleRightCode⟩

/-- No erased Hall-pair word strictly precedes itself. -/
lemma erased_before_irrefl
    (word : CWord HPAtom) :
    ¬erasedShapeBefore word word := by
  unfold erasedShapeBefore
  intro hbefore
  rcases hbefore with hdegree | ⟨_hdegree, hcode⟩
  · exact (Nat.lt_irrefl _ hdegree)
  · exact (lt_irrefl _ hcode)

/-- Strict primary precedence implies distinct erased Hall-pair words. -/
lemma ne_erased_before
    {left right : CWord HPAtom}
    (hbefore : erasedShapeBefore left right) :
    left ≠ right := by
  intro hshape
  subst right
  exact erased_before_irrefl left hbefore

namespace DFTerm

/-- Decorated primary precedence is exactly erased-word primary precedence. -/
lemma erased_before_decorated
    {M N K : ℕ}
    {left right : DFTerm M N K}
    (hbefore : left.decorated.shapeBefore right.decorated) :
    erasedShapeBefore left.erasedShape right.erasedShape := by
  simpa [erasedShapeBefore, DTerm.shapeBefore,
    DTerm.higherDegreeBefore, DTerm.erasedDegree,
    DTerm.erasedShapeCode, DFTerm.erasedShape] using
      hbefore

/-- Replacing the left endpoint of a primary comparison by an equal-shape
family term preserves the comparison. -/
lemma decorated_before_erased
    {M N K : ℕ}
    {left middle right : DFTerm M N K}
    (hshape : left.erasedShape = middle.erasedShape)
    (hbefore : middle.decorated.shapeBefore right.decorated) :
    left.decorated.shapeBefore right.decorated := by
  have hdecoratedShape :
      left.decorated.erasedShape = middle.decorated.erasedShape := by
    simpa [DFTerm.erasedShape] using hshape
  simpa [DTerm.shapeBefore, DTerm.higherDegreeBefore,
    DTerm.erasedDegree, DTerm.erasedShapeCode,
    hdecoratedShape] using hbefore

/-- Maximal equal-shape runs in a sorted family endpoint are strictly ordered
by their first erased shapes. -/
lemma pairwise_blocks_sorted
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (hsorted :
      terms.Pairwise fun left right =>
        left.erasedShape = right.erasedShape ∨
          left.decorated.shapeBefore right.decorated) :
    ((sameErasedBlocks terms).map firstErasedShape).Pairwise
      erasedShapeBefore := by
  rw [List.pairwise_map]
  let blocks := sameErasedBlocks terms
  let blockBefore :
      List (DFTerm M N K) →
        List (DFTerm M N K) → Prop :=
    fun leftBlock rightBlock =>
      ∃ hleftBlockNe : leftBlock ≠ [],
        ∃ hrightBlockNe : rightBlock ≠ [],
          (leftBlock.head hleftBlockNe).decorated.shapeBefore
            (rightBlock.head hrightBlockNe).decorated
  letI : Trans blockBefore blockBefore blockBefore :=
    ⟨by
      rintro leftBlock middleBlock rightBlock
        ⟨hleftBlockNe, hmiddleBlockNe, hleftMiddle⟩
        ⟨_hmiddleBlockNe, hrightBlockNe, hmiddleRight⟩
      exact
        ⟨hleftBlockNe, hrightBlockNe,
          shapeBefore_trans hleftMiddle hmiddleRight⟩⟩
  have hflattenSorted :
      blocks.flatten.Pairwise fun left right =>
        left.erasedShape = right.erasedShape ∨
          left.decorated.shapeBefore right.decorated := by
    simpa [blocks, flatten_same_blocks] using hsorted
  have hblocksSorted :=
    (List.pairwise_flatten.mp hflattenSorted).2
  have hblocksBoundary :
      blocks.IsChain fun leftBlock rightBlock =>
        ∃ hleftBlockNe : leftBlock ≠ [],
          ∃ hrightBlockNe : rightBlock ≠ [],
            decide
              ((leftBlock.getLast hleftBlockNe).erasedShape =
                (rightBlock.head hrightBlockNe).erasedShape) = false := by
    simpa [blocks, sameErasedBlocks] using
      (List.isChain_getLast_head_splitBy
        (fun left right =>
          decide (left.erasedShape = right.erasedShape))
        terms)
  have hblocksBefore : blocks.IsChain blockBefore := by
    rw [List.isChain_iff_getElem] at hblocksBoundary ⊢
    intro index hindex
    rcases hblocksBoundary index hindex with
      ⟨hleftBlockNe, hrightBlockNe, hboundary⟩
    refine ⟨hleftBlockNe, hrightBlockNe, ?_⟩
    have hcross :=
      hblocksSorted.isChain.getElem index hindex
        ((blocks[index]).getLast hleftBlockNe)
          (List.getLast_mem hleftBlockNe)
        ((blocks[index + 1]).head hrightBlockNe)
          (List.head_mem hrightBlockNe)
    rcases hcross with hcross | hcross
    · simp [hcross] at hboundary
    · apply decorated_before_erased _ hcross
      have hleftBlockMem : blocks[index] ∈ blocks :=
        List.getElem_mem (by omega)
      rcases
          same_erased_blocks
            terms blocks[index] (by
              simp only [blocks] at hleftBlockMem
              exact hleftBlockMem) with
        ⟨shape, hshape⟩
      exact
        (hshape _ (List.head_mem hleftBlockNe)).trans
          (hshape _ (List.getLast_mem hleftBlockNe)).symm
  exact hblocksBefore.pairwise.imp (by
    rintro leftBlock rightBlock
      ⟨hleftBlockNe, hrightBlockNe, hbefore⟩
    cases leftBlock with
    | nil =>
        exact False.elim (hleftBlockNe rfl)
    | cons leftHead leftTail =>
        cases rightBlock with
        | nil =>
            exact False.elim (hrightBlockNe rfl)
        | cons rightHead rightTail =>
            simpa [firstErasedShape] using
              erased_before_decorated hbefore)

/--
For a primary-shape-sorted family endpoint, the first erased shapes of its
maximal equal-shape runs are duplicate-free.
-/
lemma nodup_blocks_sorted
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (hsorted :
      terms.Pairwise fun left right =>
        left.erasedShape = right.erasedShape ∨
          left.decorated.shapeBefore right.decorated) :
    ((sameErasedBlocks terms).map firstErasedShape).Nodup :=
  (pairwise_blocks_sorted
    hsorted).imp ne_erased_before

end DFTerm

namespace NRLayer

/-- Compressed natural run words remain strictly primary-shape ordered. -/
lemma pairwise_erased_before
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ((layer.factors M N).map NRFactor.word).Pairwise
      erasedShapeBefore := by
  rw [
    CRLayer.NRLayer.factors,
    naturalRunFactors, naturalShapeFactors,
    List.map_map]
  exact
    DFTerm.pairwise_blocks_sorted
      (pairwise_sorted_decorated
        (layer.endpoint M N).decorated_collected)

/-- Compressed natural run words are duplicate-free at every specialization. -/
lemma nodup_word_factors
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ((layer.factors M N).map NRFactor.word).Nodup :=
  (pairwise_erased_before layer M N).imp
    ne_erased_before

/--
Every natural specialization uses at most one compressed run per word in the
fixed finite correction-closure vocabulary.
-/
lemma length_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (layer.factors M N).length ≤
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  let words :=
    (layer.factors M N).map NRFactor.word
  have hwordsNodup : words.Nodup :=
    nodup_word_factors layer M N
  have hvocabularyNodup :
      (erasedShapeVocabulary n leftWeight rightWeight).Nodup := by
    exact List.nodup_dedup _
  have hsubset :
      ∀ word ∈ words,
        word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
    intro word hword
    rcases List.mem_map.mp hword with ⟨factor, hfactor, rfl⟩
    exact
      erased_vocabulary_factors
        layer hleftWeight hrightWeight M N factor hfactor
  calc
    (layer.factors M N).length =
        words.length := by
      simp [words]
    _ =
        words.toFinset.card :=
      (List.toFinset_card_of_nodup hwordsNodup).symm
    _ ≤
        (erasedShapeVocabulary n leftWeight rightWeight).toFinset.card := by
      apply Finset.card_le_card
      intro word hword
      rw [List.mem_toFinset] at hword ⊢
      exact hsubset word hword
    _ =
        (erasedShapeVocabulary n leftWeight rightWeight).length :=
      List.toFinset_card_of_nodup hvocabularyNodup

end NRLayer

end CRSubinv
end TCTex
end Submission

/-!
# Fixed ordered vocabularies for natural cutoff recollection

The finite correction-closure vocabulary is an unordered support universe.
The cutoff-aware full collector has more structure: after equal-shape run
compression, every specialization is strictly ordered by the More3 primary
shape key.

This file sorts the finite vocabulary by that same key and proves that every
natural run-word list is a literal sublist of the resulting fixed ordered
vocabulary.  This is the order-preserving finite skeleton needed before
padding absent specialization words by zero multiplicity.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace NRSubinv

open HACoeff
open FVSuppor
open
  FVSuppor.NRLayer
open CRLayer
open CRSubinv
open
  CRSubinv.NRLayer
open DSBridge
open UCSuppor

/-- Lexicographic primary key: larger erased Hall degree first, then shape
code. -/
abbrev ErasedPrimaryKey :=
  OrderDual ℕ ×ₗ List ℕ

/-- Primary More3 key of one erased Hall-pair word. -/
def erasedPrimaryKey
    (word : CWord HPAtom) :
    ErasedPrimaryKey :=
  toLex
    (word.weight (HPAtom.weight 1 1), pairShapeCode word)

/-- The erased-word primary key remembers the complete Hall-pair word. -/
lemma primary_key_injective :
    Function.Injective erasedPrimaryKey := by
  intro left right hkey
  apply pair_code_injective
  have hpair :
      (left.weight (HPAtom.weight 1 1), pairShapeCode left) =
        (right.weight (HPAtom.weight 1 1), pairShapeCode right) :=
    congrArg ofLex hkey
  exact congrArg Prod.snd hpair

/-- Nonstrict primary ordering on erased Hall-pair words. -/
def erasedShapeLE
    (left right : CWord HPAtom) :
    Prop :=
  erasedPrimaryKey left ≤ erasedPrimaryKey right

instance erasedShapeDecidable :
    DecidableRel erasedShapeLE := by
  intro left right
  unfold erasedShapeLE
  infer_instance

instance erasedShapeTotal :
    Std.Total erasedShapeLE := by
  change Std.Total (erasedPrimaryKey ⁻¹'o (· ≤ ·))
  infer_instance

instance erasedShapeTrans :
    IsTrans (CWord HPAtom) erasedShapeLE := by
  change
    IsTrans (CWord HPAtom)
      (erasedPrimaryKey ⁻¹'o (· ≤ ·))
  infer_instance

instance erasedShapeAntisymm :
    Std.Antisymm erasedShapeLE := by
  change Std.Antisymm (erasedPrimaryKey ⁻¹'o (· ≤ ·))
  exact Order.Preimage.antisymm primary_key_injective

/-- Strict primary precedence implies nonstrict primary ordering. -/
lemma erased_shape_before
    {left right : CWord HPAtom}
    (hbefore : erasedShapeBefore left right) :
    erasedShapeLE left right := by
  unfold erasedShapeLE erasedPrimaryKey
  apply le_of_lt
  rw [Prod.Lex.toLex_lt_toLex]
  exact hbefore

/-- Fixed finite support skeleton in primary More3 order. -/
noncomputable def orderedErasedVocabulary
    (n leftWeight rightWeight : ℕ) :
    List (CWord HPAtom) :=
  (erasedShapeVocabulary n leftWeight rightWeight).insertionSort erasedShapeLE

/-- Sorting preserves the finite correction-closure support set. -/
@[simp]
lemma ordered_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom} :
    word ∈ orderedErasedVocabulary n leftWeight rightWeight ↔
      word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  simp [orderedErasedVocabulary]

/-- Sorting preserves the vocabulary cardinality. -/
@[simp]
lemma length_shape_vocabulary
    (n leftWeight rightWeight : ℕ) :
    (orderedErasedVocabulary n leftWeight rightWeight).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  simp [orderedErasedVocabulary]

/-- The sorted finite vocabulary remains duplicate-free. -/
lemma nodup_erased_vocabulary
    (n leftWeight rightWeight : ℕ) :
    (orderedErasedVocabulary n leftWeight rightWeight).Nodup := by
  unfold orderedErasedVocabulary
  exact
    (List.perm_insertionSort erasedShapeLE
      (erasedShapeVocabulary n leftWeight rightWeight)).nodup_iff.mpr
        (List.nodup_dedup _)

/-- The fixed vocabulary is nondecreasing in the primary More3 key. -/
lemma pairwise_erased_vocabulary
    (n leftWeight rightWeight : ℕ) :
    (orderedErasedVocabulary n leftWeight rightWeight).Pairwise
      erasedShapeLE := by
  exact
    List.pairwise_insertionSort erasedShapeLE
      (erasedShapeVocabulary n leftWeight rightWeight)

namespace NRLayer

/-- Every compressed specialization word list is nondecreasing in the fixed
primary order. -/
lemma pairwise_erased_factors
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ((layer.factors M N).map NRFactor.word).Pairwise
      erasedShapeLE :=
  (pairwise_erased_before layer M N).imp
    erased_shape_before

/--
Every natural specialization word list is a literal ordered sublist of the
fixed sorted correction-closure vocabulary.
-/
lemma sublist_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List.Sublist
      ((layer.factors M N).map NRFactor.word)
      (orderedErasedVocabulary n leftWeight rightWeight) := by
  apply List.sublist_insertionSort'
  · exact pairwise_erased_factors layer M N
  · apply (nodup_word_factors layer M N).subperm
    intro word hword
    rcases List.mem_map.mp hword with ⟨factor, hfactor, rfl⟩
    exact
      erased_vocabulary_factors
        layer hleftWeight hrightWeight M N factor hfactor

end NRLayer

end NRSubinv
end TCTex
end Submission

/-!
# Fixed-slot coordinates for natural cutoff recollection

The cutoff-aware full collector produces an ordered specialization-dependent
sublist of one fixed finite erased-shape vocabulary.  This file fills absent
vocabulary slots with zero multiplicity and exposes the resulting fixed-length
natural multiplicity vector.

The fixed skeleton and its specialization-dependent coordinate vector still
evaluate to the powered commutator in every matching nilpotent target.  The
remaining interpolation problem is therefore scalar: represent each slot
multiplicity by an integer-valued polynomial.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace NRCoordi

open scoped commutatorElement

open CRLayer
open NRSubinv
open
  NRSubinv.NRLayer

/--
`FSAlign factors skeleton slots` says that `slots` is obtained from
`factors` by inserting zero-multiplicity factors in absent skeleton positions.
Retained factors are not reordered.
-/
inductive FSAlign :
    List NRFactor →
      List (CWord HPAtom) →
        List NRFactor →
          Prop
  | nil :
      FSAlign [] [] []
  | skip
      (word : CWord HPAtom)
      {factors skeleton slots}
      (alignment : FSAlign factors skeleton slots) :
      FSAlign factors (word :: skeleton)
        ({ word := word, multiplicity := 0 } :: slots)
  | keep
      (factor : NRFactor)
      {factors skeleton slots}
      (alignment : FSAlign factors skeleton slots) :
      FSAlign (factor :: factors) (factor.word :: skeleton)
        (factor :: slots)

namespace FSAlign

/-- An ordered sublist witness constructs aligned fixed slots. -/
lemma exists_of_sublist :
    ∀ {factors : List NRFactor}
      {skeleton : List (CWord HPAtom)},
      List.Sublist (factors.map NRFactor.word) skeleton →
        ∃ slots, FSAlign factors skeleton slots
  | [], [], .slnil =>
      ⟨[], .nil⟩
  | factors, _ :: skeleton, .cons _ alignment => by
      rcases exists_of_sublist alignment with ⟨slots, hslots⟩
      exact ⟨_ :: slots, .skip _ hslots⟩
  | _ :: factors, _ :: skeleton, .cons_cons _ alignment => by
      rcases exists_of_sublist alignment with ⟨slots, hslots⟩
      exact ⟨_ :: slots, .keep _ hslots⟩

/-- Every fixed skeleton position is represented by exactly one slot. -/
lemma map_word_eq :
    ∀ {factors skeleton slots},
      FSAlign factors skeleton slots →
        slots.map NRFactor.word = skeleton
  | _, _, _, .nil =>
      rfl
  | _, _, _, .skip _ alignment => by
      simp only [List.map_cons]
      rw [map_word_eq alignment]
  | _, _, _, .keep _ alignment => by
      simp only [List.map_cons]
      rw [map_word_eq alignment]

/-- Fixed-slot padding preserves the ordered group evaluation. -/
lemma map_at_eq :
    ∀ {factors skeleton slots}
      {G : Type*}
      [Group G]
      (x y : G)
      (_alignment : FSAlign factors skeleton slots),
        (slots.map fun factor => factor.evalAt x y).prod =
          (factors.map fun factor => factor.evalAt x y).prod := by
  intro factors skeleton slots G _ x y alignment
  induction alignment with
  | nil =>
      rfl
  | skip _ _alignment ih =>
      simp only [List.map_cons, List.prod_cons, NRFactor.evalAt,
        pow_zero, one_mul]
      exact ih
  | keep _ _alignment ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih]

end FSAlign

/-- Fixed-slot natural coordinates for one multiplicity specialization. -/
structure NSCoordi
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) where
  slots :
    List NRFactor
  alignment :
    FSAlign (layer.factors M N)
      (orderedErasedVocabulary n leftWeight rightWeight) slots

/-- Positive source weights construct fixed-slot coordinates at every natural
specialization. -/
noncomputable def fixedSlotCoordinates
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    NSCoordi layer M N := by
  let hsublist :=
    sublist_erased_vocabulary
      layer hleftWeight hrightWeight M N
  exact
    ⟨Classical.choose (FSAlign.exists_of_sublist hsublist),
      Classical.choose_spec (FSAlign.exists_of_sublist hsublist)⟩

namespace NSCoordi

/-- The padded words are independent of the natural specialization. -/
lemma slots_erased_vocabulary
    {n leftWeight rightWeight M N : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (coordinates : NSCoordi layer M N) :
    coordinates.slots.map NRFactor.word =
      orderedErasedVocabulary n leftWeight rightWeight :=
  coordinates.alignment.map_word_eq

/-- Every padded specialization has the fixed vocabulary length. -/
lemma length_slots_vocabulary
    {n leftWeight rightWeight M N : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (coordinates : NSCoordi layer M N) :
    coordinates.slots.length =
      (orderedErasedVocabulary n leftWeight rightWeight).length := by
  rw [← coordinates.slots_erased_vocabulary,
    List.length_map]

/-- Fixed-slot padding preserves the ordered group evaluation. -/
lemma eval_prod_factors
    {n leftWeight rightWeight M N : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (coordinates : NSCoordi layer M N)
    {G : Type*}
    [Group G]
    (x y : G) :
    (coordinates.slots.map fun factor => factor.evalAt x y).prod =
      ((layer.factors M N).map fun factor => factor.evalAt x y).prod :=
  coordinates.alignment.map_at_eq x y

/-- Fixed-slot padding still computes the powered commutator. -/
lemma prod_commutator_pow
    {n leftWeight rightWeight M N : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (coordinates : NSCoordi layer M N)
    {G : Type*}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (coordinates.slots.map fun factor => factor.evalAt x y).prod =
      ⁅x ^ M, y ^ N⁆ :=
  (coordinates.eval_prod_factors x y).trans
    (layer.factors_commutator_pow
      M N x y hleftWeight hrightWeight hx hy hbot)

end NSCoordi

/-- The specialization-dependent natural multiplicity vector on the fixed
ordered erased-shape vocabulary. -/
noncomputable def naturalSlotVector
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List ℕ :=
  (fixedSlotCoordinates layer hleftWeight hrightWeight M N).slots.map
    NRFactor.multiplicity

/-- Every specialization-dependent multiplicity vector has fixed length. -/
lemma slot_multiplicity_vector
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (naturalSlotVector layer hleftWeight hrightWeight M N).length =
      (orderedErasedVocabulary n leftWeight rightWeight).length := by
  rw [naturalSlotVector, List.length_map]
  exact
    (fixedSlotCoordinates layer hleftWeight hrightWeight M N)
      |>.length_slots_vocabulary

/-- Zipping the fixed words with the fixed-slot multiplicities recovers the
evaluation of the padded slot list. -/
lemma zip_word_multiplicity
    {G : Type*}
    [Group G]
    (x y : G)
    (slots : List NRFactor) :
    (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (slots.map NRFactor.word)
        (slots.map NRFactor.multiplicity)).prod =
      (slots.map fun factor => factor.evalAt x y).prod := by
  induction slots with
  | nil =>
      rfl
  | cons factor slots ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.prod_cons]
      rw [ih]
      rfl

/--
The fixed erased-shape skeleton paired with its natural coordinate vector
computes the powered commutator in every matching nilpotent target.
-/
lemma zip_slot_vector
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (orderedErasedVocabulary n leftWeight rightWeight)
        (naturalSlotVector
          layer hleftWeight hrightWeight M N)).prod =
      ⁅x ^ M, y ^ N⁆ := by
  let coordinates :=
    fixedSlotCoordinates layer hleftWeight hrightWeight M N
  rw [naturalSlotVector]
  change
    (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (orderedErasedVocabulary n leftWeight rightWeight)
        (coordinates.slots.map NRFactor.multiplicity)).prod =
      ⁅x ^ M, y ^ N⁆
  rw [← coordinates.slots_erased_vocabulary,
    zip_word_multiplicity]
  exact coordinates.prod_commutator_pow
    x y hleftWeight hrightWeight hx hy hbot

end NRCoordi
end TCTex
end Submission

/-!
# Signed-profile interpolation boundary for cutoff-full collection

The cutoff-aware collector now produces a fixed erased-word skeleton and a
specialization-dependent natural multiplicity vector on that skeleton.  This
file isolates the remaining scalar interpolation theorem: attach one
homogeneous signed-profile packet to every fixed slot and prove that its value
at natural source exponents is the corresponding padded multiplicity.

Such scalar interpolation data automa supplies the existing fixed-packet
stabilization record and, at root weights, the natural signed-block packet used
by subsequent all-integral lifting.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace FSInterp

open scoped commutatorElement

open CFStab
open CRLayer
open
  NRCoordi
open NRSubinv
open
  CFSubsti
open UNPkt
open SCFactor

/--
A fixed signed-profile packet list interpolates the padded natural coordinate
vector produced by cutoff-full collection.
-/
structure NSInterp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (packets : List RFPkt) :
    Prop where
  map_word_packets :
    packets.map RFPkt.word =
      orderedErasedVocabulary n leftWeight rightWeight
  map_nat_cast :
    ∀ M N : ℕ,
      packets.map (fun packet =>
        packet.profiles.value (M : ℤ) (N : ℤ)) =
          (naturalSlotVector
            layer hleftWeight hrightWeight M N).map fun
              (multiplicity : ℕ) =>
              (multiplicity : ℤ)

/-- Packet evaluation is the zip of packet words and packet exponents. -/
lemma zpow_zip_value
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ)
    (packets : List RFPkt) :
    (packets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent).prod =
      (List.zipWith
        (fun word exponent =>
          word.eval (HPAtom.eval left right) ^ exponent)
        (packets.map RFPkt.word)
        (packets.map fun packet =>
          packet.profiles.value leftExponent rightExponent)).prod := by
  induction packets with
  | nil =>
      rfl
  | cons packet packets ih =>
      simp only [List.map_cons, List.prod_cons, List.zipWith_cons_cons]
      rw [ih]

/-- Casting a natural multiplicity vector converts integer powers to natural
powers slot by slot. -/
lemma zip_zpow_cast
    {G : Type*}
    [Group G] :
    ∀ (words : List (CWord HPAtom))
      (multiplicities : List ℕ)
      (left right : G),
      List.zipWith
          (fun word (exponent : ℤ) =>
            word.eval (HPAtom.eval left right) ^ exponent)
          words (multiplicities.map fun (multiplicity : ℕ) =>
            (multiplicity : ℤ)) =
        List.zipWith
          (fun word (multiplicity : ℕ) =>
            word.eval (HPAtom.eval left right) ^ multiplicity)
          words multiplicities
  | [], _, _, _ =>
      rfl
  | _ :: _, [], _, _ =>
      rfl
  | word :: words, multiplicity :: multiplicities, left, right => by
      simp only [List.map_cons, List.zipWith_cons_cons, zpow_natCast]
      rw [zip_zpow_cast words multiplicities
        left right]

namespace NSInterp

/--
Interpolated fixed-slot packets compute the powered commutator at every
natural source multiplicity.
-/
lemma packet_cast_pow
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer hleftWeight hrightWeight packets)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G)
    (hleft :
      left ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hright :
      right ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (packets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [zpow_zip_value,
    interpolation.map_word_packets,
    interpolation.map_nat_cast,
    zip_zpow_cast]
  exact
    zip_slot_vector
      layer hleftWeight hrightWeight M N left right hleft hright hbot

/--
Scalar fixed-slot interpolation supplies the existing natural shape-run packet
stabilization boundary.
-/
def runPacketStabilization
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer hleftWeight hrightWeight packets)
    (d : ℕ) :
    NRStab
      layer d packets where
  leftWeight_pos :=
    hleftWeight
  rightWeight_pos :=
    hrightWeight
  packet_prod_factors M N left right hleft hright :=
    (interpolation.packet_cast_pow
      M N left right hleft hright
        trunc_last_bot).trans
      (layer.factors_commutator_pow
        M N left right hleftWeight hrightWeight hleft hright
          trunc_last_bot).symm

/--
At root weights, scalar fixed-slot interpolation supplies the natural
signed-block packet consumed by all-integral lifting.
-/
def truncNaturalPacket
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer (by simp) (by simp) packets) :
    TBPkt d n :=
  interpolation.runPacketStabilization d
    |>.truncNaturalPacket

@[simp]
lemma packetsTruncNatural
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer (by simp) (by simp) packets) :
    (interpolation.truncNaturalPacket (d := d)).packets =
      packets :=
  rfl

end NSInterp

end FSInterp
end TCTex
end Submission

/-!
# Fixed-slot coordinates as compressed-run multiplicities

The cutoff-full collector pads its specialization-dependent compressed run list
to one fixed ordered vocabulary.  This file identifies each padded coordinate
with the corresponding word-local sum of compressed-run multiplicities.

Because compressed run words are duplicate-free, that sum is either the unique
retained run multiplicity or zero.  This is the first scalar counting form of
the fixed-slot interpolation problem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace RMCoordi

open CRLayer
open CRSubinv
open
  NRCoordi
open NRSubinv

/-- Sum the multiplicities of compressed runs with one erased Hall shape. -/
def naturalRunMultiplicity
    (factors : List NRFactor)
    (word : CWord HPAtom) :
    ℕ :=
  ((factors.filter fun factor => decide (factor.word = word)).map
    NRFactor.multiplicity).sum

@[simp]
lemma natural_run_nil
    (word : CWord HPAtom) :
    naturalRunMultiplicity [] word = 0 :=
  rfl

/-- A word absent from the compressed run inventory has multiplicity zero. -/
lemma natural_run_not
    {factors : List NRFactor}
    {word : CWord HPAtom}
    (hnotmem :
      word ∉ factors.map NRFactor.word) :
    naturalRunMultiplicity factors word = 0 := by
  unfold naturalRunMultiplicity
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro factor hfactor hword
    apply hnotmem
    exact List.mem_map.mpr ⟨factor, hfactor, of_decide_eq_true hword⟩

/-- Adding a run with a different word does not change one word-local sum. -/
lemma natural_run_cons
    {factors : List NRFactor}
    {factor : NRFactor}
    {word : CWord HPAtom}
    (hne : factor.word ≠ word) :
    naturalRunMultiplicity (factor :: factors) word =
      naturalRunMultiplicity factors word := by
  simp [naturalRunMultiplicity, hne]

/-- A duplicate-free leading run is the complete contribution to its word. -/
lemma run_cons_self
    {factors : List NRFactor}
    (factor : NRFactor)
    (hnotmem :
      factor.word ∉ factors.map NRFactor.word) :
    naturalRunMultiplicity (factor :: factors) factor.word =
      factor.multiplicity := by
  rw [naturalRunMultiplicity]
  simp only [List.filter_cons, decide_true, if_true, List.map_cons,
    List.sum_cons]
  change
    factor.multiplicity + naturalRunMultiplicity factors factor.word =
      factor.multiplicity
  rw [natural_run_not hnotmem, Nat.add_zero]

namespace FSAlign

/-- The retained compressed-run words form an ordered sublist of the skeleton
used by any fixed-slot alignment. -/
lemma word_factors_sublist :
    ∀ {factors : List NRFactor}
      {skeleton : List (CWord HPAtom)}
      {slots : List NRFactor},
      FSAlign factors skeleton slots →
        List.Sublist (factors.map NRFactor.word) skeleton
  | _, _, _, .nil =>
      .slnil
  | _, _, _, .skip _ alignment =>
      .cons _ (word_factors_sublist alignment)
  | _, _, _, .keep _ alignment =>
      .cons_cons _ (word_factors_sublist alignment)

/--
Padding a duplicate-free skeleton computes the compressed-run multiplicity
function slot by slot.
-/
lemma multiplicity_natural_run :
    ∀ {factors : List NRFactor}
      {skeleton : List (CWord HPAtom)}
      {slots : List NRFactor}
      (_alignment : FSAlign factors skeleton slots),
      skeleton.Nodup →
        slots.map NRFactor.multiplicity =
          skeleton.map (naturalRunMultiplicity factors)
  | _, _, _, .nil, _ =>
      rfl
  | factors, _ :: skeleton, _, .skip skipped alignment, hnodup => by
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons]
      rw [multiplicity_natural_run alignment hnodup.2]
      have hnotmem :
          skipped ∉ factors.map NRFactor.word := by
        intro hword
        exact hnodup.1
          ((word_factors_sublist alignment).subset hword)
      rw [natural_run_not hnotmem]
  | _ :: factors, _, _, .keep retained alignment, hnodup => by
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons]
      have hnotmem :
          retained.word ∉ factors.map NRFactor.word := by
        intro hword
        exact hnodup.1
          ((word_factors_sublist alignment).subset hword)
      rw [run_cons_self retained hnotmem,
        multiplicity_natural_run alignment hnodup.2]
      congr 1
      apply List.map_congr_left
      intro word hword
      symm
      apply natural_run_cons
      intro heq
      apply hnodup.1
      rwa [heq]

end FSAlign

/--
The padded cutoff-full coordinate vector is the fixed vocabulary mapped through
the compressed-run multiplicity function.
-/
lemma natural_slot_run
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    naturalSlotVector layer hleftWeight hrightWeight M N =
      (orderedErasedVocabulary n leftWeight rightWeight).map
        (naturalRunMultiplicity (layer.factors M N)) := by
  rw [naturalSlotVector]
  exact
    FSAlign.multiplicity_natural_run
      (fixedSlotCoordinates layer hleftWeight hrightWeight M N).alignment
      (nodup_erased_vocabulary n leftWeight rightWeight)

end RMCoordi
end TCTex
end Submission

/-!
# Local homogeneous profiles for retained raw shape fibers

The retained inverse-raw packet has an exact multiplicity-preserving family
inventory.  Filtering that inventory by one erased Hall shape produces a
finite list of complete source families.  Summing their recipe coefficients
therefore gives a homogeneous signed-block formula packet whose value at the
chosen natural multiplicities is exactly the corresponding raw shape-fiber
cardinality.

The recipe list in this local packet still depends on the natural
specialization.  A later stabilization theorem must replace it by a fixed
multiplicity-independent raw transversal.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  RFLocal

open HACoeff
open BRSpec
open FIFilter
open IMPropag
open ISEnd
open
  CFSubsti
open RRTrunc
open
  ACAlign

/-- Complete retained inverse-raw family inventory restricted to one shape. -/
noncomputable def retainedRawInventory
    (M N n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    MIBlock
      ((retainedRawTerms M N n leftWeight rightWeight).filter fun term =>
        term.family.recipe.erasedShape = word) :=
  FIFilter.MIBlock.filterShape
    (multiplicityInventoryBlock M N n leftWeight rightWeight)
    word

/-- Recipe list of the complete retained inverse-raw families of one shape. -/
noncomputable def rawShapeRecipes
    (M N n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    List BRecipe :=
  (retainedRawInventory M N n leftWeight rightWeight word).families.map
    BFam.recipe

/-- Every recipe selected from the raw shape inventory has the chosen shape. -/
lemma erased_raw_recipes
    {M N n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ rawShapeRecipes M N n leftWeight rightWeight word) :
    recipe.erasedShape = word := by
  rcases List.mem_map.mp hrecipe with ⟨family, hfamily, rfl⟩
  exact
    MIBlock.filter_shape_families
      (multiplicityInventoryBlock M N n leftWeight rightWeight)
      word family (by simpa [retainedRawInventory] using hfamily)

/-- The recipe coefficient sum of a concrete family list counts its slots. -/
lemma cast_realization_length
    {M N : ℕ} :
    ∀ families : List (BFam M N),
      (families.map fun family =>
        coefficientValue family.recipe (M : ℤ) (N : ℤ)).sum =
          ((BFam.realizationList families).length : ℤ)
  | [] => by
      rfl
  | family :: families => by
      rw [List.map_cons, List.sum_cons,
        BFam.coeffvalue_natcast_eqlength,
        BFam.realizationList_cons, List.length_append, Int.natCast_add,
        cast_realization_length families]

/--
The retained raw shape-family recipe sum counts the corresponding concrete
raw shape fiber.
-/
lemma recipes_filter_length
    (M N n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    ((rawShapeRecipes M N n leftWeight rightWeight word).map
      fun recipe => coefficientValue recipe (M : ℤ) (N : ℤ)).sum =
        (((retainedRawTerms M N n leftWeight rightWeight).filter fun term =>
          term.family.recipe.erasedShape = word).length : ℤ) := by
  rw [rawShapeRecipes, List.map_map]
  change
    (((retainedRawInventory
      M N n leftWeight rightWeight word).families.map fun family =>
        coefficientValue family.recipe (M : ℤ) (N : ℤ)).sum) =
      _
  rw [cast_realization_length]
  exact_mod_cast
    RIFor.realization_list_lengtheq
      (retainedRawInventory M N n leftWeight rightWeight word).inventory

/--
At one natural specialization, the retained raw shape fiber has a homogeneous
recipe-chunk profile.
-/
noncomputable def retainedFiberProfile
    (M N n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  HFPkt.ofRecipeChunk word
    (rawShapeRecipes M N n leftWeight rightWeight word)
    fun _recipe hrecipe =>
      erased_raw_recipes hrecipe

/--
The local homogeneous raw profile specializes to the exact retained raw
shape-fiber cardinality.
-/
lemma fiber_filter_length
    (M N n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    (retainedFiberProfile
      M N n leftWeight rightWeight word).value (M : ℤ) (N : ℤ) =
        (((retainedRawTerms M N n leftWeight rightWeight).filter fun term =>
          decide (term.family.recipe.erasedShape = word)).length : ℤ) := by
  rw [retainedFiberProfile,
    HFPkt.value_recipe_chunk,
    recipes_filter_length]

end
  RFLocal
end TCTex
end Submission

/-!
# Fixed-slot coordinates as endpoint erased-shape fiber lengths

The cutoff-full collector first compresses maximal adjacent erased-shape runs
and then pads the resulting ordered factor list to a fixed vocabulary.  This
file identifies the scalar coordinate of every vocabulary word with the length
of its complete retained endpoint fiber.

This is the concrete cardinality interface needed by symbolic recollection
formula compilers: ordering and zero padding no longer appear in the remaining
scalar problem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace FFCoordi

open HACoeff
open CRLayer
open CRSubinv
open
  CRSubinv.NRLayer
open
  RMCoordi
open
  NRCoordi
open NRSubinv

/-- The first erased shape of a nonempty same-shape block is the erased shape
of each of its terms. -/
lemma first_same_block
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    (hsame : SameErasedBlock block)
    {term : DFTerm M N K}
    (hterm : term ∈ block) :
    firstErasedShape block = term.erasedShape := by
  rcases hsame with ⟨shape, hshape⟩
  cases block with
  | nil =>
      simp at hterm
  | cons head tail =>
      change head.erasedShape = term.erasedShape
      exact
        (hshape head (by simp)).trans
          (hshape term hterm).symm

/-- In a duplicate-free compressed run list, a retained factor contributes
exactly its own multiplicity to its word-local sum. -/
lemma natural_run_nodup :
    ∀ {factors : List NRFactor}
      (factor : NRFactor),
      factor ∈ factors →
        (factors.map NRFactor.word).Nodup →
          naturalRunMultiplicity factors factor.word =
            factor.multiplicity
  | [], factor, hfactor, _ => by
      simp at hfactor
  | head :: factors, factor, hfactor, hnodup => by
      simp only [List.map_cons] at hnodup
      rw [List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hfactor with rfl | hfactor
      · exact run_cons_self factor hnodup.1
      · rw [natural_run_cons]
        · exact
            natural_run_nodup
              factor hfactor hnodup.2
        · intro heq
          apply hnodup.1
          exact List.mem_map.mpr ⟨factor, hfactor, heq.symm⟩

namespace NRLayer

/-- If a word has no compressed endpoint run, its retained endpoint
recipe-shape fiber is empty. -/
lemma endpoint_filter_nil
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom)
    (hnotmem :
      word ∉ (layer.factors M N).map NRFactor.word) :
    (layer.endpoint M N).factors.filter
        (fun term => term.family.recipe.erasedShape = word) =
      [] := by
  apply List.filter_eq_nil_iff.mpr
  intro term hterm htermWord
  apply hnotmem
  rw [
    CRLayer.NRLayer.factors,
    naturalRunFactors, naturalShapeFactors]
  have htermFlatten :
      term ∈ (sameErasedBlocks (layer.endpoint M N).factors).flatten := by
    rwa [flatten_same_blocks]
  rcases List.mem_flatten.mp htermFlatten with
    ⟨block, hblock, htermBlock⟩
  apply List.mem_map.mpr
  refine ⟨naturalRunFactor block, List.mem_map.mpr ⟨block, hblock, rfl⟩, ?_⟩
  change firstErasedShape block = word
  rw [first_same_block
      (same_erased_blocks
        (layer.endpoint M N).factors block hblock) htermBlock,
    DFTerm.erased_shape_family]
  exact of_decide_eq_true htermWord

/-- The complete endpoint recipe-shape fiber of a retained compressed run has
length equal to that run's multiplicity. -/
lemma endpoint_filter_factor
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (factor : NRFactor)
    (hfactor : factor ∈ layer.factors M N) :
    ((layer.endpoint M N).factors.filter
      (fun term => term.family.recipe.erasedShape = factor.word)).length =
        factor.multiplicity := by
  rw [
    CRLayer.NRLayer.factors,
    naturalRunFactors, naturalShapeFactors] at hfactor
  rcases List.mem_map.mp hfactor with ⟨block, hblock, rfl⟩
  rcases layer.endpoint_filter_eq M N block hblock with ⟨shape, hfilter⟩
  have hblockNe : block ≠ [] := by
    apply List.ne_nil_of_mem_splitBy
      (show
        block ∈ (layer.endpoint M N).factors.splitBy
          fun left right => decide (left.erasedShape = right.erasedShape) by
        simpa [sameErasedBlocks] using hblock)
  let term := block.head hblockNe
  have htermBlock : term ∈ block :=
    List.head_mem hblockNe
  have htermFilter :
      term ∈ (layer.endpoint M N).factors.filter
        (fun next => next.family.recipe.erasedShape = shape) := by
    rw [hfilter]
    exact htermBlock
  have hshape :
      shape = firstErasedShape block := by
    calc
      shape = term.family.recipe.erasedShape :=
        (of_decide_eq_true (List.mem_filter.mp htermFilter).2).symm
      _ = term.erasedShape :=
        term.erased_shape_family.symm
      _ = firstErasedShape block :=
        (first_same_block
          (same_erased_blocks
            (layer.endpoint M N).factors block hblock) htermBlock).symm
  change
    ((layer.endpoint M N).factors.filter
      (fun next => next.family.recipe.erasedShape =
        firstErasedShape block)).length =
      block.length
  rw [← hshape, hfilter]

/-- Every compressed-run scalar coordinate is exactly the cardinality of its
retained endpoint erased-shape fiber. -/
lemma natural_run_length
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    naturalRunMultiplicity (layer.factors M N) word =
      ((layer.endpoint M N).factors.filter
        (fun term => term.family.recipe.erasedShape = word)).length := by
  by_cases hword :
      word ∈ (layer.factors M N).map NRFactor.word
  · rcases List.mem_map.mp hword with ⟨factor, hfactor, rfl⟩
    rw [natural_run_nodup
      factor hfactor (nodup_word_factors layer M N)]
    exact (endpoint_filter_factor layer
      M N factor hfactor).symm
  · rw [natural_run_not hword,
      endpoint_filter_nil layer M N word hword]
    rfl

end NRLayer

/--
The padded cutoff-full coordinate vector is the fixed vocabulary mapped
through retained endpoint erased-shape fiber cardinality.
-/
lemma natural_filter_length
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    naturalSlotVector layer hleftWeight hrightWeight M N =
      (orderedErasedVocabulary n leftWeight rightWeight).map fun word =>
        ((layer.endpoint M N).factors.filter
          (fun term => term.family.recipe.erasedShape = word)).length := by
  rw [natural_slot_run]
  apply List.map_congr_left
  intro word _hword
  exact
    NRLayer.natural_run_length
      layer M N word

end FFCoordi
end TCTex
end Submission

/-!
# Fixed-slot coordinates as endpoint shape-fiber cardinalities

Compressed-run multiplicities are lengths of maximal equal-shape blocks.  Since
those blocks partition the cutoff-full endpoint, summing the retained run
multiplicities for one erased Hall word is the cardinality of the corresponding
endpoint shape fiber.

This file rewrites every padded fixed-slot coordinate in that form.  The
remaining profile interpolation theorem is therefore a symbolic counting
theorem for concrete endpoint recipe-shape filters.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace FFCard

open HACoeff
open CRLayer
open CRSubinv
open
  RMCoordi
open
  NRCoordi
open NRSubinv
open OCPartit

/-- Number of retained endpoint terms with one erased Hall shape. -/
def endpointErasedMultiplicity
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    ℕ :=
  ((layer.endpoint M N).factors.filter fun term =>
    decide (term.erasedShape = word)).length

/-- The same endpoint shape-fiber cardinality, expressed using recipe shapes. -/
def endpointRecipeMultiplicity
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    ℕ :=
  ((layer.endpoint M N).factors.filter fun term =>
    decide (term.family.recipe.erasedShape = word)).length

/-- Every term of a nonempty same-shape block has the block's first shape. -/
lemma erased_shape_first
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    (hne : block ≠ [])
    (hsame : SameErasedBlock block) :
    ∀ term ∈ block, term.erasedShape = firstErasedShape block := by
  rcases hsame with ⟨shape, hshape⟩
  cases block with
  | nil =>
      exact False.elim (hne rfl)
  | cons head tail =>
      intro term hterm
      simpa only [firstErasedShape] using
        (hshape term hterm).trans (hshape head (by simp)).symm

/-- Filtering one nonempty same-shape block either retains the whole block or
removes it. -/
lemma length_filter_ite
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (hne : block ≠ [])
    (hsame : SameErasedBlock block)
    (word : CWord HPAtom) :
    (block.filter fun term => decide (term.erasedShape = word)).length =
      if firstErasedShape block = word then block.length else 0 := by
  by_cases hword : firstErasedShape block = word
  · rw [if_pos hword]
    apply congrArg List.length
    apply List.filter_eq_self.mpr
    intro term hterm
    simpa only [decide_eq_true_eq] using
      (erased_shape_first hne hsame term hterm).trans hword
  · rw [if_neg hword]
    have hfilter :
        block.filter (fun term => decide (term.erasedShape = word)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro term hterm htermWord
      apply hword
      exact
        (erased_shape_first hne hsame term hterm).symm.trans
          (of_decide_eq_true htermWord)
    rw [hfilter]
    rfl

/--
For a partition into nonempty same-shape blocks, endpoint filtering is the sum
of the corresponding compressed-run multiplicities.
-/
lemma filter_flatten_run :
    ∀ {M N K : ℕ}
      (blocks : List (List (DFTerm M N K)))
      (_hnonempty : ∀ block ∈ blocks, block ≠ [])
      (_hsame : ∀ block ∈ blocks, SameErasedBlock block)
      (word : CWord HPAtom),
      (blocks.flatten.filter fun term =>
        decide (term.erasedShape = word)).length =
          naturalRunMultiplicity (naturalShapeFactors blocks) word
  | _, _, _, [], _, _, word => by
      simp [naturalShapeFactors, naturalRunMultiplicity]
  | _, _, _, block :: blocks, hnonempty, hsame, word => by
      rw [List.flatten_cons, List.filter_append, List.length_append,
        length_filter_ite block
          (hnonempty block (by simp)) (hsame block (by simp)) word,
        filter_flatten_run
          blocks
          (fun next hnext => hnonempty next (by simp [hnext]))
          (fun next hnext => hsame next (by simp [hnext])) word]
      by_cases hword : firstErasedShape block = word
      · simp [naturalShapeFactors, naturalRunFactor,
          naturalRunMultiplicity, hword]
      · simp [naturalShapeFactors, naturalRunFactor,
          naturalRunMultiplicity, hword]

/-- Shape-fiber cardinality of any term list equals the corresponding sum over
its compressed runs. -/
lemma length_filter_run
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (word : CWord HPAtom) :
    (terms.filter fun term => decide (term.erasedShape = word)).length =
      naturalRunMultiplicity (naturalRunFactors terms) word := by
  change
    (terms.filter fun term => decide (term.erasedShape = word)).length =
      naturalRunMultiplicity
        (naturalShapeFactors (sameErasedBlocks terms)) word
  calc
    (terms.filter fun term => decide (term.erasedShape = word)).length =
        ((sameErasedBlocks terms).flatten.filter fun term =>
          decide (term.erasedShape = word)).length := by
      rw [flatten_same_blocks]
    _ =
        naturalRunMultiplicity
          (naturalShapeFactors (sameErasedBlocks terms)) word := by
      exact
        filter_flatten_run
          (sameErasedBlocks terms)
          (fun block hblock => by
            apply List.ne_nil_of_mem_splitBy
            simpa [sameErasedBlocks] using hblock)
          (same_erased_blocks terms)
          word

/-- Endpoint erased-shape fibers compute the compressed-run multiplicity
function. -/
lemma endpoint_natural_run
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    endpointErasedMultiplicity layer M N word =
      naturalRunMultiplicity (layer.factors M N) word := by
  exact
    length_filter_run
      (layer.endpoint M N).factors word

/-- Recipe shape and erased decorated shape define the same endpoint fiber. -/
lemma endpoint_multiplicity_erased
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    endpointRecipeMultiplicity layer M N word =
      endpointErasedMultiplicity layer M N word := by
  simp [endpointRecipeMultiplicity, endpointErasedMultiplicity,
    DFTerm.erased_shape_family]

/-- Recipe-shape fibers compute the compressed-run multiplicity function. -/
lemma endpoint_multiplicity_run
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    endpointRecipeMultiplicity layer M N word =
      naturalRunMultiplicity (layer.factors M N) word :=
  (endpoint_multiplicity_erased
    layer M N word).trans
      (endpoint_natural_run
        layer M N word)

/--
The padded cutoff-full coordinate vector is the fixed vocabulary mapped through
endpoint recipe-shape fiber cardinalities.
-/
lemma natural_slot_shape
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    naturalSlotVector layer hleftWeight hrightWeight M N =
      (orderedErasedVocabulary n leftWeight rightWeight).map
        (endpointRecipeMultiplicity layer M N) := by
  rw [natural_slot_run]
  apply List.map_congr_left
  intro word _hword
  exact
    (endpoint_multiplicity_run
      layer M N word).symm

end FFCard
end TCTex
end Submission

/-!
# Endpoint shape-fiber profile interpolation boundary

The padded cutoff-full coordinate vector is now identified with the fixed
vocabulary of endpoint recipe-shape fiber cardinalities.  This file restates
the remaining scalar theorem in that concrete counting form and proves it
equivalent to fixed-slot signed-profile interpolation.

A future symbolic counting argument can work directly with endpoint filters:
for every retained vocabulary word, construct one homogeneous signed-profile
packet whose natural values count that recipe-shape fiber.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  FPInterp

open
  FSInterp
open CFStab
open
  FFCard
open CRLayer
open NRSubinv
open
  CFSubsti

/--
A fixed signed-profile packet list interpolates the concrete endpoint
recipe-shape fiber cardinalities on the ordered finite vocabulary.
-/
structure EFInterp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (packets : List RFPkt) :
    Prop where
  map_word_packets :
    packets.map RFPkt.word =
      orderedErasedVocabulary n leftWeight rightWeight
  map_nat_cast :
    ∀ M N : ℕ,
      packets.map (fun packet =>
        packet.profiles.value (M : ℤ) (N : ℤ)) =
          (orderedErasedVocabulary n leftWeight rightWeight).map fun word =>
            (endpointRecipeMultiplicity layer M N word : ℤ)

namespace EFInterp

/--
Endpoint shape-fiber interpolation supplies padded fixed-slot interpolation.
-/
def naturalFixedInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    NSInterp
      layer hleftWeight hrightWeight packets where
  map_word_packets :=
    interpolation.map_word_packets
  map_nat_cast M N := by
    rw [
      natural_slot_shape]
    simpa only [List.map_map, Function.comp_apply] using
      interpolation.map_nat_cast M N

/--
Padded fixed-slot interpolation recovers endpoint shape-fiber interpolation.
-/
def naturalSlotInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer hleftWeight hrightWeight packets) :
    EFInterp layer packets where
  map_word_packets :=
    interpolation.map_word_packets
  map_nat_cast M N := by
    rw [interpolation.map_nat_cast,
      natural_slot_shape]
    simp only [List.map_map, Function.comp_def]

/--
Endpoint shape-fiber interpolation is equivalent to padded fixed-slot
interpolation.
-/
theorem natural_slot_interpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {packets : List RFPkt}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    EFInterp layer packets ↔
      NSInterp
        layer hleftWeight hrightWeight packets :=
  ⟨fun interpolation =>
      interpolation.naturalFixedInterpolation
        hleftWeight hrightWeight,
    naturalSlotInterpolation⟩

/--
Endpoint shape-fiber interpolation supplies the existing natural shape-run
stabilization record.
-/
def runPacketStabilization
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (d : ℕ) :
    NRStab layer d packets :=
  (interpolation.naturalFixedInterpolation
    hleftWeight hrightWeight)
      |>.runPacketStabilization d

end EFInterp

end
  FPInterp
end TCTex
end Submission

/-!
# Retained-correction inventories for cutoff-full collection

The cutoff-full collector retains a generated correction precisely when its
weighted Hall degree is below the quotient cutoff.  This file records those
retained corrections in a companion traced relation.  Filtered endpoint
cardinalities are then the filtered cardinalities of the initially retained
raw packet plus the filtered cardinalities of this correction trace.

This is an arbitrary-cutoff recurrence for actual collector endpoints.  It
does not replace the cutoff scheduler by a larger formal correction closure.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace CRInv

open HACoeff
open CFCollec.DFTerm
open
  FFCard
open CRLayer
open OCPartit
open RRTrunc

namespace DFTerm

/--
Cutoff insertion together with the finite list of corrections introduced and
retained by its actual recursive schedule.
-/
inductive CICorrec
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    List (DFTerm M N K) →
      DFTerm M N K →
        List (DFTerm M N K) →
          List (DFTerm M N K) →
            Prop where
  | nil
      (A : DFTerm M N K) :
      CICorrec
        n leftWeight rightWeight [] A [A] []
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hBA : B.decorated.collectorLe A.decorated) :
      CICorrec
        n leftWeight rightWeight (P ++ [B]) A (P ++ [B, A]) []
  | retained
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.collectorBefore B.decorated)
      (hweight :
        decoratedFamilyWeight leftWeight rightWeight (B.correction A) < n)
      {Q R : List (DFTerm M N K)}
      {leftCorrections rightCorrections :
        List (DFTerm M N K)}
      (hcorrection :
        CICorrec
          n leftWeight rightWeight P (B.correction A) Q leftCorrections)
      (hinsert :
        CICorrec
          n leftWeight rightWeight Q A R rightCorrections) :
      CICorrec
        n leftWeight rightWeight (P ++ [B]) A (R ++ [B])
          (leftCorrections ++ [B.correction A] ++ rightCorrections)
  | residual
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.collectorBefore B.decorated)
      (hweight :
        n ≤ decoratedFamilyWeight leftWeight rightWeight (B.correction A))
      {R corrections : List (DFTerm M N K)}
      (hinsert :
        CICorrec
          n leftWeight rightWeight P A R corrections) :
      CICorrec
        n leftWeight rightWeight (P ++ [B]) A (R ++ [B]) corrections

/-- Forgetting the correction trace recovers cutoff insertion. -/
lemma CICorrec.cutoffInserts
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    CInsert n leftWeight rightWeight L A R := by
  induction hinsert with
  | nil A =>
      exact .nil A
  | append P B A hBA =>
      exact .append P B A hBA
  | retained P B A hAB hweight _hcorrection _hinsert
      ihcorrection ihinsert =>
      exact .retained P B A hAB hweight ihcorrection ihinsert
  | residual P B A hAB hweight _hinsert ihinsert =>
      exact .residual P B A hAB hweight ihinsert

/-- Every cutoff-insertion schedule admits a finite retained-correction trace. -/
lemma cutoff_inserts_retained
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R) :
    ∃ corrections,
      CICorrec
        n leftWeight rightWeight L A R corrections := by
  induction hinsert with
  | nil A =>
      exact ⟨[], .nil A⟩
  | append P B A hBA =>
      exact ⟨[], .append P B A hBA⟩
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      rcases ihcorrection with ⟨leftCorrections, hleftCorrections⟩
      rcases ihinsert with ⟨rightCorrections, hrightCorrections⟩
      exact
        ⟨leftCorrections ++ [B.correction A] ++ rightCorrections,
          .retained P B A hAB hweight hleftCorrections hrightCorrections⟩
  | residual P B A hAB hweight hinsert ihinsert =>
      rcases ihinsert with ⟨corrections, hcorrections⟩
      exact ⟨corrections, .residual P B A hAB hweight hcorrections⟩

/--
Every filtered occurrence count after traced cutoff insertion is the input
count, plus the inserted term, plus all retained generated corrections.
-/
lemma length_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    (predicate : DFTerm M N K → Bool)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    (R.filter predicate).length =
      (L.filter predicate).length +
        ([A].filter predicate).length +
          (corrections.filter predicate).length := by
  induction hinsert with
  | nil A =>
      simp
  | append P B A _hBA =>
      rw [show [B, A] = [B] ++ [A] by rfl]
      simp only [List.filter_append, List.length_append, List.filter_nil,
        List.length_nil, add_zero]
      omega
  | retained P B A _hAB _hweight hcorrection hinsert
      ihcorrection ihinsert =>
      simp only [List.filter_append, List.length_append]
      rw [ihinsert, ihcorrection]
      omega
  | residual P B A _hAB _hweight hinsert ihinsert =>
      simp only [List.filter_append, List.length_append]
      rw [ihinsert]
      omega

/-- Every generated correction recorded by traced insertion remains below cutoff. -/
lemma cutoff_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A term : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections)
    (hterm : term ∈ corrections) :
    decoratedFamilyWeight leftWeight rightWeight term < n := by
  induction hinsert with
  | nil A =>
      simp at hterm
  | append P B A _hBA =>
      simp at hterm
  | retained P B A _hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      simp only [List.mem_append, List.mem_singleton] at hterm
      rcases hterm with (hterm | hterm) | hterm
      · exact ihcorrection hterm
      · subst term
        exact hweight
      · exact ihinsert hterm
  | residual P B A _hAB _hweight hinsert ihinsert =>
      exact ihinsert hterm

/--
Cutoff collection together with all corrections introduced and retained by
its actual recursive insertion schedules.
-/
inductive CCCorrec
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    List (DFTerm M N K) →
      List (DFTerm M N K) →
        List (DFTerm M N K) →
          Prop where
  | nil :
      CCCorrec
        n leftWeight rightWeight [] [] []
  | retained
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hweight :
        decoratedFamilyWeight leftWeight rightWeight A < n)
      {C R collectCorrections insertCorrections :
        List (DFTerm M N K)}
      (hcollect :
        CCCorrec
          n leftWeight rightWeight P C collectCorrections)
      (hinsert :
        CICorrec
          n leftWeight rightWeight C A R insertCorrections) :
      CCCorrec
        n leftWeight rightWeight (P ++ [A]) R
          (collectCorrections ++ insertCorrections)
  | residual
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hweight :
        n ≤ decoratedFamilyWeight leftWeight rightWeight A)
      {C corrections : List (DFTerm M N K)}
      (hcollect :
        CCCorrec
          n leftWeight rightWeight P C corrections) :
      CCCorrec
        n leftWeight rightWeight (P ++ [A]) C corrections

/-- Forgetting the correction trace recovers cutoff collection. -/
lemma CCCorrec.cutoffCollects
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    CCollec n leftWeight rightWeight L R := by
  induction hcollect with
  | nil =>
      exact .nil
  | retained P A hweight _hcollect hinsert ihcollect =>
      exact .retained P A hweight ihcollect hinsert.cutoffInserts
  | residual P A hweight _hcollect ihcollect =>
      exact .residual P A hweight ihcollect

/-- Every cutoff-collection schedule admits a finite retained-correction trace. -/
lemma cutoff_collects_retained
    {M N K n leftWeight rightWeight : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : CCollec n leftWeight rightWeight L R) :
    ∃ corrections,
      CCCorrec
        n leftWeight rightWeight L R corrections := by
  induction hcollect with
  | nil =>
      exact ⟨[], .nil⟩
  | retained P A hweight hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨collectCorrections, hcollectCorrections⟩
      rcases cutoff_inserts_retained hinsert with
        ⟨insertCorrections, hinsertCorrections⟩
      exact
        ⟨collectCorrections ++ insertCorrections,
          .retained P A hweight hcollectCorrections hinsertCorrections⟩
  | residual P A hweight hcollect ihcollect =>
      rcases ihcollect with ⟨corrections, hcorrections⟩
      exact ⟨corrections, .residual P A hweight hcorrections⟩

/--
Every filtered endpoint count of traced collection is the corresponding
below-cutoff input count plus the count of retained generated corrections.
-/
lemma length_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    (predicate : DFTerm M N K → Bool)
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    (R.filter predicate).length =
      ((belowCutoffTerms n leftWeight rightWeight L).filter predicate).length +
        (corrections.filter predicate).length := by
  induction hcollect with
  | nil =>
      rfl
  | retained P A hweight hcollect hinsert ihcollect =>
      rw [length_inserts_corrections predicate hinsert,
        ihcollect]
      simp [belowCutoffTerms, List.filter_append, hweight]
      omega
  | residual P A hweight hcollect ihcollect =>
      rw [ihcollect]
      simp [belowCutoffTerms, List.filter_append, Nat.not_lt.mpr hweight]

/-- Every generated correction recorded by traced collection remains below cutoff. -/
lemma cutoff_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {term : DFTerm M N K}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections)
    (hterm : term ∈ corrections) :
    decoratedFamilyWeight leftWeight rightWeight term < n := by
  induction hcollect with
  | nil =>
      simp at hterm
  | retained P A _hweight hcollect hinsert ihcollect =>
      simp only [List.mem_append] at hterm
      rcases hterm with hterm | hterm
      · exact ihcollect hterm
      · exact
          cutoff_inserts_corrections hinsert hterm
  | residual P A _hweight hcollect ihcollect =>
      exact ihcollect hterm

end DFTerm

/--
One finite retained-correction inventory selected from the cutoff-full
endpoint schedule.
-/
structure EndpointCorrectionInventory
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) where
  corrections :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  family_collects_corrections :
    DFTerm.CCCorrec
      n leftWeight rightWeight
        (inverseDecoratedTerms M N)
          (layer.endpoint M N).factors corrections

/-- Every natural endpoint admits a finite retained-correction inventory. -/
noncomputable def endpointCorrectionInventory
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    EndpointCorrectionInventory layer M N :=
  let hexists :=
    DFTerm.cutoff_collects_retained
      (layer.endpoint M N).family_cutoff_collects
  {
    corrections := Classical.choose hexists
    family_collects_corrections :=
      Classical.choose_spec hexists
  }

/--
At every cutoff, a selected natural recollection endpoint consists exactly of
its initially retained inverse-raw terms and its retained scheduler-generated
corrections, as measured by any Boolean filter.
-/
lemma filter_length_corrections
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (predicate :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length → Bool) :
    ((layer.endpoint M N).factors.filter predicate).length =
      ((retainedRawTerms M N n leftWeight rightWeight).filter predicate).length +
        (((endpointCorrectionInventory layer M N).corrections.filter
          predicate).length) := by
  simpa [retainedRawTerms] using
    DFTerm.length_collects_corrections
      predicate
        (endpointCorrectionInventory layer M
          N).family_collects_corrections

/--
Arbitrary-cutoff recipe-shape fibers split into the inverse-raw contribution
and the retained scheduler-correction contribution.
-/
lemma endpoint_filter_corrections
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    endpointRecipeMultiplicity layer M N word =
      ((retainedRawTerms M N n leftWeight rightWeight).filter fun term =>
        decide (term.family.recipe.erasedShape = word)).length +
        (((endpointCorrectionInventory layer M N).corrections.filter
          fun term =>
            decide (term.family.recipe.erasedShape = word)).length) := by
  exact
    filter_length_corrections
      layer M N fun term =>
        decide (term.family.recipe.erasedShape = word)

end CRInv
end TCTex
end Submission

/-!
# Shape-fiber profile assignments for cutoff-full collection

The finite correction-closure profile assignment attaches one homogeneous
signed-block formula to every erased Hall word.  This file sorts those packets
onto the cutoff-full vocabulary and isolates the remaining scalar theorem:
each assigned formula must count the corresponding endpoint recipe-shape
fiber at natural exponents.

Once that scalar property is available, the fixed-slot interpolation and
natural stabilization records follow formally.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  FCAssign

open
  FFCard
open
  FPInterp
open CFStab
open CRLayer
open NRSubinv
open
  CFSubsti
open
  UCSuppor

namespace SPAssign

/--
Attach the assigned profile formulas in the ordered cutoff-full vocabulary.
-/
noncomputable def erasedVocabPackets
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight) :
    List RFPkt :=
  (orderedErasedVocabulary n leftWeight rightWeight).attach.map fun word =>
    {
      word := word.1
      positive :=
        bidegree_positive_vocabulary
          (ordered_erased_vocabulary.mp word.2)
      profiles :=
        assignment.profiles word.1
          (ordered_erased_vocabulary.mp word.2)
    }

/-- Forgetting the assigned formulas recovers the ordered cutoff-full
vocabulary. -/
@[simp]
lemma ordered_vocabulary_packets
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight) :
    assignment.erasedVocabPackets.map
        RFPkt.word =
      orderedErasedVocabulary n leftWeight rightWeight := by
  classical
  simp [erasedVocabPackets]

/--
The scalar symbolic-counting obligation for a finite-closure profile
assignment: at natural exponents its profile for each vocabulary word counts
the corresponding cutoff-full endpoint recipe-shape fiber.
-/
def CountsFibersCast
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (assignment :
      SPAssign n leftWeight rightWeight) :
    Prop :=
  ∀ M N : ℕ,
    ∀ word : CWord HPAtom,
      ∀ hword :
          word ∈ orderedErasedVocabulary n leftWeight rightWeight,
        (assignment.profiles word
          (ordered_erased_vocabulary.mp hword)).value
            (M : ℤ) (N : ℤ) =
          (endpointRecipeMultiplicity layer M N word : ℤ)

/--
An assignment satisfying the scalar counting obligation interpolates all
ordered packet values.
-/
lemma cast_vocabulary_packets
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hcounts :
      CountsFibersCast layer assignment)
    (M N : ℕ) :
    assignment.erasedVocabPackets.map (fun packet =>
      packet.profiles.value (M : ℤ) (N : ℤ)) =
        (orderedErasedVocabulary n leftWeight rightWeight).map fun word =>
          (endpointRecipeMultiplicity layer M N word : ℤ) := by
  classical
  unfold erasedVocabPackets
  rw [List.map_map]
  calc
    (orderedErasedVocabulary n leftWeight rightWeight).attach.map
          (fun word =>
            (assignment.profiles word.1
              (ordered_erased_vocabulary.mp word.2)).value
                (M : ℤ) (N : ℤ)) =
        (orderedErasedVocabulary n leftWeight rightWeight).attach.map
          (fun word =>
            (endpointRecipeMultiplicity layer M N word.1 : ℤ)) := by
      apply List.map_congr_left
      intro word _hword
      exact hcounts M N word.1 word.2
    _ =
        (orderedErasedVocabulary n leftWeight rightWeight).map fun word =>
          (endpointRecipeMultiplicity layer M N word : ℤ) := by
      simpa only [List.map_map, Function.comp_apply] using
        congrArg
          (List.map fun word =>
            (endpointRecipeMultiplicity layer M N word : ℤ))
          (List.attach_map_subtype_val
            (orderedErasedVocabulary n leftWeight rightWeight))

/--
A finite-closure profile assignment satisfying the scalar fiber-counting
obligation supplies the cutoff-full endpoint interpolation package.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hcounts :
      CountsFibersCast layer assignment) :
    EFInterp
      layer assignment.erasedVocabPackets where
  map_word_packets :=
    assignment.ordered_vocabulary_packets
  map_nat_cast M N :=
    assignment.cast_vocabulary_packets
      hcounts M N

/--
The same scalar obligation supplies the existing natural shape-run
stabilization record.
-/
noncomputable def runPacketStabilization
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hcounts :
      CountsFibersCast layer assignment)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (d : ℕ) :
    NRStab layer d
      assignment.erasedVocabPackets :=
  (assignment.fiberProfileInterpolation hcounts)
    |>.runPacketStabilization
      hleftWeight hrightWeight d

end SPAssign

end
  FCAssign
end TCTex
end Submission

/-!
# Multiset accounting for cutoff-full retained corrections

The traced cutoff-full scheduler records precisely the generated corrections
that survive the quotient cutoff.  This file upgrades filtered cardinality
accounting to exact multiset accounting.  Consequently, every selected
endpoint is a permutation of its below-cutoff inverse-raw packet followed by
its retained scheduler-correction packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  CMAccoun

open HACoeff
open CFCollec.DFTerm
open
  FVSuppor
open
  FVSuppor.IDTerms
open
  CRLayer
open
  CRInv
open
  CRInv.DFTerm
open OCPartit
open RRTrunc
open
  UCSuppor
open
  UCVocabu

lemma multisetCoe_append
    {α : Type*}
    (left right : List α) :
    ((left ++ right : List α) : Multiset α) =
      (left : Multiset α) + (right : Multiset α) :=
  (Multiset.coe_add left right).symm

lemma multisetCoe_cons
    {α : Type*}
    (head : α)
    (tail : List α) :
    ((head :: tail : List α) : Multiset α) =
      {head} + (tail : Multiset α) :=
  rfl

namespace DFTerm

/--
Traced cutoff insertion preserves exactly the source terms, the inserted term,
and its retained generated corrections.
-/
lemma coe_result_inserted
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    (R : Multiset (DFTerm M N K)) =
      (L : Multiset (DFTerm M N K)) +
        {A} + corrections := by
  induction hinsert with
  | nil A =>
      simp only [Multiset.coe_nil, Multiset.coe_singleton, add_zero, zero_add]
  | append P B A _hBA =>
      simp only [multisetCoe_append, multisetCoe_cons,
        Multiset.coe_nil, add_zero]
      simp only [add_assoc]
  | retained P B A _hAB _hweight hcorrection hinsert
      ihcorrection ihinsert =>
      simp only [multisetCoe_append, multisetCoe_cons,
        Multiset.coe_nil, add_zero]
      rw [ihinsert, ihcorrection]
      simp only [add_comm, add_left_comm, add_assoc]
  | residual P B A _hAB _hweight hinsert ihinsert =>
      simp only [multisetCoe_append, multisetCoe_cons,
        Multiset.coe_nil, add_zero]
      rw [ihinsert]
      simp only [add_comm, add_left_comm, add_assoc]

/-- List-permutation form of traced cutoff-insertion accounting. -/
lemma result_append_inserted
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    List.Perm R (L ++ [A] ++ corrections) := by
  apply Multiset.coe_eq_coe.mp
  rw [multisetCoe_append, multisetCoe_append, Multiset.coe_singleton]
  exact coe_result_inserted hinsert

/--
Traced cutoff collection retains exactly the below-cutoff source terms and its
retained generated corrections.
-/
lemma coe_result_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    (R : Multiset (DFTerm M N K)) =
      (belowCutoffTerms n leftWeight rightWeight L :
        Multiset (DFTerm M N K)) +
          corrections := by
  induction hcollect with
  | nil =>
      rfl
  | @retained P A hweight C R collectCorrections insertCorrections
      hcollect hinsert ihcollect =>
      rw [coe_result_inserted hinsert,
        ihcollect]
      have hbelow :
          belowCutoffTerms n leftWeight rightWeight (P ++ [A]) =
            belowCutoffTerms n leftWeight rightWeight P ++ [A] := by
        simp [belowCutoffTerms, List.filter_append, hweight]
      rw [hbelow, multisetCoe_append, multisetCoe_append,
        Multiset.coe_singleton]
      simp only [add_assoc]
      rw [add_left_comm (collectCorrections : Multiset _) {A}]
  | residual P A hweight hcollect ihcollect =>
      rw [ihcollect]
      have hbelow :
          belowCutoffTerms n leftWeight rightWeight (P ++ [A]) =
            belowCutoffTerms n leftWeight rightWeight P := by
        simp [belowCutoffTerms, List.filter_append, Nat.not_lt.mpr hweight]
      rw [hbelow]

/-- List-permutation form of traced cutoff-collection accounting. -/
lemma result_perm_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    List.Perm R
      (belowCutoffTerms n leftWeight rightWeight L ++ corrections) := by
  apply Multiset.coe_eq_coe.mp
  rw [multisetCoe_append]
  exact coe_result_corrections hcollect

end DFTerm

/--
Every natural cutoff-full endpoint is a permutation of the initially retained
inverse-raw packet followed by the selected retained-correction trace.
-/
lemma endpoint_perm_corrections
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    List.Perm (layer.endpoint M N).factors
      (retainedRawTerms M N n leftWeight rightWeight ++
        (endpointCorrectionInventory layer M N).corrections) := by
  simpa [retainedRawTerms] using
    DFTerm.result_perm_corrections
      (endpointCorrectionInventory layer M
        N).family_collects_corrections

/-- Every selected retained correction occurs in the cutoff-full endpoint. -/
lemma endpoint_factors_corrections
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      term ∈ (endpointCorrectionInventory layer M N).corrections) :
    term ∈ (layer.endpoint M N).factors := by
  have hterm' :
      term ∈ retainedRawTerms M N n leftWeight rightWeight ++
        (endpointCorrectionInventory layer M N).corrections :=
    List.mem_append_right _ hterm
  exact
    (endpoint_perm_corrections
      layer M N).mem_iff.mpr hterm'

/--
Every selected retained correction has a representative in the canonical
finite correction-closure vocabulary.
-/
lemma recipe_endpoint_corrections
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      term ∈ (endpointCorrectionInventory layer M N).corrections) :
    ∃ recipe ∈
        correctionClosureRecipes n leftWeight rightWeight,
      recipe.erasedShape = term.erasedShape :=
  IDTerms.exists_of_mem
    (layer.endpoint M N) hleftWeight hrightWeight term
      (endpoint_factors_corrections layer M N hterm)

/-- Every selected retained correction shape lies in the finite vocabulary. -/
lemma erased_vocabulary_corrections
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      term ∈ (endpointCorrectionInventory layer M N).corrections) :
    term.erasedShape ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  rcases recipe_endpoint_corrections
      layer hleftWeight hrightWeight M N hterm with
    ⟨recipe, hrecipe, hshape⟩
  rw [← hshape]
  exact shape_vocabulary_recipes hrecipe

end
  CMAccoun
end TCTex
end Submission

/-!
# Uniform unrestricted packets for cutoff-full endpoint shape fibers

Concrete operational certificates may choose a different signed-profile packet
at every natural specialization.  Universal collection polynomials need one
packet per erased Hall word, independent of the two source multiplicities.

This file isolates that uniform symbolic boundary in two stages.  First,
construct one unrestricted signed-block packet whose natural values count the
endpoint recipe-shape fiber.  Second, give that unrestricted packet a
homogeneous presentation in the target Hall bidegree.  The resulting
homogeneous packets compile directly to the fixed endpoint-fiber profile
assignment.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  FFInhomo

open
  CFStab
open
  FFCard
open
  FPInterp
open CRLayer
open NRSubinv
open
  CFSubsti
open
  SHPres
open
  CSComp
open
  FCAssign
open
  UCSuppor

/--
One multiplicity-independent unrestricted signed-block packet for every
retained erased Hall word, with natural values equal to the corresponding
cutoff-full endpoint recipe-shape fiber cardinalities.
-/
structure EndpointFiberInhomogeneous
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight) where
  packet :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      IFPkt
  nat_cast :
    ∀ (M N : ℕ) word hword,
      (packet word hword).value (M : ℤ) (N : ℤ) =
        (endpointRecipeMultiplicity layer M N word : ℤ)

/--
The uniform unrestricted packets have homogeneous presentations in their
target Hall bidegrees.
-/
structure FHPres
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    extends EndpointFiberInhomogeneous layer where
  presentation :
    ∀ word hword,
      HPres
        (toEndpointFiberInhomogeneous.packet
          word hword)
        word.pairLeftDegree word.pairRightDegree

namespace FHPres

/--
Any fixed homogeneous profile assignment that already counts endpoint fibers
can be regarded as a uniform unrestricted packet kernel.
-/
def counts_fibers_cast
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hcounts :
      assignment.CountsFibersCast layer) :
    FHPres layer where
  packet word hword :=
    IFPkt.ofHomogeneous
      (assignment.profiles word hword)
  nat_cast M N word hword := by
    rw [IFPkt.value_ofHomogeneous]
    exact
      hcounts M N word
        (ordered_erased_vocabulary.mpr hword)
  presentation word hword :=
    HPres.ofHomogeneous
      (assignment.profiles word hword)

/--
Forget each unrestricted packet to the homogeneous packet selected by its
presentation.
-/
def signedProfileAssignment
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      FHPres layer) :
    SPAssign n leftWeight rightWeight where
  profiles word hword :=
    (kernel.presentation word hword).homogeneous

/--
Promoting an already-counted homogeneous assignment and then forgetting the
unrestricted presentation recovers its original profiles.
-/
@[simp]
lemma profiles_counts_fibers
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hcounts :
      assignment.CountsFibersCast layer)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ((counts_fibers_cast assignment hcounts)
      |>.signedProfileAssignment.profiles word hword) =
        assignment.profiles word hword :=
  rfl

/--
The selected homogeneous packets count the endpoint recipe-shape fibers at
natural source multiplicities.
-/
lemma counts_fibers_assignment
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      FHPres layer) :
    kernel.signedProfileAssignment
      |>.CountsFibersCast layer := by
  intro M N word hword
  let hword' :=
    ordered_erased_vocabulary.mp hword
  exact
    (kernel.presentation word hword').value_eq (M : ℤ) (N : ℤ) |>.trans
      (kernel.nat_cast M N word hword')

/--
Uniform unrestricted packets with homogeneous presentations supply fixed
cutoff-full endpoint-fiber interpolation.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      FHPres layer) :
    EFInterp layer
      (kernel.signedProfileAssignment
        |>.erasedVocabPackets) :=
  kernel.signedProfileAssignment
    |>.fiberProfileInterpolation
      kernel.counts_fibers_assignment

/--
The same uniform presentation kernel supplies the natural shape-run
stabilization record.
-/
noncomputable def runPacketStabilization
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      FHPres layer)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (d : ℕ) :
    NRStab layer d
      (kernel.signedProfileAssignment
        |>.erasedVocabPackets) :=
  kernel.fiberProfileInterpolation
    |>.runPacketStabilization
      hleftWeight hrightWeight d

end FHPres

open FHPres

/--
Uniform unrestricted endpoint-fiber packets with homogeneous presentations
exist exactly when a fixed homogeneous profile assignment counts those fibers.
-/
theorem homogeneous_counted_assignment
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight) :
    Nonempty (FHPres layer) ↔
      ∃ assignment : SPAssign n leftWeight rightWeight,
        assignment.CountsFibersCast layer := by
  constructor
  · rintro ⟨kernel⟩
    exact
      ⟨kernel.signedProfileAssignment,
        kernel.counts_fibers_assignment⟩
  · rintro ⟨assignment, hcounts⟩
    exact
      ⟨counts_fibers_cast assignment hcounts⟩

end
  FFInhomo
end TCTex
end Submission

/-!
# Recursive semantic profiles for cutoff-full shape fibers

The recursive finite-closure assignment machinery propagates arbitrary
word-local motives from source recipes through correction recipes.  This file
connects that interface to cutoff-full endpoint shape-fiber interpolation.

It is enough to propagate a motive implying that each selected homogeneous
signed profile counts the corresponding endpoint recipe-shape fiber at
natural exponents.  The list-level interpolation and stabilization records
then follow automa.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  RPAssign

open
  CFStab
open
  FFCard
open
  FPInterp
open CRLayer
open NRSubinv
open
  CFSubsti
open
  RASem
open
  FCAssign

/--
A word-local homogeneous signed profile counts its cutoff-full endpoint
recipe-shape fiber at every pair of natural exponents.
-/
def EndpointRecipeFiber
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (word : CWord HPAtom)
    (profiles :
      HFPkt
        word.pairLeftDegree word.pairRightDegree) :
    Prop :=
  ∀ M N : ℕ,
    profiles.value (M : ℤ) (N : ℤ) =
      (endpointRecipeMultiplicity layer M N word : ℤ)

/--
Any propagated profile motive implying the endpoint-fiber property supplies
the scalar counting obligation for the underlying finite-closure assignment.
-/
lemma counts_fibers_motive
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {profileMotive :
      ∀ word : CWord HPAtom,
        HFPkt
            word.pairLeftDegree word.pairRightDegree →
          Prop}
    (assignment :
      PAMotive
        n leftWeight rightWeight profileMotive)
    (hprofile :
      ∀ word profiles,
        profileMotive word profiles →
          EndpointRecipeFiber layer word profiles) :
    assignment.toSPAssign
      |>.CountsFibersCast layer := by
  intro M N word hword
  exact
    hprofile word
      (assignment.toSPAssign.profiles word
        (ordered_erased_vocabulary.mp hword))
      (assignment.profiles_motive word
        (ordered_erased_vocabulary.mp hword))
      M N

/--
A recursive semantic kernel whose propagated motive implies endpoint-fiber
counting supplies the cutoff-full endpoint interpolation package.
-/
noncomputable def
    RPSem.fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      RPSem n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hprofile :
      ∀ word profiles,
        kernel.profileMotive word profiles →
          EndpointRecipeFiber layer word profiles) :
    EFInterp layer
      ((kernel.profileAssignmentMotive
          hleftWeight hrightWeight).toSPAssign
        |>.erasedVocabPackets) :=
  let assignment :=
    kernel.profileAssignmentMotive
      hleftWeight hrightWeight
  assignment.toSPAssign
    |>.fiberProfileInterpolation
      (counts_fibers_motive
        assignment hprofile)

/--
The same recursive semantic invariant supplies the existing natural shape-run
stabilization record.
-/
noncomputable def
    RPSem.runPacketStabilization
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      RPSem n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hprofile :
      ∀ word profiles,
        kernel.profileMotive word profiles →
          EndpointRecipeFiber layer word profiles)
    (d : ℕ) :
    NRStab layer d
      ((kernel.profileAssignmentMotive
          hleftWeight hrightWeight).toSPAssign
        |>.erasedVocabPackets) :=
  (RPSem.fiberProfileInterpolation
    kernel hleftWeight hrightWeight hprofile)
      |>.runPacketStabilization
        hleftWeight hrightWeight d

end
  RPAssign
end TCTex
end Submission

/-!
# Zero endpoint packets below the initial commutator weight

Every positive Hall-Petresco block recipe has weighted degree at least the
initial commutator degree `leftWeight + rightWeight`.  Hence a cutoff no larger
than that degree retains no cutoff-full endpoint term.  This file packages the
result as an actual uniform unrestricted endpoint-fiber packet kernel: every
fiber is represented by the zero packet and has a homogeneous presentation in
its target bidegree.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace FLZero

open HACoeff
open BRSpec
open CFStab
open FFCard
open
  FFInhomo
open CRLayer
open OCPartit
open
  SHPres
open
  CSComp
open
  CSComp.IFPkt
open
  UCSuppor
open UCVocabu

/--
At a cutoff no larger than the initial commutator degree, every selected
cutoff-full endpoint is empty.
-/
lemma endpoint_factors_nil
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hcutoff : n ≤ leftWeight + rightWeight)
    (M N : ℕ) :
    (layer.endpoint M N).factors = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro term hterm
  have hlt :
      decoratedFamilyWeight leftWeight rightWeight term < n :=
    layer.endpoint_weight_lt M N term hterm
  have hmin :
      leftWeight + rightWeight ≤
        decoratedFamilyWeight leftWeight rightWeight term := by
    simpa only [decoratedFamilyWeight, weighted_word_pair] using
      weighted_weight_basic leftWeight rightWeight term.family.recipe
  omega

/-- The compressed natural endpoint packet is empty in the same low-cutoff range. -/
lemma factors_nil_initial
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hcutoff : n ≤ leftWeight + rightWeight)
    (M N : ℕ) :
    layer.factors M N = [] := by
  simp [
    NRLayer.factors,
    naturalRunFactors,
    naturalShapeFactors,
    sameErasedBlocks,
    endpoint_factors_nil layer hcutoff M N]

/-- Every endpoint recipe-shape fiber has cardinality zero below the initial degree. -/
lemma endpoint_recipe_multiplicity
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hcutoff : n ≤ leftWeight + rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    endpointRecipeMultiplicity layer M N word = 0 := by
  simp [endpointRecipeMultiplicity,
    endpoint_factors_nil layer hcutoff M N]

/-- The conservative erased-shape vocabulary is itself empty below the initial degree. -/
lemma shape_vocabulary_nil
    {n leftWeight rightWeight : ℕ}
    (hcutoff : n ≤ leftWeight + rightWeight) :
    erasedShapeVocabulary n leftWeight rightWeight = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro word hword
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, rfl⟩
  have hlt :
      weightedWordWeight leftWeight rightWeight recipe < n :=
    weighted_closure_recipes hrecipe
  have hmin :
      leftWeight + rightWeight ≤
        weightedWordWeight leftWeight rightWeight recipe := by
    simpa only [weighted_word_pair] using
      weighted_weight_basic leftWeight rightWeight recipe
  omega

/--
Below the initial degree, every endpoint shape fiber has one uniform zero
unrestricted packet and a homogeneous presentation in its requested bidegree.
-/
def endpointFiberHomogeneous
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hcutoff : n ≤ leftWeight + rightWeight) :
    FHPres layer where
  packet _word _hword :=
    IFPkt.zero
  nat_cast M N word _hword := by
    rw [IFPkt.value_zero,
      endpoint_recipe_multiplicity
        layer hcutoff M N word]
    rfl
  presentation word _hword :=
    HPres.zero
      word.pairLeftDegree word.pairRightDegree

/--
The zero endpoint packets supply fixed natural stabilization at every
low-cutoff specialization.
-/
def shapeRunStabilization
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hcutoff : n ≤ leftWeight + rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (d : ℕ) :
    NRStab layer d
      ((endpointFiberHomogeneous
          layer hcutoff).signedProfileAssignment
        |>.erasedVocabPackets) :=
  (endpointFiberHomogeneous
      layer hcutoff).runPacketStabilization
    hleftWeight hrightWeight d

end FLZero
end TCTex
end Submission

/-!
# Profile splitting for cutoff-full retained corrections

The cutoff-full endpoint fiber count is the sum of two disjoint inventories:
the initially retained inverse-raw terms and the scheduler-generated
corrections retained below cutoff.  This file packages the corresponding
homogeneous-profile compiler.

It reduces construction of a counted endpoint profile assignment to separate
homogeneous formulas for those two inventories.  The remaining recursive
problem is concentrated in the retained-correction trace.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  CRSplit

open HACoeff
open
  CFStab
open
  FFInhomo
open
  FPInterp
open CRLayer
open
  NRSubinv
open
  CRInv
open
  CFAlg
open
  CFAlg.FPkt
open
  CFSubsti
open RRTrunc
open
  FCAssign
open
  UCSuppor

/--
Separate homogeneous formulas for the initially retained raw terms and for the
retained scheduler-correction trace.
-/
structure EFProf
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight) where
  rawProfiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  retainedCorrectionProfiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  raw_profiles_cast :
    ∀ (M N : ℕ) word hword,
      (rawProfiles word hword).value (M : ℤ) (N : ℤ) =
        (((retainedRawTerms M N n leftWeight rightWeight).filter fun term =>
          decide (term.family.recipe.erasedShape = word)).length : ℤ)
  retained_correction_cast :
    ∀ (M N : ℕ) word hword,
      (retainedCorrectionProfiles word hword).value (M : ℤ) (N : ℤ) =
        ((((endpointCorrectionInventory layer M N).corrections.filter
          fun term =>
            decide (term.family.recipe.erasedShape = word)).length : ℕ) : ℤ)

namespace EFProf

/-- Add the two inventory profiles word by word. -/
def signedProfileAssignment
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel : EFProf layer) :
    SPAssign n leftWeight rightWeight where
  profiles word hword :=
    FPkt.add
      (kernel.rawProfiles word hword)
      (kernel.retainedCorrectionProfiles word hword)

/--
The summed assignment counts every cutoff-full endpoint recipe-shape fiber at
natural source multiplicities.
-/
lemma counts_fibers_assignment
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel : EFProf layer) :
    kernel.signedProfileAssignment
      |>.CountsFibersCast layer := by
  intro M N word hword
  let hword' :=
    ordered_erased_vocabulary.mp hword
  rw [signedProfileAssignment, FPkt.value_add,
    kernel.raw_profiles_cast M N word hword',
    kernel.retained_correction_cast M N word hword',
    endpoint_filter_corrections,
    Int.natCast_add]

/--
The split kernel supplies the uniform homogeneous endpoint-fiber
presentation consumed by fixed-slot stabilization.
-/
def endpointFiberPresentation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel : EFProf layer) :
    FHPres layer :=
  FHPres.counts_fibers_cast
    kernel.signedProfileAssignment
      kernel.counts_fibers_assignment

/-- The split kernel supplies fixed cutoff-full endpoint-fiber interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel : EFProf layer) :
    EFInterp layer
      (kernel.signedProfileAssignment
        |>.erasedVocabPackets) :=
  kernel.signedProfileAssignment
    |>.fiberProfileInterpolation
      kernel.counts_fibers_assignment

/-- The split kernel supplies natural shape-run packet stabilization. -/
noncomputable def runPacketStabilization
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel : EFProf layer)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (d : ℕ) :
    NRStab layer d
      (kernel.signedProfileAssignment
        |>.erasedVocabPackets) :=
  kernel.fiberProfileInterpolation
    |>.runPacketStabilization
      hleftWeight hrightWeight d

end EFProf

end
  CRSplit
end TCTex
end Submission

/-!
# Profile splitting through retained raw histories

The raw-source half of the cutoff-full endpoint profile can be counted either
with indexed decorated family terms or with the exact retained inverse
histories.  The history presentation has the recursive shape of the genuine
inverse trace and is therefore the better input for an arbitrary-cutoff
symbolic counting argument.

This file transports homogeneous raw-history shape-fiber profiles into the
retained-correction profile split kernel.  The scheduler-generated correction
trace remains a separate explicit obligation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  RHSplit

open HACoeff
open CRLayer
open
  CRInv
open
  CRSplit
open
  RHFiber
open
  CFSubsti
open RHRecipe
open HHTrunc
open
  UCSuppor

/--
Separate homogeneous formulas for exact retained inverse-history shape fibers
and for the scheduler-generated retained-correction trace.
-/
structure EFSplit
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight) where
  rawHistoryProfiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  retainedCorrectionProfiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  raw_history_cast :
    ∀ (M N : ℕ) word hword,
      (rawHistoryProfiles word hword).value (M : ℤ) (N : ℤ) =
        (((retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N)).filter fun history =>
            decide (collapseWord history.word = word)).length : ℤ)
  retained_correction_cast :
    ∀ (M N : ℕ) word hword,
      (retainedCorrectionProfiles word hword).value (M : ℤ) (N : ℤ) =
        ((((endpointCorrectionInventory layer M N).corrections.filter
          fun term =>
            decide (term.family.recipe.erasedShape = word)).length : ℕ) : ℤ)

namespace EFSplit

/--
Transport raw-history shape-fiber profiles to the indexed retained-raw packet
used by the endpoint inventory split.
-/
def endpointRecipeFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      EFSplit layer) :
    EFProf layer where
  rawProfiles :=
    kernel.rawHistoryProfiles
  retainedCorrectionProfiles :=
    kernel.retainedCorrectionProfiles
  raw_profiles_cast M N word hword := by
    rw [kernel.raw_history_cast M N word hword,
      ←
        length_collapse_histories]
    simp only [DFTerm.erased_shape_family]
  retained_correction_cast :=
    kernel.retained_correction_cast

/--
Raw-history and retained-correction profiles supply fixed cutoff-full
endpoint-fiber interpolation.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (kernel :
      EFSplit layer) :=
  kernel.endpointRecipeFiber
    |>.fiberProfileInterpolation

end EFSplit

end
  RHSplit
end TCTex
end Submission

/-!
# Uniform profiles for retained raw shape fibers

Every natural retained raw shape fiber already has a local homogeneous
recipe-chunk profile.  Universal collection polynomials require one fixed
profile per erased Hall word, independent of the natural source
multiplicities.

This file isolates that raw stabilization theorem.  A fixed raw profile family
which agrees with every local recipe-chunk specialization, together with
homogeneous profiles for the retained scheduler-correction trace, supplies the
history-correction split kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  FUBounda

open HACoeff
open CRLayer
open
  CRInv
open
  RHSplit
open
  RHFiber
open
  RFLocal
open
  CFSubsti
open RHRecipe
open HHTrunc
open
  UCSuppor

/--
One multiplicity-independent homogeneous profile per retained erased Hall
word, agreeing with the locally compiled retained-raw recipe chunk at every
natural specialization.
-/
structure FUProf
    (n leftWeight rightWeight : ℕ) where
  profiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  profiles_cast_local :
    ∀ (M N : ℕ) word hword,
      (profiles word hword).value (M : ℤ) (N : ℤ) =
        (retainedFiberProfile
          M N n leftWeight rightWeight word).value (M : ℤ) (N : ℤ)

namespace FUProf

/--
Uniform raw profiles count exact retained inverse-history shape fibers.
-/
lemma profiles_histories_length
    {n leftWeight rightWeight : ℕ}
    (kernel :
      FUProf n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    (kernel.profiles word hword).value (M : ℤ) (N : ℤ) =
      (((retainedHistories n leftWeight rightWeight
        (inverseRawHistories M N)).filter fun history =>
          decide (collapseWord history.word = word)).length : ℤ) := by
  rw [kernel.profiles_cast_local M N word hword,
    fiber_filter_length]
  simpa only [DFTerm.erased_shape_family] using
    congrArg (fun length : ℕ => (length : ℤ))
      (length_collapse_histories
        M N n leftWeight rightWeight word)

end FUProf

namespace EFSplit

/--
Stable raw-history profiles and retained scheduler-correction profiles supply
the history-correction endpoint-fiber split.
-/
def fiber_uniform_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (raw :
      FUProf n leftWeight rightWeight)
    (retainedCorrectionProfiles :
      ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
        HFPkt
          word.pairLeftDegree word.pairRightDegree)
    (retained_correction_cast :
      ∀ (M N : ℕ) word hword,
        (retainedCorrectionProfiles word hword).value (M : ℤ) (N : ℤ) =
          ((((endpointCorrectionInventory layer M N).corrections.filter
            fun term =>
              decide (term.family.recipe.erasedShape = word)).length : ℕ) :
                ℤ)) :
    EFSplit layer where
  rawHistoryProfiles :=
    raw.profiles
  retainedCorrectionProfiles :=
    retainedCorrectionProfiles
  raw_history_cast :=
    raw.profiles_histories_length
  retained_correction_cast :=
    retained_correction_cast

end EFSplit

end
  FUBounda
end TCTex
end Submission

/-!
# The first nonempty cutoff-full endpoint packet

At cutoff three with source weights `(1, 1)`, every generated correction has
weight at least four and is therefore residual.  The cutoff-full collector
only reorders the retained raw roots.  Exact raw histories show that there are
`M * N` such roots, and the finite vocabulary has the single erased shape
`hallPairBase`.

This file packages that occurrence-preserving count as the first nonempty
uniform endpoint-fiber packet kernel.  It is intentionally not imported by
the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace CTBoundaa

open HACoeff
open BRSpec
open CFCollec.DFTerm
open CFStab
open FFCard
open
  FFInhomo
open CRLayer
open CCAggreg
open OCPartit
open
  SHPres
open
  CSComp
open
  CSComp.IFPkt
open RHRecurs
open RHRecipe
open HHTrunc
open RRTrunc
open
  CPSplit
open
  UCAdapt
open
  UCSuppor
open UCVocabu

namespace DFTerm

/--
If the cutoff is no larger than twice the initial commutator degree, every
correction generated by insertion is residual.  Insertion therefore increases
the retained endpoint length by exactly one.
-/
lemma inserts_twice_initial
    {M N K n leftWeight rightWeight : ℕ}
    (hcutoff : n ≤ 2 * (leftWeight + rightWeight))
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R) :
    R.length = L.length + 1 := by
  induction hinsert with
  | nil A =>
      rfl
  | append P B A _hBA =>
      simp
  | retained P B A _hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      have hBmin :
          leftWeight + rightWeight ≤
            decoratedFamilyWeight leftWeight rightWeight B := by
        simpa only [decoratedFamilyWeight, weighted_word_pair] using
          weighted_weight_basic leftWeight rightWeight B.family.recipe
      have hAmin :
          leftWeight + rightWeight ≤
            decoratedFamilyWeight leftWeight rightWeight A := by
        simpa only [decoratedFamilyWeight, weighted_word_pair] using
          weighted_weight_basic leftWeight rightWeight A.family.recipe
      rw [decorated_family_correction] at hweight
      omega
  | residual P B A _hAB _hweight hinsert ihinsert =>
      simp [ihinsert]

/--
In the same shallow range, cutoff collection preserves the length of the
initial below-cutoff filter.
-/
lemma collects_twice_initial
    {M N K n leftWeight rightWeight : ℕ}
    (hcutoff : n ≤ 2 * (leftWeight + rightWeight))
    {L R : List (DFTerm M N K)}
    (hcollect : CCollec n leftWeight rightWeight L R) :
    R.length = (belowCutoffTerms n leftWeight rightWeight L).length := by
  induction hcollect with
  | nil =>
      rfl
  | retained P A hweight hcollect hinsert ihcollect =>
      rw [inserts_twice_initial
        hcutoff hinsert, ihcollect]
      simp [belowCutoffTerms, hweight]
  | residual P A hweight hcollect ihcollect =>
      rw [ihcollect]
      simp [belowCutoffTerms, Nat.not_lt.mpr hweight]

end DFTerm

namespace RHistor

/-- Root histories are precisely the raw histories with no conjugation parent. -/
def isBasic
    {M N : ℕ} :
    RHistor M N → Bool
  | .hallPair _ _ =>
      true
  | .conjugate _ _ =>
      false

/-- Every raw history has weighted degree at least two at source weights `(1, 1)`. -/
lemma two_weight_one
    {M N : ℕ} :
    ∀ history : RHistor M N,
      2 ≤ RHistor.weight 1 1 history
  | .hallPair left right => by
      have hleft :
          HPAtom.weight 1 1 (collapseLabel left) = 1 := by
        cases left <;> rfl
      have hright :
          HPAtom.weight 1 1 (collapseLabel right) = 1 := by
        cases right <;> rfl
      rw [RHistor.weight_hallPair, hleft, hright]
  | .conjugate parent emitted => by
      rw [RHistor.weight_conjugate]
      exact Nat.le_add_right_of_le (two_weight_one emitted)

end RHistor

/-- Conjugating one history preserves its unique root-history occurrence. -/
@[simp]
lemma filter_atom_histories
    {M N : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    (conjugateAtomHistories parent emitted).filter RHistor.isBasic =
      [emitted].filter RHistor.isBasic := by
  cases emitted <;> rfl

/-- A history expansion preserving root sublists does so after flat-mapping. -/
lemma filter_flat_singleton
    {M N : ℕ}
    (transform : RHistor M N → List (RHistor M N))
    (htransform :
      ∀ history,
        (transform history).filter RHistor.isBasic =
          [history].filter RHistor.isBasic) :
    ∀ histories : List (RHistor M N),
      (histories.flatMap transform).filter RHistor.isBasic =
        histories.filter RHistor.isBasic
  | [] => by
      rfl
  | history :: histories => by
      rw [List.flatMap_cons, List.filter_append, htransform,
        filter_flat_singleton transform htransform]
      cases history <;> rfl

/-- Conjugating one history across any atom list preserves its root occurrence. -/
lemma filter_conj_histories
    {M N : ℕ} :
    ∀ (parents : List (LabelledAtom M N)) (emitted : RHistor M N),
      (inverseConjHistories parents emitted).filter RHistor.isBasic =
        [emitted].filter RHistor.isBasic
  | [], emitted => by
      rfl
  | parent :: parents, emitted => by
      rw [inverseConjHistories,
        filter_flat_singleton
          (conjugateAtomHistories parent)
          (filter_atom_histories parent),
        filter_conj_histories]

/-- Conjugating a history list preserves its ordered root-history sublist. -/
lemma filter_history_list
    {M N : ℕ}
    (parents : List (LabelledAtom M N)) :
    ∀ histories : List (RHistor M N),
      (inverseConjHistory parents histories).filter RHistor.isBasic =
        histories.filter RHistor.isBasic
  | [] => by
      rfl
  | history :: histories => by
      rw [inverseConjHistory,
        filter_flat_singleton
          (inverseConjHistories parents)
          (filter_conj_histories parents)]

/-- One right row has one root history for each right source atom. -/
lemma length_basic_histories
    {M N : ℕ}
    (left : LabelledAtom M N) :
    ∀ rights : List (LabelledAtom M N),
      ((inverseRightHistories left rights).filter RHistor.isBasic).length =
        rights.length
  | [] => by
      rfl
  | right :: rights => by
      simp [inverseRightHistories, filter_history_list,
        length_basic_histories left rights,
        RHistor.isBasic]

/-- The complete inverse trace has one root history for each source-atom pair. -/
lemma filter_basic_histories
    {M N : ℕ} :
    ∀ (lefts rights : List (LabelledAtom M N)),
      ((inverseLeftHistories lefts rights).filter RHistor.isBasic).length =
        lefts.length * rights.length
  | [], rights => by
      simp [inverseLeftHistories]
  | left :: lefts, rights => by
      rw [inverseLeftHistories, List.filter_append, List.length_append,
        filter_history_list,
        filter_basic_histories,
        length_basic_histories]
      simp [Nat.succ_mul]

/--
At source weights `(1, 1)` and cutoff at most three, the retained raw histories
are exactly the root histories.
-/
lemma histories_filter_n
    {M N n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    ∀ histories : List (RHistor M N),
      retainedHistories n 1 1 histories =
        histories.filter RHistor.isBasic := by
  intro histories
  unfold retainedHistories
  apply congrArg (fun predicate => histories.filter predicate)
  funext history
  cases history with
  | hallPair left right =>
      have hleft :
          HPAtom.weight 1 1 (collapseLabel left) = 1 := by
        cases left <;> rfl
      have hright :
          HPAtom.weight 1 1 (collapseLabel right) = 1 := by
        cases right <;> rfl
      simp [RHistor.isBasic, hleft, hright]
      omega
  | conjugate parent emitted =>
      have hemittedMin :
          2 ≤ RHistor.weight 1 1 emitted :=
        RHistor.two_weight_one emitted
      have hparent :
          HPAtom.weight 1 1 (collapseLabel parent) = 1 := by
        cases parent <;> rfl
      rw [RHistor.weight_conjugate, hparent]
      change decide (RHistor.weight 1 1 emitted + 1 < n) = false
      rw [decide_eq_false_iff_not]
      omega

/-- The retained class-two raw history packet has cardinality `M * N`. -/
lemma length_histories_n
    {M N n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    (retainedHistories n 1 1 (inverseRawHistories M N)).length =
      M * N := by
  rw [histories_filter_n
    hlow hhigh]
  simpa [inverseRawHistories, labelledLeftAtoms, labelledRightAtoms] using
    filter_basic_histories
      (labelledLeftAtoms M N) (labelledRightAtoms M N)

/-- The retained indexed raw recipe packet has the same class-two cardinality. -/
lemma length_terms_n
    {M N n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    (retainedRawTerms M N n 1 1).length = M * N := by
  have hwords :=
    congrArg List.length
      (history_words_histories
        M N n 1 1)
  have hlength :
      (retainedRawTerms M N n 1 1).length =
        (retainedHistories n 1 1 (inverseRawHistories M N)).length := by
    simpa [historyWords, decoratedFamilyList] using hwords.symm
  exact hlength.trans
    (length_histories_n
      hlow hhigh)

/-- Every selected cutoff-full class-two endpoint has cardinality `M * N`. -/
lemma endpoint_length_n
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 2 < n)
    (hhigh : n ≤ 3)
    (M N : ℕ) :
    (layer.endpoint M N).factors.length = M * N := by
  calc
    (layer.endpoint M N).factors.length =
        (belowCutoffTerms n 1 1
          (inverseDecoratedTerms M N)).length := by
      exact
        DFTerm.collects_twice_initial
          (by omega) (layer.endpoint M N).family_cutoff_collects
    _ = (retainedRawTerms M N n 1 1).length :=
      rfl
    _ = M * N :=
      length_terms_n hlow hhigh

/-- The unique class-two endpoint recipe-shape fiber has cardinality `M * N`. -/
lemma endpoint_multiplicity_n
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 2 < n)
    (hhigh : n ≤ 3)
    (M N : ℕ) :
    endpointRecipeMultiplicity layer M N CWord.hallPairBase =
      M * N := by
  rw [endpointRecipeMultiplicity, List.filter_eq_self.mpr]
  · exact endpoint_length_n
      layer hlow hhigh M N
  · intro term hterm
    simp only [decide_eq_true_eq]
    rw [← term.erased_shape_family]
    have hword :
        term.erasedShape ∈ erasedShapeVocabulary n 1 1 :=
      FVSuppor.IDTerms.erased_vocab_factors
        (layer.endpoint M N) (by omega) (by omega) term hterm
    rw [
      erased_vocabulary_singleton
        hlow hhigh] at hword
    simpa using hword

/--
The unique class-two endpoint shape fiber is represented uniformly by the
ordinary basic Hall-Petresco recipe packet.
-/
def fiberHomogeneousPresentation
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    FHPres layer where
  packet _word _hword :=
    IFPkt.ofHomogeneous
      (homogeneousFormulaRecipe hallPair)
  nat_cast M N word hword := by
    have hwordEq :
        word = CWord.hallPairBase := by
      have hword' := hword
      rw [
        erased_vocabulary_singleton
          hlow hhigh] at hword'
      simpa using hword'
    subst word
    rw [IFPkt.value_ofHomogeneous,
      value_homogeneous_recipe,
      coefficient_value_pair,
      endpoint_multiplicity_n
        layer hlow hhigh M N]
    norm_cast
  presentation word hword := by
    have hwordEq :
        word = CWord.hallPairBase := by
      have hword' := hword
      rw [
        erased_vocabulary_singleton
          hlow hhigh] at hword'
      simpa using hword'
    subst word
    simpa [erased_shape_pair] using
      HPres.ofHomogeneous
        (homogeneousFormulaRecipe hallPair)

/-- The class-two packet kernel supplies fixed natural stabilization. -/
def naturalRunStabilization
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 2 < n)
    (hhigh : n ≤ 3)
    (d : ℕ) :
    NRStab layer d
      ((fiberHomogeneousPresentation
          layer hlow hhigh).signedProfileAssignment
        |>.erasedVocabPackets) :=
  (fiberHomogeneousPresentation
      layer hlow hhigh).runPacketStabilization
    (by omega) (by omega) d

end CTBoundaa
end TCTex
end Submission

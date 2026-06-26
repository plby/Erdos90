import Submission.Group.Zassenhaus.ConcreteRetainedCorrection
import Submission.Group.Zassenhaus.ErasedShapePrograms
import Submission.Group.Zassenhaus.GuardedGridCoverage
import Submission.Group.Zassenhaus.SchedulePrograms
import Submission.Group.Zassenhaus.InverseUniversalOrbit
import Submission.Group.Zassenhaus.CompatibleListBoundary
import Submission.Group.Zassenhaus.CompatibleGridBridge
import Submission.Group.Zassenhaus.OrderedRetainedLaw
import Submission.Group.Zassenhaus.CompatiblePacketRouting


-- Merged from FamilyCutoffFullCollector.lean

/-!
# Determinism of retained-correction inventories

The cutoff-full collector is presented relationally, but its scheduler is
deterministic.  This file proves that the traced insertion and collection
relations have unique endpoints and unique ordered retained-correction traces.

This gives the proof-free scalar local-model interface a canonical concrete
reference semantics.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  IDBounda

open
  HACoeff
open
  CRInv
open
  CRInv.DFTerm

namespace DFTerm

/--
Two decompositions of the same list into a prefix and final term agree.
-/
lemma eq_and_eq
    {α : Type*}
    {P Q : List α}
    {A B : α}
    (h : P ++ [A] = Q ++ [B]) :
    P = Q ∧ A = B := by
  have hreverse : A :: P.reverse = B :: Q.reverse := by
    simpa using congrArg List.reverse h
  injection hreverse with hAB hPQ
  exact ⟨by simpa using congrArg List.reverse hPQ, hAB⟩

/--
Traced cutoff insertion has a unique endpoint and a unique ordered retained
correction trace.
-/
lemma inserts_retained_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R leftCorrections rightEndpoint rightCorrections :
      List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hleft :
      CICorrec
        n leftWeight rightWeight L A R leftCorrections)
    (hright :
      CICorrec
        n leftWeight rightWeight L A rightEndpoint rightCorrections) :
    R = rightEndpoint ∧
      leftCorrections = rightCorrections := by
  induction hleft generalizing rightEndpoint rightCorrections with
  | nil A =>
      generalize hsource : ([] : List (DFTerm M N K)) = source at hright
      cases hright with
      | nil =>
          exact ⟨rfl, rfl⟩
      | append P B A hBA =>
          simp at hsource
      | retained P B A hAB hweight hcorrection hinsert =>
          simp at hsource
      | residual P B A hAB hweight hinsert =>
          simp at hsource
  | append P B A hBA =>
      generalize hsource : P ++ [B] = source at hright
      cases hright with
      | nil =>
          simp at hsource
      | append Q C _ hCA =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      | retained Q C _ hAC hweight hcorrection hinsert =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          exact False.elim (hBA hAC)
      | residual Q C _ hAC hweight hinsert =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          exact False.elim (hBA hAC)
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      generalize hsource : P ++ [B] = source at hright
      cases hright with
      | nil =>
          simp at hsource
      | append Q C _ hCA =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          exact False.elim (hCA hAB)
      | retained Q C _ hAC hweight' hcorrection' hinsert' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          rcases ihcorrection hcorrection' with
            ⟨rfl, rfl⟩
          rcases ihinsert hinsert' with
            ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      | residual Q C _ hAC hweight' hinsert' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          omega
  | residual P B A hAB hweight hinsert ihinsert =>
      generalize hsource : P ++ [B] = source at hright
      cases hright with
      | nil =>
          simp at hsource
      | append Q C _ hCA =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          exact False.elim (hCA hAB)
      | retained Q C _ hAC hweight' hcorrection' hinsert' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          omega
      | residual Q C _ hAC hweight' hinsert' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          rcases ihinsert hinsert' with
            ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩

/--
Traced cutoff collection has a unique endpoint and a unique ordered retained
correction trace.
-/
lemma collects_retained_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R leftCorrections rightEndpoint rightCorrections :
      List (DFTerm M N K)}
    (hleft :
      CCCorrec
        n leftWeight rightWeight L R leftCorrections)
    (hright :
      CCCorrec
        n leftWeight rightWeight L rightEndpoint rightCorrections) :
    R = rightEndpoint ∧
      leftCorrections = rightCorrections := by
  induction hleft generalizing rightEndpoint rightCorrections with
  | nil =>
      generalize hsource : ([] : List (DFTerm M N K)) = source at hright
      cases hright with
      | nil =>
          exact ⟨rfl, rfl⟩
      | retained P A hweight hcollect hinsert =>
          simp at hsource
      | residual P A hweight hcollect =>
          simp at hsource
  | retained P A hweight hcollect hinsert ihcollect =>
      generalize hsource : P ++ [A] = source at hright
      cases hright with
      | nil =>
          simp at hsource
      | retained Q B hweight' hcollect' hinsert' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          rcases ihcollect hcollect' with
            ⟨rfl, rfl⟩
          rcases inserts_retained_corrections
              hinsert hinsert' with
            ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      | residual Q B hweight' hcollect' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          omega
  | residual P A hweight hcollect ihcollect =>
      generalize hsource : P ++ [A] = source at hright
      cases hright with
      | nil =>
          simp at hsource
      | retained Q B hweight' hcollect' hinsert' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          omega
      | residual Q B hweight' hcollect' =>
          rcases
              eq_and_eq hsource with
            ⟨rfl, rfl⟩
          exact ihcollect hcollect'

end DFTerm

end
  IDBounda
end TCTex
end Submission

/-!
# Canonical local scalar semantics for the cutoff-full collector

The retained-correction collector relation is deterministic, and its
well-founded insertion measure works without a below-cutoff hypothesis on the
initial inserted term: only a recursively retained correction needs that
hypothesis, and its strict cutoff bound implies it automa.

This file constructs unconditional selected traced insertion and collection
runs, uses their correction traces as proof-free scalar evaluators, proves the
local-model equations, and reduces the arbitrary-cutoff symbolic comparison to
equality with this canonical scalar semantics on the inverse-raw source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  MLModel

universe u

open
  HACoeff
open
  BRSpec
open
  MIKern
open
  RLModel
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRLayer
open
  CRInv
open
  CRInv.DFTerm
open
  IDBounda
open
  IDBounda.DFTerm
open
  FIProf
open
  FCTermin
open
  CCAggreg
open
  OCPartit
open
  RTProgra

namespace DFTerm

/--
One selected traced insertion run from an arbitrary finite prefix.
-/
structure SelectedInsertionCorrections
    {M N K n leftWeight rightWeight : ℕ}
    (L : List (DFTerm M N K))
    (A : DFTerm M N K) where
  endpoint :
    List (DFTerm M N K)
  corrections :
    List (DFTerm M N K)
  inserts :
    CICorrec
      n leftWeight rightWeight L A endpoint corrections

/--
Every finite prefix and inserted term supports a traced cutoff insertion run.

Unlike the older termination wrapper, this statement does not assume that the
initial inserted term lies below cutoff.  If a recursive correction is
retained, its strict cutoff bound and positive parent weight imply the bound
needed by the well-founded defect argument.
-/
lemma selected_insertion_corrections
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ∀ (L : List (DFTerm M N K))
      (A : DFTerm M N K),
      Nonempty
        (SelectedInsertionCorrections
          (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
          L A) := by
  intro L A
  refine
    (insertion_before_wf
      (M := M) (N := N) (K := K) n leftWeight rightWeight).induction
        (C := fun state =>
          Nonempty
            (SelectedInsertionCorrections
              (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
              state.1 state.2))
        (L, A) ?_
  rintro ⟨L, A⟩ ih
  rcases List.eq_nil_or_concat' L with rfl | ⟨P, B, rfl⟩
  · exact ⟨{
      endpoint := [A]
      corrections := []
      inserts := .nil A }⟩
  · by_cases hBA : B.decorated.collectorLe A.decorated
    · exact ⟨{
        endpoint := P ++ [B, A]
        corrections := []
        inserts := .append P B A hBA }⟩
    · have hAB :
          A.decorated.collectorBefore B.decorated := by
        simpa [DTerm.collectorLe] using hBA
      by_cases hcorrectionWeight :
          decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) < n
      · have hAweight :
            decoratedFamilyWeight leftWeight rightWeight A < n := by
          have hBpositive :
              0 < decoratedFamilyWeight leftWeight rightWeight B :=
            weighted_weight_pos hleftWeight hrightWeight B.family.recipe
          rw [decorated_family_correction] at hcorrectionWeight
          omega
        rcases
            ih (P, B.correction A)
              (insertion_before_correction
                hleftWeight hrightWeight P B A hAweight hcorrectionWeight) with
          ⟨left⟩
        rcases
            ih (left.endpoint, A)
              (insertion_before_after
                P hAB left.inserts.cutoffInserts) with
          ⟨right⟩
        exact ⟨{
          endpoint := right.endpoint ++ [B]
          corrections :=
            left.corrections ++ [B.correction A] ++ right.corrections
          inserts :=
            .retained P B A hAB hcorrectionWeight
              left.inserts right.inserts }⟩
      · have hcorrectionWeightGe :
            n ≤ decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) :=
          Nat.le_of_not_gt hcorrectionWeight
        rcases
            ih (P, A)
              (insertion_state_before P B A hAB) with
          ⟨next⟩
        exact ⟨{
          endpoint := next.endpoint ++ [B]
          corrections := next.corrections
          inserts :=
            .residual P B A hAB hcorrectionWeightGe next.inserts }⟩

/--
Canonical selected traced insertion run.
-/
noncomputable def selectedInsertionCorrections
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K))
    (A : DFTerm M N K) :
    SelectedInsertionCorrections
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      L A :=
  Classical.choice
    (selected_insertion_corrections
      hleftWeight hrightWeight L A)

/--
The selected insertion trace agrees with every traced insertion derivation
from the same problem.
-/
lemma corrections_selected_insertion
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    (selectedInsertionCorrections
      (n := n)
      hleftWeight hrightWeight L A).corrections =
        corrections :=
  (inserts_retained_corrections
    (selectedInsertionCorrections
      (n := n)
      hleftWeight hrightWeight L A).inserts
    hinsert).2

/--
One selected traced collection run from an arbitrary finite source list.
-/
structure SelectedCollectionCorrections
    {M N K n leftWeight rightWeight : ℕ}
    (L : List (DFTerm M N K)) where
  endpoint :
    List (DFTerm M N K)
  corrections :
    List (DFTerm M N K)
  collects :
    CCCorrec
      n leftWeight rightWeight L endpoint corrections

/--
Every finite list admits a selected traced cutoff collection run.
-/
lemma nonempty_selected_corrections
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ∀ L : List (DFTerm M N K),
      Nonempty
        (SelectedCollectionCorrections
          (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
          L) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
      exact ⟨{
        endpoint := []
        corrections := []
        collects := .nil }⟩
  | append_singleton P A ih =>
      rcases ih with ⟨collect⟩
      by_cases hA :
          decoratedFamilyWeight leftWeight rightWeight A < n
      · let insert :=
          selectedInsertionCorrections
            (n := n)
            hleftWeight hrightWeight collect.endpoint A
        exact ⟨{
          endpoint := insert.endpoint
          corrections := collect.corrections ++ insert.corrections
          collects :=
            .retained P A hA collect.collects insert.inserts }⟩
      · exact ⟨{
          endpoint := collect.endpoint
          corrections := collect.corrections
          collects :=
            .residual P A (Nat.le_of_not_gt hA) collect.collects }⟩

/--
Canonical selected traced collection run.
-/
noncomputable def selectedCollectionCorrections
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) :
    SelectedCollectionCorrections
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      L :=
  Classical.choice
    (nonempty_selected_corrections
      hleftWeight hrightWeight L)

/--
The selected collection trace agrees with every traced collection derivation
from the same source list.
-/
lemma corrections_selected_collection
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    (selectedCollectionCorrections
      (n := n)
      hleftWeight hrightWeight L).corrections =
        corrections :=
  (collects_retained_corrections
    (selectedCollectionCorrections
      (n := n)
      hleftWeight hrightWeight L).collects
    hcollect).2

/--
Canonical proof-free insertion multiplicity for one erased Hall shape.
-/
noncomputable def canonicalInsertionMultiplicity
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (L : List (DFTerm M N K))
    (A : DFTerm M N K) :
    ℕ :=
  (erasedShapeTrace
    (selectedInsertionCorrections
      (n := n)
      hleftWeight hrightWeight L A).corrections).count word

/--
Canonical proof-free collection multiplicity for one erased Hall shape.
-/
noncomputable def canonicalCollectionMultiplicity
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (L : List (DFTerm M N K)) :
    ℕ :=
  (erasedShapeTrace
    (selectedCollectionCorrections
      (n := n)
      hleftWeight hrightWeight L).corrections).count word

/--
The canonical proof-free multiplicities satisfy every local collector
equation.
-/
noncomputable def canonicalMultiplicityModel
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom) :
    EMModel
      (M := M) (N := N) (K := K)
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      word where
  insertion :=
    fun L A =>
      canonicalInsertionMultiplicity
        (n := n) hleftWeight hrightWeight word L A
  collection :=
    fun L =>
      canonicalCollectionMultiplicity
        (n := n) hleftWeight hrightWeight word L
  insertion_nil A := by
    unfold canonicalInsertionMultiplicity
    rw [
      corrections_selected_insertion
        hleftWeight hrightWeight (.nil A)]
    rfl
  insertion_append P B A hBA := by
    unfold canonicalInsertionMultiplicity
    rw [
      corrections_selected_insertion
        hleftWeight hrightWeight (.append P B A hBA)]
    rfl
  insertion_retained P B A hAB hweight Q R leftCorrections
      rightCorrections hcorrection hinsert := by
    unfold canonicalInsertionMultiplicity
    rw [
      corrections_selected_insertion
        hleftWeight hrightWeight
          (.retained P B A hAB hweight hcorrection hinsert),
      corrections_selected_insertion
        hleftWeight hrightWeight hcorrection,
      corrections_selected_insertion
        hleftWeight hrightWeight hinsert]
    simp [erasedShapeTrace, List.count_append, List.count_cons]
    omega
  insertion_residual P B A hAB hweight R corrections hinsert := by
    unfold canonicalInsertionMultiplicity
    rw [
      corrections_selected_insertion
        hleftWeight hrightWeight
          (.residual P B A hAB hweight hinsert),
      corrections_selected_insertion
        hleftWeight hrightWeight hinsert]
  collection_nil := by
    unfold canonicalCollectionMultiplicity
    rw [
      corrections_selected_collection
        hleftWeight hrightWeight .nil]
    rfl
  collection_retained P A hweight C R collectCorrections
      insertCorrections hcollect hinsert := by
    unfold canonicalCollectionMultiplicity
    unfold canonicalInsertionMultiplicity
    rw [
      corrections_selected_collection
        hleftWeight hrightWeight
          (.retained P A hweight hcollect hinsert),
      corrections_selected_collection
        hleftWeight hrightWeight hcollect,
      corrections_selected_insertion
        hleftWeight hrightWeight hinsert]
    simp [erasedShapeTrace, List.count_append]
  collection_residual P A hweight C corrections hcollect := by
    unfold canonicalCollectionMultiplicity
    rw [
      corrections_selected_collection
        hleftWeight hrightWeight
          (.residual P A hweight hcollect),
      corrections_selected_collection
        hleftWeight hrightWeight hcollect]

end DFTerm

/--
Reduced arbitrary-cutoff target: identify the guarded symbolic sum with the
canonical proof-free concrete collection multiplicity on the inverse-raw
source.
-/
structure
    GMModel
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  branch_recurrence_collection :
    ∀ M N word,
      guardedBranchRecurrence
          raw M N word =
        DFTerm.canonicalCollectionMultiplicity
          (n := n)
          hleftWeight hrightWeight word
          (inverseDecoratedTerms M N)

namespace
  GMModel

/--
Compile canonical concrete scalar equality to the local-model endpoint kernel.
-/
noncomputable def
    idxMultModel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMModel
        layer hleftWeight hrightWeight) :
    PMModel
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  localModel M N word :=
    DFTerm.canonicalMultiplicityModel
      hleftWeight hrightWeight word
  branch_sum_collection M N word := by
    simpa [
      DFTerm.canonicalMultiplicityModel] using
        kernel.branch_recurrence_collection M N word

/--
Compile canonical concrete scalar equality directly to endpoint
interpolation.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMModel
        layer hleftWeight hrightWeight) :=
  kernel.idxMultModel
    |>.fiberProfileInterpolation

end
  GMModel

end
  MLModel
end TCTex
end Submission

/-!
# Semantic exactness of canonical cutoff-full collector multiplicities

The canonical proof-free scalar evaluators selected by the cutoff-full collector
compute the correction trace of every traced derivation from the same problem.
Consequently, they compute the erased-shape multiplicity of every recursively
compiled concrete schedule.

At the inverse-raw endpoint this identifies the canonical collection
multiplicity with the earlier provenance-selected concrete schedule
multiplicity.  Thus the canonical arbitrary-cutoff comparison target is
equivalent to the earlier concrete-schedule target while exposing a genuine
list evaluator with local collector equations.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  MSExactn

open
  HACoeff
open
  MIKern
open
  RMRec
open
  RMRec.RSPrograa
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  PRCompb
open
  RLModel
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRLayer
open
  CRInv
open
  CRInv.DFTerm
open
  MLModel
open
  MLModel.DFTerm
open
  OCPartit
open
  RTProgra

/--
The canonical insertion evaluator is the literal correction-trace count of
every traced insertion run from the same problem.
-/
lemma insertion_multiplicity_count
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    canonicalInsertionMultiplicity
        (n := n)
        hleftWeight hrightWeight word L A =
      (erasedShapeTrace corrections).count word := by
  unfold canonicalInsertionMultiplicity
  rw [
    corrections_selected_insertion
      hleftWeight hrightWeight hinsert]

/--
The canonical collection evaluator is the literal correction-trace count of
every traced collection run from the same source list.
-/
lemma canonical_multiplicity_count
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    canonicalCollectionMultiplicity
        (n := n)
        hleftWeight hrightWeight word L =
      (erasedShapeTrace corrections).count word := by
  unfold canonicalCollectionMultiplicity
  rw [
    corrections_selected_collection
      hleftWeight hrightWeight hcollect]

/--
The canonical insertion evaluator computes the erased-shape multiplicity of
every recursively compiled concrete insertion schedule.
-/
lemma insertion_mult_compiles
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      RSPrograa.CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program) :
    canonicalInsertionMultiplicity
        (n := n)
        hleftWeight hrightWeight word L A =
      RSPrograa.erasedShapeMultiplicity
        program word := by
  rw [
    insertion_multiplicity_count
      hleftWeight hrightWeight word hinsert]
  exact
    (RSPrograa.mult_inserts_corrections
      hcompile word).symm

/--
The canonical collection evaluator computes the erased-shape multiplicity of
every recursively compiled concrete collection schedule.
-/
lemma collect_mult_compiles
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      RSPrograa.CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program) :
    canonicalCollectionMultiplicity
        (n := n)
        hleftWeight hrightWeight word L =
      RSPrograa.erasedShapeMultiplicity
        program word := by
  rw [
    canonical_multiplicity_count
      hleftWeight hrightWeight word hcollect]
  exact
    (RSPrograa.mult_collects_corrections
      hcompile word).symm

/--
On the inverse-raw source, canonical collection multiplicity is exactly the
multiplicity of the explicitly recursively compiled endpoint schedule.
-/
lemma collect_recursively_compiled
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    canonicalCollectionMultiplicity
        (n := n)
        hleftWeight hrightWeight word
        (inverseDecoratedTerms M N) =
      RSPrograa.erasedShapeMultiplicity
        (recursivelyCompiledConcrete
          layer M N).program word :=
  collect_mult_compiles
    hleftWeight hrightWeight word
    (recursivelyCompiledConcrete
      layer M N).compiles

/--
On the inverse-raw source, canonical collection multiplicity is also exactly
the multiplicity of the earlier provenance-selected endpoint schedule.
-/
lemma collect_mult_endpoint
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    canonicalCollectionMultiplicity
        (n := n)
        hleftWeight hrightWeight word
        (inverseDecoratedTerms M N) =
      RSPrograa.erasedShapeMultiplicity
        (endpointScheduleProgram
          layer M N).program word := by
  rw [
    collect_recursively_compiled
      layer hleftWeight hrightWeight M N word]
  unfold RSPrograa.erasedShapeMultiplicity
  rw [
    recursively_compiled_generated]

namespace
  GMInduct

/--
Convert the earlier concrete-schedule scalar comparison to the canonical
proof-free collection comparison.
-/
noncomputable def
    polyMultModel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMInduct
        layer hleftWeight hrightWeight) :
    GMModel
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_recurrence_collection M N word := by
    rw [
      kernel.branch_schedule_multiplicity M N word,
      ←
        collect_mult_endpoint
          layer hleftWeight hrightWeight M N word]

end
  GMInduct

namespace
  GMModel

/--
Convert the canonical proof-free collection comparison back to the earlier
concrete-schedule scalar comparison.
-/
noncomputable def
    scheduleMultInduction
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMModel
        layer hleftWeight hrightWeight) :
    GMInduct
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_schedule_multiplicity M N word := by
    rw [
      kernel.branch_recurrence_collection M N word,
      collect_mult_endpoint
        layer hleftWeight hrightWeight M N word]

end
  GMModel

/--
The canonical proof-free comparison target and the earlier concrete-schedule
comparison target are equivalent data.
-/
noncomputable def
    guardedMultInduction
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GMModel
        layer hleftWeight hrightWeight ≃
      GMInduct
        layer hleftWeight hrightWeight where
  toFun :=
    GMModel.scheduleMultInduction
  invFun :=
    GMInduct.polyMultModel
  left_inv kernel := by
    cases kernel
    rfl
  right_inv kernel := by
    cases kernel
    rfl

end
  MSExactn
end TCTex
end Submission

/-!
# Canonical multiplicity and guarded erased-shape expansion equivalence

The proof-free canonical collection evaluator on the inverse-raw source is the
count of the literal selected retained-correction shape trace.  Therefore the
canonical scalar arbitrary-cutoff target is equivalent to the structural
criterion that the flattened guarded polynomial-orbit expansion permutes to
that selected trace.

This exposes the remaining symbolic Hall collector theorem simultaneously as a
list permutation and as equality with an executable scalar evaluator.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  SEEquiv

open
  HACoeff
open
  PBMult
open
  MIKern
open
  PMCoales
open
  PRCompb
open
  CRLayer
open
  MLModel
open
  MLModel.DFTerm
open
  MSExactn
open
  FIProf
open
  GGErased
open
  SEAlg

/--
On the inverse-raw source, the canonical proof-free collection evaluator is
the multiplicity in the literal selected retained-correction shape trace.
-/
lemma collect_mult_erased
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    canonicalCollectionMultiplicity
        (n := n)
        hleftWeight hrightWeight word
        (inverseDecoratedTerms M N) =
      (selectedErasedShape layer M N).count word := by
  rw [
    collect_recursively_compiled
      layer hleftWeight hrightWeight M N word,
    recursively_compiled_program]

namespace
  GEDecomp

/--
Compile a guarded erased-shape trace permutation to equality with the
canonical proof-free collection evaluator.
-/
noncomputable def
    polyMultModel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GEDecomp
        layer hleftWeight hrightWeight) :
    GMModel
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  branch_recurrence_collection M N word := by
    rw [←
      guarded_idx_erased]
    rw [←
      count_guarded_erased]
    unfold guardedExpansionErased
    rw [(decomposition.shape_trace_perm M N).count_eq word]
    rw [←
      collect_mult_erased
        layer hleftWeight hrightWeight M N word]

end
  GEDecomp

namespace
  GMModel

/--
Recover the guarded erased-shape trace permutation from equality with the
canonical proof-free collection evaluator.
-/
noncomputable def
    guardedErasedDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMModel
        layer hleftWeight hrightWeight) :
    GEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  shape_trace_perm M N := by
    classical
    rw [List.perm_iff_count]
    intro word
    change
      (guardedExpansionErased
        kernel.raw M N).count word =
        (selectedErasedShape layer M N).count word
    rw [
      count_guarded_erased,
      guarded_idx_erased,
      kernel.branch_recurrence_collection M N word,
      collect_mult_erased
        layer hleftWeight hrightWeight M N word]

end
  GMModel

/--
Guarded erased-shape expansion permutations and canonical scalar comparison
kernels are equivalent data.
-/
noncomputable def
    guardedMultModel
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GEDecomp
        layer hleftWeight hrightWeight ≃
      GMModel
        layer hleftWeight hrightWeight where
  toFun :=
    GEDecomp.polyMultModel
  invFun :=
    GMModel.guardedErasedDecomp
  left_inv decomposition := by
    cases decomposition
    rfl
  right_inv kernel := by
    cases kernel
    rfl

/--
Through cutoff four, the canonical proof-free scalar comparison follows from
the empty guarded erased-shape expansion.
-/
noncomputable def
    correctionGuardedFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GMModel
      layer (by simp) (by simp) :=
  GEDecomp.polyMultModel
    (erasedNFour
      layer hhigh raw)

end
  SEEquiv
end TCTex
end Submission

/-!
# Layer-free canonical trace target for the cutoff-full collector

Determinism identifies the proof-free canonical selected collection run with
the retained-correction inventory selected from every natural recollection
layer.  In particular, its correction-shape trace is independent of that layer.

This file packages the remaining guarded polynomial-orbit comparison as a
layer-free permutation theorem: the flattened guarded expansion must permute to
the canonical selected collection trace on the inverse-raw source.  Once proved,
that single theorem supplies the older layer-indexed shape decomposition, the
canonical scalar comparison, and endpoint interpolation for every natural
recollection layer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  LFExp

open
  HACoeff
open
  PMCoales
open
  CFCollec
open
  CRLayer
open
  CRInv
open
  CRInv.DFTerm
open
  SEEquiv
open
  MLModel
open
  MLModel.DFTerm
open
  IDBounda.DFTerm
open
  FIProf
open
  RTProgra
open
  GGErased
open
  SEAlg

/--
Proof-free ordered erased-shape trace emitted by the canonical selected
cutoff-full collection run.
-/
noncomputable def canonicalCollectionErased
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) :
    List (CWord HPAtom) :=
  erasedShapeTrace
    (selectedCollectionCorrections
      (n := n)
      hleftWeight hrightWeight L).corrections

/--
Canonical scalar multiplicity is count in the canonical selected
correction-shape trace.
-/
lemma collection_multiplicity_count
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (L : List (DFTerm M N K)) :
    canonicalCollectionMultiplicity
        (n := n)
        hleftWeight hrightWeight word L =
      (canonicalCollectionErased
        (n := n)
        hleftWeight hrightWeight L).count word :=
  rfl

/--
The canonical selected collection run and every layer-selected endpoint
inventory have exactly the same endpoint and ordered correction list.
-/
lemma endpoint_corrections_inventory
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (selectedCollectionCorrections
        (n := n)
        hleftWeight hrightWeight
        (inverseDecoratedTerms M N)).endpoint =
          (layer.endpoint M N).factors ∧
      (selectedCollectionCorrections
        (n := n)
        hleftWeight hrightWeight
        (inverseDecoratedTerms M N)).corrections =
          (endpointCorrectionInventory layer M N).corrections :=
  collects_retained_corrections
    (selectedCollectionCorrections
      (n := n)
      hleftWeight hrightWeight
      (inverseDecoratedTerms M N)).collects
    (endpointCorrectionInventory layer M N
      |>.family_collects_corrections)

/--
The canonical proof-free correction-shape trace on the inverse-raw source is
the selected correction-shape trace attached to every natural recollection
layer.
-/
lemma collect_erased_shape
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    canonicalCollectionErased
        (n := n)
        hleftWeight hrightWeight
        (inverseDecoratedTerms M N) =
      selectedErasedShape layer M N := by
  unfold canonicalCollectionErased
  rw [
    (endpoint_corrections_inventory
      layer hleftWeight hrightWeight M N).2]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/--
Layer-free remaining structural target: the flattened guarded polynomial-orbit
expansion permutes to the proof-free canonical selected collection trace on
the inverse-raw source.
-/
structure
    GIExp
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  shape_trace_perm :
    ∀ M N,
      List.Perm
        (guardedExpansionErased
          raw M N)
        (canonicalCollectionErased
          (n := n)
          hleftWeight hrightWeight
          (inverseDecoratedTerms M N))

namespace
  GIExp

/--
Install the layer-free canonical trace permutation into any natural
recollection layer.
-/
noncomputable def
    guardedErasedDecomp
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIExp
        (n := n)
        hleftWeight hrightWeight)
    (layer : NRLayer n leftWeight rightWeight) :
    GEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  shape_trace_perm M N := by
    rw [←
      collect_erased_shape
        layer hleftWeight hrightWeight M N]
    simpa [
      guardedExpansionErased] using
        kernel.shape_trace_perm M N

/--
Install the layer-free trace permutation directly as equality with the
canonical proof-free scalar collection evaluator.
-/
noncomputable def
    polyMultModel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIExp
        (n := n)
        hleftWeight hrightWeight)
    (layer : NRLayer n leftWeight rightWeight) :
    GMModel
      layer hleftWeight hrightWeight :=
  SEEquiv.GEDecomp.polyMultModel
    (kernel.guardedErasedDecomp
      layer)

/--
The layer-free trace theorem compiles directly to endpoint interpolation for
every natural recollection layer.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIExp
        (n := n)
        hleftWeight hrightWeight)
    (layer : NRLayer n leftWeight rightWeight) :=
  kernel.polyMultModel
      layer
    |>.fiberProfileInterpolation

end
  GIExp

namespace
  GEDecomp

/--
Forget the layer wrapper from an erased-shape guarded expansion decomposition.
-/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GEDecomp
        layer hleftWeight hrightWeight) :
    GIExp
      (n := n)
      hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  shape_trace_perm M N := by
    rw [
      collect_erased_shape
        layer hleftWeight hrightWeight M N]
    simpa [
      guardedExpansionErased] using
        decomposition.shape_trace_perm M N

end
  GEDecomp

/--
For any chosen layer, the older erased-shape decomposition and the layer-free
canonical trace criterion are equivalent data.
-/
noncomputable def
    correctionGuardedKernel
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GEDecomp
        layer hleftWeight hrightWeight ≃
      GIExp
        (n := n)
        hleftWeight hrightWeight where
  toFun :=
    GEDecomp.guardedShapeExpansion
  invFun :=
    fun kernel =>
      kernel.guardedErasedDecomp
        layer
  left_inv decomposition := by
    cases decomposition
    rfl
  right_inv kernel := by
    cases kernel
    rfl

end
  LFExp
end TCTex
end Submission

/-!
# Layer-free canonical multiplicity kernel for the cutoff-full collector

The guarded symbolic branch sum and the proof-free canonical collection
evaluator do not depend on a chosen natural recollection endpoint.  This file
extracts their scalar comparison as a layer-free kernel and proves that it is
equivalent to the layer-free erased-shape trace permutation criterion.

A single layer-free kernel installs into every natural recollection layer and
therefore compiles to endpoint interpolation uniformly.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  LFKern

open
  HACoeff
open
  PBMult
open
  MIKern
open
  PMCoales
open
  CRLayer
open
  MLModel
open
  MLModel.DFTerm
open
  LFExp
open
  FIProf

/--
Layer-free scalar arbitrary-cutoff target: the guarded symbolic branch sum
equals the proof-free canonical collection multiplicity on the inverse-raw
source.
-/
structure
    GIMult
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  branch_recurrence_collection :
    ∀ M N word,
      guardedBranchRecurrence
          raw M N word =
        canonicalCollectionMultiplicity
          (n := n)
          hleftWeight hrightWeight word
          (inverseDecoratedTerms M N)

namespace
  GIExp

/--
Compile the layer-free trace permutation criterion to the layer-free scalar
comparison kernel.
-/
noncomputable def
    guardedErasedMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIExp
        (n := n)
        hleftWeight hrightWeight) :
    GIMult
      (n := n)
      hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_recurrence_collection M N word := by
    rw [←
      guarded_idx_erased]
    rw [←
      count_guarded_erased]
    rw [(kernel.shape_trace_perm M N).count_eq word]
    rw [←
      collection_multiplicity_count]

end
  GIExp

namespace
  GIMult

/--
Recover the layer-free trace permutation criterion from the layer-free scalar
comparison kernel.
-/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIMult
        (n := n)
        hleftWeight hrightWeight) :
    GIExp
      (n := n)
      hleftWeight hrightWeight where
  raw :=
    kernel.raw
  shape_trace_perm M N := by
    classical
    rw [List.perm_iff_count]
    intro word
    rw [
      count_guarded_erased,
      guarded_idx_erased,
      kernel.branch_recurrence_collection M N word,
      collection_multiplicity_count]

/--
Install a layer-free scalar kernel into any natural recollection layer.
-/
noncomputable def
    polyMultModel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIMult
        (n := n)
        hleftWeight hrightWeight)
    (layer : NRLayer n leftWeight rightWeight) :
    GMModel
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_recurrence_collection :=
    kernel.branch_recurrence_collection

/--
The layer-free scalar theorem compiles directly to endpoint interpolation for
every natural recollection layer.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIMult
        (n := n)
        hleftWeight hrightWeight)
    (layer : NRLayer n leftWeight rightWeight) :=
  kernel.polyMultModel
      layer
    |>.fiberProfileInterpolation

end
  GIMult

/--
The layer-free erased-shape trace criterion and layer-free scalar comparison
kernel are equivalent data.
-/
noncomputable def
    guardedRetainedMult
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GIExp
        (n := n)
        hleftWeight hrightWeight ≃
      GIMult
        (n := n)
        hleftWeight hrightWeight where
  toFun :=
    GIExp.guardedErasedMult
  invFun :=
    GIMult.guardedShapeExpansion
  left_inv kernel := by
    cases kernel
    rfl
  right_inv kernel := by
    cases kernel
    rfl

namespace
  GMModel

/--
Forget the endpoint-layer wrapper from a canonical scalar comparison kernel.
-/
noncomputable def
    guardedErasedMult
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMModel
        layer hleftWeight hrightWeight) :
    GIMult
      (n := n)
      hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_recurrence_collection :=
    kernel.branch_recurrence_collection

end
  GMModel

/--
For any chosen layer, the older canonical scalar wrapper and the layer-free
scalar kernel are equivalent data.
-/
noncomputable def
    correctionGuardedMult
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GMModel
        layer hleftWeight hrightWeight ≃
      GIMult
        (n := n)
        hleftWeight hrightWeight where
  toFun :=
    GMModel.guardedErasedMult
  invFun :=
    fun kernel =>
      kernel.polyMultModel
        layer
  left_inv kernel := by
    cases kernel
    rfl
  right_inv kernel := by
    cases kernel
    rfl

end
  LFKern
end TCTex
end Submission

/-!
# Ordered local equations for the canonical cutoff-full correction trace

The scalar canonical evaluator satisfies the local collector recurrence after
counting one Hall shape at a time.  This file records the stronger ordered
statement.  A trace-valued local model emits the literal correction list in the
recursive scheduler order:

* retained insertion emits the recursive left trace, the retained crossing,
  and the recursive right trace;
* residual insertion emits the recursive prefix trace;
* retained collection concatenates the preceding collection trace and the
  final insertion trace.

Determinism supplies a canonical proof-free instance.  These equations expose
the induction interface needed to compare a symbolic Hall collector directly
with the concrete cutoff scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  TLEquati

open
  HACoeff
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRInv
open
  CRInv.DFTerm
open
  MLModel
open
  MLModel.DFTerm
open
  LFExp
open
  OCPartit
open
  RTProgra

namespace DFTerm

/--
A proof-free ordered interpretation of the retained-correction collector.

The evaluator values depend only on the current list and inserted term.  The
fields assert the exact ordered trace equations at each concrete scheduler
constructor.
-/
structure CEModel
    {M N K n leftWeight rightWeight : ℕ} where
  insertion :
    List (DFTerm M N K) →
      DFTerm M N K →
        List (CWord HPAtom)
  collection :
    List (DFTerm M N K) →
      List (CWord HPAtom)
  insertion_nil :
    ∀ A : DFTerm M N K,
      insertion [] A = []
  insertion_append :
    ∀ (P : List (DFTerm M N K))
        (B A : DFTerm M N K),
      B.decorated.collectorLe A.decorated →
        insertion (P ++ [B]) A = []
  insertion_retained :
    ∀ (P : List (DFTerm M N K))
        (B A : DFTerm M N K),
      A.decorated.collectorBefore B.decorated →
        decoratedFamilyWeight leftWeight rightWeight (B.correction A) < n →
          ∀ {Q R leftCorrections rightCorrections :
              List (DFTerm M N K)},
            CICorrec
                n leftWeight rightWeight
                P (B.correction A) Q leftCorrections →
              CICorrec
                  n leftWeight rightWeight
                  Q A R rightCorrections →
                insertion (P ++ [B]) A =
                  insertion P (B.correction A) ++
                    [(B.correction A).family.recipe.erasedShape] ++
                      insertion Q A
  insertion_residual :
    ∀ (P : List (DFTerm M N K))
        (B A : DFTerm M N K),
      A.decorated.collectorBefore B.decorated →
        n ≤ decoratedFamilyWeight leftWeight rightWeight (B.correction A) →
          ∀ {R corrections : List (DFTerm M N K)},
            CICorrec
                n leftWeight rightWeight P A R corrections →
              insertion (P ++ [B]) A =
                insertion P A
  collection_nil :
    collection [] = []
  collection_retained :
    ∀ (P : List (DFTerm M N K))
        (A : DFTerm M N K),
      decoratedFamilyWeight leftWeight rightWeight A < n →
        ∀ {C R collectCorrections insertCorrections :
            List (DFTerm M N K)},
          CCCorrec
              n leftWeight rightWeight P C collectCorrections →
            CICorrec
                n leftWeight rightWeight C A R insertCorrections →
              collection (P ++ [A]) =
                collection P ++ insertion C A
  collection_residual :
    ∀ (P : List (DFTerm M N K))
        (A : DFTerm M N K),
      n ≤ decoratedFamilyWeight leftWeight rightWeight A →
        ∀ {C corrections : List (DFTerm M N K)},
          CCCorrec
              n leftWeight rightWeight P C corrections →
            collection (P ++ [A]) =
              collection P

namespace CEModel

/--
The local insertion equations fold to the literal ordered correction trace of
every traced insertion derivation.
-/
lemma insertion_erased_shape
    {M N K n leftWeight rightWeight : ℕ}
    (model :
      CEModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight))
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    model.insertion L A =
      erasedShapeTrace corrections := by
  induction hinsert with
  | nil A =>
      exact model.insertion_nil A
  | append P B A hBA =>
      exact model.insertion_append P B A hBA
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      rw [model.insertion_retained P B A hAB hweight hcorrection hinsert,
        ihcorrection, ihinsert]
      simp [erasedShapeTrace]
  | residual P B A hAB hweight hinsert ihinsert =>
      rw [model.insertion_residual P B A hAB hweight hinsert, ihinsert]

/--
The local collection equations fold to the literal ordered correction trace of
every traced collection derivation.
-/
lemma collection_erased_shape
    {M N K n leftWeight rightWeight : ℕ}
    (model :
      CEModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight))
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    model.collection L =
      erasedShapeTrace corrections := by
  induction hcollect with
  | nil =>
      exact model.collection_nil
  | retained P A hweight hcollect hinsert ihcollect =>
      rw [model.collection_retained P A hweight hcollect hinsert,
        ihcollect, model.insertion_erased_shape hinsert]
      simp [erasedShapeTrace]
  | residual P A hweight hcollect ihcollect =>
      rw [model.collection_residual P A hweight hcollect, ihcollect]

end CEModel

/--
Proof-free ordered erased-shape trace emitted by the canonical selected
cutoff-full insertion run.
-/
noncomputable def canonicalInsertionErased
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K))
    (A : DFTerm M N K) :
    List (CWord HPAtom) :=
  erasedShapeTrace
    (selectedInsertionCorrections
      (n := n)
      hleftWeight hrightWeight L A).corrections

/--
The canonical insertion trace agrees with every traced insertion run from the
same source list and inserted term.
-/
lemma canonical_insertion_erased
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    canonicalInsertionErased
        (n := n)
        hleftWeight hrightWeight L A =
      erasedShapeTrace corrections := by
  unfold canonicalInsertionErased
  rw [
    corrections_selected_insertion
      hleftWeight hrightWeight hinsert]

/--
The canonical collection trace agrees with every traced collection run from
the same source list.
-/
lemma canonical_collection_erased
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    canonicalCollectionErased
        (n := n)
        hleftWeight hrightWeight L =
      erasedShapeTrace corrections := by
  unfold canonicalCollectionErased
  rw [
    corrections_selected_collection
      hleftWeight hrightWeight hcollect]

/--
The canonical proof-free ordered traces satisfy every local collector equation.
-/
noncomputable def canonicalErasedModel
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    CEModel
      (M := M) (N := N) (K := K)
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight) where
  insertion :=
    canonicalInsertionErased
      (n := n) hleftWeight hrightWeight
  collection :=
    canonicalCollectionErased
      (n := n) hleftWeight hrightWeight
  insertion_nil A :=
    canonical_insertion_erased
      hleftWeight hrightWeight (.nil A)
  insertion_append P B A hBA :=
    canonical_insertion_erased
      hleftWeight hrightWeight (.append P B A hBA)
  insertion_retained P B A hAB hweight Q R leftCorrections
      rightCorrections hcorrection hinsert := by
    rw [
      canonical_insertion_erased
        hleftWeight hrightWeight
          (.retained P B A hAB hweight hcorrection hinsert),
      canonical_insertion_erased
        hleftWeight hrightWeight hcorrection,
      canonical_insertion_erased
        hleftWeight hrightWeight hinsert]
    simp [erasedShapeTrace]
  insertion_residual P B A hAB hweight R corrections hinsert := by
    rw [
      canonical_insertion_erased
        hleftWeight hrightWeight
          (.residual P B A hAB hweight hinsert),
      canonical_insertion_erased
        hleftWeight hrightWeight hinsert]
  collection_nil :=
    canonical_collection_erased
      hleftWeight hrightWeight .nil
  collection_retained P A hweight C R collectCorrections
      insertCorrections hcollect hinsert := by
    rw [
      canonical_collection_erased
        hleftWeight hrightWeight
          (.retained P A hweight hcollect hinsert),
      canonical_collection_erased
        hleftWeight hrightWeight hcollect,
      canonical_insertion_erased
        hleftWeight hrightWeight hinsert]
    simp [erasedShapeTrace]
  collection_residual P A hweight C corrections hcollect := by
    rw [
      canonical_collection_erased
        hleftWeight hrightWeight
          (.residual P A hweight hcollect),
      canonical_collection_erased
        hleftWeight hrightWeight hcollect]

end DFTerm

end
  TLEquati
end TCTex
end Submission

/-!
# Layer-free canonical concrete schedules for the cutoff-full collector

The existing endpoint schedule packages are indexed by a chosen natural
recollection layer.  Deterministic canonical collection makes that layer
unnecessary.  This file recursively compiles the proof-free canonical selected
run from any source list into a concrete schedule carrying:

* the constructor-level compilation derivation;
* its exact ordered correction trace;
* provenance of every retained crossing from the original source list.

For inverse-raw sources, this gives a layer-free constructor-induction target
for the guarded symbolic scheduler.  Structural coalescing with that canonical
schedule compiles directly to the layer-free canonical trace theorem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  SLFree

open
  HACoeff
open
  RPCoales
open
  RPCrit
open
  RPCrit.SPCrit
open
  PMCoales
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  PRCompb
open
  RCProven
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRInv
open
  CRInv.DFTerm
open
  MLModel
open
  MLModel.DFTerm
open
  LFExp
open
  TLEquati
open
  FIProf
open
  ISLift
open
  RTProgra
open
  GRProgra

/--
One constructor-level concrete schedule recursively compiled from the canonical
selected collection run on an arbitrary source list.
-/
structure RecursivelyCompiledProgram
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) where
  program :
    RSPrograa
      (M := M) (N := N) (K := K) n leftWeight rightWeight
  compiles :
    RSPrograa.CompilesCollectsCorrections
      n leftWeight rightWeight
      (selectedCollectionCorrections
        (n := n) hleftWeight hrightWeight L).collects
      program
  correctionTrace_eq :
    program.correctionTrace =
      (selectedCollectionCorrections
        (n := n) hleftWeight hrightWeight L).corrections
  crossings_generated :
    CGFroma L program

/--
Select the canonical recursively compiled concrete schedule from the canonical
traced collection derivation.
-/
noncomputable def
    recursivelyCompiledGenerated
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) :
    RecursivelyCompiledProgram
      (n := n) hleftWeight hrightWeight L :=
  let hcollect :=
    (selectedCollectionCorrections
      (n := n) hleftWeight hrightWeight L).collects
  let hexists :=
    RSPrograa.compiles_collects_corrections
      hcollect
  let program :=
    Classical.choose hexists
  let hcompile :=
    Classical.choose_spec hexists
  {
    program := program
    compiles := hcompile
    correctionTrace_eq :=
      RSPrograa.correction_collects_corrections
        hcompile
    crossings_generated :=
      RSPrograa.crossings_compiles_corrections
        hcompile
  }

/--
The canonical recursively compiled schedule emits exactly the canonical
proof-free ordered collection trace.
-/
lemma
    erasedRecursivelyProgram
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) :
    (recursivelyCompiledGenerated
      (n := n) hleftWeight hrightWeight L).program.shapeTraceProgram.trace =
        canonicalCollectionErased
          (n := n) hleftWeight hrightWeight L := by
  rw [
    RSPrograa.trace_erased_shape,
    (recursivelyCompiledGenerated
      (n := n) hleftWeight hrightWeight L).correctionTrace_eq]
  rfl

/--
Every crossing in the canonical recursively compiled schedule is generated
from its source list.
-/
lemma
    crossingsRecursivelyCompiled
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) :
    CGFroma L
      (recursivelyCompiledGenerated
        (n := n) hleftWeight hrightWeight L).program :=
  (recursivelyCompiledGenerated
    (n := n) hleftWeight hrightWeight L).crossings_generated

/--
Layer-free constructor-level arbitrary-cutoff target.  The guarded symbolic
scheduler structurally coalesces with the recursively compiled canonical
concrete schedule on the inverse-raw source.
-/
structure
    GICoales
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  program_coalesces_schedule :
    ∀ M N,
      MCSched
        (guardedSchedulerProgram
          (multiplicityProfileShape raw)
          M N)
        (recursivelyCompiledGenerated
          (n := n) hleftWeight hrightWeight
          (inverseDecoratedTerms M N)).program

namespace
  GICoales

/--
Compile layer-free constructor-level coalescing to the layer-free canonical
trace theorem.
-/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GICoales
        (n := n) hleftWeight hrightWeight) :
    GIExp
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  shape_trace_perm M N := by
    rw [←
      erasedRecursivelyProgram
        hleftWeight hrightWeight (inverseDecoratedTerms M N)]
    exact
      (idxSchedulerProgram
        kernel.raw M N).trans
          (kernel.program_coalesces_schedule M N).trace_perm

/--
Compile layer-free constructor-level coalescing to endpoint interpolation for
any natural recollection layer.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GICoales
        (n := n) hleftWeight hrightWeight)
    (layer :
      CRLayer.NRLayer
        n leftWeight rightWeight) :=
  kernel.guardedShapeExpansion
    |>.fiberProfileInterpolation layer

end
  GICoales

namespace
  GIExp

/--
Recover layer-free constructor-level coalescing from the layer-free canonical
trace theorem.  Structural coalescing is complete for trace permutations.
-/
noncomputable def
    guardedCollectCoalescing
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIExp
        (n := n) hleftWeight hrightWeight) :
    GICoales
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  program_coalesces_schedule M N := by
    apply coalesces_perm
    rw [
      erasedRecursivelyProgram
        hleftWeight hrightWeight (inverseDecoratedTerms M N)]
    exact
      (idxSchedulerProgram
        kernel.raw M N).symm.trans
          (kernel.shape_trace_perm M N)

end
  GIExp

/--
The layer-free canonical trace theorem and layer-free constructor-level
coalescing criterion are equivalent data.
-/
noncomputable def
    guardedIdxCoalescing
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GIExp
        (n := n) hleftWeight hrightWeight ≃
      GICoales
        (n := n) hleftWeight hrightWeight where
  toFun :=
    GIExp.guardedCollectCoalescing
  invFun :=
    GICoales.guardedShapeExpansion
  left_inv kernel := by
    cases kernel
    rfl
  right_inv kernel := by
    cases kernel
    rfl

end
  SLFree
end TCTex
end Submission

/-!
# Layer-free guarded-grid coverage for the canonical concrete schedule

The generic guarded-grid coverage compiler applies to every concrete schedule
whose crossings are generated from the inverse-raw source.  The layer-free
canonical recursively compiled schedule has exactly that provenance.

This file instantiates the generic compiler.  Every concrete crossing in the
canonical schedule determines a guarded symbolic branch, every selected branch
lies in the canonical guarded grid, and erasing the selected correction-root
indices recovers the canonical ordered correction trace exactly.

Thus the remaining arbitrary-cutoff theorem is an occurrence-accounting
statement, not a support statement.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  CLFree

open
  HACoeff
open
  RRPkt
open
  CRAlign
open
  CGCovera
open
  EGCovera
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  CFCollec
open
  SLFree
open
  LFExp
open
  FIProf
open
  RITrace
open
  PGSrc
open
  ESIdx

/--
The canonical recursively compiled concrete schedule specialized to the
inverse-raw source.
-/
noncomputable def
    inverseRecursivelyCompiled
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    RecursivelyCompiledProgram
      (n := n) hleftWeight hrightWeight (inverseDecoratedTerms M N) :=
  recursivelyCompiledGenerated
    (n := n) hleftWeight hrightWeight (inverseDecoratedTerms M N)

/--
The inverse-raw canonical schedule emits exactly the layer-free canonical
ordered collection trace.
-/
lemma
    erasedScheduleProgram
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (inverseRecursivelyCompiled
      (n := n) hleftWeight hrightWeight M N).program.shapeTraceProgram.trace =
        canonicalCollectionErased
          (n := n) hleftWeight hrightWeight
          (inverseDecoratedTerms M N) :=
  erasedRecursivelyProgram
    hleftWeight hrightWeight (inverseDecoratedTerms M N)

/--
Every crossing in the inverse-raw canonical schedule is generated from the
inverse-raw source.
-/
lemma
    crossingsRecursivelyProgram
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    CGFroma (inverseDecoratedTerms M N)
      (inverseRecursivelyCompiled
        (n := n) hleftWeight hrightWeight M N).program :=
  (inverseRecursivelyCompiled
    (n := n) hleftWeight hrightWeight M N).crossings_generated

/--
Canonical guarded branch represented by one crossing of the layer-free
inverse-raw canonical schedule.
-/
noncomputable def
    gridBranchCrossing
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hcrossing :
      crossing ∈
        (inverseRecursivelyCompiled
          (n := n) hleftWeight hrightWeight M N).program.crossings) :
    IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight :=
  guardedBranchCrossing
    hleftWeight hrightWeight
    (inverseRecursivelyCompiled
      (n := n) hleftWeight hrightWeight M N).program
    (crossingsRecursivelyProgram
      hleftWeight hrightWeight M N)
    crossing hcrossing

/--
Every canonical concrete crossing branch belongs to the guarded symbolic grid.
-/
lemma
    branchIdxBranches
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hcrossing :
      crossing ∈
        (inverseRecursivelyCompiled
          (n := n) hleftWeight hrightWeight M N).program.crossings) :
    gridBranchCrossing
        hleftWeight hrightWeight M N crossing hcrossing ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight :=
  guardedBranchBranches
    hleftWeight hrightWeight
    (inverseRecursivelyCompiled
      (n := n) hleftWeight hrightWeight M N).program
    (crossingsRecursivelyProgram
      hleftWeight hrightWeight M N)
    crossing hcrossing

/--
Ordered guarded branches selected by the crossings of the layer-free canonical
schedule.
-/
noncomputable def generatedGridBranches
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight) :=
  generatedGuardedBranches
    hleftWeight hrightWeight
    (inverseRecursivelyCompiled
      (n := n) hleftWeight hrightWeight M N).program
    (crossingsRecursivelyProgram
      hleftWeight hrightWeight M N)

/--
Every guarded branch selected by the canonical schedule is a member of the
full guarded symbolic root grid.
-/
lemma
    guarded_supported_branches
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight}
    (hbranch :
      branch ∈
        generatedGridBranches
          hleftWeight hrightWeight M N) :
    branch ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight := by
  unfold generatedGridBranches at hbranch
  unfold generatedGuardedBranches at hbranch
  rcases List.mem_map.mp hbranch with ⟨crossing, _hcrossing, rfl⟩
  exact
    guardedBranchBranches
      hleftWeight hrightWeight
      (inverseRecursivelyCompiled
        (n := n) hleftWeight hrightWeight M N).program
      (crossingsRecursivelyProgram
        hleftWeight hrightWeight M N)
      crossing.1 crossing.2

/--
Forgetting the canonical selected guarded branches recovers the literal
obstruction list of the canonical concrete schedule.
-/
lemma obstruction_grid_branches
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (generatedGridBranches
      (n := n) hleftWeight hrightWeight M N).map
        IOBranch.obstruction =
      polynomialOrbitObstructions
        (inverseRecursivelyCompiled
          (n := n) hleftWeight hrightWeight M N).program :=
  obstruction_guarded_branches
    hleftWeight hrightWeight
    (inverseRecursivelyCompiled
      (n := n) hleftWeight hrightWeight M N).program
    (crossingsRecursivelyProgram
      hleftWeight hrightWeight M N)

/--
Every obstruction emitted by the canonical concrete schedule is represented
exactly by a member of the guarded symbolic root grid.
-/
lemma
    guarded_schedule_program
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {obstruction : POObstru}
    (hobstruction :
      obstruction ∈
        polynomialOrbitObstructions
          (inverseRecursivelyCompiled
            (n := n) hleftWeight hrightWeight M N).program) :
    ∃ branch ∈
        guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight,
      branch.obstruction = obstruction := by
  rw [←
    obstruction_grid_branches
      hleftWeight hrightWeight M N] at hobstruction
  rcases List.mem_map.mp hobstruction with ⟨branch, hbranch, rfl⟩
  exact
    ⟨branch,
      guarded_supported_branches
        hleftWeight hrightWeight M N hbranch,
      rfl⟩

/--
Ordered compiler-selected correction-root indices attached to the canonical
concrete schedule.
-/
noncomputable def
    generatedGridBranch
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  generatedGuardedBranch
    hleftWeight hrightWeight
    (inverseRecursivelyCompiled
      (n := n) hleftWeight hrightWeight M N).program
    (crossingsRecursivelyProgram
      hleftWeight hrightWeight M N)

/--
Erasing canonical guarded root indices recovers the layer-free canonical
ordered correction trace exactly.
-/
lemma
    key_erased_trace
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (generatedGridBranch
      (n := n) hleftWeight hrightWeight M N).map (fun index =>
        (retainedOrbitKey index).erasedShape) =
      canonicalCollectionErased
        (n := n) hleftWeight hrightWeight
        (inverseDecoratedTerms M N) := by
  unfold
    generatedGridBranch
  rw [
    key_branch_program,
    erasedScheduleProgram]

end
  CLFree
end TCTex
end Submission

/-!
# Layer-free occurrence synchronization for the canonical concrete schedule

The proof-free canonical cutoff-full collection run already compiles to a
constructor-level concrete retained-correction schedule.  This file attaches
the cutoff-aware occurrence rewrite run extracted from that same selected
collector derivation.

For inverse-raw sources, the resulting certificate simultaneously carries:

* recursive compilation of the canonical concrete schedule;
* provenance of every retained parent crossing from the inverse-raw source;
* the exact ordered canonical correction trace;
* a literal cutoff-aware occurrence run to the canonical endpoint.

The inverse-raw specialization also exposes the parent-pair operational rewrite
and pairs the occurrence run with the guarded-grid root-index trace.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  SLFreea

universe u

open scoped commutatorElement

open
  HACoeff
open
  EGCovera
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  TOSync
open
  CFCollec
open
  CFCollec.DFTerm
open
  FCEnd
open
  FCEnd.IDTerms
open
  CRInv
open
  CRInv.DFTerm
open
  CLFree
open
  SLFree
open
  MLModel
open
  MLModel.DFTerm
open
  LFExp
open
  RITrace
open
  PTOcc
open
  PCBridge

/--
One layer-free canonical recursively compiled schedule together with the
cutoff-aware occurrence run extracted from the same selected collection
derivation.
-/
structure
    RCCert
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K))
    (x y : G) where
  schedule :
    RecursivelyCompiledProgram
      (n := n) hleftWeight hrightWeight L
  rewrites :
    TORwa
      (collapsedEvaluatedFactors x y L)
      (collapsedEvaluatedFactors x y
        (selectedCollectionCorrections
          (n := n) hleftWeight hrightWeight L).endpoint)

/--
Construct the layer-free synchronized certificate from the canonical selected
collection derivation.
-/
noncomputable def
    recursivelyCompiledCertificate
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K))
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    RCCert
      (n := n) hleftWeight hrightWeight L x y where
  schedule :=
    recursivelyCompiledGenerated
      (n := n) hleftWeight hrightWeight L
  rewrites :=
    DFTerm.CCollec.truncatedOccurrenceRewrites
      hleftWeight hrightWeight hx hy hbot
        (selectedCollectionCorrections
          (n := n) hleftWeight hrightWeight L).collects.cutoffCollects

namespace
  RCCert

/--
Forget recursive compilation while retaining the synchronized occurrence
certificate.
-/
noncomputable def
    collectsOccurrenceCertificate
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {L : List (DFTerm M N K)}
    {x y : G}
    (certificate :
      RCCert
        (n := n) hleftWeight hrightWeight L x y) :
    COCert
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      L
      (selectedCollectionCorrections
        (n := n) hleftWeight hrightWeight L).endpoint
      (selectedCollectionCorrections
        (n := n) hleftWeight hrightWeight L).corrections
      x y where
  program :=
    certificate.schedule.program
  correctionTrace_eq :=
    certificate.schedule.correctionTrace_eq
  crossings_generated :=
    certificate.schedule.crossings_generated
  rewrites :=
    certificate.rewrites

/--
The synchronized canonical schedule emits exactly the proof-free ordered
canonical correction trace.
-/
lemma program_collection_correction
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {L : List (DFTerm M N K)}
    {x y : G}
    (certificate :
      RCCert
        (n := n) hleftWeight hrightWeight L x y) :
    certificate.schedule.program.shapeTraceProgram.trace =
      canonicalCollectionErased
        (n := n) hleftWeight hrightWeight L := by
  rw [
    RSPrograa.trace_erased_shape,
    certificate.schedule.correctionTrace_eq]
  rfl

/--
Every crossing in the synchronized canonical schedule is generated from its
source list.
-/
lemma crossingsGeneratedFrom
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {L : List (DFTerm M N K)}
    {x y : G}
    (certificate :
      RCCert
        (n := n) hleftWeight hrightWeight L x y) :
    CGFroma L certificate.schedule.program :=
  certificate.schedule.crossings_generated

end
  RCCert

/--
The canonical selected inverse-raw endpoint viewed as an ordinary cutoff-full
collected endpoint.
-/
noncomputable def collectedDecoratedTerms
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    IDTerms
      M N n leftWeight rightWeight where
  factors :=
    (selectedCollectionCorrections
      (n := n) hleftWeight hrightWeight
      (inverseDecoratedTerms M N)).endpoint
  family_cutoff_collects :=
    (selectedCollectionCorrections
      (n := n) hleftWeight hrightWeight
      (inverseDecoratedTerms M N)).collects.cutoffCollects

/--
Layer-free inverse-raw specialization of the synchronized canonical occurrence
certificate.
-/
noncomputable def
    recursivelyCompiledOcc
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    RCCert
      (n := n) hleftWeight hrightWeight
      (inverseDecoratedTerms M N) x y :=
  recursivelyCompiledCertificate
    hleftWeight hrightWeight (inverseDecoratedTerms M N)
      x y hx hy hbot

/--
Adjoining the powered parents turns the layer-free canonical inverse-raw
occurrence run into the natural parent-pair operational rewrite.
-/
lemma parent_occurrence_rewrites
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      RCCert
        (n := n) hleftWeight hrightWeight
        (inverseDecoratedTerms M N) x y)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y
          (collectedDecoratedTerms
            (n := n) hleftWeight hrightWeight M N).factors ++
        [y ^ N, x ^ M]) := by
  have hrawProd :
      (collapsedEvaluatedFactors x y
        (inverseDecoratedTerms M N)).prod =
          ⁅x ^ M, y ^ N⁆ := by
    calc
      (collapsedEvaluatedFactors x y
            (inverseDecoratedTerms M N)).prod =
          (collapsedEvaluatedFactors x y
            (collectedDecoratedTerms
              (n := n) hleftWeight hrightWeight M N).factors).prod :=
        certificate.rewrites.list_prod_eq.symm
      _ = ⁅x ^ M, y ^ N⁆ := by
        simpa [collapsedEvaluatedFactors, collapsedList] using
          (collectedDecoratedTerms
            (n := n) hleftWeight hrightWeight M N
              |>.collapsed_list_pow
                x y hleftWeight hrightWeight hx hy hbot)
  have hparents :
      CORw
        [x ^ M, y ^ N]
        (collapsedEvaluatedFactors x y
            (inverseDecoratedTerms M N) ++
          [y ^ N, x ^ M]) := by
    apply Relation.ReflTransGen.single
    simpa using
      (COStep.obstruction
        [] [] (x ^ M) (y ^ N)
        (collapsedEvaluatedFactors x y
          (inverseDecoratedTerms M N))
        (by
          rw [hrawProd]
          simp [commutatorElement_def, mul_assoc]))
  apply
    (TORwa.ofOccurrenceRewrites hparents).trans
  simpa using
    certificate.rewrites.context [] [y ^ N, x ^ M]

/--
The canonical inverse-raw occurrence run and the guarded-grid correction-root
encoding are available simultaneously from the same layer-free selected
schedule.
-/
lemma
    occurrence_rewrites_erasure
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    TORwa
        (collapsedEvaluatedFactors x y (inverseDecoratedTerms M N))
        (collapsedEvaluatedFactors x y
          (collectedDecoratedTerms
            (n := n) hleftWeight hrightWeight M N).factors) ∧
      (generatedGridBranch
        (n := n) hleftWeight hrightWeight M N).map (fun index =>
          (retainedOrbitKey index).erasedShape) =
        canonicalCollectionErased
          (n := n) hleftWeight hrightWeight
          (inverseDecoratedTerms M N) := by
  constructor
  · exact
      (recursivelyCompiledOcc
        hleftWeight hrightWeight M N x y hx hy hbot).rewrites
  · exact
      key_erased_trace
        hleftWeight hrightWeight M N

end
  SLFreea
end TCTex
end Submission

/-!
# Layer-free structural-coalescing local models for the canonical collector

The remaining arbitrary-cutoff Hall collector argument is an exact occurrence
accounting theorem.  A symbolic scheduler naturally proves that theorem by
assigning an erased-shape program to each insertion and collection problem and
checking one structural-coalescing equation for each collector constructor.

This file packages that local interface.  Its equations fold through every
constructor-level concrete schedule compilation.  Applied to the proof-free
canonical selected collector, they produce the layer-free structural-coalescing
target used by the polynomial pipeline.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  MLFree

open
  HACoeff
open
  RPCoales
open
  RPCoales.EMCoales
open
  PMCoales
open
  CRProgra
open
  PRCompb
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRInv
open
  CRInv.DFTerm
open
  SLFree
open
  LFExp
open
  FIProf
open
  OCPartit
open
  ISLift
open
  RTProgra
open
  GRProgra

/--
A proof-free program-valued interpretation of the retained-correction
collector.  Every local equation is structural coalescing, rather than merely
an equality of scalar Hall-shape counts.
-/
structure
    SCModel
    {M N K n leftWeight rightWeight : ℕ} where
  insertion :
    List (DFTerm M N K) →
      DFTerm M N K →
        ESProgra
  collection :
    List (DFTerm M N K) →
      ESProgra
  insertion_nil :
    ∀ A : DFTerm M N K,
      Rel (insertion [] A)
        ESProgra.empty
  insertion_append :
    ∀ (P : List (DFTerm M N K))
        (B A : DFTerm M N K),
      B.decorated.collectorLe A.decorated →
        Rel (insertion (P ++ [B]) A)
          ESProgra.empty
  insertion_retained :
    ∀ (P : List (DFTerm M N K))
        (B A : DFTerm M N K),
      A.decorated.collectorBefore B.decorated →
        decoratedFamilyWeight leftWeight rightWeight (B.correction A) < n →
          ∀ {Q R leftCorrections rightCorrections :
              List (DFTerm M N K)},
            CICorrec
                n leftWeight rightWeight
                P (B.correction A) Q leftCorrections →
              CICorrec
                  n leftWeight rightWeight
                  Q A R rightCorrections →
                Rel (insertion (P ++ [B]) A)
                  (ESProgra.retained
                    (insertion P (B.correction A))
                    (B.correction A).family.recipe.erasedShape
                    (insertion Q A))
  insertion_residual :
    ∀ (P : List (DFTerm M N K))
        (B A : DFTerm M N K),
      A.decorated.collectorBefore B.decorated →
        n ≤ decoratedFamilyWeight leftWeight rightWeight (B.correction A) →
          ∀ {R corrections : List (DFTerm M N K)},
            CICorrec
                n leftWeight rightWeight P A R corrections →
              Rel (insertion (P ++ [B]) A)
                (insertion P A)
  collection_nil :
    Rel (collection [])
      ESProgra.empty
  collection_retained :
    ∀ (P : List (DFTerm M N K))
        (A : DFTerm M N K),
      decoratedFamilyWeight leftWeight rightWeight A < n →
        ∀ {C R collectCorrections insertCorrections :
            List (DFTerm M N K)},
          CCCorrec
              n leftWeight rightWeight P C collectCorrections →
            CICorrec
                n leftWeight rightWeight C A R insertCorrections →
              Rel (collection (P ++ [A]))
                (ESProgra.append
                  (collection P) (insertion C A))
  collection_residual :
    ∀ (P : List (DFTerm M N K))
        (A : DFTerm M N K),
      n ≤ decoratedFamilyWeight leftWeight rightWeight A →
        ∀ {C corrections : List (DFTerm M N K)},
          CCCorrec
              n leftWeight rightWeight P C corrections →
            Rel (collection (P ++ [A]))
              (collection P)

namespace
  SCModel

/--
The local insertion equations fold through every recursively compiled traced
insertion schedule.
-/
lemma insertion_coalesces_compiles
    {M N K n leftWeight rightWeight : ℕ}
    (model :
      SCModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight))
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      RSPrograa.CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program) :
    MCSched
      (model.insertion L A) program := by
  induction hcompile with
  | nil A =>
      exact model.insertion_nil A
  | append P B A hBA =>
      exact model.insertion_append P B A hBA
  | retained P B A hAB hweight hcorrection hinsert
      hleft hright ihleft ihright =>
      exact
        (model.insertion_retained P B A hAB hweight hcorrection hinsert).trans
          (MCSched.retained
            B A hweight ihleft ihright)
  | residual P B A hAB hweight hinsert hprogram ihprogram =>
      exact
        (model.insertion_residual P B A hAB hweight hinsert).trans
          ihprogram

/--
The local collection equations fold through every recursively compiled traced
collection schedule.
-/
lemma collection_coalesces_compiles
    {M N K n leftWeight rightWeight : ℕ}
    (model :
      SCModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight))
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      RSPrograa.CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program) :
    MCSched
      (model.collection L) program := by
  induction hcompile with
  | nil =>
      exact model.collection_nil
  | retained P A hweight hcollect hinsert
      hcollectProgram hinsertProgram ihcollect =>
      exact
        (model.collection_retained P A hweight hcollect hinsert).trans
          (MCSched.append
            ihcollect
            (model.insertion_coalesces_compiles hinsertProgram))
  | residual P A hweight hcollect hprogram ihprogram =>
      exact
        (model.collection_residual P A hweight hcollect).trans
          ihprogram

/--
The local collection equations therefore coalesce with the layer-free
canonical recursively compiled schedule on every source list.
-/
lemma coalescesRecursivelyCompiled
    {M N K n leftWeight rightWeight : ℕ}
    (model :
      SCModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight))
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) :
    MCSched
      (model.collection L)
      (recursivelyCompiledGenerated
        (n := n) hleftWeight hrightWeight L).program :=
  model.collection_coalesces_compiles
    (recursivelyCompiledGenerated
      (n := n) hleftWeight hrightWeight L).compiles

end
  SCModel

/--
Layer-free local-equation form of the arbitrary-cutoff structural-coalescing
target.  A symbolic collector supplies one program-valued local model at each
natural input pair and identifies the guarded symbolic scheduler with that
model's inverse-raw collection program.
-/
structure
    GCModel
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  localModel :
    ∀ M N,
      SCModel
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
  coalesces_local_collection :
    ∀ M N,
      Rel
        (guardedSchedulerProgram
          (multiplicityProfileShape raw)
          M N)
        ((localModel M N).collection (inverseDecoratedTerms M N))

namespace
  GCModel

/--
Fold local structural equations through the canonical recursive compiler to
obtain the layer-free constructor-level coalescing target.
-/
noncomputable def
    guardedCollectCoalescing
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GCModel
        (n := n) hleftWeight hrightWeight) :
    GICoales
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  program_coalesces_schedule M N :=
    (kernel.coalesces_local_collection M N).trans
      ((kernel.localModel M N)
        |>.coalescesRecursivelyCompiled
          hleftWeight hrightWeight (inverseDecoratedTerms M N))

/--
Compile local structural equations directly to layer-free canonical trace
expansion.
-/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GCModel
        (n := n) hleftWeight hrightWeight) :
    GIExp
      (n := n) hleftWeight hrightWeight :=
  kernel.guardedCollectCoalescing
    |>.guardedShapeExpansion

end
  GCModel

end
  MLFree
end TCTex
end Submission

/-!
# Canonical layer-free structural-coalescing local model

The ordered canonical trace equations can be promoted to the program-valued
local structural-coalescing interface.  Encode each ordered Hall-shape trace as
a scheduler concatenation of singleton retained roots.  Trace equality then
implies structural coalescing by the flat-root permutation criterion.

This produces an unconditional canonical local program model.  The remaining
arbitrary-cutoff theorem is equivalently the assertion that the guarded
symbolic scheduler coalesces with this explicit canonical model on the
inverse-raw source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  LFBounda

open
  HACoeff
open
  RPCoales
open
  RPCoales.EMCoales
open
  CNForm
open
  CNForm.EFForm
open
  RPCrit
open
  RPCrit.SPCrit
open
  PMCoales
open
  CFCollec
open
  CFCollec.DFTerm
open
  SLFree
open
  MLFree
open
  LFExp
open
  TLEquati
open
  TLEquati.DFTerm
open
  FIProf
open
  ISLift
open
  RTProgra
open
  GRProgra
open
  REProgra

/--
Flat-root program encoding of an ordered erased Hall-shape trace.
-/
def erasedShapeProgram
    (trace : List (CWord HPAtom)) :
    ESProgra :=
  REProgra.ESProgra.schedulerConcat
    (trace.map singletonRootProgram)

/--
The flat-root encoding emits its source ordered trace literally.
-/
@[simp]
lemma erased_shape_program
    (trace : List (CWord HPAtom)) :
    (erasedShapeProgram trace).trace =
      trace := by
  unfold erasedShapeProgram
  rw [
    REProgra.ESProgra.traceSchedulerConcat]
  induction trace with
  | nil =>
      rfl
  | cons shape trace ih =>
      simp only [List.map_cons, List.flatMap_cons,
        trace_singleton_program, ih, List.singleton_append]

/--
Promote ordered trace equations to program-valued structural-coalescing local
equations by flat-root encoding.
-/
noncomputable def
    structuralCoalescingModel
    {M N K n leftWeight rightWeight : ℕ}
    (model :
      CEModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)) :
    SCModel
      (M := M) (N := N) (K := K)
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight) where
  insertion :=
    fun L A =>
      erasedShapeProgram (model.insertion L A)
  collection :=
    fun L =>
      erasedShapeProgram (model.collection L)
  insertion_nil A := by
    apply coalesces_perm
    simp [model.insertion_nil A]
  insertion_append P B A hBA := by
    apply coalesces_perm
    simp [model.insertion_append P B A hBA]
  insertion_retained P B A hAB hweight Q R leftCorrections
      rightCorrections hcorrection hinsert := by
    apply coalesces_perm
    simp only [erased_shape_program,
      ESProgra.trace_retained]
    rw [model.insertion_retained P B A hAB hweight hcorrection hinsert]
  insertion_residual P B A hAB hweight R corrections hinsert := by
    apply coalesces_perm
    simp only [erased_shape_program]
    rw [model.insertion_residual P B A hAB hweight hinsert]
  collection_nil := by
    apply coalesces_perm
    simp [model.collection_nil]
  collection_retained P A hweight C R collectCorrections
      insertCorrections hcollect hinsert := by
    apply coalesces_perm
    simp only [erased_shape_program,
      ESProgra.trace_append]
    rw [model.collection_retained P A hweight hcollect hinsert]
  collection_residual P A hweight C corrections hcollect := by
    apply coalesces_perm
    simp only [erased_shape_program]
    rw [model.collection_residual P A hweight hcollect]

namespace DFTerm

/--
Canonical proof-free program-valued local model obtained from the canonical
ordered correction traces.
-/
noncomputable def
    programCoalescingModel
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SCModel
      (M := M) (N := N) (K := K)
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight) :=
  structuralCoalescingModel
    (canonicalErasedModel
      (M := M) (N := N) (K := K) (n := n)
        hleftWeight hrightWeight)

/--
The canonical program-valued collection model emits exactly the proof-free
ordered canonical collection trace.
-/
lemma
    collectCoalescingModel
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L : List (DFTerm M N K)) :
    ((programCoalescingModel
      (M := M) (N := N) (K := K) (n := n)
      hleftWeight hrightWeight).collection L).trace =
        canonicalCollectionErased
          (n := n) hleftWeight hrightWeight L := by
  simp [programCoalescingModel,
    structuralCoalescingModel,
    canonicalErasedModel]

end DFTerm

/--
Reduced layer-free arbitrary-cutoff target: the guarded symbolic scheduler
coalesces with the explicit canonical flat-root collection model.
-/
structure
    GMCoales
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  program_coalesces_collection :
    ∀ M N,
      Rel
        (guardedSchedulerProgram
          (multiplicityProfileShape raw)
          M N)
        ((DFTerm.programCoalescingModel
          (M := M) (N := N)
          (K := (inverseLabelledCollection M N).factors.length)
          (n := n) hleftWeight hrightWeight).collection
            (inverseDecoratedTerms M N))

namespace
  GMCoales

/--
The canonical local model folds through the recursive compiler to the layer-free
canonical concrete schedule.
-/
noncomputable def
    guardedCoalescingModel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMCoales
        (n := n) hleftWeight hrightWeight) :
    GCModel
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  localModel M N :=
    DFTerm.programCoalescingModel
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      (n := n) hleftWeight hrightWeight
  coalesces_local_collection :=
    kernel.program_coalesces_collection

/--
Compile canonical-local-model coalescing directly to the layer-free canonical
trace theorem.
-/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMCoales
        (n := n) hleftWeight hrightWeight) :
    GIExp
      (n := n) hleftWeight hrightWeight :=
  kernel.guardedCoalescingModel
    |>.guardedShapeExpansion

end
  GMCoales

namespace
  GIExp

/--
Recover coalescing with the explicit canonical flat-root collection model from
the layer-free canonical trace theorem.
-/
noncomputable def
    modelCoalescingKernel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIExp
        (n := n) hleftWeight hrightWeight) :
    GMCoales
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  program_coalesces_collection M N := by
    apply coalesces_perm
    rw [
      DFTerm.collectCoalescingModel
        hleftWeight hrightWeight (inverseDecoratedTerms M N)]
    exact
      (idxSchedulerProgram
        kernel.raw M N).symm.trans
          (kernel.shape_trace_perm M N)

end
  GIExp

/--
The layer-free canonical trace theorem and coalescing with the explicit
canonical flat-root local model are equivalent data.
-/
noncomputable def
    guardedModelCoalescing
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GIExp
        (n := n) hleftWeight hrightWeight ≃
      GMCoales
        (n := n) hleftWeight hrightWeight where
  toFun :=
    GIExp.modelCoalescingKernel
  invFun :=
    GMCoales.guardedShapeExpansion
  left_inv kernel := by
    cases kernel
    congr
  right_inv kernel := by
    cases kernel
    congr

end
  LFBounda
end TCTex
end Submission

/-!
# Layer-free finite-index occurrence accounting for the canonical collector

The remaining arbitrary-cutoff collector theorem is an occurrence-accounting
statement.  Shape multiplicities are sufficient for endpoint coordinates, but
the symbolic compiler and the canonical concrete schedule both carry a stronger
finite-index trace.  Those indices retain the polynomial-orbit key of every
correction occurrence.

This file packages the stronger finite-index target in scheduler order and in
the original root-first expansion order.  The two formulations are equivalent.
Either one compiles by finite-index erasure to the canonical local structural
coalescing target.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  ALFree

open
  HACoeff
open
  RPCoales.EMCoales
open
  RPCrit.SPCrit
open
  PMCoales
open
  CFCollec
open
  CLFree
open
  LFBounda
open
  LFBounda.DFTerm
open
  LFExp
open
  FIProf
open
  RITrace
open
  PGSrc
open
  ISLift
open
  FISchedu
open
  GRProgra

/--
Layer-free finite-index occurrence-accounting target in operational scheduler
order.  Every symbolic scheduled root occurrence is matched with a canonical
concrete crossing root before erasing polynomial-orbit indices to Hall shapes.
-/
structure
    SOAccoun
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  scheduler_perm_root :
    ∀ M N,
      List.Perm
        (guardedIdxFin
          (multiplicityProfileShape raw)
          M N)
        (generatedGridBranch
          (n := n) hleftWeight hrightWeight M N)

/--
Equivalent layer-free finite-index occurrence-accounting target in the
root-first expansion order emitted by the polynomial compiler.
-/
structure
    GOAccoun
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  expansion_perm_root :
    ∀ M N,
      List.Perm
        (((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace
              (multiplicityProfileShape
                raw)
              M N).flatten)
        (generatedGridBranch
          (n := n) hleftWeight hrightWeight M N)

/--
Erase exact root-first finite-index occurrence accounting to the canonical
Hall-shape trace theorem.
-/
noncomputable def
    erasedOccurrenceAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GOAccoun
        (n := n) hleftWeight hrightWeight) :
    GIExp
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  shape_trace_perm M N := by
    unfold
      guardedExpansionErased
    rw [←
      key_erased_trace
        hleftWeight hrightWeight M N]
    exact
      (kernel.expansion_perm_root M N).map
        (fun index => (retainedOrbitKey index).erasedShape)

namespace
  SOAccoun

/-- Forget scheduler order and recover the root-first finite-index target. -/
noncomputable def
    guardedOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight) :
    GOAccoun
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  expansion_perm_root M N :=
    (guarded_perm_scheduler
      (multiplicityProfileShape
        kernel.raw)
      M N).trans
        (kernel.scheduler_perm_root M N)

/--
Finite-index scheduler accounting erases to a permutation of the canonical
ordered correction trace.
-/
lemma
    keyErasedTrace
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight)
    (M N : ℕ) :
    List.Perm
      ((guardedIdxFin
        (multiplicityProfileShape
          kernel.raw)
        M N).map fun index =>
          (retainedOrbitKey index).erasedShape)
      (canonicalCollectionErased
        (n := n) hleftWeight hrightWeight
        (inverseDecoratedTerms M N)) := by
  rw [←
    key_erased_trace
      hleftWeight hrightWeight M N]
  exact
    (kernel.scheduler_perm_root M N).map
      (fun index => (retainedOrbitKey index).erasedShape)

/--
Finite-index scheduler accounting directly supplies structural coalescing with
the explicit canonical local collection program.
-/
lemma scheduler_coalesces_collection
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight)
    (M N : ℕ) :
    Rel
      (guardedSchedulerProgram
        (multiplicityProfileShape
          kernel.raw)
        M N)
      ((DFTerm.programCoalescingModel
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        (n := n) hleftWeight hrightWeight).collection
          (inverseDecoratedTerms M N)) := by
  apply coalesces_perm
  rw [←
    key_erased_program]
  rw [
    DFTerm.collectCoalescingModel
      hleftWeight hrightWeight (inverseDecoratedTerms M N)]
  exact
    kernel.keyErasedTrace
      M N

/--
Erase finite orbit indices from scheduler-level occurrence accounting and
recover the layer-free canonical Hall-shape trace theorem.
-/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight) :
    GIExp
      (n := n) hleftWeight hrightWeight :=
  erasedOccurrenceAccounting
    kernel.guardedOccAccounting

/--
Compile scheduler-level finite-index accounting to coalescing with the explicit
canonical local collection model.
-/
noncomputable def
    modelCoalescingKernel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight) :
    GMCoales
      (n := n) hleftWeight hrightWeight :=
  LFBounda.GIExp.modelCoalescingKernel
    kernel.guardedShapeExpansion

/--
Compile scheduler-level finite-index accounting directly to endpoint
interpolation for any natural recollection layer.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight)
    (layer :
      CRLayer.NRLayer
        n leftWeight rightWeight) :=
  kernel.guardedShapeExpansion
    |>.fiberProfileInterpolation layer

end
  SOAccoun

namespace
  GOAccoun

/-- Reorder root-first accounting into operational scheduler order. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GOAccoun
        (n := n) hleftWeight hrightWeight) :
    SOAccoun
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  scheduler_perm_root M N :=
    (guarded_perm_scheduler
      (multiplicityProfileShape
        kernel.raw)
      M N).symm.trans
        (kernel.expansion_perm_root M N)

/-- Erase root-first finite-index accounting to the shared Hall-shape target. -/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GOAccoun
        (n := n) hleftWeight hrightWeight) :
    GIExp
      (n := n) hleftWeight hrightWeight :=
  erasedOccurrenceAccounting
    kernel

/--
Compile exact root-first finite-index accounting to coalescing with the
explicit canonical local collection model.
-/
noncomputable def
    modelCoalescingKernel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GOAccoun
        (n := n) hleftWeight hrightWeight) :
    GMCoales
      (n := n) hleftWeight hrightWeight :=
  LFBounda.GIExp.modelCoalescingKernel
    kernel.guardedShapeExpansion

end
  GOAccoun

/--
Scheduler-order and root-first finite-index occurrence accounting are
equivalent data.
-/
noncomputable def
    idxOccAccounting
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SOAccoun
        (n := n) hleftWeight hrightWeight ≃
      GOAccoun
        (n := n) hleftWeight hrightWeight where
  toFun :=
    SOAccoun.guardedOccAccounting
  invFun :=
    GOAccoun.schedulerOccAccounting
  left_inv kernel := by
    cases kernel
    congr
  right_inv kernel := by
    cases kernel
    congr

end
  ALFree
end TCTex
end Submission

/-!
# Local finite-index models for canonical occurrence accounting

The canonical concrete collector root trace satisfies exact `empty`, `append`,
and `retained` equations before polynomial-orbit indices are erased.  A
symbolic repeated-block collector should satisfy those same equations.

This file packages that constructor-facing interface.  Any local finite-index
trace model agrees with the canonical concrete trace by structural induction
on a schedule program.  Consequently it is enough to compare the symbolic
scheduler trace with a local model evaluated on the canonical recursively
compiled schedule.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  ALModel

open
  HACoeff
open
  ITRec
open
  EGCovera
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  CFCollec
open
  CFCollec.DFTerm
open
  ALFree
open
  CLFree
open
  FIProf
open
  OCPartit
open
  RITrace
open
  ISLift
open
  FISchedu

/--
A proof-free finite-index interpretation of a provenance-certified concrete
schedule.  The three equations are exactly the operational collector
constructors after retaining polynomial-orbit indices.
-/
structure GBModel
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  trace :
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight) →
      CGFroma (inverseDecoratedTerms M N) program →
        List (RetainedOrbitIndex n leftWeight rightWeight)
  trace_empty :
    trace
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight)
        (CGFroma.empty _) =
      []
  trace_append :
    ∀ (left right :
        RSPrograa
          (M := M) (N := N)
          (K := (inverseLabelledCollection M N).factors.length)
          n leftWeight rightWeight)
      (hgenerated :
        CGFroma (inverseDecoratedTerms M N)
          (RSPrograa.append left right)),
      trace
          (RSPrograa.append left right)
          hgenerated =
        trace left (crossings_left_append hgenerated) ++
          trace right (crossings_generated_append hgenerated)
  trace_retained :
    ∀ (left right :
        RSPrograa
          (M := M) (N := N)
          (K := (inverseLabelledCollection M N).factors.length)
          n leftWeight rightWeight)
      (crossedLeft crossedRight :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
      (hweight :
        decoratedFamilyWeight leftWeight rightWeight
          (crossedLeft.correction crossedRight) < n)
      (hgenerated :
        CGFroma (inverseDecoratedTerms M N)
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)),
      trace
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          hgenerated =
        trace left (crossings_generated_left hgenerated) ++
          [guardedGridParents
            hleftWeight hrightWeight (crossedLeft, crossedRight)
              (generated_parents_retained hgenerated) hweight] ++
          trace right (crossings_generated_retained hgenerated)

/-- The literal generated concrete root trace is a local finite-index model. -/
noncomputable def generatedBranchModel
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GBModel
      M N n leftWeight rightWeight hleftWeight hrightWeight where
  trace :=
    generatedGuardedBranch
      hleftWeight hrightWeight
  trace_empty :=
    generated_branch_empty
      hleftWeight hrightWeight
  trace_append :=
    generated_branch_append
      hleftWeight hrightWeight
  trace_retained :=
    generated_guarded_branch
      hleftWeight hrightWeight

namespace
  GBModel

/--
Every local finite-index trace model computes the literal generated concrete
root trace on every provenance-certified schedule.
-/
lemma grid_branch_index
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (model :
      GBModel
        M N n leftWeight rightWeight hleftWeight hrightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program) :
    model.trace program hgenerated =
      generatedGuardedBranch
        hleftWeight hrightWeight program hgenerated := by
  induction program with
  | empty =>
      rw [model.trace_empty]
      exact
        generated_branch_empty
          hleftWeight hrightWeight |>.symm
  | append left right ihleft ihright =>
      rw [
        model.trace_append,
        generated_branch_append,
        ihleft, ihright]
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      rw [
        model.trace_retained,
        generated_guarded_branch,
        ihleft, ihright]

end
  GBModel

/--
Constructor-facing reduction of canonical exact occurrence accounting.  A
symbolic Hall collector may choose any local model satisfying the three
schedule equations and only needs to compare the scheduler trace with that
model on the canonical recursively compiled schedule.
-/
structure
    GAModela
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  model :
    ∀ M N,
      GBModel
        M N n leftWeight rightWeight hleftWeight hrightWeight
  scheduler_perm_model :
    ∀ M N,
      List.Perm
        (guardedIdxFin
          (multiplicityProfileShape raw)
          M N)
        ((model M N).trace
          (inverseRecursivelyCompiled
            (n := n) hleftWeight hrightWeight M N).program
          (crossingsRecursivelyProgram
            hleftWeight hrightWeight M N))

namespace
  GAModela

/--
Compile a constructor-facing local model comparison to exact canonical
finite-index occurrence accounting.
-/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GAModela
        (n := n) hleftWeight hrightWeight) :
    SOAccoun
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  scheduler_perm_root M N :=
    (kernel.scheduler_perm_model M N).trans
      (List.Perm.of_eq (by
        unfold
          generatedGridBranch
        exact
          (kernel.model M
            N).grid_branch_index
            (inverseRecursivelyCompiled
              (n := n) hleftWeight hrightWeight M N).program
            (crossingsRecursivelyProgram
              hleftWeight hrightWeight M N)))

end
  GAModela

namespace
  SOAccoun

/--
Exact canonical occurrence accounting canonically supplies the constructor
local-model comparison, using the literal generated concrete root trace model.
-/
noncomputable def
    guardedAccountingModel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight) :
    GAModela
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  model M N :=
    generatedBranchModel
      M N n leftWeight rightWeight hleftWeight hrightWeight
  scheduler_perm_model M N := by
    simpa [
      generatedBranchModel,
      generatedGridBranch] using
        kernel.scheduler_perm_root M N

end
  SOAccoun

end
  ALModel
end TCTex
end Submission

/-!
# Generated-source local models for finite-index occurrence accounting

The canonical concrete collector now has exact finite-index trace equations at
the schedule constructors.  A symbolic Hall collector is more naturally
defined on insertion and collection problems than on already compiled
schedules.

This file packages that source-facing interface.  Its evaluators are defined
on terms generated from the inverse-raw source, so a retained insertion can
emit the guarded polynomial-orbit root index of its two concrete parents.
The local equations fold through the actual recursive compiler.  Consequently
a symbolic scheduler comparison with one source-local model compiles directly
to exact canonical finite-index occurrence accounting.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  ILModela

open
  HACoeff
open
  ITRec
open
  EGCovera
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  PRCompb
open
  PRCompb.RSPrograa
open
  RCProven
open
  CFCollec
open
  CFCollec.DFTerm
open
  FVSuppor
open
  CRInv
open
  CRInv.DFTerm
open
  ALFree
open
  ALModel
open
  CLFree
open
  SLFree
open
  FIProf
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  RITrace
open
  ISLift
open
  FISchedu

/-- A concrete term generated by finitely many corrections from the inverse-raw source. -/
abbrev InverseRawGenerated
    (M N : ℕ)
    (term :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length) : Prop :=
  CGFrom (inverseDecoratedTerms M N) term

/-- Restrict inverse-raw generation to the prefix before a final list term. -/
def generated_append_last
    {M N : ℕ}
    {P :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    (hgenerated :
      ∀ term ∈ P ++ [A], InverseRawGenerated M N term) :
    ∀ term ∈ P, InverseRawGenerated M N term :=
  fun term hterm =>
    hgenerated term (List.mem_append_left [A] hterm)

/-- Recover inverse-raw generation of the final term of an appended list. -/
def generated_last_append
    {M N : ℕ}
    {P :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    (hgenerated :
      ∀ term ∈ P ++ [A], InverseRawGenerated M N term) :
    InverseRawGenerated M N A :=
  hgenerated A (by simp)

/-- Pairwise correction preserves inverse-raw generation. -/
def inverse_generated_correction
    {M N : ℕ}
    {left right :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    (hleft : InverseRawGenerated M N left)
    (hright : InverseRawGenerated M N right) :
    InverseRawGenerated M N (left.correction right) :=
  CGFrom.correction hleft hright

/-- A traced cutoff insertion preserves inverse-raw generation at its endpoint. -/
def inverse_generated_inserts
    {M N n leftWeight rightWeight : ℕ}
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term)
    (hA : InverseRawGenerated M N A) :
    ∀ term ∈ R, InverseRawGenerated M N term :=
  FVSuppor.DFTerm.correction_cutoff_inserts
    hinsert.cutoffInserts hL hA

/-- A traced cutoff collection preserves inverse-raw generation at its endpoint. -/
def inverse_generated_collects
    {M N n leftWeight rightWeight : ℕ}
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term) :
    ∀ term ∈ R, InverseRawGenerated M N term :=
  fun term hterm =>
    (FVSuppor.DFTerm.correction_cutoff_collects
      hcollect.cutoffCollects term hterm).bind hL

/-- Every literal inverse-raw source term is inverse-raw generated. -/
def inverse_generated_source
    (M N : ℕ) :
    ∀ term ∈ inverseDecoratedTerms M N,
      InverseRawGenerated M N term :=
  fun _term hterm =>
    CGFrom.source hterm

/--
Generated-parent provenance for one recursively compiled insertion schedule,
specialized to the inverse-raw source.
-/
def crossings_compiles_inserts
    {M N n leftWeight rightWeight : ℕ}
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term)
    (hA : InverseRawGenerated M N A) :
    CGFroma (inverseDecoratedTerms M N) program :=
  RSPrograa.crossings_inserts_corrections
    hcompile hL hA

/--
Generated-parent provenance for one recursively compiled collection schedule,
specialized to the inverse-raw source.
-/
def crossings_compiles_collects
    {M N n leftWeight rightWeight : ℕ}
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term) :
    CGFroma (inverseDecoratedTerms M N) program :=
  fun crossing hcrossing =>
    ⟨((RSPrograa.crossings_compiles_corrections
      hcompile crossing hcrossing).1).bind hL,
      ((RSPrograa.crossings_compiles_corrections
        hcompile crossing hcrossing).2).bind hL⟩

/--
A finite-index interpretation of inverse-raw generated insertion and
collection problems.  The retained equation is the symbolic Hall collector
obligation: recursive left corrections, the selected guarded root occurrence,
and recursive right corrections.
-/
structure IIModel
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  insertion :
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)) →
      (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length) →
        (∀ term ∈ L, InverseRawGenerated M N term) →
          InverseRawGenerated M N A →
            List (RetainedOrbitIndex n leftWeight rightWeight)
  collection :
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)) →
      (∀ term ∈ L, InverseRawGenerated M N term) →
        List (RetainedOrbitIndex n leftWeight rightWeight)
  insertion_nil :
    ∀ (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
      (hL : ∀ term ∈ ([] :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length)),
            InverseRawGenerated M N term)
      (hA : InverseRawGenerated M N A),
      insertion [] A hL hA = []
  insertion_append :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (B A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      B.decorated.collectorLe A.decorated →
        ∀ (hPB : ∀ term ∈ P ++ [B], InverseRawGenerated M N term)
          (hA : InverseRawGenerated M N A),
          insertion (P ++ [B]) A hPB hA = []
  insertion_retained :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (B A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      A.decorated.collectorBefore B.decorated →
        ∀ (hweight :
            decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) < n)
          {Q R leftCorrections rightCorrections :
            List (DFTerm M N
              (inverseLabelledCollection M N).factors.length)}
          (hcorrection :
            CICorrec
              n leftWeight rightWeight
              P (B.correction A) Q leftCorrections)
          (_hinsert :
            CICorrec
              n leftWeight rightWeight Q A R rightCorrections)
          (hPB : ∀ term ∈ P ++ [B], InverseRawGenerated M N term)
          (hA : InverseRawGenerated M N A),
          insertion (P ++ [B]) A hPB hA =
            insertion P (B.correction A)
                (generated_append_last hPB)
                (inverse_generated_correction
                  (generated_last_append hPB) hA) ++
              [guardedGridParents
                hleftWeight hrightWeight (B, A)
                  ⟨generated_last_append hPB, hA⟩
                  hweight] ++
                insertion Q A
                  (inverse_generated_inserts
                    hcorrection
                    (generated_append_last hPB)
                    (inverse_generated_correction
                      (generated_last_append hPB) hA))
                  hA
  insertion_residual :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (B A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      A.decorated.collectorBefore B.decorated →
        n ≤ decoratedFamilyWeight leftWeight rightWeight
          (B.correction A) →
            ∀ {R corrections :
                List (DFTerm M N
                  (inverseLabelledCollection M N).factors.length)}
              (_hinsert :
                CICorrec
                  n leftWeight rightWeight P A R corrections)
              (hPB : ∀ term ∈ P ++ [B], InverseRawGenerated M N term)
              (hA : InverseRawGenerated M N A),
              insertion (P ++ [B]) A hPB hA =
                insertion P A
                  (generated_append_last hPB) hA
  collection_nil :
    ∀ hL : ∀ term ∈ ([] :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length)),
            InverseRawGenerated M N term,
      collection [] hL = []
  collection_retained :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      decoratedFamilyWeight leftWeight rightWeight A < n →
        ∀ {C R collectCorrections insertCorrections :
            List (DFTerm M N
              (inverseLabelledCollection M N).factors.length)}
          (hcollect :
            CCCorrec
              n leftWeight rightWeight P C collectCorrections)
          (_hinsert :
            CICorrec
              n leftWeight rightWeight C A R insertCorrections)
          (hPA : ∀ term ∈ P ++ [A], InverseRawGenerated M N term),
          collection (P ++ [A]) hPA =
            collection P
                (generated_append_last hPA) ++
              insertion C A
                (inverse_generated_collects hcollect
                  (generated_append_last hPA))
                (generated_last_append hPA)
  collection_residual :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      n ≤ decoratedFamilyWeight leftWeight rightWeight A →
        ∀ {C corrections :
            List (DFTerm M N
              (inverseLabelledCollection M N).factors.length)}
          (_hcollect :
            CCCorrec
              n leftWeight rightWeight P C corrections)
          (hPA : ∀ term ∈ P ++ [A], InverseRawGenerated M N term),
          collection (P ++ [A]) hPA =
            collection P
              (generated_append_last hPA)

namespace
  IIModel

/--
The local insertion equations fold through every recursively compiled
insertion schedule with inverse-raw generated inputs.
-/
lemma insertion_idx_compiles
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (model :
      IIModel
        M N n leftWeight rightWeight hleftWeight hrightWeight)
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term)
    (hA : InverseRawGenerated M N A) :
    model.insertion L A hL hA =
      generatedGuardedBranch
        hleftWeight hrightWeight program
          (crossings_compiles_inserts
            hcompile hL hA) := by
  induction hcompile with
  | nil A =>
      rw [model.insertion_nil,
        generated_branch_empty]
  | append P B A hBA =>
      rw [model.insertion_append P B A hBA,
        generated_branch_empty]
  | retained P B A hAB hweight hcorrection hinsert
      hleft hright ihleft ihright =>
      rw [
        model.insertion_retained P B A hAB hweight
          hcorrection hinsert hL hA,
        generated_guarded_branch,
        ihleft, ihright]
  | residual P B A hAB hweight hinsert hprogram ihprogram =>
      rw [
        model.insertion_residual P B A hAB hweight hinsert hL hA,
        ihprogram]

/--
The local collection equations fold through every recursively compiled
collection schedule with inverse-raw generated inputs.
-/
lemma collect_idx_compiles
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (model :
      IIModel
        M N n leftWeight rightWeight hleftWeight hrightWeight)
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term) :
    model.collection L hL =
      generatedGuardedBranch
        hleftWeight hrightWeight program
          (crossings_compiles_collects
            hcompile hL) := by
  induction hcompile with
  | nil =>
      rw [model.collection_nil,
        generated_branch_empty]
  | retained P A hweight hcollect hinsert
      hcollectProgram hinsertProgram ihcollect =>
      rw [
        model.collection_retained P A hweight hcollect hinsert hL,
        generated_branch_append,
        ihcollect,
        model.insertion_idx_compiles
          hinsertProgram]
  | residual P A hweight hcollect hprogram ihprogram =>
      rw [
        model.collection_residual P A hweight hcollect hL,
        ihprogram]

/--
Evaluating one source-local model on the literal inverse-raw source computes
the canonical recursively compiled concrete root-index trace.
-/
lemma collect_decorated_branch
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (model :
      IIModel
        M N n leftWeight rightWeight hleftWeight hrightWeight) :
    model.collection
        (inverseDecoratedTerms M N)
        (inverse_generated_source M N) =
      generatedGridBranch
        (n := n) hleftWeight hrightWeight M N := by
  unfold
    generatedGridBranch
  exact
    model.collect_idx_compiles
      (inverseRecursivelyCompiled
        (n := n) hleftWeight hrightWeight M N).compiles
      (inverse_generated_source M N)

end
  IIModel

/--
Source-local form of exact finite-index occurrence accounting.  The remaining
symbolic Hall collector work is to construct one generated-source local model
and identify the scheduler trace with its collection evaluator on the
inverse-raw source.
-/
structure
    GSModel
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  localModel :
    ∀ M N,
      IIModel
        M N n leftWeight rightWeight hleftWeight hrightWeight
  scheduler_index_collection :
    ∀ M N,
      List.Perm
        (guardedIdxFin
          (multiplicityProfileShape raw)
          M N)
        ((localModel M N).collection
          (inverseDecoratedTerms M N)
          (inverse_generated_source M N))

namespace
  GSModel

/--
Compile generated-source local equations to exact canonical finite-index
occurrence accounting.
-/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSModel
        (n := n) hleftWeight hrightWeight) :
    SOAccoun
      (n := n) hleftWeight hrightWeight where
  raw :=
    kernel.raw
  scheduler_perm_root M N :=
    (kernel.scheduler_index_collection M N).trans
      (List.Perm.of_eq
        ((kernel.localModel M N)
          |>.collect_decorated_branch))

end
  GSModel

end
  ILModela
end TCTex
end Submission

/-!
# Canonical generated-source finite-index local model

Generated concrete finite-index traces are independent of the recursively
compiled schedule chosen for a fixed retained-correction derivation: decoding
them gives the polynomial-orbit key map of the literal correction trace, and
finite lookup is injective.

This file uses that uniqueness theorem to choose canonical recursively
compiled insertion and collection schedules and package their root-index traces
as a proof-free generated-source local model.  Thus the source-facing local
interface is inhabited without assuming the missing symbolic Hall collector
comparison.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  ILModel

open
  HACoeff
open
  RRPkt
open
  ROAggreg
open
  CRAlign
open
  CGCovera
open
  ITRec
open
  EGCovera
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  PRCompb
open
  PRCompb.RSPrograa
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRInv
open
  CRInv.DFTerm
open
  ILModela
open
  MLModel
open
  MLModel.DFTerm
open
  OCPartit
open
  RITrace
open
  ISLift

/--
The decoded polynomial-orbit roots of a concrete program are determined by
its literal correction trace.
-/
lemma obstructions_key_trace
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    (polynomialOrbitObstructions program).map
        POObstru.correction =
      program.correctionTrace.map fun term =>
        polynomialOrbitKey term.family.recipe := by
  rw [← program.map_correction_crossings]
  simp [polynomialOrbitObstructions, List.map_map]

/--
Inverse-raw generated root-index traces are uniquely determined by their
literal concrete correction traces.
-/
lemma generated_grid_branch
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hleftGenerated :
      CGFroma (inverseDecoratedTerms M N) left)
    (hrightGenerated :
      CGFroma (inverseDecoratedTerms M N) right)
    (htrace : left.correctionTrace = right.correctionTrace) :
    generatedGuardedBranch
        hleftWeight hrightWeight left hleftGenerated =
      generatedGuardedBranch
        hleftWeight hrightWeight right hrightGenerated := by
  apply listMap_injective retainedOrbitKey
    orbit_key_injective
  rw [
    key_generated_branch,
    key_generated_branch,
    obstructions_key_trace,
    obstructions_key_trace,
    htrace]

/-- Canonical recursively compiled schedule selected for one insertion run. -/
noncomputable def
    recursivelyCompiledSelected
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length))
    (A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length) :
    RSPrograa
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      n leftWeight rightWeight :=
  Classical.choose
    (RSPrograa.compiles_inserts_corrections
      (selectedInsertionCorrections
        (n := n) hleftWeight hrightWeight L A).inserts)

/-- The selected insertion schedule recursively compiles its selected run. -/
lemma compiles_compiled_program
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length))
    (A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length) :
    CompilesInsertsCorrections
      n leftWeight rightWeight
      (selectedInsertionCorrections
        (n := n) hleftWeight hrightWeight L A).inserts
      (recursivelyCompiledSelected
        (n := n) hleftWeight hrightWeight L A) :=
  Classical.choose_spec
    (RSPrograa.compiles_inserts_corrections
      (selectedInsertionCorrections
        (n := n) hleftWeight hrightWeight L A).inserts)

/-- Canonical recursively compiled schedule selected for one collection run. -/
noncomputable def
    recursivelyCompiledProgram
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)) :
    RSPrograa
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      n leftWeight rightWeight :=
  Classical.choose
    (RSPrograa.compiles_collects_corrections
      (selectedCollectionCorrections
        (n := n) hleftWeight hrightWeight L).collects)

/-- The selected collection schedule recursively compiles its selected run. -/
lemma compiles_recursively_compiled
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)) :
    CompilesCollectsCorrections
      n leftWeight rightWeight
      (selectedCollectionCorrections
        (n := n) hleftWeight hrightWeight L).collects
      (recursivelyCompiledProgram
        (n := n) hleftWeight hrightWeight L) :=
  Classical.choose_spec
    (RSPrograa.compiles_collects_corrections
      (selectedCollectionCorrections
        (n := n) hleftWeight hrightWeight L).collects)

/-- Canonical finite-index trace evaluator for one inverse-raw generated insertion problem. -/
noncomputable def generatedInsertionGrid
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length))
    (A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term)
    (hA : InverseRawGenerated M N A) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  generatedGuardedBranch
    hleftWeight hrightWeight
    (recursivelyCompiledSelected
      (n := n) hleftWeight hrightWeight L A)
    (crossings_compiles_inserts
      (compiles_compiled_program
        (n := n) hleftWeight hrightWeight L A)
      hL hA)

/-- Canonical finite-index trace evaluator for one inverse-raw generated collection problem. -/
noncomputable def generatedGuardedGrid
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length))
    (hL : ∀ term ∈ L, InverseRawGenerated M N term) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  generatedGuardedBranch
    hleftWeight hrightWeight
    (recursivelyCompiledProgram
      (n := n) hleftWeight hrightWeight L)
    (crossings_compiles_collects
      (compiles_recursively_compiled
        (n := n) hleftWeight hrightWeight L)
      hL)

/--
The canonical insertion evaluator agrees with every recursively compiled
schedule for the same insertion problem.
-/
lemma insertion_grid_compiles
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term)
    (hA : InverseRawGenerated M N A) :
    generatedInsertionGrid
        hleftWeight hrightWeight L A hL hA =
      generatedGuardedBranch
        hleftWeight hrightWeight program
          (crossings_compiles_inserts
            hcompile hL hA) := by
  unfold generatedInsertionGrid
  apply
    generated_grid_branch
  rw [
    RSPrograa.correction_inserts_corrections
      (compiles_compiled_program
        (n := n) hleftWeight hrightWeight L A),
    RSPrograa.correction_inserts_corrections
      hcompile,
    corrections_selected_insertion
      hleftWeight hrightWeight hinsert]

/--
The canonical collection evaluator agrees with every recursively compiled
schedule for the same collection problem.
-/
lemma generated_grid_compiles
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term) :
    generatedGuardedGrid
        hleftWeight hrightWeight L hL =
      generatedGuardedBranch
        hleftWeight hrightWeight program
          (crossings_compiles_collects
            hcompile hL) := by
  unfold generatedGuardedGrid
  apply
    generated_grid_branch
  rw [
    RSPrograa.correction_collects_corrections
      (compiles_recursively_compiled
        (n := n) hleftWeight hrightWeight L),
    RSPrograa.correction_collects_corrections
      hcompile,
    corrections_selected_collection
      hleftWeight hrightWeight hcollect]

/--
Canonical proof-free generated-source finite-index local model obtained by
recursively compiling the canonical selected insertion and collection runs.
-/
noncomputable def
    guardedGridModel
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    IIModel
      M N n leftWeight rightWeight hleftWeight hrightWeight where
  insertion :=
    generatedInsertionGrid
      (n := n) hleftWeight hrightWeight
  collection :=
    generatedGuardedGrid
      (n := n) hleftWeight hrightWeight
  insertion_nil A hL hA := by
    rw [
      insertion_grid_compiles
        hleftWeight hrightWeight (.nil A) hL hA,
      generated_branch_empty]
  insertion_append P B A hBA hPB hA := by
    rw [
      insertion_grid_compiles
        hleftWeight hrightWeight (.append P B A hBA) hPB hA,
      generated_branch_empty]
  insertion_retained P B A hAB hweight Q R leftCorrections rightCorrections
      hcorrection hinsert hPB hA := by
    rcases
        RSPrograa.compiles_inserts_corrections
          hcorrection with
      ⟨left, hleft⟩
    rcases
        RSPrograa.compiles_inserts_corrections
          hinsert with
      ⟨right, hright⟩
    rw [
      insertion_grid_compiles
        hleftWeight hrightWeight
        (.retained P B A hAB hweight hcorrection hinsert
          hleft hright)
        hPB hA,
      generated_guarded_branch,
      ← insertion_grid_compiles
        hleftWeight hrightWeight hleft,
      ← insertion_grid_compiles
        hleftWeight hrightWeight hright]
  insertion_residual P B A hAB hweight R corrections hinsert hPB hA := by
    rcases
        RSPrograa.compiles_inserts_corrections
          hinsert with
      ⟨program, hprogram⟩
    rw [
      insertion_grid_compiles
        hleftWeight hrightWeight
        (.residual P B A hAB hweight hinsert
          hprogram)
        hPB hA,
      ← insertion_grid_compiles
        hleftWeight hrightWeight hprogram]
  collection_nil hL := by
    rw [
      generated_grid_compiles
        hleftWeight hrightWeight .nil hL,
      generated_branch_empty]
  collection_retained P A hweight C R collectCorrections insertCorrections
      hcollect hinsert hPA := by
    rcases
        RSPrograa.compiles_collects_corrections
          hcollect with
      ⟨collectProgram, hcollectProgram⟩
    rcases
        RSPrograa.compiles_inserts_corrections
          hinsert with
      ⟨insertProgram, hinsertProgram⟩
    rw [
      generated_grid_compiles
        hleftWeight hrightWeight
        (.retained P A hweight hcollect hinsert
          hcollectProgram hinsertProgram)
        hPA,
      generated_branch_append,
      ← generated_grid_compiles
        hleftWeight hrightWeight hcollectProgram,
      ← insertion_grid_compiles
        hleftWeight hrightWeight hinsertProgram]
  collection_residual P A hweight C corrections hcollect hPA := by
    rcases
        RSPrograa.compiles_collects_corrections
          hcollect with
      ⟨program, hprogram⟩
    rw [
      generated_grid_compiles
        hleftWeight hrightWeight
        (.residual P A hweight hcollect
          hprogram)
        hPA,
      ← generated_grid_compiles
        hleftWeight hrightWeight hprogram]

end
  ILModel
end TCTex
end Submission

/-!
# Canonical generated-source local-model target for exact finite-index accounting

The canonical generated-source finite-index local model is now available
unconditionally. This file packages the remaining symbolic Hall collector
statement as a direct comparison between the guarded scheduler trace and that
canonical collection evaluator, and proves it equivalent to exact canonical
finite-index occurrence accounting.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  LMKern

open
  HACoeff
open
  ILModel
open
  ILModela
open
  ALFree
open
  FIProf
open
  FISchedu
open CFCollec
open
  RITrace
open
  ISLift

/--
Canonical generated-source local-model form of exact finite-index occurrence
accounting. The only remaining field is the symbolic scheduler comparison.
-/
structure
    GIModel
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  scheduler_perm_collection :
    ∀ M N,
      List.Perm
        (guardedIdxFin
          (multiplicityProfileShape raw)
          M N)
        ((guardedGridModel
          M N n leftWeight rightWeight hleftWeight hrightWeight).collection
            (inverseDecoratedTerms M N)
            (inverse_generated_source M N))

namespace
  GIModel

/-- Promote the canonical comparison to the general generated-source interface. -/
noncomputable def
    guardedSchedulerModel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIModel
        (n := n) hleftWeight hrightWeight) :
    GSModel
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  localModel M N :=
    guardedGridModel
      M N n leftWeight rightWeight hleftWeight hrightWeight
  scheduler_index_collection :=
    kernel.scheduler_perm_collection

/-- Compile canonical generated-source comparison to exact occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIModel
        (n := n) hleftWeight hrightWeight) :
    SOAccoun
      (n := n) hleftWeight hrightWeight :=
  kernel.guardedSchedulerModel
    |>.schedulerOccAccounting

end
  GIModel

namespace
  SOAccoun

/-- Recover the explicit canonical generated-source scheduler comparison. -/
noncomputable def
    schedulerModelKernel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight) :
    GIModel
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  scheduler_perm_collection M N :=
    (kernel.scheduler_perm_root M N).trans
      (List.Perm.of_eq
        ((guardedGridModel
          M N n leftWeight rightWeight hleftWeight hrightWeight)
          |>.collect_decorated_branch).symm)

end
  SOAccoun

/--
Exact occurrence accounting and the explicit canonical generated-source
scheduler comparison are equivalent data.
-/
noncomputable def
    guardedIdxModel
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SOAccoun
        (n := n) hleftWeight hrightWeight ≃
      GIModel
        (n := n) hleftWeight hrightWeight where
  toFun :=
    SOAccoun.schedulerModelKernel
  invFun :=
    GIModel.schedulerOccAccounting
  left_inv kernel := by
    cases kernel
    congr
  right_inv kernel := by
    cases kernel
    congr

end
  LMKern
end TCTex
end Submission

/-!
# Generated-source finite-index multiplicity local models

The canonical generated-source collector already has a local model whose
evaluators return complete retained polynomial-orbit index traces.  Symbolic
Hall collection arguments are usually scalar: after fixing one retained orbit
index, each retained crossing contributes either one occurrence or zero.

This file records that scalar local-model interface, proves that its local
equations fold through every recursively compiled collector derivation, and
constructs the canonical scalar model by counting entries in the canonical
trace local model.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  LMBounda

open
  HACoeff
open
  ITRec
open
  EGCovera
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  PRCompb
open
  PRCompb.RSPrograa
open
  RCProven
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRInv
open
  CRInv.DFTerm
open
  ILModel
open
  ILModela
open
  CLFree
open
  OCPartit
open
  RITrace

/--
A proof-free scalar interpretation of inverse-raw generated retained-correction
collection after fixing one retained polynomial-orbit index.
-/
structure GGModel
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) where
  insertion :
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)) →
      (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length) →
        (∀ term ∈ L, InverseRawGenerated M N term) →
          InverseRawGenerated M N A →
            ℕ
  collection :
    (L :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)) →
      (∀ term ∈ L, InverseRawGenerated M N term) →
        ℕ
  insertion_nil :
    ∀ (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
      (hL : ∀ term ∈ ([] :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length)),
            InverseRawGenerated M N term)
      (hA : InverseRawGenerated M N A),
      insertion [] A hL hA = 0
  insertion_append :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (B A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      B.decorated.collectorLe A.decorated →
        ∀ (hPB : ∀ term ∈ P ++ [B], InverseRawGenerated M N term)
          (hA : InverseRawGenerated M N A),
          insertion (P ++ [B]) A hPB hA = 0
  insertion_retained :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (B A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      A.decorated.collectorBefore B.decorated →
        ∀ (hweight :
            decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) < n)
          {Q R leftCorrections rightCorrections :
            List (DFTerm M N
              (inverseLabelledCollection M N).factors.length)}
          (hcorrection :
            CICorrec
              n leftWeight rightWeight
              P (B.correction A) Q leftCorrections)
          (_hinsert :
            CICorrec
              n leftWeight rightWeight Q A R rightCorrections)
          (hPB : ∀ term ∈ P ++ [B], InverseRawGenerated M N term)
          (hA : InverseRawGenerated M N A),
          insertion (P ++ [B]) A hPB hA =
            insertion P (B.correction A)
                (generated_append_last hPB)
                (inverse_generated_correction
                  (generated_last_append hPB) hA) +
              (if
                guardedGridParents
                    hleftWeight hrightWeight (B, A)
                    ⟨generated_last_append hPB, hA⟩
                    hweight =
                  index then
                1
              else
                0) +
                insertion Q A
                  (inverse_generated_inserts
                    hcorrection
                    (generated_append_last hPB)
                    (inverse_generated_correction
                      (generated_last_append hPB) hA))
                  hA
  insertion_residual :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (B A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      A.decorated.collectorBefore B.decorated →
        n ≤ decoratedFamilyWeight leftWeight rightWeight
          (B.correction A) →
            ∀ {R corrections :
                List (DFTerm M N
                  (inverseLabelledCollection M N).factors.length)}
              (_hinsert :
                CICorrec
                  n leftWeight rightWeight P A R corrections)
              (hPB : ∀ term ∈ P ++ [B], InverseRawGenerated M N term)
              (hA : InverseRawGenerated M N A),
              insertion (P ++ [B]) A hPB hA =
                insertion P A
                  (generated_append_last hPB) hA
  collection_nil :
    ∀ hL : ∀ term ∈ ([] :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length)),
            InverseRawGenerated M N term,
      collection [] hL = 0
  collection_retained :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      decoratedFamilyWeight leftWeight rightWeight A < n →
        ∀ {C R collectCorrections insertCorrections :
            List (DFTerm M N
              (inverseLabelledCollection M N).factors.length)}
          (hcollect :
            CCCorrec
              n leftWeight rightWeight P C collectCorrections)
          (_hinsert :
            CICorrec
              n leftWeight rightWeight C A R insertCorrections)
          (hPA : ∀ term ∈ P ++ [A], InverseRawGenerated M N term),
          collection (P ++ [A]) hPA =
            collection P
                (generated_append_last hPA) +
              insertion C A
                (inverse_generated_collects hcollect
                  (generated_append_last hPA))
                (generated_last_append hPA)
  collection_residual :
    ∀ (P :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (A :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      n ≤ decoratedFamilyWeight leftWeight rightWeight A →
        ∀ {C corrections :
            List (DFTerm M N
              (inverseLabelledCollection M N).factors.length)}
          (_hcollect :
            CCCorrec
              n leftWeight rightWeight P C corrections)
          (hPA : ∀ term ∈ P ++ [A], InverseRawGenerated M N term),
          collection (P ++ [A]) hPA =
            collection P
              (generated_append_last hPA)

namespace GGModel

/--
The scalar insertion equations fold through every recursively compiled
insertion schedule.
-/
lemma insertion_count_compiles
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {index : RetainedOrbitIndex n leftWeight rightWeight}
    (model :
      GGModel
        M N n leftWeight rightWeight hleftWeight hrightWeight index)
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {A :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term)
    (hA : InverseRawGenerated M N A) :
    model.insertion L A hL hA =
      (generatedGuardedBranch
        hleftWeight hrightWeight program
          (crossings_compiles_inserts
            hcompile hL hA)).count index := by
  induction hcompile with
  | nil A =>
      rw [model.insertion_nil,
        generated_branch_empty]
      rfl
  | append P B A hBA =>
      rw [model.insertion_append P B A hBA,
        generated_branch_empty]
      rfl
  | retained P B A hAB hweight hcorrection hinsert
      hleft hright ihleft ihright =>
      rw [
        model.insertion_retained P B A hAB hweight
          hcorrection hinsert hL hA,
        generated_guarded_branch,
        List.count_append, List.count_append, List.count_singleton,
        ihleft, ihright]
      simp only [beq_iff_eq]
  | residual P B A hAB hweight hinsert hprogram ihprogram =>
      rw [
        model.insertion_residual P B A hAB hweight hinsert hL hA,
        ihprogram]

/--
The scalar collection equations fold through every recursively compiled
collection schedule.
-/
lemma collect_count_compiles
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {index : RetainedOrbitIndex n leftWeight rightWeight}
    (model :
      GGModel
        M N n leftWeight rightWeight hleftWeight hrightWeight index)
    {L R corrections :
      List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (hcompile :
      CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program)
    (hL : ∀ term ∈ L, InverseRawGenerated M N term) :
    model.collection L hL =
      (generatedGuardedBranch
        hleftWeight hrightWeight program
          (crossings_compiles_collects
            hcompile hL)).count index := by
  induction hcompile with
  | nil =>
      rw [model.collection_nil,
        generated_branch_empty]
      rfl
  | retained P A hweight hcollect hinsert
      hcollectProgram hinsertProgram ihcollect =>
      rw [
        model.collection_retained P A hweight hcollect hinsert hL,
        generated_branch_append,
        List.count_append,
        ihcollect,
        model.insertion_count_compiles
          hinsertProgram]
  | residual P A hweight hcollect hprogram ihprogram =>
      rw [
        model.collection_residual P A hweight hcollect hL,
        ihprogram]

end GGModel

/--
Counting one retained index in every trace evaluator turns any generated-source
trace local model into a scalar local model.
-/
noncomputable def rootMultiplicityModel
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (model :
      IIModel
        M N n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    GGModel
      M N n leftWeight rightWeight hleftWeight hrightWeight index where
  insertion L A hL hA :=
    (model.insertion L A hL hA).count index
  collection L hL :=
    (model.collection L hL).count index
  insertion_nil A hL hA := by
    rw [model.insertion_nil]
    rfl
  insertion_append P B A hBA hPB hA := by
    rw [model.insertion_append P B A hBA]
    rfl
  insertion_retained P B A hAB hweight Q R leftCorrections rightCorrections
      hcorrection hinsert hPB hA := by
    rw [model.insertion_retained P B A hAB hweight
      hcorrection hinsert hPB hA]
    simp only [List.count_append, List.count_singleton, beq_iff_eq]
  insertion_residual P B A hAB hweight R corrections hinsert hPB hA := by
    rw [model.insertion_residual P B A hAB hweight hinsert hPB hA]
  collection_nil hL := by
    rw [model.collection_nil]
    rfl
  collection_retained P A hweight C R collectCorrections insertCorrections
      hcollect hinsert hPA := by
    rw [model.collection_retained P A hweight hcollect hinsert hPA,
      List.count_append]
  collection_residual P A hweight C corrections hcollect hPA := by
    rw [model.collection_residual P A hweight hcollect hPA]

/-- Canonical generated-source scalar local model at one retained orbit index. -/
noncomputable def
    generatedGridModel
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    GGModel
      M N n leftWeight rightWeight hleftWeight hrightWeight index :=
  rootMultiplicityModel
    (guardedGridModel
      M N n leftWeight rightWeight hleftWeight hrightWeight)
    index

/--
Evaluating the canonical scalar local model on the literal inverse-raw source
computes the canonical concrete collector root-index multiplicity.
-/
lemma
    decorated_branch_idx
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (generatedGridModel
      M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
        (inverseDecoratedTerms M N)
        (inverse_generated_source M N) =
      (generatedGridBranch
        (n := n) hleftWeight hrightWeight M N).count index := by
  unfold
    generatedGridModel
  unfold rootMultiplicityModel
  change
    ((guardedGridModel
      M N n leftWeight rightWeight hleftWeight hrightWeight).collection
        (inverseDecoratedTerms M N)
        (inverse_generated_source M N)).count index =
      (generatedGridBranch
        (n := n) hleftWeight hrightWeight M N).count index
  rw [
    IIModel.collect_decorated_branch]

end
  LMBounda
end TCTex
end Submission

/-!
# Scheduler-root alignment for canonical generated-source collection

The source-local finite-index collector emits the guarded root index attached
directly to a pair of generated concrete parents.  The recursive symbolic
scheduler emits the correction index of the corresponding polynomial-orbit
obstruction.  Both are lookups in the same deduplicated retained vocabulary.

This file identifies those two indices before any erasure to Hall shapes.  It
also specializes the one-branch scheduler recurrence so that its replicated
middle block is written in the source-local collector's root-index vocabulary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  SRAlign

open
  HACoeff
open
  RRPkt
open
  CRAlign
open
  CGCovera
open
  ITRec
open
  CFCollec
open
  CFCollec.DFTerm
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  ESIdx
open
  ISLift
open
  FISchedu
open
  FISchedu.IOBranch

/--
The root index emitted by a source-local retained crossing is the symbolic
scheduler correction index for the induced concrete polynomial-orbit
obstruction.  The support proof is irrelevant: retained-vocabulary lookup is
injective after decoding.
-/
lemma guarded_grid_parents
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight
        (concreteCrossingObstruction crossing)) :
    guardedGridParents
        hleftWeight hrightWeight crossing hparents hrootWeight =
      MPFam.correctionIndex
        hleftWeight hrightWeight
        (concreteCrossingObstruction crossing) hsupport := by
  apply orbit_key_injective
  rw [
    key_generated_parents,
    MPFam.retained_key_index]

/--
The replicated scheduler root block for a generated crossing is literally a
replicated block of the source-local retained root index.
-/
lemma replicate_grid_parents
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight
        (concreteCrossingObstruction crossing))
    (count : ℕ) :
    List.replicate count
        (guardedGridParents
          hleftWeight hrightWeight crossing hparents hrootWeight) =
      List.replicate count
        (MPFam.correctionIndex
          hleftWeight hrightWeight
          (concreteCrossingObstruction crossing) hsupport) := by
  rw [
    guarded_grid_parents
      hleftWeight hrightWeight crossing hparents hrootWeight hsupport]

namespace IOBranch

/--
The scheduler-order finite-index trace of one raw-source branch exposes its
two nested branches and its repeated guarded-grid root block.
-/
lemma scheduler_idx_append
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    schedulerFinIdx raw branch M N =
      (if hleft :
          branch.obstruction.operationalNestedLeft.weight
              leftWeight rightWeight < n then
        profiledExpansionScheduler
          hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight branch.obstruction branch.support hleft)
          (raw.multiplicityProfileFamily branch.leftIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          M N
      else
        []) ++
      List.replicate
          ((raw.multiplicityProfileFamily branch.leftIndex).multiplicity M N *
            (raw.multiplicityProfileFamily branch.rightIndex).multiplicity M N)
        (guardedGridBranch branch) ++
      (if hright :
          branch.obstruction.operationalNestedRight.weight
              leftWeight rightWeight < n then
        profiledExpansionScheduler
          hleftWeight hrightWeight branch.obstruction.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight branch.obstruction branch.support hright)
          (raw.multiplicityProfileFamily branch.rightIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          M N
      else
        []) := by
  exact
    profiled_expansion_append
      hleftWeight hrightWeight branch.obstruction branch.support
        (raw.multiplicityProfileFamily branch.leftIndex)
        (raw.multiplicityProfileFamily branch.rightIndex)
        M N

end IOBranch

/--
For a generated concrete crossing, the raw-branch scheduler recurrence has a
middle block consisting of copies of exactly the root index emitted by the
source-local retained insertion equation.
-/
lemma scheduler_parents_append
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (inputLeft inputRight : ℕ) :
    let branch :=
      gridBranchParents
        hleftWeight hrightWeight crossing hparents hrootWeight
    schedulerFinIdx raw branch inputLeft inputRight =
      (if hleft :
          branch.obstruction.operationalNestedLeft.weight
              leftWeight rightWeight < n then
        profiledExpansionScheduler
          hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight branch.obstruction branch.support hleft)
          (raw.multiplicityProfileFamily branch.leftIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          inputLeft inputRight
      else
        []) ++
      List.replicate
          ((raw.multiplicityProfileFamily branch.leftIndex).multiplicity
              inputLeft inputRight *
            (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
              inputLeft inputRight)
        (guardedGridParents
          hleftWeight hrightWeight crossing hparents hrootWeight) ++
      (if hright :
          branch.obstruction.operationalNestedRight.weight
              leftWeight rightWeight < n then
        profiledExpansionScheduler
          hleftWeight hrightWeight branch.obstruction.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight branch.obstruction branch.support hright)
          (raw.multiplicityProfileFamily branch.rightIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          inputLeft inputRight
      else
        []) := by
  exact
    IOBranch.scheduler_idx_append
      raw
      (gridBranchParents
        hleftWeight hrightWeight crossing hparents hrootWeight)
      inputLeft inputRight

end
  SRAlign
end TCTex
end Submission

/-!
# Compatible-grid alignment for canonical generated-source collection

The source-local collector emits one retained root index for each generated
parent crossing.  The compatible-grid packet compiler packages a whole
support-compatible Cartesian crossing fiber as repeated copies of one
retained root index.

This file specializes that compiler to the exact retained root emitted by a
provenance-certified generated crossing.  It also records the rewrite from
that local root to the recursive symbolic scheduler's correction index.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  GABounda

open
  HACoeff
open
  RRPkt
open
  CRAlign
open
  ITRec
open
  CFCollec
open
  CFCollec.DFTerm
open
  SRAlign
open
  CCAggreg
open
  CCGrida
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  CCGrid
open
  GBList

/--
The retained root emitted by one generated concrete crossing has the
commutator erased shape of its two concrete parents.
-/
lemma key_grid_parents
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n) :
    (retainedOrbitKey
      (guardedGridParents
        hleftWeight hrightWeight crossing hparents hrootWeight)).erasedShape =
      CWord.commutator
        crossing.1.erasedShape crossing.2.erasedShape := by
  rw [
    key_generated_parents,
    concrete_crossing_obstruction,
    DFTerm.erasedShape_corr]

/--
If a compatible-grid family has the two generated-parent shapes, the local
retained root supplies exactly the selected-shape certificate required by
the homogeneous compatible-grid packet compiler.
-/
lemma erased_parents_commutator
    {M N n leftWeight rightWeight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (_family :
      CGFam K leftShape rightShape)
    (hleftShape : crossing.1.erasedShape = leftShape)
    (hrightShape : crossing.2.erasedShape = rightShape) :
    (retainedOrbitKey
      (guardedGridParents
        hleftWeight hrightWeight crossing hparents hrootWeight)).erasedShape =
      CWord.commutator leftShape rightShape := by
  rw [
    key_grid_parents
      hleftWeight hrightWeight crossing hparents hrootWeight,
    hleftShape, hrightShape]

/--
Package one support-compatible crossing fiber using exactly the retained root
emitted by the source-local generated-parent collector.
-/
noncomputable def profiledBranchParents
    {M N n leftWeight rightWeight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (family :
      CGFam K leftShape rightShape)
    (hleftShape : crossing.1.erasedShape = leftShape)
    (hrightShape : crossing.2.erasedShape = rightShape) :
    PGBranch n leftWeight rightWeight where
  K :=
    K
  selected :=
    guardedGridParents
      hleftWeight hrightWeight crossing hparents hrootWeight
  leftShape :=
    leftShape
  rightShape :=
    rightShape
  selectedShape_eq :=
    erased_parents_commutator
      hleftWeight hrightWeight crossing hparents hrootWeight family
        hleftShape hrightShape
  family :=
    family

@[simp]
lemma selected_profiled_parents
    {M N n leftWeight rightWeight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (family :
      CGFam K leftShape rightShape)
    (hleftShape : crossing.1.erasedShape = leftShape)
    (hrightShape : crossing.2.erasedShape = rightShape) :
    (profiledBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight family
        hleftShape hrightShape).selected =
      guardedGridParents
        hleftWeight hrightWeight crossing hparents hrootWeight := by
  rfl

/--
The concrete trace of the specialized compatible-grid branch is a repeated
block of the exact source-local retained root.
-/
lemma profiled_branch_parents
    {M N n leftWeight rightWeight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (family :
      CGFam K leftShape rightShape)
    (hleftShape : crossing.1.erasedShape = leftShape)
    (hrightShape : crossing.2.erasedShape = rightShape)
    (inputLeft inputRight : ℕ) :
    (profiledBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight family
        hleftShape hrightShape).indexTrace inputLeft inputRight =
      List.replicate
        (compatibleCorrectionGrid
          (family.leftTerms inputLeft inputRight)
          (family.rightTerms inputLeft inputRight)).length
        (guardedGridParents
          hleftWeight hrightWeight crossing hparents hrootWeight) := by
  rfl

/--
The compiled homogeneous family attached to the specialized branch retains
the same source-local repeated-root trace.
-/
lemma profiledGridParents
    {M N n leftWeight rightWeight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (family :
      CGFam K leftShape rightShape)
    (hleftShape : crossing.1.erasedShape = leftShape)
    (hrightShape : crossing.2.erasedShape = rightShape)
    (inputLeft inputRight : ℕ) :
    (profiledBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight family
        hleftShape hrightShape).profiledIndexFamily.trace
          inputLeft inputRight =
      List.replicate
        (compatibleCorrectionGrid
          (family.leftTerms inputLeft inputRight)
          (family.rightTerms inputLeft inputRight)).length
        (guardedGridParents
          hleftWeight hrightWeight crossing hparents hrootWeight) := by
  rw [
    PGBranch.profiled_index_family,
    profiled_branch_parents]

/--
After root alignment, the specialized compatible-grid trace is the same
repeated block expressed in the recursive symbolic scheduler vocabulary.
-/
lemma profiled_replicate_idx
    {M N n leftWeight rightWeight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hparents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2)
    (hrootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight
        (concreteCrossingObstruction crossing))
    (family :
      CGFam K leftShape rightShape)
    (hleftShape : crossing.1.erasedShape = leftShape)
    (hrightShape : crossing.2.erasedShape = rightShape)
    (inputLeft inputRight : ℕ) :
    (profiledBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight family
        hleftShape hrightShape).profiledIndexFamily.trace
          inputLeft inputRight =
      List.replicate
        (compatibleCorrectionGrid
          (family.leftTerms inputLeft inputRight)
          (family.rightTerms inputLeft inputRight)).length
        (MPFam.correctionIndex
          hleftWeight hrightWeight
          (concreteCrossingObstruction crossing) hsupport) := by
  rw [
    profiledGridParents
      hleftWeight hrightWeight crossing hparents hrootWeight family
        hleftShape hrightShape,
    replicate_grid_parents
      hleftWeight hrightWeight crossing hparents hrootWeight hsupport]

end
  GABounda
end TCTex
end Submission

/-!
# Generated compatible-grid branch lists for canonical source-local collection

One provenance-certified generated crossing selects a retained root index.
One compatible-grid profile family supplies a homogeneous packet for the
support-compatible crossing fiber attached to that root.  This file bundles
that data into a generated batch, maps finite generated-batch lists into the
existing compatible-grid branch-list compiler, and isolates the remaining
collector-specific permutation statement.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  OBList

open
  HACoeff
open
  RRPkt
open
  CRAlign
open
  ITRec
open
  EGCovera
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRLayer
open
  ISFiber
open
  GABounda
open
  SRAlign
open
  CCGrida
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  RITrace
open
  RIRecurs
open
  FIBridge
open
  IMProf
open
  CCGrid
open
  GBList
open
  OEBounda

/--
One generated-parent support-compatible crossing fiber.  Its root is selected
from a concrete crossing with inverse-raw provenance, while its family packet
counts the whole two-parameter compatible grid represented by that crossing.
-/
structure GPBatch
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  sourceLeft :
    ℕ
  sourceRight :
    ℕ
  K :
    ℕ
  leftShape :
    CWord HPAtom
  rightShape :
    CWord HPAtom
  crossing :
    DFTerm sourceLeft sourceRight
        (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
      DFTerm sourceLeft sourceRight
        (inverseLabelledCollection sourceLeft sourceRight).factors.length
  parents :
    CGFrom
        (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
      CGFrom
        (inverseDecoratedTerms sourceLeft sourceRight) crossing.2
  rootWeight :
    decoratedFamilyWeight leftWeight rightWeight
      (crossing.1.correction crossing.2) < n
  family :
    CGFam K leftShape rightShape
  leftShape_eq :
    crossing.1.erasedShape = leftShape
  rightShape_eq :
    crossing.2.erasedShape = rightShape

namespace GPBatch

/-- The recursive polynomial-orbit packet rooted at a generated batch is supported. -/
lemma isSupported
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight) :
    IsSupported (n := n) hleftWeight hrightWeight
      (concreteCrossingObstruction batch.crossing) := by
  exact
    supported_crossing_poly
      hleftWeight hrightWeight batch.crossing batch.parents batch.rootWeight

/-- Forget generated-parent packaging and retain the generic compatible-grid branch. -/
noncomputable def profiledGridBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight) :
    PGBranch n leftWeight rightWeight :=
  profiledBranchParents
    hleftWeight hrightWeight batch.crossing batch.parents batch.rootWeight
      batch.family batch.leftShape_eq batch.rightShape_eq

/-- Concrete repeated-root trace attached directly to a generated batch. -/
def indexTrace
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  List.replicate
    (compatibleCorrectionGrid
      (batch.family.leftTerms M N)
      (batch.family.rightTerms M N)).length
    (guardedGridParents
      hleftWeight hrightWeight batch.crossing batch.parents batch.rootWeight)

@[simp]
lemma profiledCompatBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    batch.profiledGridBranch.indexTrace M N =
      batch.indexTrace M N := by
  rfl

@[simp]
lemma profiled_grid_branch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    (batch.profiledGridBranch
      |>.profiledIndexFamily).trace M N =
      batch.indexTrace M N := by
  rw [
    PGBranch.profiled_index_family,
    profiledCompatBranch]

/--
The generated batch trace can be written using the recursive symbolic
scheduler correction index without changing its compatible-grid cardinality.
-/
lemma index_replicate_correction
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    batch.indexTrace M N =
      List.replicate
        (compatibleCorrectionGrid
          (batch.family.leftTerms M N)
          (batch.family.rightTerms M N)).length
        (MPFam.correctionIndex
          hleftWeight hrightWeight
          (concreteCrossingObstruction batch.crossing)
          batch.isSupported) := by
  rw [indexTrace]
  exact
    replicate_grid_parents
      hleftWeight hrightWeight batch.crossing batch.parents batch.rootWeight
        batch.isSupported _

end GPBatch

/--
Compile a finite generated-batch list to the generic compatible-grid branch
list consumed by the profile algebra.
-/
noncomputable def profiledBranchesParents
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batches :
      List (GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight)) :
    List (PGBranch
      n leftWeight rightWeight) :=
  batches.map
    GPBatch.profiledGridBranch

/--
The generic compatible-grid branch compiler applied to generated batches has
the flattened concrete source-local repeated-root trace.
-/
lemma concat_branches_parents
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batches :
      List (GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight))
    (M N : ℕ) :
    (PGBranch.concat
      (profiledBranchesParents
        batches)).trace M N =
      (batches.map fun batch => batch.indexTrace M N).flatten := by
  rw [
    PGBranch.trace_concat,
    profiledBranchesParents,
    List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro batch _hbatch
  exact
    GPBatch.profiledCompatBranch
      batch M N

/--
The same compiled generated-batch trace is a flattened list of
support-compatible crossing fibers written in symbolic scheduler-root
vocabulary.
-/
lemma concat_compat_flatten
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batches :
      List (GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight))
    (M N : ℕ) :
    (PGBranch.concat
      (profiledBranchesParents
        batches)).trace M N =
      (batches.map fun batch =>
        List.replicate
          (compatibleCorrectionGrid
            (batch.family.leftTerms M N)
            (batch.family.rightTerms M N)).length
          (MPFam.correctionIndex
            hleftWeight hrightWeight
            (concreteCrossingObstruction batch.crossing)
            batch.isSupported)).flatten := by
  rw [
    concat_branches_parents]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro batch _hbatch
  exact batch.index_replicate_correction M N

/--
A finite generated compatible-grid decomposition of the literal selected
retained-correction trace.  All polynomial packet construction is discharged
batchwise; the remaining field is the collector-specific occurrence
permutation theorem.
-/
structure GPDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  batches :
    List (GPBatch
      n leftWeight rightWeight hleftWeight hrightWeight)
  trace_perm :
    ∀ M N,
      List.Perm
        ((batches.map fun batch => batch.indexTrace M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace GPDecomp

/--
Forget generated-parent witnesses and retain the exact compatible-grid index
decomposition consumed by the existing finite-index profile compiler.
-/
noncomputable def selectedProfiledCompatible
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GPDecomp
        layer hleftWeight hrightWeight) :
    SPDecomp
      layer hleftWeight hrightWeight where
  branches :=
    profiledBranchesParents
      decomposition.batches
  trace_perm M N := by
    rw [profiledBranchesParents,
      List.map_map]
    exact
      (List.Perm.of_eq (by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro batch _hbatch
        exact
          GPBatch.profiledCompatBranch
            batch M N)).trans
        (decomposition.trace_perm M N)

/-- Compile generated compatible-grid batches to per-index multiplicity profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GPDecomp
        layer hleftWeight hrightWeight) :
    MPKern
      layer hleftWeight hrightWeight :=
  decomposition.selectedProfiledCompatible
    |>.multiplicityProfileKernel

end GPDecomp

end
  OBList
end TCTex
end Submission

/-!
# Shape-erased generated compatible-grid branch lists

Exact finite orbit representatives are stronger than endpoint coordinate
polynomials require.  One generated compatible-grid batch contributes a
repeated retained root index, but after erasure its contribution is simply a
repeated block of the commutator of the two parent shapes.

This file packages the corresponding generated erased-shape decomposition,
maps it into the existing compatible-grid interpolation pipeline, and records
the automatic downgrade from an exact generated index decomposition.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  BLAlign

open
  HACoeff
open
  EBList
open
  CRLayer
open
  ISFiber
open
  GABounda
open
  OBList
open
  FIProf
open
  CCGrida
open
  RITrace
open
  GBList
open
  SEAlg

/-- Shape-erased repeated block contributed by one generated compatible grid. -/
def generatedParentsBatch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List (CWord HPAtom) :=
  List.replicate
    (compatibleCorrectionGrid
      (batch.family.leftTerms M N)
      (batch.family.rightTerms M N)).length
    (CWord.commutator batch.leftShape batch.rightShape)

/--
Erasing the local retained roots in one generated batch gives its repeated
commutator-shape block literally.
-/
@[simp]
lemma key_erased_shape
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batch :
      GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    (batch.indexTrace M N).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      generatedParentsBatch
        batch M N := by
  rw [GPBatch.indexTrace,
    generatedParentsBatch,
    List.map_replicate]
  rw [
    erased_parents_commutator
      hleftWeight hrightWeight batch.crossing batch.parents batch.rootWeight
        batch.family batch.leftShape_eq batch.rightShape_eq]

/--
Erasing the flattened local retained-root traces of generated batches is the
same as flattening their repeated commutator-shape blocks.
-/
lemma keyGridBatch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batches :
      List (GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight))
    (M N : ℕ) :
    ((batches.map fun batch => batch.indexTrace M N).flatten).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      (batches.map fun batch =>
        generatedParentsBatch
          batch M N).flatten := by
  induction batches with
  | nil =>
      rfl
  | cons batch batches ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        key_erased_shape, ih]

/--
After erasure, a finite compiled generated-batch list is the flattened list
of its repeated commutator-shape blocks.
-/
lemma keyBranchesParents
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (batches :
      List (GPBatch
        n leftWeight rightWeight hleftWeight hrightWeight))
    (M N : ℕ) :
    (((profiledBranchesParents
      batches).map fun branch => branch.indexTrace M N).flatten).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      (batches.map fun batch =>
        generatedParentsBatch
          batch M N).flatten := by
  induction batches with
  | nil =>
      rfl
  | cons batch batches ih =>
      simp only [
        profiledBranchesParents,
        List.map_cons, List.flatten_cons, List.map_append,
        GPBatch.profiledCompatBranch,
        key_erased_shape]
      change
        generatedParentsBatch
              batch M N ++
            (((profiledBranchesParents
              batches).map fun branch => branch.indexTrace M N).flatten).map
                (fun index =>
                  (retainedOrbitKey index).erasedShape) =
          generatedParentsBatch
              batch M N ++
            (batches.map fun batch =>
              generatedParentsBatch
                batch M N).flatten
      rw [ih]

/--
A finite generated compatible-grid decomposition at the erased Hall-shape
level.  This is the collector-specific occurrence statement needed by the
power-coordinate interpolation pipeline.
-/
structure PGDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  batches :
    List (GPBatch
      n leftWeight rightWeight hleftWeight hrightWeight)
  shape_trace_perm :
    ∀ M N,
      List.Perm
        ((batches.map fun batch =>
          generatedParentsBatch
            batch M N).flatten)
        (selectedErasedShape layer M N)

namespace
  PGDecomp

/--
Forget generated-parent witnesses and retain the generic erased-shape
compatible-grid decomposition consumed by endpoint interpolation.
-/
noncomputable def
    profiledGridDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PGDecomp
        layer hleftWeight hrightWeight) :
    PCDecompb
      layer hleftWeight hrightWeight where
  branches :=
    profiledBranchesParents
      decomposition.batches
  shape_trace_perm M N := by
    exact
      (List.Perm.of_eq
        (keyBranchesParents
          decomposition.batches M N)).trans
        (decomposition.shape_trace_perm M N)

/--
Compile generated erased-shape compatible-grid batches directly to the
endpoint interpolation object consumed by the power-coordinate pipeline.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PGDecomp
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :=
  decomposition.profiledGridDecomp
    |>.fiberProfileInterpolation raw

/--
Every exact generated index decomposition induces the weaker generated
erased-shape decomposition by mapping its permutation through key erasure.
-/
noncomputable def exactIndexDecomposition
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GPDecomp
        layer hleftWeight hrightWeight) :
    PGDecomp
      layer hleftWeight hrightWeight where
  batches :=
    decomposition.batches
  shape_trace_perm M N := by
    rw [←
      key_erased_selected
        layer M N hleftWeight hrightWeight]
    exact
      (List.Perm.of_eq
        (keyGridBatch
          decomposition.batches M N).symm).trans
        ((decomposition.trace_perm M N).map
          (fun index => (retainedOrbitKey index).erasedShape))

end
  PGDecomp

end
  BLAlign
end TCTex
end Submission

/-!
# Generated compatible-grid batches aligned with recursive expansion

The endpoint decomposition consumed by the power-coordinate pipeline asks for
one finite list of generated compatible-grid batches whose erased-shape blocks
permute directly to the selected collector trace.  The symbolic Hall collector
naturally proves a slightly more modular statement: those blocks permute to
the recursive guarded raw-source expansion.

This file packages that intermediate criterion.  Existing scheduler
permutation theorems then transport it to the selected endpoint trace.  The
remaining arbitrary-cutoff batch construction is consequently independent of
the endpoint representation chosen by the collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  SEAlign

open
  PGBridge
open
  RPCrit
open
  PMCoales
open
  CRLayer
open
  OBList
open
  BLAlign
open
  FIProf
open
  GGErased

/--
Universal generated-batch criterion before comparison with a selected
endpoint: the flattened compatible-grid shape blocks permute to the recursive
guarded raw-source expansion trace.
-/
structure
    PCDecomp
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  batches :
    List (GPBatch
      n leftWeight rightWeight hleftWeight hrightWeight)
  expansion_shape_perm :
    ∀ M N,
      List.Perm
        ((batches.map fun batch =>
          generatedParentsBatch
            batch M N).flatten)
        (guardedExpansionErased
          raw M N)

namespace
  PCDecomp

/--
Transport universal generated batches through an erased-shape scheduler
theorem to the selected endpoint trace.
-/
noncomputable def
    parentsCompatDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (scheduler :
      GEDecomp
        layer hleftWeight hrightWeight)
    (decomposition :
      PCDecomp
        hleftWeight hrightWeight scheduler.raw) :
    PGDecomp
      layer hleftWeight hrightWeight where
  batches :=
    decomposition.batches
  shape_trace_perm M N :=
    (decomposition.expansion_shape_perm M N).trans
      (scheduler.shape_trace_perm M N)

/--
Transport universal generated batches through the concrete operational
root-trace permutation kernel to the selected endpoint trace.
-/
noncomputable def
    parentsCompatPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (scheduler :
      GPPerm
        layer hleftWeight hrightWeight)
    (decomposition :
      PCDecomp
        hleftWeight hrightWeight scheduler.raw) :
    PGDecomp
      layer hleftWeight hrightWeight where
  batches :=
    decomposition.batches
  shape_trace_perm M N :=
    (decomposition.expansion_shape_perm M N).trans
      ((scheduler.expanded_root_perm M N).trans
        (List.Perm.of_eq
          (endpoint_guarded_erased
            layer hleftWeight hrightWeight M N)))

/--
Compile universal generated batches and an erased-shape scheduler theorem
directly to endpoint interpolation.
-/
noncomputable def
    endpointExpansionDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (scheduler :
      GEDecomp
        layer hleftWeight hrightWeight)
    (decomposition :
      PCDecomp
        hleftWeight hrightWeight scheduler.raw) :=
  decomposition.parentsCompatDecomp
      scheduler
    |>.fiberProfileInterpolation scheduler.raw

/--
Compile universal generated batches and the operational root-trace
permutation kernel directly to endpoint interpolation.
-/
noncomputable def
    fiberInterpolationPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (scheduler :
      GPPerm
        layer hleftWeight hrightWeight)
    (decomposition :
      PCDecomp
        hleftWeight hrightWeight scheduler.raw) :=
  decomposition.parentsCompatPermutation
      scheduler
    |>.fiberProfileInterpolation scheduler.raw

end
  PCDecomp

end
  SEAlign
end TCTex
end Submission

/-!
# Claim 5 from generated source-local compatible-grid batches

Generated source-local compatible-grid batches specialize the generic
shape-erased compatible-grid profile compiler.  Once their flattened erased
trace is a permutation of the selected collector correction trace, the
existing signed-lift boundary and Claim 5 constructor apply directly.

This file restates those final inputs in generated-parent vocabulary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open
  EBList
open
  FPInterp
open
  CRLayer
open
  FIProf
open
  CFSubsti

namespace
  BLAlign

namespace
  PGDecomp

/--
The remaining signed extension after generated source-local compatible-grid
batches have been compiled to endpoint interpolation.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PGDecomp
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    Prop :=
  PCDecompb.AILift.{u}
    (d := d)
    decomposition.profiledGridDecomp
    raw

/--
The truncated signed recollection law for packets compiled from generated
source-local compatible-grid batches.
-/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PGDecomp
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    Prop :=
  PCDecompb.SatisfiesTruncEval.{u}
    (d := d)
    decomposition.profiledGridDecomp
    raw

/--
For generated source-local compatible-grid batches, the remaining signed
extension is exactly their truncated signed recollection law.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PGDecomp
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    SatisfiesTruncEval.{u} (d := d) decomposition raw ↔
      AILift.{u} (d := d) decomposition raw :=
  decomposition.profiledGridDecomp
    |>.satisfies_trunc_lift raw

end
  PGDecomp

end
  BLAlign

namespace TSInput

open
  BLAlign

/--
Generated source-local compatible-grid batches, their signed lift, singleton
recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem
    polyBranchesLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (decomposition :
      PGDecomp
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (lift :
      PGDecomp.AILift.{u}
        (d := d) decomposition raw)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.gridBranchesLift
    hn H hH
      decomposition.profiledGridDecomp
      raw lift hsourceSupported factorNormalization hinputWeight

/--
The direct generated-batch truncated signed recollection law is an
equivalent constructor input for the Claim 5 coordinate polynomials.
-/
theorem
    coordParentsTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (decomposition :
      PGDecomp
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (hlistEval :
      PGDecomp.SatisfiesTruncEval.{u}
        (d := d) decomposition raw)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordGridTrunc
    hn H hH
      decomposition.profiledGridDecomp
      raw hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Generated batches from uniform support-avoidance parent families

The generated compatible-grid batch API consumes a packaged profile family.
The recursive homogeneous compiler naturally produces two uniform
support-avoidance parent families.  This file joins those interfaces and
records the resulting repeated-root and erased-shape traces.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  OBList

open
  HACoeff
open
  RRPkt
open
  ITRec
open
  CFCollec
open
  CFCollec.DFTerm
open
  BLAlign
open
  AAProf
open
  CCGrida
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  RITrace

namespace GPBatch

/--
Construct one generated support-compatible crossing batch directly from two
uniform homogeneous support-avoidance parent families.
-/
noncomputable def uniformAvoidanceFamilies
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {sourceLeft sourceRight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length)
    (parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2)
    (rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (left :
      USAvoida K leftShape)
    (right :
      USAvoida K rightShape)
    (hcompatible :
      ∀ M N : ℕ,
        correctionPairCompatible (left.witness M N) (right.witness M N))
    (leftShape_eq :
      crossing.1.erasedShape = leftShape)
    (rightShape_eq :
      crossing.2.erasedShape = rightShape) :
    GPBatch
      n leftWeight rightWeight hleftWeight hrightWeight where
  sourceLeft :=
    sourceLeft
  sourceRight :=
    sourceRight
  K :=
    K
  leftShape :=
    leftShape
  rightShape :=
    rightShape
  crossing :=
    crossing
  parents :=
    parents
  rootWeight :=
    rootWeight
  family :=
    left.compatibleGridFamily right hcompatible
  leftShape_eq :=
    leftShape_eq
  rightShape_eq :=
    rightShape_eq

/--
The generated-batch root trace obtained from uniform parents is the expected
support-compatible-grid cardinality followed by repeated root selection.
-/
@[simp]
lemma support_avoidance_families
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {sourceLeft sourceRight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length)
    (parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2)
    (rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (left :
      USAvoida K leftShape)
    (right :
      USAvoida K rightShape)
    (hcompatible :
      ∀ M N : ℕ,
        correctionPairCompatible (left.witness M N) (right.witness M N))
    (leftShape_eq :
      crossing.1.erasedShape = leftShape)
    (rightShape_eq :
      crossing.2.erasedShape = rightShape)
    (M N : ℕ) :
    (uniformAvoidanceFamilies
      (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
      crossing parents rootWeight left right hcompatible
        leftShape_eq rightShape_eq).indexTrace M N =
      List.replicate
        (compatibleCorrectionGrid (left.terms M N) (right.terms M N)).length
        (guardedGridParents
          hleftWeight hrightWeight crossing parents rootWeight) := by
  rfl

/--
After shape erasure, the same generated batch is the repeated commutator shape
of its two uniform parent families.
-/
@[simp]
lemma uniform_avoidance_families
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {sourceLeft sourceRight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length)
    (parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2)
    (rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (left :
      USAvoida K leftShape)
    (right :
      USAvoida K rightShape)
    (hcompatible :
      ∀ M N : ℕ,
        correctionPairCompatible (left.witness M N) (right.witness M N))
    (leftShape_eq :
      crossing.1.erasedShape = leftShape)
    (rightShape_eq :
      crossing.2.erasedShape = rightShape)
    (M N : ℕ) :
    generatedParentsBatch
        (uniformAvoidanceFamilies
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          crossing parents rootWeight left right hcompatible
            leftShape_eq rightShape_eq)
        M N =
      List.replicate
        (compatibleCorrectionGrid (left.terms M N) (right.terms M N)).length
        (CWord.commutator leftShape rightShape) := by
  rfl

end GPBatch

end
  OBList
end TCTex
end Submission

-- Merged from FamilyCompatibleGridExpansionPowerCoordinatePolynomialBridge.lean

/-!
# Claim 5 from generated compatible-grid expansion batches

Universal generated compatible-grid batches are most naturally compared with
the recursive guarded raw-source expansion before any endpoint is selected.
The operational root-trace permutation kernel transports that expansion to the
actual cutoff-full collector endpoint.

This file composes those two inputs with the signed extension boundary and
restates the Claim 5 constructor in that modular vocabulary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RPCrit
open
  FPInterp
open
  CRLayer
open
  BLAlign
open
  SEAlign
open
  FIProf

namespace
  SEAlign

namespace
  PCDecomp

/--
The remaining signed extension after universal generated batches have been
transported through the operational root-trace permutation kernel.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (decomposition :
      PCDecomp
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PGDecomp.AILift.{u}
    (d := d)
    (decomposition.parentsCompatPermutation
      scheduler)
    scheduler.raw

/--
The truncated signed recollection law after universal generated batches have
been transported through the operational root-trace permutation kernel.
-/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (decomposition :
      PCDecomp
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PGDecomp.SatisfiesTruncEval.{u}
    (d := d)
    (decomposition.parentsCompatPermutation
      scheduler)
    scheduler.raw

/--
For universal generated batches transported through operational root-trace
permutation, the signed lift is exactly the truncated recollection law.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (decomposition :
      PCDecomp
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler decomposition ↔
      AILift.{u} (d := d) scheduler decomposition :=
  PGDecomp.satisfies_trunc_lift
    (decomposition.parentsCompatPermutation
      scheduler) scheduler.raw

end
  PCDecomp

end
  SEAlign

namespace TSInput

open
  SEAlign

/--
Operational root permutation, universal generated compatible-grid batches,
their signed lift, singleton recollections, and graded Hall bases construct
the Claim 5 coordinate polynomials.
-/
theorem
    coordBranchesLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (decomposition :
      PCDecomp
        (by simp) (by simp) scheduler.raw)
    (lift :
      PCDecomp.AILift.{u}
        (d := d) scheduler decomposition)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.polyBranchesLift
    hn H hH
      (decomposition.parentsCompatPermutation
        scheduler)
      scheduler.raw lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent constructor input for
the generated-expansion Claim 5 route.
-/
theorem
    coordPolyTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (decomposition :
      PCDecomp
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      PCDecomp.SatisfiesTruncEval.{u}
        (d := d) scheduler decomposition)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordParentsTrunc
    hn H hH
      (decomposition.parentsCompatPermutation
        scheduler)
      scheduler.raw hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from FamilyUniformInhomogeneous.lean

/-!
# Uniform unrestricted support-avoidance profile families

Physical-slot deletion is not homogeneous before cancellation.  This file
packages unrestricted support-avoidance formulas uniformly over the source
multiplicities, closes that representation under append and Cartesian
correction grids, and records the exact cancellation boundary for re-entering
the homogeneous compatible-grid profile compiler.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  IAProf

open HACoeff
open CCAggreg
open CEAlg
open CFSubsti
open
  SHPres
open
  CSComp
open
  CSComp.IFPkt
open
  CSComp.AISpec
open COAvoida
open SEComp
open
  SFSpec
open HSPacket
open
  AAProf

/--
A homogeneous presentation of one unrestricted avoidance packet produces the
concrete homogeneous avoidance expression specialized at natural source
multiplicities.
-/
def avoidanceInhomogeneousPresentation
    {M N K leftDegree rightDegree : ℕ}
    {terms : List (DFTerm M N K)}
    {packets :
      ∀ _slots : Finset (Fin K),
        IFPkt}
    (specialization :
      AISpec terms packets)
    (slots : Finset (Fin K))
    (presentation :
      HPres (packets slots) leftDegree rightDegree) :
    SAExpr
      terms slots leftDegree rightDegree where
  expression :=
    HBExpr.ofProfiles
      presentation.homogeneous.profiles
      presentation.homogeneous.profiles_leftDegree
      presentation.homogeneous.profiles_rightDegree
  length_eq := by
    rw [← specialization.value_cast_length slots,
      ← presentation.value_eq]
    exact presentation.homogeneous.value_natCast

/--
Pointwise homogeneous presentations of unrestricted avoidance packets recover
the fixed-packet specialization consumed by the homogeneous compiler.
-/
def avoidanceInhomogeneousPresentations
    {M N K leftDegree rightDegree : ℕ}
    {terms : List (DFTerm M N K)}
    {packets :
      ∀ _slots : Finset (Fin K),
        IFPkt}
    (specialization :
      AISpec terms packets)
    (presentations :
      ∀ slots : Finset (Fin K),
        HPres (packets slots) leftDegree rightDegree) :
    SASpec
      terms
      (fun slots => (presentations slots).homogeneous)
      (fun slots =>
        avoidanceInhomogeneousPresentation
          specialization slots (presentations slots)) where
  ofExpression_eq _slots := by
    rfl

/--
A multiplicity-independent unrestricted support-avoidance packet family with
same-shape concrete terms and a uniformly nonempty witness.
-/
structure ISAvoida
    (K : ℕ)
    (shape : CWord HPAtom) where
  terms :
    ∀ M N : ℕ, List (DFTerm M N K)
  packets :
    ∀ _slots : Finset (Fin K),
      IFPkt
  specialization :
    ∀ M N : ℕ,
      AISpec
        (terms M N) packets
  shape_eq :
    ∀ (M N : ℕ) term,
      term ∈ terms M N →
        term.erasedShape = shape
  witness :
    ∀ M N : ℕ, DFTerm M N K
  witness_mem :
    ∀ M N : ℕ, witness M N ∈ terms M N

namespace ISAvoida

/-- Regard a homogeneous uniform family as an unrestricted one. -/
def ofHomogeneous
    {K : ℕ}
    {shape : CWord HPAtom}
    (family : USAvoida K shape) :
    ISAvoida K shape where
  terms :=
    family.terms
  packets slots :=
    IFPkt.ofHomogeneous
      (family.packets slots)
  specialization M N := by
    constructor
    intro slots
    rw [IFPkt.value_ofHomogeneous]
    exact
      (family.specialization M N).cast_avoiding_slots
        slots
  shape_eq :=
    family.shape_eq
  witness :=
    family.witness
  witness_mem :=
    family.witness_mem

/-- Append two unrestricted uniform families carrying the same erased shape. -/
def append
    {K : ℕ}
    {shape : CWord HPAtom}
    (left right :
      ISAvoida K shape) :
    ISAvoida K shape where
  terms M N :=
    left.terms M N ++ right.terms M N
  packets slots :=
    IFPkt.add
      (left.packets slots) (right.packets slots)
  specialization M N :=
    AISpec.append
      (left.specialization M N) (right.specialization M N)
  shape_eq M N term hterm := by
    rcases List.mem_append.mp hterm with hterm | hterm
    · exact left.shape_eq M N term hterm
    · exact right.shape_eq M N term hterm
  witness :=
    left.witness
  witness_mem M N :=
    List.mem_append_left _ (left.witness_mem M N)

/--
Cartesian correction of two unrestricted uniform families.  Their avoidance
packets multiply pointwise before any homogeneous cancellation theorem is
invoked.
-/
noncomputable def correctionGrid
    {K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (left :
      ISAvoida K leftShape)
    (right :
      ISAvoida K rightShape) :
    ISAvoida K
      (CWord.commutator leftShape rightShape) where
  terms M N :=
    DFTerm.correctionGrid (left.terms M N) (right.terms M N)
  packets slots :=
    IFPkt.multiply
      (left.packets slots) (right.packets slots)
  specialization M N :=
    AISpec.correctionGrid
      (left.specialization M N) (right.specialization M N)
  shape_eq M N term hterm := by
    rcases List.mem_flatMap.mp hterm with ⟨leftTerm, hleftTerm, hterm⟩
    rcases List.mem_map.mp hterm with ⟨rightTerm, hrightTerm, rfl⟩
    rw [DFTerm.erasedShape_corr,
      left.shape_eq M N leftTerm hleftTerm,
      right.shape_eq M N rightTerm hrightTerm]
  witness M N :=
    (left.witness M N).correction (right.witness M N)
  witness_mem M N := by
    apply List.mem_flatMap.mpr
    exact
      ⟨left.witness M N, left.witness_mem M N,
        List.mem_map.mpr
          ⟨right.witness M N, right.witness_mem M N, rfl⟩⟩

/--
Uniform cancellation data: every unrestricted avoidance packet has one fixed
homogeneous presentation in the family shape's bidegree.
-/
structure UniformHomogeneousPresentation
    {K : ℕ}
    {shape : CWord HPAtom}
    (family :
      ISAvoida K shape) where
  presentations :
    ∀ slots : Finset (Fin K),
      HPres
        (family.packets slots)
        shape.pairLeftDegree shape.pairRightDegree

/-- Already homogeneous families carry tautological cancellation data. -/
def uniformHomogeneousPresentation
    {K : ℕ}
    {shape : CWord HPAtom}
    (family : USAvoida K shape) :
    UniformHomogeneousPresentation (ofHomogeneous family) where
  presentations slots :=
    HPres.ofHomogeneous (family.packets slots)

/--
Promote an unrestricted uniform family into the homogeneous profile compiler
once pointwise uniform cancellation presentations have been supplied.
-/
noncomputable def uniformSupportAvoidance
    {K : ℕ}
    {shape : CWord HPAtom}
    (family :
      ISAvoida K shape)
    (presentation :
      UniformHomogeneousPresentation family) :
    USAvoida K shape where
  terms :=
    family.terms
  packets slots :=
    (presentation.presentations slots).homogeneous
  expressions M N slots :=
    avoidanceInhomogeneousPresentation
      (family.specialization M N) slots (presentation.presentations slots)
  specialization M N :=
    avoidanceInhomogeneousPresentations
      (family.specialization M N) presentation.presentations
  shape_eq :=
    family.shape_eq
  witness :=
    family.witness
  witness_mem :=
    family.witness_mem

end ISAvoida

end
  IAProf
end TCTex
end Submission

/-!
# Generated batches from unrestricted support-avoidance families

Operational support deletion is naturally unrestricted before cancellation.
This file composes uniform unrestricted parent families and their homogeneous
presentations directly into generated compatible-grid batches.  It exposes
the exact input shape expected from a future symbolic Hall collector.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  OBList

open HACoeff
open RRPkt
open
  ITRec
open CFCollec
open CFCollec.DFTerm
open
  BLAlign
open
  IAProf
open
  AAProf
open CCGrida
open OCClos
open OCClos.DFTerm
open OCPartit
open RITrace

namespace GPBatch

/--
Construct one generated crossing batch from unrestricted uniform parent
families once their pointwise support-avoidance formulas have homogeneous
presentations.
-/
noncomputable def uniform_inhomogeneous_families
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {sourceLeft sourceRight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length)
    (parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2)
    (rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (left :
      ISAvoida K leftShape)
    (right :
      ISAvoida K rightShape)
    (leftPresentation :
      left.UniformHomogeneousPresentation)
    (rightPresentation :
      right.UniformHomogeneousPresentation)
    (hcompatible :
      ∀ M N : ℕ,
        correctionPairCompatible (left.witness M N) (right.witness M N))
    (leftShape_eq :
      crossing.1.erasedShape = leftShape)
    (rightShape_eq :
      crossing.2.erasedShape = rightShape) :
    GPBatch
      n leftWeight rightWeight hleftWeight hrightWeight :=
  uniformAvoidanceFamilies
    crossing parents rootWeight
      (left.uniformSupportAvoidance leftPresentation)
      (right.uniformSupportAvoidance rightPresentation)
      hcompatible leftShape_eq rightShape_eq

/--
The promoted unrestricted-parent batch has the expected repeated-root trace
with the original unrestricted parent term lists.
-/
@[simp]
lemma inhomogeneous_avoidance_families
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {sourceLeft sourceRight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length)
    (parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2)
    (rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (left :
      ISAvoida K leftShape)
    (right :
      ISAvoida K rightShape)
    (leftPresentation :
      left.UniformHomogeneousPresentation)
    (rightPresentation :
      right.UniformHomogeneousPresentation)
    (hcompatible :
      ∀ M N : ℕ,
        correctionPairCompatible (left.witness M N) (right.witness M N))
    (leftShape_eq :
      crossing.1.erasedShape = leftShape)
    (rightShape_eq :
      crossing.2.erasedShape = rightShape)
    (M N : ℕ) :
    (uniform_inhomogeneous_families
      (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
      crossing parents rootWeight left right
        leftPresentation rightPresentation hcompatible
        leftShape_eq rightShape_eq).indexTrace M N =
      List.replicate
        (compatibleCorrectionGrid (left.terms M N) (right.terms M N)).length
        (guardedGridParents
          hleftWeight hrightWeight crossing parents rootWeight) := by
  rfl

/--
Shape erasure of the promoted unrestricted-parent batch is the corresponding
repeated parent-shape commutator block.
-/
@[simp]
lemma erased_avoidance_families
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {sourceLeft sourceRight K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length)
    (parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2)
    (rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n)
    (left :
      ISAvoida K leftShape)
    (right :
      ISAvoida K rightShape)
    (leftPresentation :
      left.UniformHomogeneousPresentation)
    (rightPresentation :
      right.UniformHomogeneousPresentation)
    (hcompatible :
      ∀ M N : ℕ,
        correctionPairCompatible (left.witness M N) (right.witness M N))
    (leftShape_eq :
      crossing.1.erasedShape = leftShape)
    (rightShape_eq :
      crossing.2.erasedShape = rightShape)
    (M N : ℕ) :
    generatedParentsBatch
        (uniform_inhomogeneous_families
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          crossing parents rootWeight left right
            leftPresentation rightPresentation hcompatible
            leftShape_eq rightShape_eq)
        M N =
      List.replicate
        (compatibleCorrectionGrid (left.terms M N) (right.terms M N)).length
        (CWord.commutator leftShape rightShape) := by
  rfl

end GPBatch

end
  OBList
end TCTex
end Submission

/-!
# Scheduled generated batches from unrestricted uniform support profiles

Every retained node of a concrete collector schedule stores its crossing
parents and cutoff proof.  Generated-source provenance supplies the remaining
parent-generation proofs.  This file adds one unrestricted uniform
support-profile annotation to each stored crossing, compiles the annotations
to generated compatible-grid batches, and proves the three schedule
constructor equations.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UIComp

open HACoeff
open RRPkt
open
  ITRec
open CRProgra
open
  CRProgra.RSPrograa
open CPProven
open CFCollec
open CFCollec.DFTerm
open
  OBList
open
  IAProf
open CCGrida
open OCClos
open OCClos.DFTerm
open OCPartit

/--
Uniform unrestricted support-profile data attached to one concrete
inverse-raw generated crossing.  The provenance and cutoff proofs remain the
responsibility of the ambient concrete schedule.
-/
structure UIAvoida
    {sourceLeft sourceRight : ℕ}
    (crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length) where
  K :
    ℕ
  leftShape :
    CWord HPAtom
  rightShape :
    CWord HPAtom
  left :
    ISAvoida K leftShape
  right :
    ISAvoida K rightShape
  leftPresentation :
    left.UniformHomogeneousPresentation
  rightPresentation :
    right.UniformHomogeneousPresentation
  compatible :
    ∀ M N : ℕ,
      correctionPairCompatible (left.witness M N) (right.witness M N)
  leftShape_eq :
    crossing.1.erasedShape = leftShape
  rightShape_eq :
    crossing.2.erasedShape = rightShape

namespace UIAvoida

/-- Compile one annotated scheduled crossing to one generated batch. -/
noncomputable def toBatch
    {sourceLeft sourceRight n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length}
    (profile :
      UIAvoida crossing)
    (parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2)
    (rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n) :
    GPBatch
      n leftWeight rightWeight hleftWeight hrightWeight :=
  GPBatch.uniform_inhomogeneous_families
    crossing parents rootWeight profile.left profile.right
      profile.leftPresentation profile.rightPresentation profile.compatible
      profile.leftShape_eq profile.rightShape_eq

end UIAvoida

/-- Crossing annotations for every retained node of one concrete schedule. -/
abbrev InhomogeneousAvoidanceProfiles
    {M N n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight) :=
  ∀ crossing,
    crossing ∈ program.crossings →
      UIAvoida crossing

/--
Compile all annotated retained nodes of one generated concrete schedule into
the corresponding ordered generated-batch list.
-/
noncomputable def generatedBatchesProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program) :
    List (GPBatch
      n leftWeight rightWeight hleftWeight hrightWeight) :=
  program.crossings.attach.map fun crossing =>
    (profiles crossing.1 crossing.2).toBatch
      (generated crossing.1 crossing.2)
      (program.weight_correction_crossings crossing.2)

/-- Restrict append annotations to the left child. -/
def profilesLeftAppend
    {M N n leftWeight rightWeight : ℕ}
    {left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right)) :
    InhomogeneousAvoidanceProfiles
      left :=
  fun crossing hcrossing =>
    profiles crossing (List.mem_append_left _ hcrossing)

/-- Restrict append annotations to the right child. -/
def profilesRightAppend
    {M N n leftWeight rightWeight : ℕ}
    {left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right)) :
    InhomogeneousAvoidanceProfiles
      right :=
  fun crossing hcrossing =>
    profiles crossing (List.mem_append_right _ hcrossing)

/-- The empty schedule compiles to no generated batches. -/
@[simp]
lemma generated_batches_empty
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight)) :
    generatedBatchesProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        RSPrograa.empty
        (CGFroma.empty _) profiles =
      [] := by
  rfl

/-- Generated-batch compilation distributes over schedule append. -/
lemma generated_batches_append
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right)) :
    generatedBatchesProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.append left right)
        generated profiles =
      generatedBatchesProgram left
        (crossings_left_append generated)
        (profilesLeftAppend profiles) ++
      generatedBatchesProgram right
        (crossings_generated_append generated)
        (profilesRightAppend profiles) := by
  simp only [generatedBatchesProgram, RSPrograa.crossings,
    List.attach_append, List.map_append, List.map_map,
    profilesLeftAppend, profilesRightAppend]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro crossing _hcrossing
    rfl
  · apply List.map_congr_left
    intro crossing _hcrossing
    rfl

/-- Restrict retained-node annotations to the left child. -/
def profilesLeftRetained
    {M N n leftWeight rightWeight : ℕ}
    {left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    {crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    {hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    InhomogeneousAvoidanceProfiles
      left :=
  fun crossing hcrossing =>
    profiles crossing
      (List.mem_append_left _
        (List.mem_append_left _ hcrossing))

/-- Restrict retained-node annotations to the right child. -/
def profilesRightRetained
    {M N n leftWeight rightWeight : ℕ}
    {left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    {crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    {hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    InhomogeneousAvoidanceProfiles
      right :=
  fun crossing hcrossing =>
    profiles crossing (List.mem_append_right _ hcrossing)

/-- Recover the unrestricted profile attached to a retained root node. -/
def profileRootRetained
    {M N n leftWeight rightWeight : ℕ}
    {left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    {crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    {hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    UIAvoida
      (crossedLeft, crossedRight) :=
  profiles (crossedLeft, crossedRight) (by
    change
      (crossedLeft, crossedRight) ∈
        left.crossings ++ [(crossedLeft, crossedRight)] ++ right.crossings
    simp)

/--
A retained schedule node compiles its left child batches, one root batch, and
its right child batches.
-/
lemma generated_batches_program
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    generatedBatchesProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles =
      generatedBatchesProgram left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) ++
        [(profileRootRetained profiles).toBatch
          (generated_parents_retained generated) hweight] ++
      generatedBatchesProgram right
        (crossings_generated_retained generated)
        (profilesRightRetained profiles) := by
  simp only [generatedBatchesProgram, RSPrograa.crossings,
    List.attach_append, List.map_append, List.map_map,
    List.append_assoc, List.cons_append, List.nil_append]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro crossing _hcrossing
    rfl
  · apply congrArg₂ (· :: ·)
    · rfl
    · apply List.map_congr_left
      intro crossing _hcrossing
      rfl

end UIComp
end TCTex
end Submission

/-!
# Erased-shape traces of scheduled unrestricted generated batches

The scheduled unrestricted batch compiler produces a finite generated-batch
list.  This file erases each batch to its repeated commutator-shape block and
proves that the flattened trace satisfies the concrete schedule constructors.
The retained-node equation exposes the compatible-grid cardinality attached
to the root annotation.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UISchedu

open HACoeff
open RRPkt
open
  ITRec
open CRProgra
open
  CRProgra.RSPrograa
open CPProven
open CFCollec
open CFCollec.DFTerm
open
  OBList
open
  BLAlign
open CCGrida
open OCClos
open OCClos.DFTerm
open OCPartit
open UIComp

/-- Flatten the repeated erased-shape blocks of all annotated scheduled batches. -/
noncomputable def erasedTraceProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program)
    (sourceLeft sourceRight : ℕ) :
    List (CWord HPAtom) :=
  ((generatedBatchesProgram
      (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
      program generated profiles).map fun batch =>
        generatedParentsBatch
          batch sourceLeft sourceRight).flatten

/-- The empty schedule has no erased generated-batch trace. -/
@[simp]
lemma erased_shape_empty
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight))
    (sourceLeft sourceRight : ℕ) :
    erasedTraceProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        RSPrograa.empty
        (CGFroma.empty _) profiles sourceLeft sourceRight =
      [] := by
  rfl

/-- Erased generated-batch traces distribute over schedule append. -/
lemma erased_shape_append
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right))
    (sourceLeft sourceRight : ℕ) :
    erasedTraceProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.append left right)
        generated profiles sourceLeft sourceRight =
      erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight ++
        erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight := by
  rw [erasedTraceProgram, generated_batches_append,
    List.map_append, List.flatten_append]
  rfl

/--
A retained schedule node contributes its left erased trace, the repeated
compatible-grid commutator block attached to its root annotation, and its
right erased trace.
-/
lemma erased_shape_retained
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ) :
    erasedTraceProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight =
      erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight ++
        List.replicate
          (compatibleCorrectionGrid
            ((profileRootRetained profiles).left.terms
              sourceLeft sourceRight)
            ((profileRootRetained profiles).right.terms
              sourceLeft sourceRight)).length
          (CWord.commutator
            (profileRootRetained profiles).leftShape
            (profileRootRetained profiles).rightShape) ++
        erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight := by
  rw [erasedTraceProgram, generated_batches_program,
    List.map_append, List.flatten_append, List.map_append,
    List.flatten_append]
  simp only [List.map_singleton, List.flatten_singleton]
  rw [
    UIAvoida.toBatch,
    GPBatch.erased_avoidance_families]
  rfl

end UISchedu
end TCTex
end Submission

/-!
# Recursive erased-shape programs for scheduled unrestricted batches

The scheduled unrestricted batch compiler was previously flattened to a list
of repeated Hall-shape blocks.  The guarded raw-source expansion is already
packaged as a recursive erased-shape program.  This file retains the recursive
shape of the annotated concrete schedule as well.

At a retained node the compiler emits the left child program, one repeated
commutator block whose cardinality is the compatible correction grid, and the
right child program.  Its trace is exactly the flattened generated-batch trace.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UIErased

open HACoeff
open
  ITRec
open CRProgra
open
  CRProgra.RSPrograa
open CPProven
open CFCollec
open CCGrida
open OCPartit
open UIComp
open UISchedu
open RTProgra
open
  GRProgra

/--
Compile one annotated concrete schedule to a recursive erased-shape program.
The generated-source witness is retained so the recursive children carry the
same provenance evidence as the flattened batch compiler.
-/
noncomputable def erasedProgram
    {M N n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program)
    (sourceLeft sourceRight : ℕ) :
    ESProgra :=
  match program with
  | .empty =>
      ESProgra.empty
  | .append left right =>
      ESProgra.append
        (erasedProgram left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight)
        (erasedProgram right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight)
  | .retained left _crossedLeft _crossedRight _hweight right =>
      ESProgra.append
        (erasedProgram left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight)
        (ESProgra.append
          (replicateErasedProgram
            (CWord.commutator
              (profileRootRetained profiles).leftShape
              (profileRootRetained profiles).rightShape)
            (compatibleCorrectionGrid
              ((profileRootRetained profiles).left.terms
                sourceLeft sourceRight)
              ((profileRootRetained profiles).right.terms
                sourceLeft sourceRight)).length)
          (erasedProgram right
            (crossings_generated_retained generated)
            (profilesRightRetained profiles) sourceLeft sourceRight))

/-- The empty annotated schedule compiles to the empty erased-shape program. -/
@[simp]
lemma shape_program_empty
    {M N n leftWeight rightWeight : ℕ}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight))
    (sourceLeft sourceRight : ℕ) :
    erasedProgram
        RSPrograa.empty
        (CGFroma.empty _) profiles sourceLeft sourceRight =
      ESProgra.empty := by
  rfl

/-- Recursive erased-shape program compilation distributes over append. -/
lemma shape_program_append
    {M N n leftWeight rightWeight : ℕ}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right))
    (sourceLeft sourceRight : ℕ) :
    erasedProgram
        (RSPrograa.append left right)
        generated profiles sourceLeft sourceRight =
      ESProgra.append
        (erasedProgram left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight)
        (erasedProgram right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight) := by
  rfl

/-- A retained node exposes its left program, repeated root block, and right program. -/
lemma shape_program_retained
    {M N n leftWeight rightWeight : ℕ}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ) :
    erasedProgram
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight =
      ESProgra.append
        (erasedProgram left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight)
        (ESProgra.append
          (replicateErasedProgram
            (CWord.commutator
              (profileRootRetained profiles).leftShape
              (profileRootRetained profiles).rightShape)
            (compatibleCorrectionGrid
              ((profileRootRetained profiles).left.terms
                sourceLeft sourceRight)
              ((profileRootRetained profiles).right.terms
                sourceLeft sourceRight)).length)
          (erasedProgram right
            (crossings_generated_retained generated)
            (profilesRightRetained profiles) sourceLeft sourceRight)) := by
  rfl

/-- Tracing the recursive annotated program recovers the flattened generated-batch trace. -/
lemma trace_shape_program
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program)
    (sourceLeft sourceRight : ℕ) :
    (erasedProgram
      program generated profiles sourceLeft sourceRight).trace =
        erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          program generated profiles sourceLeft sourceRight := by
  induction program with
  | empty =>
      rfl
  | append left right ihleft ihright =>
      rw [shape_program_append,
        ESProgra.trace_append,
        erased_shape_append,
        ihleft, ihright]
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      rw [shape_program_retained,
        ESProgra.trace_append,
        ESProgra.trace_append,
        replicate_erased_program,
        erased_shape_retained,
        ihleft, ihright]
      simp only [List.append_assoc]

end UIErased
end TCTex
end Submission

/-!
# Scheduled unrestricted generated batches aligned with guarded expansion

The unrestricted support-profile compiler produces generated compatible-grid
batches from one concrete retained-correction schedule.  The universal
generated-batch expansion boundary only asks that their flattened erased-shape
trace permute to the guarded raw-source expansion.

This file packages that schedule-local synchronization obligation and also
records the induction-friendly variant comparing against the scheduler-order
recursive erased-shape program.  The existing guarded expansion permutation
transports the recursive-program comparison to the universal batch criterion.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UIAlign

open HACoeff
open CRProgra
open CPProven
open
  PMCoales
open CFCollec
open
  OBList
open
  SEAlign
open FIProf
open OCPartit
open UIComp
open UISchedu
open
  ISLift
open
  GRProgra

/--
Schedule-local form of the universal generated-batch expansion criterion.
The concrete schedule and its annotations are retained so that the remaining
permutation can be proved by schedule recursion.
-/
structure SGDecomp
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  sourceLeft :
    ℕ
  sourceRight :
    ℕ
  program :
    RSPrograa
      (M := sourceLeft) (N := sourceRight)
      (K := (inverseLabelledCollection sourceLeft sourceRight).factors.length)
      n leftWeight rightWeight
  generated :
    CGFroma
      (inverseDecoratedTerms sourceLeft sourceRight) program
  profiles :
    InhomogeneousAvoidanceProfiles
      program
  expansion_shape_perm :
    ∀ M N,
      List.Perm
        (erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          program generated profiles M N)
        (guardedExpansionErased
          raw M N)

namespace SGDecomp

/-- Forget the concrete schedule after compiling its annotated retained nodes. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (decomposition :
      SGDecomp
        hleftWeight hrightWeight raw) :
    PCDecomp
      hleftWeight hrightWeight raw where
  batches :=
    generatedBatchesProgram
      (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
      decomposition.program decomposition.generated decomposition.profiles
  expansion_shape_perm M N := by
    change
      List.Perm
        (erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          decomposition.program decomposition.generated decomposition.profiles
          M N)
        (guardedExpansionErased
          raw M N)
    exact decomposition.expansion_shape_perm M N

end SGDecomp

/--
Induction-ready schedule-local criterion.  Both sides are now expressed in
scheduler order: the annotated concrete schedule on the left and the
recursive guarded raw-source expansion program on the right.
-/
structure SSDecomp
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  sourceLeft :
    ℕ
  sourceRight :
    ℕ
  program :
    RSPrograa
      (M := sourceLeft) (N := sourceRight)
      (K := (inverseLabelledCollection sourceLeft sourceRight).factors.length)
      n leftWeight rightWeight
  generated :
    CGFroma
      (inverseDecoratedTerms sourceLeft sourceRight) program
  profiles :
    InhomogeneousAvoidanceProfiles
      program
  scheduler_program_perm :
    ∀ M N,
      List.Perm
        (erasedTraceProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          program generated profiles M N)
        (guardedSchedulerProgram
          (multiplicityProfileShape
            raw)
          M N).trace

namespace SSDecomp

/-- Transport the scheduler-order comparison through the guarded expansion permutation. -/
noncomputable def schedu_gener_decom
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (decomposition :
      SSDecomp
        hleftWeight hrightWeight raw) :
    SGDecomp
      hleftWeight hrightWeight raw where
  sourceLeft :=
    decomposition.sourceLeft
  sourceRight :=
    decomposition.sourceRight
  program :=
    decomposition.program
  generated :=
    decomposition.generated
  profiles :=
    decomposition.profiles
  expansion_shape_perm M N :=
    (decomposition.scheduler_program_perm M N).trans
      (idxSchedulerProgram
        raw M N).symm

/-- Compile the induction-ready schedule comparison to universal generated batches. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (decomposition :
      SSDecomp
        hleftWeight hrightWeight raw) :
    PCDecomp
      hleftWeight hrightWeight raw :=
  decomposition.schedu_gener_decom
    |>.generatedParentsDecomposition

end SSDecomp

end UIAlign
end TCTex
end Submission

/-!
# Finite-index traces of scheduled unrestricted generated batches

The scheduled unrestricted batch compiler produces generated compatible-grid
batches.  Before erasing their roots to Hall shapes, each batch has a repeated
finite polynomial-orbit index block.  This file flattens those blocks and
records the concrete schedule constructor equations.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UFIdx

open HACoeff
open
  ITRec
open CRProgra
open
  CRProgra.RSPrograa
open CPProven
open CFCollec
open
  OBList
open
  BLAlign
open CCGrida
open OCPartit
open UIComp
open UISchedu
open
  RITrace

/-- Flatten the repeated finite-index blocks of all annotated scheduled batches. -/
noncomputable def finIdxProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program)
    (sourceLeft sourceRight : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  ((generatedBatchesProgram
      (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
      program generated profiles).map fun batch =>
        batch.indexTrace sourceLeft sourceRight).flatten

/-- The empty schedule has no finite-index generated-batch trace. -/
@[simp]
lemma index_program_empty
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight))
    (sourceLeft sourceRight : ℕ) :
    finIdxProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        RSPrograa.empty
        (CGFroma.empty _) profiles sourceLeft sourceRight =
      [] := by
  rfl

/-- Finite generated-batch traces distribute over schedule append. -/
lemma index_program_append
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right))
    (sourceLeft sourceRight : ℕ) :
    finIdxProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.append left right)
        generated profiles sourceLeft sourceRight =
      finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight ++
        finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight := by
  rw [finIdxProgram, generated_batches_append,
    List.map_append, List.flatten_append]
  rfl

/--
A retained schedule node contributes its left finite trace, the repeated
concrete root index block, and its right finite trace.
-/
lemma index_program_retained
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ) :
    finIdxProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight =
      finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight ++
        List.replicate
          (compatibleCorrectionGrid
            ((profileRootRetained profiles).left.terms
              sourceLeft sourceRight)
            ((profileRootRetained profiles).right.terms
              sourceLeft sourceRight)).length
          (guardedGridParents
            hleftWeight hrightWeight (crossedLeft, crossedRight)
            (generated_parents_retained generated) hweight) ++
        finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight := by
  rw [finIdxProgram, generated_batches_program,
    List.map_append, List.flatten_append, List.map_append,
    List.flatten_append]
  simp only [List.map_singleton, List.flatten_singleton]
  rfl

/-- Erasing the finite-index batch trace recovers the existing erased-shape trace. -/
lemma key_shape_program
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program)
    (sourceLeft sourceRight : ℕ) :
    (finIdxProgram
      (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
      program generated profiles sourceLeft sourceRight).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      erasedTraceProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        program generated profiles sourceLeft sourceRight := by
  unfold finIdxProgram
  unfold erasedTraceProgram
  exact
    keyGridBatch
      (generatedBatchesProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        program generated profiles)
      sourceLeft sourceRight

end UFIdx
end TCTex
end Submission

/-!
# Multiplicity recurrences for scheduled unrestricted generated batches

The flattened erased-shape trace of annotated generated batches satisfies the
same scheduler constructors as the concrete retained-correction program.  This
file records the corresponding scalar Hall-shape multiplicity recurrence.

At a retained node the root contribution is the cardinality of the compatible
correction grid when its commutator shape matches the requested Hall word, and
zero otherwise.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UMRec

open HACoeff
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open CCGrida
open OCPartit
open UIComp
open UISchedu

/-- Multiplicity of one erased Hall shape in an annotated generated-batch schedule. -/
noncomputable def erasedMultiplicityProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program)
    (sourceLeft sourceRight : ℕ)
    (word : CWord HPAtom) :
    ℕ :=
  (erasedTraceProgram
    (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
    program generated profiles sourceLeft sourceRight).count word

/-- The empty annotated schedule has zero shape multiplicity. -/
@[simp]
lemma erased_program_empty
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight))
    (sourceLeft sourceRight : ℕ)
    (word : CWord HPAtom) :
    erasedMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        RSPrograa.empty
        (CGFroma.empty _) profiles sourceLeft sourceRight word =
      0 := by
  rfl

/-- Annotated schedule concatenation adds Hall-shape multiplicities. -/
lemma erased_program_append
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right))
    (sourceLeft sourceRight : ℕ)
    (word : CWord HPAtom) :
    erasedMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.append left right)
        generated profiles sourceLeft sourceRight word =
      erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight word +
        erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight word := by
  rw [erasedMultiplicityProgram, erased_shape_append,
    List.count_append]
  rfl

/--
A retained node contributes its child multiplicities and the matching
compatible-grid root cardinality.
-/
lemma erased_program_retained
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ)
    (word : CWord HPAtom) :
    erasedMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight word =
      erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight word +
        (if
          CWord.commutator
              (profileRootRetained profiles).leftShape
              (profileRootRetained profiles).rightShape =
            word then
          (compatibleCorrectionGrid
            ((profileRootRetained profiles).left.terms
              sourceLeft sourceRight)
            ((profileRootRetained profiles).right.terms
              sourceLeft sourceRight)).length
        else
          0) +
        erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight word := by
  rw [erasedMultiplicityProgram, erased_shape_retained,
    List.count_append, List.count_append, List.count_replicate]
  simp only [erasedMultiplicityProgram, beq_iff_eq]

/-- A matching retained root contributes its full compatible-grid cardinality. -/
lemma erased_multiplicity_program
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ)
    (word : CWord HPAtom)
    (hword :
      CWord.commutator
          (profileRootRetained profiles).leftShape
          (profileRootRetained profiles).rightShape =
        word) :
    erasedMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight word =
      erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight word +
        (compatibleCorrectionGrid
          ((profileRootRetained profiles).left.terms sourceLeft sourceRight)
          ((profileRootRetained profiles).right.terms
            sourceLeft sourceRight)).length +
        erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight word := by
  rw [erased_program_retained, if_pos hword]

/-- A nonmatching retained root contributes no multiplicity. -/
lemma erased_program_ne
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ)
    (word : CWord HPAtom)
    (hword :
      CWord.commutator
          (profileRootRetained profiles).leftShape
          (profileRootRetained profiles).rightShape ≠
        word) :
    erasedMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight word =
      erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight word +
        erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight word := by
  rw [erased_program_retained, if_neg hword, Nat.add_zero]

end UMRec
end TCTex
end Submission

/-!
# Structural alignment for scheduled unrestricted generated batches

The annotated schedule compiler and the guarded raw-source expansion now both
produce recursive erased-shape programs.  This file packages the remaining
alignment at that structural level.  A constructorwise coalescing derivation,
or equivalently pointwise Hall-shape count equalities, compiles to the
schedule-local scheduler-program permutation and then to the universal
generated-batch expansion decomposition.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UIStruct

open HACoeff
open
  RPCoales
open
  RPCrit
open CRProgra
open CPProven
open CFCollec
open
  SEAlign
open FIProf
open OCPartit
open UIComp
open UIErased
open UISchedu
open UIAlign
open
  ISLift
open RTProgra
open
  GRProgra

/--
Constructor-level comparison between the annotated concrete schedule and the
guarded raw-source scheduler program.
-/
structure SSCoales
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  sourceLeft :
    ℕ
  sourceRight :
    ℕ
  program :
    RSPrograa
      (M := sourceLeft) (N := sourceRight)
      (K := (inverseLabelledCollection sourceLeft sourceRight).factors.length)
      n leftWeight rightWeight
  generated :
    CGFroma
      (inverseDecoratedTerms sourceLeft sourceRight) program
  profiles :
    InhomogeneousAvoidanceProfiles
      program
  programs_coalesce :
    ∀ M N,
      EMCoales.Rel
        (erasedProgram program generated profiles M N)
        (guardedSchedulerProgram
          (multiplicityProfileShape
            raw)
          M N)

namespace SSCoales

/-- Structural coalescing supplies the schedule-local scheduler-program permutation. -/
noncomputable def schedu_sched_decom
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (decomposition :
      SSCoales
        hleftWeight hrightWeight raw) :
    SSDecomp
      hleftWeight hrightWeight raw where
  sourceLeft :=
    decomposition.sourceLeft
  sourceRight :=
    decomposition.sourceRight
  program :=
    decomposition.program
  generated :=
    decomposition.generated
  profiles :=
    decomposition.profiles
  scheduler_program_perm M N := by
    rw [←
      trace_shape_program
        hleftWeight hrightWeight decomposition.program
          decomposition.generated decomposition.profiles M N]
    exact (decomposition.programs_coalesce M N).trace_perm

/-- Compile structural schedule alignment to the universal generated-batch criterion. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (decomposition :
      SSCoales
        hleftWeight hrightWeight raw) :
    PCDecomp
      hleftWeight hrightWeight raw :=
  decomposition.schedu_sched_decom
    |>.generatedParentsDecomposition

end SSCoales

/--
Multiplicity formulation of the structural schedule comparison.  The left
side is the flattened generated-batch trace, so its constructor recurrences
are available directly.
-/
structure SBDecomp
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  sourceLeft :
    ℕ
  sourceRight :
    ℕ
  program :
    RSPrograa
      (M := sourceLeft) (N := sourceRight)
      (K := (inverseLabelledCollection sourceLeft sourceRight).factors.length)
      n leftWeight rightWeight
  generated :
    CGFroma
      (inverseDecoratedTerms sourceLeft sourceRight) program
  profiles :
    InhomogeneousAvoidanceProfiles
      program
  scheduler_program_count :
    ∀ M N word,
      (erasedTraceProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        program generated profiles M N).count word =
      (guardedSchedulerProgram
        (multiplicityProfileShape raw)
        M N).trace.count word

namespace SBDecomp

/-- Pointwise Hall-shape multiplicities supply structural coalescing. -/
noncomputable def
    scheduledStructuralCoalescing
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (decomposition :
      SBDecomp
        hleftWeight hrightWeight raw) :
    SSCoales
      hleftWeight hrightWeight raw where
  sourceLeft :=
    decomposition.sourceLeft
  sourceRight :=
    decomposition.sourceRight
  program :=
    decomposition.program
  generated :=
    decomposition.generated
  profiles :=
    decomposition.profiles
  programs_coalesce M N := by
    apply
      SPCrit.coalesces_count.mpr
    intro word
    rw [
      trace_shape_program
        hleftWeight hrightWeight decomposition.program
          decomposition.generated decomposition.profiles M N]
    exact decomposition.scheduler_program_count M N word

/-- Compile pointwise schedule multiplicities to the universal generated-batch criterion. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (decomposition :
      SBDecomp
        hleftWeight hrightWeight raw) :
    PCDecomp
      hleftWeight hrightWeight raw :=
  decomposition.scheduledStructuralCoalescing
    |>.generatedParentsDecomposition

end SBDecomp

end UIStruct
end TCTex
end Submission

/-!
# Finite-index multiplicity recurrences for scheduled generated batches

The flattened finite-index trace of annotated generated batches satisfies the
same schedule constructors as its erased Hall-shape trace.  This file records
the scalar recurrence for one retained polynomial-orbit index.

At a retained node the root contribution is the cardinality of the compatible
correction grid when the concrete retained root index matches the requested
index, and zero otherwise.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  UIRec

open HACoeff
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open CCGrida
open OCPartit
open UIComp
open UFIdx
open RITrace

/-- Multiplicity of one retained orbit index in an annotated generated-batch schedule. -/
noncomputable def indexMultiplicityProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program)
    (sourceLeft sourceRight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  (finIdxProgram
    (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
    program generated profiles sourceLeft sourceRight).count index

/-- The empty annotated schedule has zero finite-index multiplicity. -/
@[simp]
lemma multiplicity_program_empty
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight))
    (sourceLeft sourceRight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        RSPrograa.empty
        (CGFroma.empty _) profiles sourceLeft sourceRight index =
      0 := by
  rfl

/-- Annotated schedule concatenation adds finite-index multiplicities. -/
lemma multiplicity_program_append
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right))
    (sourceLeft sourceRight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.append left right)
        generated profiles sourceLeft sourceRight index =
      indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight index +
        indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight index := by
  rw [indexMultiplicityProgram, index_program_append,
    List.count_append]
  rfl

/--
A retained node contributes its child multiplicities and the matching
compatible-grid root cardinality.
-/
lemma index_multiplicity_program
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight index =
      indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight index +
        (if
          guardedGridParents
              hleftWeight hrightWeight (crossedLeft, crossedRight)
              (generated_parents_retained generated) hweight =
            index then
          (compatibleCorrectionGrid
            ((profileRootRetained profiles).left.terms
              sourceLeft sourceRight)
            ((profileRootRetained profiles).right.terms
              sourceLeft sourceRight)).length
        else
          0) +
        indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight index := by
  rw [indexMultiplicityProgram, index_program_retained,
    List.count_append, List.count_append, List.count_replicate]
  simp only [indexMultiplicityProgram, beq_iff_eq]

/-- A matching retained root contributes its full compatible-grid cardinality. -/
lemma multiplicity_program_retained
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hindex :
      guardedGridParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight =
        index) :
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight index =
      indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight index +
        (compatibleCorrectionGrid
          ((profileRootRetained profiles).left.terms sourceLeft sourceRight)
          ((profileRootRetained profiles).right.terms
            sourceLeft sourceRight)).length +
        indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight index := by
  rw [index_multiplicity_program, if_pos hindex]

/-- A nonmatching retained root contributes no finite-index multiplicity. -/
lemma multiplicity_program_ne
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (crossedLeft crossedRight :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right))
    (sourceLeft sourceRight : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hindex :
      guardedGridParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight ≠
        index) :
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight index =
      indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight index +
        indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight index := by
  rw [index_multiplicity_program, if_neg hindex, Nat.add_zero]

end UIRec
end TCTex
end Submission

/-!
# Scalar synchronization for scheduled unrestricted generated batches

The annotated schedule multiplicity recurrence is the collector-facing scalar
quantity: at each retained node it adds the compatible-grid cardinality of the
matching commutator root.  The guarded raw-source expansion has its own
scheduler-order recursive erased-shape program.

This file names the remaining arbitrary-cutoff synchronization theorem
directly at that scalar interface.  A proof of the recurrence-defined count
identity compiles through structural coalescing to the universal generated
compatible-grid batch expansion decomposition.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace UIBatch

open HACoeff
open CRProgra
open CPProven
open CFCollec
open
  SEAlign
open FIProf
open OCPartit
open UIComp
open
  UMRec
open UIStruct
open
  ISLift
open
  GRProgra

/--
Scalar arbitrary-cutoff synchronization kernel.  The left side is governed by
the annotated concrete schedule recurrence; the right side is the recursive
guarded raw-source scheduler program.
-/
structure SBSync
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  sourceLeft :
    ℕ
  sourceRight :
    ℕ
  program :
    RSPrograa
      (M := sourceLeft) (N := sourceRight)
      (K := (inverseLabelledCollection sourceLeft sourceRight).factors.length)
      n leftWeight rightWeight
  generated :
    CGFroma
      (inverseDecoratedTerms sourceLeft sourceRight) program
  profiles :
    InhomogeneousAvoidanceProfiles
      program
  scheduler_program_multiplicity :
    ∀ M N word,
      erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          program generated profiles M N word =
        (guardedSchedulerProgram
          (multiplicityProfileShape
            raw)
          M N).trace.count word

namespace SBSync

/-- Scalar synchronization supplies the generic scheduler-program multiplicity criterion. -/
noncomputable def
    scheduledBatchDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (kernel :
      SBSync
        hleftWeight hrightWeight raw) :
    SBDecomp
      hleftWeight hrightWeight raw where
  sourceLeft :=
    kernel.sourceLeft
  sourceRight :=
    kernel.sourceRight
  program :=
    kernel.program
  generated :=
    kernel.generated
  profiles :=
    kernel.profiles
  scheduler_program_count M N word :=
    kernel.scheduler_program_multiplicity M N word

/-- Scalar synchronization supplies recursive-program structural coalescing. -/
noncomputable def
    scheduledStructuralCoalescing
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (kernel :
      SBSync
        hleftWeight hrightWeight raw) :
    SSCoales
      hleftWeight hrightWeight raw :=
  kernel.scheduledBatchDecomposition
    |>.scheduledStructuralCoalescing

/-- Scalar synchronization compiles to the universal generated-batch expansion criterion. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (kernel :
      SBSync
        hleftWeight hrightWeight raw) :
    PCDecomp
      hleftWeight hrightWeight raw :=
  kernel.scheduledBatchDecomposition
    |>.generatedParentsDecomposition

end SBSync

end UIBatch
end TCTex
end Submission

/-!
# Claim 5 from synchronized scheduled unrestricted generated batches

The scalar synchronization kernel compiles annotated unrestricted generated
batches to the universal guarded raw-source expansion criterion.  The existing
expansion bridge then transports those batches through the concrete endpoint
scheduler.

This file composes that operational route with the remaining signed extension
boundary and restates the Claim 5 coordinate-polynomial constructor directly
in scheduled unrestricted-batch vocabulary.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RPCrit
open
  FPInterp
open CRLayer
open
  SEAlign
open
  FIProf
open
  UIBatch

namespace
  UIBatch

namespace SBSync

/--
Remaining signed extension after synchronized scheduled batches have been
compiled through the operational endpoint scheduler.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (kernel :
      SBSync
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PCDecomp.AILift.{u}
    (d := d) scheduler
      kernel.generatedParentsDecomposition

/--
Truncated signed recollection law after synchronized scheduled batches have
been compiled through the operational endpoint scheduler.
-/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (kernel :
      SBSync
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PCDecomp.SatisfiesTruncEval.{u}
    (d := d) scheduler
      kernel.generatedParentsDecomposition

/-- For synchronized scheduled batches, the two signed extension inputs agree. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (kernel :
      SBSync
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler kernel ↔
      AILift.{u} (d := d) scheduler kernel :=
  PCDecomp.satisfies_trunc_lift
    scheduler
      kernel.generatedParentsDecomposition

end SBSync

end
  UIBatch

namespace TSInput

open
  UIBatch

/--
Synchronized scheduled unrestricted batches, their signed lift, singleton
recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem
    scheduledBatchSynchronization
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (kernel :
      SBSync
        (by simp) (by simp) scheduler.raw)
    (lift :
      SBSync.AILift.{u}
        (d := d) scheduler kernel)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordBranchesLift
    hn H hH scheduler
      kernel.generatedParentsDecomposition
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent constructor input for
the synchronized scheduled-batch Claim 5 route.
-/
theorem
    coordSynchronizationTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (kernel :
      SBSync
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SBSync.SatisfiesTruncEval.{u}
        (d := d) scheduler kernel)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordPolyTrunc
    hn H hH scheduler
      kernel.generatedParentsDecomposition
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

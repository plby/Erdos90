import Submission.Group.Zassenhaus.PolynomialOrbitVocabulary
import Submission.Group.Zassenhaus.RetainedProgramBoundary
import Submission.Group.Zassenhaus.InverseUniversalOrbit
import Submission.Group.Zassenhaus.CanonicalPacketAlignment
import Submission.Group.Zassenhaus.SelectedProfileAlgebra
import Submission.Group.Zassenhaus.SchedulePrograms
import Submission.Group.Zassenhaus.EndpointShapeInterpolation

/-!
# Recursive erased-shape programs for polynomial-orbit expansions

The recipe-free polynomial-orbit recursion emits its correction root before
the two recursive children.  The operational cutoff collector records retained
crossings in insertion order: left recursive corrections, then the retained
root crossing, then right recursive corrections.

These orders need not agree literally.  After erasing polynomial-orbit
decorations to Hall shapes, however, the root-first finite packet is a
permutation of a recursively structured scheduler-order program.  This file
records that local bridge for arbitrary cutoffs.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  REProgra

open
  RRPkt
open
  RRPkt.POObstru
open
  ROTransi
open
  RITrace
open
  OREnvelo
open
  IEDecomp
open
  ILProgra
open
  RIRecurs
open
  UOVocabu
open
  RPEnvelo
open
  RTProgra

namespace POObstru

/--
Scheduler-order erased-shape program attached to one recipe-free obstruction.
The recursive children are retained exactly when they remain below cutoff.
-/
noncomputable def schedulerErasedProgram
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru) :
    ESProgra :=
  (descends_wellFounded n leftWeight rightWeight).fix
    (fun parent recurse =>
      ESProgra.retained
        (if hleft :
            parent.operationalNestedLeft.weight leftWeight rightWeight < n then
          recurse parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft)
        else
          ESProgra.empty)
        parent.correction.erasedShape
        (if hright :
            parent.operationalNestedRight.weight leftWeight rightWeight < n then
          recurse parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright)
        else
          ESProgra.empty))
    O

/-- The scheduler-order program exposes its retained root and two branches. -/
lemma scheduler_erased_program
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru) :
    schedulerErasedProgram
        (n := n) hleftWeight hrightWeight O =
      ESProgra.retained
        (if _hleft :
            O.operationalNestedLeft.weight leftWeight rightWeight < n then
          schedulerErasedProgram
            (n := n) hleftWeight hrightWeight O.operationalNestedLeft
        else
          ESProgra.empty)
        O.correction.erasedShape
        (if _hright :
            O.operationalNestedRight.weight leftWeight rightWeight < n then
          schedulerErasedProgram
            (n := n) hleftWeight hrightWeight O.operationalNestedRight
        else
          ESProgra.empty) := by
  rw [schedulerErasedProgram, WellFounded.fix_eq]
  split <;> split <;> rfl

end POObstru

/--
Move a leading root behind a permuted left branch while independently
permuting the right branch.
-/
lemma perm_cons_singleton
    {α : Type*}
    (head : α)
    {left left' right right' : List α}
    (hleft : List.Perm left left')
    (hright : List.Perm right right') :
    List.Perm
      (head :: left ++ right)
      (left' ++ [head] ++ right') := by
  apply
    (List.Perm.cons head (List.Perm.append hleft hright)).trans
  have hcomm :
      List.Perm (([head] : List α) ++ left') (left' ++ [head]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using hcomm.append_right right'

namespace POObstru

/--
The root-first recipe-free packet and the scheduler-order shape program have
the same Hall-shape multiplicities.
-/
lemma keys_perm_program
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru) :
    List.Perm
      ((O.retainedKeys (n := n) hleftWeight hrightWeight).map fun key =>
        key.erasedShape)
      (schedulerErasedProgram
        (n := n) hleftWeight hrightWeight O).trace := by
  refine
    (descends_wellFounded n leftWeight rightWeight).induction
      (C := fun O =>
        List.Perm
          ((O.retainedKeys (n := n) hleftWeight hrightWeight).map fun key =>
            key.erasedShape)
          (schedulerErasedProgram
            (n := n) hleftWeight hrightWeight O).trace)
      O ?_
  intro parent ih
  rw [parent.keys_cons_append hleftWeight hrightWeight,
    scheduler_erased_program
      hleftWeight hrightWeight parent,
    List.map_append, List.map_cons,
    ESProgra.trace_retained]
  by_cases hleft :
      parent.operationalNestedLeft.weight leftWeight rightWeight < n
  · simp only [dif_pos hleft]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      exact
        perm_cons_singleton parent.correction.erasedShape
          (ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft))
          (ih parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright))
    · simp only [dif_neg hright,
        ESProgra.trace_empty, List.map_nil]
      exact
        perm_cons_singleton parent.correction.erasedShape
          (ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft))
          (List.Perm.refl [])
  · simp only [dif_neg hleft,
      ESProgra.trace_empty, List.map_nil]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      exact
        perm_cons_singleton parent.correction.erasedShape
          (List.Perm.refl [])
          (ih parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright))
    · simp only [dif_neg hright,
        ESProgra.trace_empty, List.map_nil]
      exact
        perm_cons_singleton parent.correction.erasedShape
          (List.Perm.refl [])
          (List.Perm.refl [])

/--
Finite dictionary encoding preserves the local scheduler-order Hall-shape
multiplicities.
-/
lemma keyShapeProgram
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport : IsSupported (n := n) hleftWeight hrightWeight O) :
    List.Perm
      ((retainedIndexTrace (n := n) hleftWeight hrightWeight O hsupport).map
        fun index => (retainedOrbitKey index).erasedShape)
      (schedulerErasedProgram
        (n := n) hleftWeight hrightWeight O).trace := by
  have hperm :=
    keys_perm_program
      (n := n) hleftWeight hrightWeight O
  rw [← key_retained_trace hleftWeight hrightWeight O hsupport] at hperm
  simpa only [List.map_map, Function.comp_apply] using hperm

end POObstru

/--
Scheduler-order erased-shape program for one concrete retained-history grid
cell.  A cell at or above cutoff emits the empty program.
-/
noncomputable def
    universalSchedulerProgram
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    ESProgra :=
  let O :=
    universalOrbitObstruction
      hleftWeight hrightWeight left right
  if _hroot : O.weight leftWeight rightWeight < n then
    POObstru.schedulerErasedProgram
      (n := n) hleftWeight hrightWeight O
  else
    ESProgra.empty

/--
One concrete retained-history grid cell has the same erased-shape
multiplicities as its scheduler-order recursive program.
-/
lemma
    keyErasedProgram
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    List.Perm
      ((universalOperationalTrace
        hleftWeight hrightWeight left right).map fun index =>
          (retainedOrbitKey index).erasedShape)
      (universalSchedulerProgram
        hleftWeight hrightWeight left right).trace := by
  let O :=
    universalOrbitObstruction
      hleftWeight hrightWeight left right
  by_cases hroot : O.weight leftWeight rightWeight < n
  · rw [
      universal_operational_weight
        hleftWeight hrightWeight left right hroot]
    unfold
      universalSchedulerProgram
    rw [dif_pos hroot]
    exact
      POObstru.keyShapeProgram
        hleftWeight hrightWeight O
        (universal_obstruction_supported
          hleftWeight hrightWeight left right hroot)
  · rw [
      universal_nil_weight
        hleftWeight hrightWeight left right hroot]
    unfold
      universalSchedulerProgram
    rw [dif_neg hroot]
    exact List.Perm.refl []

namespace ESProgra

/-- Concatenate a finite list of scheduler-order erased-shape programs. -/
def schedulerConcat :
    List ESProgra →
      ESProgra
  | [] =>
      ESProgra.empty
  | program :: programs =>
      ESProgra.append program
        (schedulerConcat programs)

@[simp]
lemma traceSchedulerConcat
    (programs : List ESProgra) :
    (schedulerConcat programs).trace =
      programs.flatMap ESProgra.trace := by
  induction programs with
  | nil =>
      rfl
  | cons program programs ih =>
      simp only [schedulerConcat,
        ESProgra.trace_append,
        List.flatMap_cons, ih]

end ESProgra

/--
Pointwise shape-trace permutations lift across a finite `flatMap` to the trace
of the concatenated scheduler-order programs.
-/
lemma perm_flat_concat
    {α β : Type*}
    (items : List α)
    (packet : α → List β)
    (erase : β → CWord HPAtom)
    (program : α → ESProgra)
    (hperm :
      ∀ item,
        List.Perm
          ((packet item).map erase)
          (program item).trace) :
    List.Perm
      ((items.flatMap packet).map erase)
      (ESProgra.schedulerConcat
        (items.map program)).trace := by
  induction items with
  | nil =>
      exact List.Perm.refl []
  | cons item items ih =>
      rw [List.flatMap_cons, List.map_append, List.map_cons,
        ESProgra.schedulerConcat,
        ESProgra.trace_append]
      exact List.Perm.append (hperm item) ih

/--
Scheduler-order erased-shape program for the complete retained-history
pairwise correction envelope.
-/
noncomputable def
    envelopeSchedulerProgram
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ESProgra :=
  ESProgra.schedulerConcat
    ((rawHistoriesAttached M N n leftWeight rightWeight).map fun left =>
      ESProgra.schedulerConcat
        ((rawHistoriesAttached M N n leftWeight rightWeight).map
          fun right =>
            universalSchedulerProgram
              hleftWeight hrightWeight left right))

/--
The complete conservative correction envelope has the same Hall-shape
multiplicities as its recursively assembled scheduler-order program.
-/
lemma
    keyEnvelopeProgram
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List.Perm
      ((universalOperationalEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight).map fun index =>
          (retainedOrbitKey index).erasedShape)
      (envelopeSchedulerProgram
        M N n leftWeight rightWeight hleftWeight hrightWeight).trace := by
  rw [
    universal_envelope_pairwise]
  unfold
    envelopeSchedulerProgram
  apply perm_flat_concat
  intro left
  apply perm_flat_concat
  intro right
  exact
    keyErasedProgram
      hleftWeight hrightWeight left right

end
  REProgra
end TCTex
end Submission

/-!
# Complete raw-source index grids for recursive polynomial-orbit expansions

This file records an unguarded finite overapproximation: enumerate the fixed
retained orbit alphabet on the left and right, keep the pairs whose full
recursive correction packets stay inside the retained vocabulary, and expand
every surviving pair using the raw-source per-index multiplicity profiles.

Indices that do not occur in the raw-source trace carry the zero polynomial.
That removes many irrelevant branches, but it does not remove roots lying at
or above the cutoff.  The operational scheduler guards those roots before
entering the recursive expansion.  Consequently the permutation structures
below package a deliberately strong exploratory condition.  The guarded
replacement is `ProductInverseCollectionPolynomialOrbitExpansionGuardedRawSourceGridBoundary`.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  ESGrid

open
  CRLayer
open
  ISFiber
open
  RITrace
open
  RIRecurs
open
  PCBridge
open
  FIBridge
open
  ESIdx

/-- Ordered enumeration of the complete retained polynomial-orbit index alphabet. -/
noncomputable def orbitIndexList
    (n leftWeight rightWeight : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  Finset.univ.toList

/-- Every retained orbit index appears in the canonical alphabet enumeration. -/
@[simp]
lemma orbit_index_list
    {n leftWeight rightWeight : ℕ}
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    index ∈ orbitIndexList n leftWeight rightWeight := by
  classical
  simp [orbitIndexList]

/--
Canonical finite grid of retained-index pairs whose full recursive orbit
packets stay inside the retained vocabulary.
-/
noncomputable def completeSupportedBranches
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight) := by
  classical
  exact
    (orbitIndexList n leftWeight rightWeight).flatMap
      fun leftIndex =>
        (orbitIndexList n leftWeight rightWeight).filterMap
          fun rightIndex =>
            if hsupport :
                IsSupported (n := n) hleftWeight hrightWeight {
                  left := retainedOrbitKey leftIndex
                  right := retainedOrbitKey rightIndex
                } then
              some {
                leftIndex := leftIndex
                rightIndex := rightIndex
                support := hsupport
              }
            else
              none

/-- Every recursively supported retained-index pair occurs in the complete grid. -/
lemma mk_complete_branches
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (leftIndex rightIndex :
      RetainedOrbitIndex n leftWeight rightWeight)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight {
        left := retainedOrbitKey leftIndex
        right := retainedOrbitKey rightIndex
      }) :
    ({
      leftIndex := leftIndex
      rightIndex := rightIndex
      support := hsupport
    } : IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight) ∈
        completeSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight := by
  classical
  simp [completeSupportedBranches,
    hsupport]

/--
Strong unguarded comparison between the selected scheduler trace and the
complete supported raw-source index-grid expansion.  The scheduler-faithful
boundary additionally filters roots by their strict cutoff guard.
-/
structure
    SCDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RMProf
      n leftWeight rightWeight hleftWeight hrightWeight
  trace_perm :
    ∀ M N,
      List.Perm
        (((completeSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace raw M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace
  SCDecomp

/--
Forget that the source-index root list is the canonical complete supported
grid and retain the general source-index expansion decomposition.
-/
noncomputable def
    idxPolyDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCDecomp
        layer hleftWeight hrightWeight) :
    SEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  branches :=
    completeSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight
  trace_perm :=
    decomposition.trace_perm

/-- Compile a canonical complete-grid decomposition to correction profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCDecomp
        layer hleftWeight hrightWeight) :
    IMProf.MPKern
      layer hleftWeight hrightWeight :=
  decomposition.idxPolyDecomp
    |>.multiplicityProfileKernel

/-- Compile a canonical complete-grid decomposition to selected endpoint profiles. -/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SCDecomp
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.idxPolyDecomp
    |>.selectedFullFiber

end
  SCDecomp

/--
Canonical-transversal form of the strong unguarded complete-grid comparison.
The scheduler-faithful boundary additionally filters roots by their strict
cutoff guard.
-/
structure
    STDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  rawCounts :
    RawTransversalCounts
      n leftWeight rightWeight hleftWeight hrightWeight
  trace_perm :
    ∀ M N,
      List.Perm
        (((completeSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace
              (multiplicityTransversalCounts
                hleftWeight hrightWeight rawCounts)
              M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace
  STDecomp

/--
Compile the concrete canonical-transversal obligations to the complete-grid
decomposition consumed by the endpoint adapter.
-/
noncomputable def
    completeIdxDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      STDecomp
        layer hleftWeight hrightWeight) :
    SCDecomp
      layer hleftWeight hrightWeight where
  raw :=
    multiplicityTransversalCounts
      hleftWeight hrightWeight decomposition.rawCounts
  trace_perm :=
    decomposition.trace_perm

/--
The two canonical-transversal scalar and scheduler obligations compile all
the way to the selected endpoint finite-index shape-fiber profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      STDecomp
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.completeIdxDecomp
    |>.selectedFullFiber

end
  STDecomp

end
  ESGrid
end TCTex
end Submission

/-!
# Exact raw-source orbit-index profiles from erased-shape profiles

The retained source packet has a stronger separation property than the full
correction closure: among raw source keys, the erased Hall shape determines
the complete polynomial-orbit key.  Since the retained orbit vocabulary is
deduplicated, it also determines the corresponding finite vocabulary index.

Consequently every stabilized raw erased-shape profile canonically refines to
one exact multiplicity profile for each retained source-orbit index: reuse the
shape profile at source indices and use zero at indices that never occur in a
source packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  ISLift

open
  ROAggreg
open
  ROTransi
open
  FIProf
open
  TCThree
open
  CFAlg
open
  CFSubsti
open
  RFIndex
open
  CWSkelet
open
  OREnvelo
open
  RITrace
open
  IEDecomp
open
  ESIdx
open
  UREnvelo
open
  UOVocabu
open
  RPEnvelo
open
  URVocabu

/-- Looking up keys in the deduplicated retained polynomial-orbit vocabulary is injective. -/
lemma orbit_key_injective
    {n leftWeight rightWeight : ℕ} :
    Function.Injective
      (@retainedOrbitKey n leftWeight rightWeight) := by
  unfold retainedOrbitKey
  apply List.Nodup.injective_get
  exact List.nodup_dedup _

/-- Every key chosen for an arbitrary raw-source occurrence belongs to the fixed dummy source-key
  list. -/
lemma keys_universal_packet
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {key : POKey}
    (hkey :
      key ∈ universalOrbitPacket
        M N n leftWeight rightWeight hleftWeight hrightWeight) :
    key ∈ sourceOrbitKeys n leftWeight rightWeight := by
  rw [←
    key_universal_packet
      M N n leftWeight rightWeight hleftWeight hrightWeight] at hkey
  rcases List.mem_map.mp hkey with ⟨recipe, hrecipe, rfl⟩
  exact
    List.mem_map.mpr
      ⟨recipe,
        recipes_universal_packet
          hleftWeight hrightWeight hrecipe,
        rfl⟩

/-- The key represented by every source finite-index occurrence belongs to the fixed dummy
  source-key list. -/
lemma keys_universal_trace
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {index : RetainedOrbitIndex n leftWeight rightWeight}
    (hindex :
      index ∈ universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight) :
    retainedOrbitKey index ∈
      sourceOrbitKeys n leftWeight rightWeight := by
  apply
    keys_universal_packet
  rw [←
    key_universal_trace
      M N n leftWeight rightWeight hleftWeight hrightWeight]
  exact List.mem_map.mpr ⟨index, hindex, rfl⟩

/-- Two raw-source keys with the same erased Hall shape are literally equal. -/
lemma keys_erased_shape
    {n leftWeight rightWeight : ℕ}
    {left right : POKey}
    (hleft : left ∈ sourceOrbitKeys n leftWeight rightWeight)
    (hright : right ∈ sourceOrbitKeys n leftWeight rightWeight)
    (hshape : left.erasedShape = right.erasedShape) :
    left = right := by
  rcases List.mem_map.mp hleft with ⟨leftRecipe, hleftRecipe, rfl⟩
  rcases List.mem_map.mp hright with ⟨rightRecipe, hrightRecipe, rfl⟩
  exact
    key_recipes_shape
      hleftRecipe hrightRecipe hshape

/--
Within a raw-source finite-index trace, the erased Hall shape separates any
occurring source index from an arbitrary retained index whose key belongs to
the fixed source vocabulary.
-/
lemma universal_erased_shape
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {left right : RetainedOrbitIndex n leftWeight rightWeight}
    (hleft :
      left ∈ universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight)
    (hright :
      retainedOrbitKey right ∈
        sourceOrbitKeys n leftWeight rightWeight)
    (hshape :
      (retainedOrbitKey left).erasedShape =
        (retainedOrbitKey right).erasedShape) :
    left = right := by
  apply orbit_key_injective
  exact
    keys_erased_shape
      (keys_universal_trace
        hleft)
      hright
      hshape

/--
For a retained source index, filtering the raw-source trace by erased shape
is the same as filtering by exact finite index.
-/
lemma
    filter_key_universal
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hindex :
      retainedOrbitKey index ∈
        sourceOrbitKeys n leftWeight rightWeight) :
    (universalIndexTrace
      M N n leftWeight rightWeight hleftWeight hrightWeight).filter
        (fun next =>
          decide
            ((retainedOrbitKey next).erasedShape =
              (retainedOrbitKey index).erasedShape)) =
      (universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight).filter
          (fun next => decide (next = index)) := by
  apply List.filter_congr
  intro next hnext
  by_cases hshape :
      (retainedOrbitKey next).erasedShape =
        (retainedOrbitKey index).erasedShape
  · have hnextEq :
        next = index :=
      universal_erased_shape
        hnext hindex hshape
    simp [hnextEq]
  · have hnextNe :
        next ≠ index := by
      intro hnextEq
      subst next
      exact hshape rfl
    simp [hshape, hnextNe]

/--
A raw-source erased-shape filter at a source index has the exact occurrence
count of that index.
-/
lemma
    length_filter_key
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hindex :
      retainedOrbitKey index ∈
        sourceOrbitKeys n leftWeight rightWeight) :
    ((universalIndexTrace
      M N n leftWeight rightWeight hleftWeight hrightWeight).filter
        (fun next =>
          decide
            ((retainedOrbitKey next).erasedShape =
              (retainedOrbitKey index).erasedShape))).length =
      (universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight).count index := by
  rw [
    filter_key_universal
      M N n leftWeight rightWeight hleftWeight hrightWeight index hindex]
  generalize
    universalIndexTrace
      M N n leftWeight rightWeight hleftWeight hrightWeight = trace
  induction trace with
  | nil =>
      rfl
  | cons next trace ih =>
      by_cases hnext : next = index
      · subst next
        simp [ih]
      · simp [hnext, ih]

/--
Every retained orbit index carries a canonical erased-shape word in the fixed
closure skeleton.
-/
lemma erased_key_vocabulary
    {n leftWeight rightWeight : ℕ}
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (retainedOrbitKey index).erasedShape ∈
      erasedShapeVocabulary n leftWeight rightWeight := by
  simpa only [orbit_block_packet] using
      erased_vocabulary_packet
        (⟨retainedOrbitKey index,
          retained_orbit_key index⟩ :
            RetainedOrbitKey n leftWeight rightWeight)

/--
Reuse the stabilized erased-shape packet at a source index and use zero at
retained indices that cannot occur in the raw-source packet.
-/
noncomputable def
    rawMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  if _hindex :
      retainedOrbitKey index ∈
        sourceOrbitKeys n leftWeight rightWeight then
    kernel.profiles
      (retainedOrbitKey index).erasedShape
      (erased_key_vocabulary index)
  else
    FPkt.zero
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree

/-- The exact-index packet induced by a shape kernel counts its source-trace coordinate. -/
lemma
    value_cast_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (rawMultiplicityProfile
      kernel index).value (M : ℤ) (N : ℤ) =
        ((universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight).count index :
            ℤ) := by
  classical
  by_cases hindex :
      retainedOrbitKey index ∈
        sourceOrbitKeys n leftWeight rightWeight
  · rw [rawMultiplicityProfile,
      dif_pos hindex,
      kernel.profiles_cast_trace]
    exact_mod_cast
      length_filter_key
        M N n leftWeight rightWeight hleftWeight hrightWeight index hindex
  · rw [rawMultiplicityProfile,
      dif_neg hindex, FPkt.value_zero]
    have hnotMem :
        index ∉ universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight := by
      intro hmem
      exact hindex
        (keys_universal_trace
          hmem)
    rw [List.count_eq_zero_of_not_mem hnotMem]
    rfl

/--
Every stabilized raw erased-shape kernel canonically refines to exact
raw-source finite-index multiplicity packets.
-/
noncomputable def
    multiplicityProfileShape
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RMProf
      n leftWeight rightWeight hleftWeight hrightWeight where
  profiles :=
    rawMultiplicityProfile kernel
  profiles_nat_count :=
    value_cast_count
      kernel

end
  ISLift

namespace RSTransv

/--
Finite-index raw-source trace counts refine all the way to exact per-index
multiplicity profiles for the raw-source polynomial-orbit trace.
-/
noncomputable def multiplicity_fiber_counts
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hcounts :
      IndexFiberCounts
        n leftWeight rightWeight hleftWeight hrightWeight) :
    ESIdx.RMProf
      n leftWeight rightWeight hleftWeight hrightWeight :=
  ISLift.multiplicityProfileShape
    (raw_fiber_counts
      hleftWeight hrightWeight hcounts)

/--
The scalar raw-source stabilization kernel also refines to exact per-index
multiplicity profiles.
-/
noncomputable def indexProfileKernel
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (kernel : StabilizationKernel n leftWeight rightWeight) :
    ESIdx.RMProf
      n leftWeight rightWeight hleftWeight hrightWeight :=
  ISLift.multiplicityProfileShape
    (rawFiberProfile
      hleftWeight hrightWeight kernel)

end RSTransv

end TCTex
end Submission

/-!
# Complete raw-source grids seeded by erased-shape profiles

The exact raw-source finite-index packets required by the recursive orbit
collector are not an independent stabilization theorem.  Raw source keys are
separated by erased Hall shape, so the earlier erased-shape kernel refines to
exact finite-index packets.

This file composes that lift with the unguarded complete supported
source-index grid.  Its permutation theorem is intentionally stronger than
the operational scheduler semantics, because the scheduler additionally
guards each root by its strict cutoff test.  The scheduler-faithful adapter is
`ProductInverseCollectionPolynomialOrbitExpansionGuardedRawSourceGridBoundary`.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  GSLift

open
  CRLayer
open
  ISFiber
open
  FIProf
open
  FUBounda
open
  PCBridge
open
  FIBridge
open
  ESGrid
open
  ISLift

/--
Strong unguarded comparison between the complete supported raw-source grid
and the selected scheduler trace after exact source-index packets have been
induced from stabilized erased-shape profiles.
-/
structure
    CEDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  trace_perm :
    ∀ M N,
      List.Perm
        (((completeSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace
              (multiplicityProfileShape
                raw)
              M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace
  CEDecomp

/--
Compile an erased-shape-seeded complete-grid decomposition to the exact
finite-index complete-grid decomposition.
-/
noncomputable def
    completeIdxDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      CEDecomp
        layer hleftWeight hrightWeight) :
    SCDecomp
      layer hleftWeight hrightWeight where
  raw :=
    multiplicityProfileShape
      decomposition.raw
  trace_perm :=
    decomposition.trace_perm

/-- Compile the single remaining scheduler theorem to correction finite-index profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      CEDecomp
        layer hleftWeight hrightWeight) :=
  decomposition.completeIdxDecomp
    |>.multiplicityProfileKernel

/-- Compile the single remaining scheduler theorem all the way to selected endpoint profiles. -/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      CEDecomp
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.completeIdxDecomp
    |>.selectedFullFiber

/--
Any uniform raw shape-fiber kernel supplies the finite-index shape kernel
needed by the reduced complete-grid boundary.
-/
noncomputable def fiber_uniform_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      FUProf
        n leftWeight rightWeight)
    (trace_perm :
      ∀ M N,
        List.Perm
          (((completeSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              branch.indexTrace
                (multiplicityProfileShape
                  (FIProf.FUProf.idxFiberProfile
                    raw hleftWeight hrightWeight))
                M N).flatten)
          (selectedIndexTrace
            layer M N hleftWeight hrightWeight)) :
    CEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    FIProf.FUProf.idxFiberProfile
      raw hleftWeight hrightWeight
  trace_perm :=
    trace_perm

end
  CEDecomp

end
  GSLift
end TCTex
end Submission

/-!
# Guarded raw-source grids for recursive polynomial-orbit expansions

The conservative recursive orbit expansion emits the correction root
unconditionally.  The operational scheduler enters that expansion only when
the root obstruction lies strictly below the cutoff.  Thus the canonical
source-index grid must retain both conditions:

* the recursive correction packet stays inside the finite vocabulary;
* the root obstruction weight is strictly below the cutoff.

This file adds that root guard, packages the corrected scheduler boundary,
and checks it against the shallow class-three range.  Through cutoff four the
guarded grid is empty for the same weight reason that makes the selected
scheduler-correction trace empty.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  PGSrc

open
  RRPkt
open
  RRPkt.POObstru
open
  ROTransi
open
  CRLayer
open
  ISFiber
open
  FIProf
open
  FUBounda
open
  CWSkelet
open
  RITrace
open
  PCBridge
open
  FIBridge
open
  ESGrid
open
  ESIdx
open
  ISLift
open
  CCThreea

/--
Canonical finite root grid for the recursive collector: enumerate all
recursively supported retained-index pairs and keep exactly the roots lying
strictly below the cutoff.
-/
noncomputable def guardedSupportedBranches
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight) :=
  (completeSupportedBranches
    n leftWeight rightWeight hleftWeight hrightWeight).filter fun branch =>
      decide (branch.obstruction.weight leftWeight rightWeight < n)

@[simp]
lemma guarded_raw_branches
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight} :
    branch ∈
        guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight ↔
      branch ∈
          completeSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight ∧
        branch.obstruction.weight leftWeight rightWeight < n := by
  classical
  simp [guardedSupportedBranches]

/-- Every recursively supported below-cutoff retained-index pair occurs in the guarded grid. -/
lemma mk_supported_branches
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (leftIndex rightIndex :
      RetainedOrbitIndex n leftWeight rightWeight)
    (hsupport :
      RIRecurs.IsSupported
        (n := n) hleftWeight hrightWeight {
          left := retainedOrbitKey leftIndex
          right := retainedOrbitKey rightIndex
        })
    (hroot :
      ({
        left := retainedOrbitKey leftIndex
        right := retainedOrbitKey rightIndex
      } : POObstru).weight leftWeight rightWeight < n) :
    ({
      leftIndex := leftIndex
      rightIndex := rightIndex
      support := hsupport
    } : IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight) ∈
        guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight := by
  rw [guarded_raw_branches]
  refine ⟨
    mk_complete_branches
      leftIndex rightIndex hsupport, ?_⟩
  simpa [
    IOBranch.obstruction] using
      hroot

/--
The remaining scheduler theorem after adding the operational root guard.
-/
structure
    SGDecompa
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RMProf
      n leftWeight rightWeight hleftWeight hrightWeight
  trace_perm :
    ∀ M N,
      List.Perm
        (((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace raw M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace
  SGDecompa

/-- Forget the canonical guarded-grid choice and retain the general source-index expansion. -/
noncomputable def
    idxPolyDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SGDecompa
        layer hleftWeight hrightWeight) :
    SEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  branches :=
    guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight
  trace_perm :=
    decomposition.trace_perm

/-- Compile a guarded-grid decomposition to correction finite-index profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SGDecompa
        layer hleftWeight hrightWeight) :=
  decomposition.idxPolyDecomp
    |>.multiplicityProfileKernel

/-- Compile a guarded-grid decomposition all the way to selected endpoint profiles. -/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      SGDecompa
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.idxPolyDecomp
    |>.selectedFullFiber

end
  SGDecompa

/--
Guarded-grid scheduler boundary after exact source-index packets have been
induced from stabilized erased-shape profiles.
-/
structure
    GIDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  trace_perm :
    ∀ M N,
      List.Perm
        (((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace
              (multiplicityProfileShape
                raw)
              M N).flatten)
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight)

namespace
  GIDecomp

/-- Compile the erased-shape-seeded guarded grid to its exact source-index form. -/
noncomputable def
    guardedPolyDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GIDecomp
        layer hleftWeight hrightWeight) :
    SGDecompa
      layer hleftWeight hrightWeight where
  raw :=
    multiplicityProfileShape
      decomposition.raw
  trace_perm :=
    decomposition.trace_perm

/-- Compile the single guarded scheduler theorem to correction finite-index profiles. -/
noncomputable def multiplicityProfileKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GIDecomp
        layer hleftWeight hrightWeight) :=
  decomposition.guardedPolyDecomp
    |>.multiplicityProfileKernel

/-- Compile the single guarded scheduler theorem all the way to selected endpoint profiles. -/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GIDecomp
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.guardedPolyDecomp
    |>.selectedFullFiber

/--
Any uniform raw shape-fiber kernel supplies the finite-index shape kernel
needed by the guarded-grid boundary.
-/
noncomputable def fiber_uniform_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      FUProf
        n leftWeight rightWeight)
    (trace_perm :
      ∀ M N,
        List.Perm
          (((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              branch.indexTrace
                (multiplicityProfileShape
                  (FIProf.FUProf.idxFiberProfile
                    raw hleftWeight hrightWeight))
                M N).flatten)
          (selectedIndexTrace
            layer M N hleftWeight hrightWeight)) :
    GIDecomp
      layer hleftWeight hrightWeight where
  raw :=
    FIProf.FUProf.idxFiberProfile
      raw hleftWeight hrightWeight
  trace_perm :=
    trace_perm

end
  GIDecomp

/--
Every retained orbit index has at least the principal Hall-pair weight.
-/
lemma sum_orbit_key
    {n leftWeight rightWeight : ℕ}
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    leftWeight + rightWeight ≤
      orbitWeight leftWeight rightWeight
        (retainedOrbitKey index) := by
  unfold orbitWeight
  rw [CWord.pair_atom_degree]
  have hpositive :=
    bidegree_positive_vocabulary
      (erased_key_vocabulary
        index)
  exact
    Nat.add_le_add
      (Nat.le_mul_of_pos_left leftWeight hpositive.1)
      (Nat.le_mul_of_pos_left rightWeight hpositive.2)

/--
Every retained-index root has at least twice the principal Hall-pair weight.
-/
lemma raw_orbit_obstruction
    {n leftWeight rightWeight : ℕ}
    (leftIndex rightIndex :
      RetainedOrbitIndex n leftWeight rightWeight) :
    2 * (leftWeight + rightWeight) ≤
      ({
        left := retainedOrbitKey leftIndex
        right := retainedOrbitKey rightIndex
      } : POObstru).weight leftWeight rightWeight := by
  unfold POObstru.weight
  change
    2 * (leftWeight + rightWeight) ≤
      orbitWeight leftWeight rightWeight
          (retainedOrbitKey leftIndex) +
        orbitWeight leftWeight rightWeight
          (retainedOrbitKey rightIndex)
  have hleft :=
    sum_orbit_key leftIndex
  have hright :=
    sum_orbit_key rightIndex
  omega

/--
Below twice the principal Hall-pair weight, the guarded canonical root grid
is empty.
-/
lemma guarded_supported_sum
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hhigh : n ≤ 2 * (leftWeight + rightWeight)) :
    guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro branch hbranch
  have hroot :=
    (guarded_raw_branches.mp
      hbranch).2
  have hweight :=
    raw_orbit_obstruction
      branch.leftIndex branch.rightIndex
  change
    ({
      left := retainedOrbitKey branch.leftIndex
      right := retainedOrbitKey branch.rightIndex
    } : POObstru).weight leftWeight rightWeight < n at hroot
  omega

/-- Through cutoff four, positive source weights make the guarded canonical root grid empty. -/
lemma branches_nil_four
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hhigh : n ≤ 4) :
    guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight = [] := by
  apply
    guarded_supported_sum
      hleftWeight hrightWeight
  omega

/--
Through cutoff four at root weights, the guarded-grid scheduler theorem is
automatic: both the guarded grid expansion and the selected correction trace
are empty.
-/
noncomputable def
    guardedNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GIDecomp
      layer (by simp) (by simp) where
  raw :=
    raw
  trace_perm M N := by
    rw [
      branches_nil_four
        (by simp) (by simp) hhigh,
      selected_nil_n
        layer hhigh M N]
    simp

/--
The guarded canonical-grid route recovers selected endpoint profiles through
cutoff four from the stabilized raw erased-shape kernel.
-/
noncomputable def
    idxGuardedGrid
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    EIFiber
      layer (by simp) (by simp) :=
  (guardedNFour
    layer hhigh raw)
    |>.selectedFullFiber

end
  PGSrc
end TCTex
end Submission

/-!
# Shape-erased guarded raw-source grids for recursive orbit expansions

The guarded raw-source grid already constructs homogeneous recursive
polynomial-orbit expansion traces.  Its previous scheduler boundary required
those traces to be a permutation of the selected correction trace as exact
finite orbit indices.

Selected correction representatives are chosen only up to erased Hall shape,
and endpoint coordinates need only shape-fiber multiplicities.  This file
therefore erases the guarded expansion trace to Hall shapes before comparing
it with the operational scheduler inventory.  The remaining scheduler
theorem is a strictly weaker shape-level permutation, while all existing
recursive profile construction is reused unchanged.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  GGErased

open
  CRLayer
open
  ISFiber
open
  FIProf
open
  FUBounda
open
  FUClass
open
  RITrace
open
  FIBridge
open
  MPAlg
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  SEAlg

/--
The existing guarded raw-source grid, compiled to one profiled finite-index
trace before orbit indices are erased.
-/
noncomputable def guardedProfiledExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    PIFam n leftWeight rightWeight :=
  POBranch.concat
    ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        branch.profiledObstructionBranch
          (multiplicityProfileShape
            raw))

@[simp]
lemma guarded_profiled_expansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    (guardedProfiledExpansion raw).trace M N =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          branch.indexTrace
            (multiplicityProfileShape
              raw)
            M N).flatten := by
  rw [guardedProfiledExpansion,
    POBranch.trace_concat]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro branch _hbranch
  rfl

/--
Guarded-grid scheduler boundary stated at the erased-shape strength needed by
endpoint coordinates.
-/
structure
    GEDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  shape_trace_perm :
    ∀ M N,
      List.Perm
        ((((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace
              (multiplicityProfileShape
                raw)
              M N).flatten).map fun index =>
                (retainedOrbitKey index).erasedShape)
        (selectedErasedShape layer M N)

namespace
  GEDecomp

/--
Compile the guarded recursive expansion to literal selected-correction shape
profiles using only shape-level permutation.
-/
noncomputable def erasedMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GEDecomp
        layer hleftWeight hrightWeight) :
    EMProf
      (selectedErasedShape layer) :=
  (profiledErasedFamily
    (guardedProfiledExpansion decomposition.raw)).kernel
      |>.permTransport (fun M N => by
        rw [profiled_erased_family,
          guarded_profiled_expansion]
        exact decomposition.shape_trace_perm M N)

/--
Compile the weaker guarded-grid scheduler theorem to selected-correction
shape-fiber profiles.
-/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GEDecomp
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.erasedMultiplicityProfile
    |>.shapeFiberProfile
      hleftWeight hrightWeight

/--
Compile the weaker guarded-grid scheduler theorem all the way to aggregate
selected-endpoint profiles.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GEDecomp
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  EIFiber.idx_fiber_profile
    decomposition.raw
    decomposition.shapeFiberProfile

/--
Compile the weaker guarded-grid scheduler theorem directly to the endpoint
shape-fiber interpolation package consumed by the power-coordinate pipeline.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GEDecomp
        layer hleftWeight hrightWeight) :=
  decomposition.selectedFullFiber
    |>.fiberProfileInterpolation

/--
Any uniform raw shape-fiber kernel supplies the finite-index shape kernel
needed by the weaker erased-shape guarded-grid boundary.
-/
noncomputable def fiber_uniform_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      FUProf
        n leftWeight rightWeight)
    (shape_trace_perm :
      ∀ M N,
        List.Perm
          ((((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              branch.indexTrace
                (multiplicityProfileShape
                  (FIProf.FUProf.idxFiberProfile
                    raw hleftWeight hrightWeight))
                M N).flatten).map fun index =>
                  (retainedOrbitKey index).erasedShape)
          (selectedErasedShape layer M N)) :
    GEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    FIProf.FUProf.idxFiberProfile
      raw hleftWeight hrightWeight
  shape_trace_perm :=
    shape_trace_perm

/--
Every exact-index guarded-grid decomposition induces the weaker erased-shape
decomposition by mapping its trace permutation through key erasure.
-/
noncomputable def exactIndexDecomposition
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GIDecomp
        layer hleftWeight hrightWeight) :
    GEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  shape_trace_perm M N := by
    rw [←
      key_erased_selected
        layer M N hleftWeight hrightWeight]
    exact
      (decomposition.trace_perm M N).map
        (fun index => (retainedOrbitKey index).erasedShape)

end
  GEDecomp

/-- Through cutoff four, the literal retained-correction shape trace is empty. -/
lemma selected_nil_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ) :
    selectedErasedShape layer M N = [] := by
  unfold selectedErasedShape
  rw [
    inventory_corrections_nil
      layer hhigh M N]
  rfl

/--
Through cutoff four, both the guarded expansion and the literal selected
correction-shape trace are empty.
-/
noncomputable def
    erasedNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GEDecomp
      layer (by simp) (by simp) where
  raw :=
    raw
  shape_trace_perm M N := by
    rw [
      branches_nil_four
        (by simp) (by simp) hhigh,
      selected_nil_four
        layer hhigh M N]
    simp

/--
The weaker guarded shape-grid route recovers selected-endpoint profiles
through cutoff four.
-/
noncomputable def
    endpointIdxGrid
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    EIFiber
      layer (by simp) (by simp) :=
  (erasedNFour
    layer hhigh raw)
      |>.selectedFullFiber

/--
Through cutoff four, the weaker guarded shape-grid route reaches the endpoint
interpolation object consumed by the power-coordinate compiler.
-/
noncomputable def
    fiberInterpolationGrid
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :=
  (erasedNFour
    layer hhigh raw)
      |>.fiberProfileInterpolation

end GGErased
end TCTex
end Submission

/-!
# Guarded recursive orbit expansions against operational shape programs

The shape-erased guarded-grid boundary compares a symbolic recursive orbit
expansion with the literal endpoint correction-shape trace.  The operational
scheduler-program boundary identifies that literal trace with the output of a
finite recursive program.

This file packages the resulting sharper target: compare the symbolic guarded
expansion directly with the recursively structured operational program.  This
is the natural interface for an arbitrary-cutoff symbolic Hall collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  GRSrc

open
  CRLayer
open
  FIProf
open
  FUBounda
open
  RITrace
open
  FIBridge
open
  PGSrc
open
  ISLift
open
  RTProgra
open
  GGErased

/--
Guarded recursive orbit expansion compared directly with the recursively
structured erased-shape program extracted from the operational scheduler.
-/
structure
    GPDecompa
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  program_shape_perm :
    ∀ M N,
      List.Perm
        ((((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            branch.indexTrace
              (multiplicityProfileShape
                raw)
              M N).flatten).map fun index =>
                (retainedOrbitKey index).erasedShape)
        ((endpointErasedProgram layer M N).trace)

namespace
  GPDecompa

/--
Forget the operational program presentation and recover the literal
erased-shape guarded-grid boundary.
-/
noncomputable def
    guardedErasedDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GPDecompa
        layer hleftWeight hrightWeight) :
    GEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  shape_trace_perm M N := by
    simpa only [
      endpoint_erased_program] using
        decomposition.program_shape_perm M N

/--
Compile the operational-program scheduler theorem directly to selected
endpoint shape-fiber profiles.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GPDecompa
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.guardedErasedDecomp
    |>.selectedFullFiber

/--
Compile the operational-program scheduler theorem directly to the endpoint
interpolation package consumed by the power-coordinate pipeline.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GPDecompa
        layer hleftWeight hrightWeight) :=
  decomposition.guardedErasedDecomp
    |>.fiberProfileInterpolation

/--
Any uniform raw shape-fiber kernel supplies the finite-index shape kernel
needed by the operational-program guarded-grid boundary.
-/
noncomputable def fiber_uniform_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      FUProf
        n leftWeight rightWeight)
    (program_shape_perm :
      ∀ M N,
        List.Perm
          ((((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              branch.indexTrace
                (multiplicityProfileShape
                  (FIProf.FUProf.idxFiberProfile
                    raw hleftWeight hrightWeight))
                M N).flatten).map fun index =>
                  (retainedOrbitKey index).erasedShape)
          ((endpointErasedProgram layer M N).trace)) :
    GPDecompa
      layer hleftWeight hrightWeight where
  raw :=
    FIProf.FUProf.idxFiberProfile
      raw hleftWeight hrightWeight
  program_shape_perm :=
    program_shape_perm

end
  GPDecompa

/--
Through cutoff four, both the guarded recursive expansion and the operational
endpoint correction-shape program emit the empty trace.
-/
noncomputable def
    programNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GPDecompa
      layer (by simp) (by simp) where
  raw :=
    raw
  program_shape_perm M N := by
    rw [
      branches_nil_four
        (by simp) (by simp) hhigh]
    have htrace :=
      endpoint_erased_program layer M N
    rw [
      selected_nil_four
        layer hhigh M N] at htrace
    simp [htrace]

/--
Through cutoff four, the operational-program guarded-grid route reaches the
endpoint interpolation object consumed by the power-coordinate pipeline.
-/
noncomputable def
    endpointInterpolationProgram
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :=
  (programNFour
    layer hhigh raw)
      |>.fiberProfileInterpolation

end GRSrc
end TCTex
end Submission

/-!
# Recursive operational programs for guarded profiled orbit expansions

The profiled polynomial-orbit compiler emits a repeated correction-root block
before its two recursive branches.  The operational cutoff collector records
the same retained crossings in scheduler order: left recursive corrections,
the repeated root block, then right recursive corrections.

This file compiles each profiled orbit branch into that scheduler-order
erased-shape program and proves that the existing root-first finite-index
expansion is a permutation of its trace.  Concatenating the guarded branch grid
therefore reduces the remaining arbitrary-cutoff theorem to a comparison
between two recursively structured erased-shape programs.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  GRProgra

open
  RRPkt
open
  RRPkt.POObstru
open
  CRLayer
open
  FIProf
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  RTProgra
open
  GRSrc
open
  REProgra

/-- Scheduler-order program for a repeated retained Hall-shape block. -/
def replicateErasedProgram
    (shape : CWord HPAtom) :
    ℕ → ESProgra
  | 0 =>
      ESProgra.empty
  | count + 1 =>
      ESProgra.append
        (ESProgra.retained
          ESProgra.empty shape
          ESProgra.empty)
        (replicateErasedProgram shape count)

@[simp]
lemma replicate_erased_program
    (shape : CWord HPAtom)
    (count : ℕ) :
    (replicateErasedProgram shape count).trace =
      List.replicate count shape := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      simp only [replicateErasedProgram,
        ESProgra.trace_append,
        ESProgra.trace_retained,
        ESProgra.trace_empty,
        List.nil_append, List.append_nil, List.singleton_append, ih,
        List.replicate_succ]

/--
Move a repeated root block behind a permuted left branch while independently
permuting the right branch.
-/
lemma perm_singleton_middle
    {α : Type*}
    (root : List α)
    {left left' right right' : List α}
    (hleft : List.Perm left left')
    (hright : List.Perm right right') :
    List.Perm
      (root ++ left ++ right)
      (left' ++ (root ++ right')) := by
  have hchildren :
      List.Perm
        (root ++ left ++ right)
        (root ++ left' ++ right') := by
    simpa [List.append_assoc] using
      List.Perm.append (List.Perm.refl root) (List.Perm.append hleft hright)
  have hcomm :
      List.Perm (root ++ left') (left' ++ root) :=
    List.perm_append_comm
  simpa [List.append_assoc] using hchildren.trans (hcomm.append_right right')

/--
Scheduler-order erased-shape program for one profiled recursive orbit
expansion.
-/
noncomputable def
    profiledSchedulerProgram
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    ESProgra :=
  let root :=
    left.correction O right
  let nestedLeft :=
    if hleft :
        O.operationalNestedLeft.weight leftWeight rightWeight < n then
      profiledSchedulerProgram
        hleftWeight hrightWeight O.operationalNestedLeft
        (operational_left_supported
          hleftWeight hrightWeight O hsupport hleft)
        left root M N
    else
      ESProgra.empty
  let nestedRight :=
    if hright :
        O.operationalNestedRight.weight leftWeight rightWeight < n then
      profiledSchedulerProgram
        hleftWeight hrightWeight O.operationalNestedRight
        (operational_nested_supported
          hleftWeight hrightWeight O hsupport hright)
        right root M N
    else
      ESProgra.empty
  ESProgra.append nestedLeft
    (ESProgra.append
      (replicateErasedProgram O.correction.erasedShape
        (left.multiplicity M N * right.multiplicity M N))
      nestedRight)
termination_by O.defect n leftWeight rightWeight
decreasing_by
  · exact
      O.nestedLeftDescends
        hleftWeight hrightWeight hleft
  · exact
      O.nestedRightDescends
        hleftWeight hrightWeight hright

/-- The profiled scheduler-order program exposes its two branches and root block. -/
lemma
    profiled_scheduler_append
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    profiledSchedulerProgram
        hleftWeight hrightWeight O hsupport left right M N =
      ESProgra.append
        (if hleft :
            O.operationalNestedLeft.weight leftWeight rightWeight < n then
          profiledSchedulerProgram
            hleftWeight hrightWeight O.operationalNestedLeft
            (operational_left_supported
              hleftWeight hrightWeight O hsupport hleft)
            left (left.correction O right) M N
        else
          ESProgra.empty)
        (ESProgra.append
          (replicateErasedProgram O.correction.erasedShape
            (left.multiplicity M N * right.multiplicity M N))
          (if hright :
              O.operationalNestedRight.weight leftWeight rightWeight < n then
            profiledSchedulerProgram
              hleftWeight hrightWeight O.operationalNestedRight
              (operational_nested_supported
                hleftWeight hrightWeight O hsupport hright)
              right (left.correction O right) M N
          else
            ESProgra.empty)) := by
  rw [
    profiledSchedulerProgram]

/--
The existing root-first profiled finite-index expansion and its scheduler-order
program have the same Hall-shape multiplicities.
-/
lemma
    keySchedulerProgram
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    List.Perm
      ((profiledOrbitExpansion
        hleftWeight hrightWeight O hsupport left right).trace M N |>.map
          fun index => (retainedOrbitKey index).erasedShape)
      (profiledSchedulerProgram
        hleftWeight hrightWeight O hsupport left right M N).trace := by
  refine
    (descends_wellFounded n leftWeight rightWeight).induction
      (C := fun O =>
        ∀ (hsupport :
            IsSupported (n := n) hleftWeight hrightWeight O)
          (left :
            MPFam O.left)
          (right :
            MPFam O.right)
          (M N : ℕ),
          List.Perm
            ((profiledOrbitExpansion
              hleftWeight hrightWeight O hsupport left right).trace M N |>.map
                fun index => (retainedOrbitKey index).erasedShape)
            (profiledSchedulerProgram
              hleftWeight hrightWeight O hsupport left right M N).trace)
      O ?_ hsupport left right M N
  intro parent ih hsupport left right M N
  rw [trace_profiled_expansion,
    profiled_scheduler_append,
    List.map_append, List.map_append, List.map_replicate,
    MPFam.retained_key_index,
    ESProgra.trace_append,
    ESProgra.trace_append,
    replicate_erased_program]
  by_cases hleft :
      parent.operationalNestedLeft.weight leftWeight rightWeight < n
  · simp only [dif_pos hleft]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      exact
        perm_singleton_middle
          (List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            parent.correction.erasedShape)
          (ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft)
            (operational_left_supported
              hleftWeight hrightWeight parent hsupport hleft)
            left (left.correction parent right) M N)
          (ih parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright)
            (operational_nested_supported
              hleftWeight hrightWeight parent hsupport hright)
            right (left.correction parent right) M N)
    · simp only [dif_neg hright,
        ESProgra.trace_empty, List.map_nil]
      exact
        perm_singleton_middle
          (List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            parent.correction.erasedShape)
          (ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft)
            (operational_left_supported
              hleftWeight hrightWeight parent hsupport hleft)
            left (left.correction parent right) M N)
          (List.Perm.refl [])
  · simp only [dif_neg hleft,
      ESProgra.trace_empty, List.map_nil]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      exact
        perm_singleton_middle
          (List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            parent.correction.erasedShape)
          (List.Perm.refl [])
          (ih parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright)
            (operational_nested_supported
              hleftWeight hrightWeight parent hsupport hright)
            right (left.correction parent right) M N)
    · simp only [dif_neg hright,
        ESProgra.trace_empty, List.map_nil]
      exact
        perm_singleton_middle
          (List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            parent.correction.erasedShape)
          (List.Perm.refl [])
          (List.Perm.refl [])

namespace POBranch

/-- Scheduler-order erased-shape program attached to one profiled branch. -/
noncomputable def schedulerShapeProgram
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    ESProgra :=
  profiledSchedulerProgram
    hleftWeight hrightWeight branch.obstruction branch.support
      branch.left branch.right M N

/-- One profiled branch permutes to its scheduler-order erased-shape program. -/
lemma keyIdxProgram
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List.Perm
      ((branch.indexTrace M N).map fun index =>
        (retainedOrbitKey index).erasedShape)
      (schedulerShapeProgram branch M N).trace := by
  exact
    keySchedulerProgram
      hleftWeight hrightWeight branch.obstruction branch.support
        branch.left branch.right M N

end POBranch

namespace IOBranch

/-- Scheduler-order erased-shape program attached to one raw-source branch. -/
noncomputable def schedulerShapeProgram
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
    ESProgra :=
  POBranch.schedulerShapeProgram
    (branch.profiledObstructionBranch raw) M N

/-- One raw-source branch permutes to its scheduler-order erased-shape program. -/
lemma keyIdxProgram
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
    List.Perm
      ((branch.indexTrace raw M N).map fun index =>
        (retainedOrbitKey index).erasedShape)
      (schedulerShapeProgram raw branch M N).trace := by
  exact
    POBranch.keyIdxProgram
      (branch.profiledObstructionBranch raw) M N

end IOBranch

/-- Scheduler-order program obtained by concatenating the guarded root grid. -/
noncomputable def
  guardedSchedulerProgram
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    ESProgra :=
  ESProgra.schedulerConcat
    ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerShapeProgram
          raw branch M N)

/--
The mapped guarded finite-index expansion permutes to its recursively
structured scheduler-order erased-shape program.
-/
lemma
    keyErasedScheduler
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List.Perm
      ((((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          branch.indexTrace raw M N).flatten).map fun index =>
            (retainedOrbitKey index).erasedShape)
      (guardedSchedulerProgram
        raw M N).trace := by
  unfold
    guardedSchedulerProgram
  simpa only [List.flatMap_map, Function.comp_apply] using
    (perm_flat_concat
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight)
      (fun branch => branch.indexTrace raw M N)
      (fun index => (retainedOrbitKey index).erasedShape)
      (fun branch =>
        IOBranch.schedulerShapeProgram
          raw branch M N)
      (fun branch =>
        IOBranch.keyIdxProgram
          raw branch M N))

/--
Reduced arbitrary-cutoff target: compare the symbolic scheduler-order guarded
program directly with the recursive program extracted from the endpoint
collector.
-/
structure
    RCDecompa
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  program_trace_perm :
    ∀ M N,
      List.Perm
        (guardedSchedulerProgram
          (multiplicityProfileShape raw)
          M N).trace
        (endpointErasedProgram layer M N).trace

namespace
  RCDecompa

/-- Compile the reduced recursive-program comparison to the earlier operational boundary. -/
noncomputable def
    guardedProgramDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight) :
    GPDecompa
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  program_shape_perm M N :=
    (keyErasedScheduler
      (multiplicityProfileShape
        decomposition.raw)
      M N).trans
        (decomposition.program_trace_perm M N)

/-- Recover the reduced recursive-program target from the earlier operational boundary. -/
noncomputable def
    guarded_expansion_decomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GPDecompa
        layer hleftWeight hrightWeight) :
    RCDecompa
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  program_trace_perm M N :=
    (keyErasedScheduler
      (multiplicityProfileShape
        decomposition.raw)
      M N).symm.trans
        (decomposition.program_shape_perm M N)

/-- Compile the reduced recursive-program theorem to endpoint interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight) :=
  decomposition.guardedProgramDecomp
    |>.fiberProfileInterpolation

end
  RCDecompa

/-- Through cutoff four, the reduced recursive-program comparison is available. -/
noncomputable def
    recNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    RCDecompa
      layer (by simp) (by simp) :=
  RCDecompa.guarded_expansion_decomp
    (programNFour
      layer hhigh raw)

end
  GRProgra
end TCTex
end Submission

/-!
# Guarded orbit expansions against concrete collector programs

The reduced arbitrary-cutoff orbit-expansion boundary compares two erased-shape
program traces.  The endpoint-side program was previously selected only after
all concrete crossing witnesses had been erased.

This file sharpens that target without strengthening it: compare the symbolic
guarded scheduler-order program with the erasure of the concrete retained
correction schedule program.  Each endpoint node then still remembers its
crossed parents and its strict cutoff proof, which is the appropriate input for
a later collector induction.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  GSGrid

open
  CRProgra
open
  CRProgra.RSPrograa
open
  CRLayer
open
  FIProf
open
  ISLift
open
  GRProgra

/--
Induction-ready reduced arbitrary-cutoff target: the symbolic guarded
scheduler-order program permutes to the erasure of a concrete endpoint program
whose nodes retain actual crossed parents and cutoff guards.
-/
structure
    PCDecompa
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  concrete_program_perm :
    ∀ M N,
      List.Perm
        (guardedSchedulerProgram
          (multiplicityProfileShape raw)
          M N).trace
        ((endpointConcreteProgram layer M N)
          |>.shapeTraceProgram).trace

namespace
  PCDecompa

/--
Forget concrete crossing witnesses and recover the earlier reduced recursive
operational-program boundary.
-/
noncomputable def
    recComparisonDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PCDecompa
        layer hleftWeight hrightWeight) :
    RCDecompa
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  program_trace_perm M N := by
    simpa only [
      trace_erased_program] using
        decomposition.concrete_program_perm M N

/--
Recover the induction-ready concrete target from the earlier erased endpoint
program boundary.
-/
noncomputable def
    guarded_comparison_decomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight) :
    PCDecompa
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  concrete_program_perm M N := by
    simpa only [
      trace_erased_program] using
        decomposition.program_trace_perm M N

/-- Compile the concrete-program comparison directly to endpoint interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      PCDecompa
        layer hleftWeight hrightWeight) :=
  decomposition.recComparisonDecomp
    |>.fiberProfileInterpolation

end
  PCDecompa

/-- Through cutoff four, the induction-ready concrete-program comparison is available. -/
noncomputable def
    decompNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    PCDecompa
      layer (by simp) (by simp) :=
  PCDecompa.guarded_comparison_decomp
    (recNFour
      layer hhigh raw)

end
  GSGrid
end TCTex
end Submission

/-!
# Finite-index scheduler traces for guarded profiled orbit expansions

The recursive operational scheduler was previously recorded after erasing
finite orbit indices to Hall shapes.  Exact occurrence accounting benefits from
retaining those indices: they remember the polynomial-orbit key of every
repeated root occurrence.

This file compiles one profiled branch to its scheduler-order finite-index
trace.  The existing root-first expansion permutes to that trace branchwise and
after concatenating the guarded root grid.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  FISchedu

open
  RRPkt
open
  RRPkt.POObstru
open
  FIProf
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  RTProgra
open
  GRProgra
open
  REProgra

/--
Scheduler-order finite-index trace for one profiled recursive orbit expansion.
The left nested branch is emitted first, followed by the polynomially repeated
correction root and the right nested branch.
-/
noncomputable def
    profiledExpansionScheduler
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  let root :=
    left.correction O right
  let nestedLeft :=
    if hleft :
        O.operationalNestedLeft.weight leftWeight rightWeight < n then
      profiledExpansionScheduler
        hleftWeight hrightWeight O.operationalNestedLeft
        (operational_left_supported
          hleftWeight hrightWeight O hsupport hleft)
        left root M N
    else
      []
  let nestedRight :=
    if hright :
        O.operationalNestedRight.weight leftWeight rightWeight < n then
      profiledExpansionScheduler
        hleftWeight hrightWeight O.operationalNestedRight
        (operational_nested_supported
          hleftWeight hrightWeight O hsupport hright)
        right root M N
    else
      []
  nestedLeft ++
    List.replicate (left.multiplicity M N * right.multiplicity M N)
      (MPFam.correctionIndex
        hleftWeight hrightWeight O hsupport) ++
      nestedRight
termination_by O.defect n leftWeight rightWeight
decreasing_by
  · exact
      O.nestedLeftDescends
        hleftWeight hrightWeight hleft
  · exact
      O.nestedRightDescends
        hleftWeight hrightWeight hright

/-- The finite-index scheduler trace exposes its two branches and root block. -/
lemma
    profiled_expansion_append
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    profiledExpansionScheduler
        hleftWeight hrightWeight O hsupport left right M N =
      (if hleft :
          O.operationalNestedLeft.weight leftWeight rightWeight < n then
        profiledExpansionScheduler
          hleftWeight hrightWeight O.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight O hsupport hleft)
          left (left.correction O right) M N
      else
        []) ++
      List.replicate (left.multiplicity M N * right.multiplicity M N)
        (MPFam.correctionIndex
          hleftWeight hrightWeight O hsupport) ++
      (if hright :
          O.operationalNestedRight.weight leftWeight rightWeight < n then
        profiledExpansionScheduler
          hleftWeight hrightWeight O.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight O hsupport hright)
          right (left.correction O right) M N
      else
        []) := by
  rw [
    profiledExpansionScheduler]

/--
The existing root-first profiled expansion permutes to its finite-index
scheduler-order trace.
-/
lemma
    profiled_perm_scheduler
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    List.Perm
      ((profiledOrbitExpansion
        hleftWeight hrightWeight O hsupport left right).trace M N)
      (profiledExpansionScheduler
        hleftWeight hrightWeight O hsupport left right M N) := by
  refine
    (descends_wellFounded n leftWeight rightWeight).induction
      (C := fun O =>
        ∀ (hsupport :
            IsSupported (n := n) hleftWeight hrightWeight O)
          (left :
            MPFam O.left)
          (right :
            MPFam O.right)
          (M N : ℕ),
          List.Perm
            ((profiledOrbitExpansion
              hleftWeight hrightWeight O hsupport left right).trace M N)
            (profiledExpansionScheduler
              hleftWeight hrightWeight O hsupport left right M N))
      O ?_ hsupport left right M N
  intro parent ih hsupport left right M N
  rw [trace_profiled_expansion,
    profiled_expansion_append]
  by_cases hleft :
      parent.operationalNestedLeft.weight leftWeight rightWeight < n
  · simp only [dif_pos hleft]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      simpa [List.append_assoc] using
        perm_singleton_middle
          (List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            (MPFam.correctionIndex
              hleftWeight hrightWeight parent hsupport))
          (ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft)
            (operational_left_supported
              hleftWeight hrightWeight parent hsupport hleft)
            left (left.correction parent right) M N)
          (ih parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright)
            (operational_nested_supported
              hleftWeight hrightWeight parent hsupport hright)
            right (left.correction parent right) M N)
    · simp only [dif_neg hright, List.append_nil]
      simpa [List.append_assoc] using
        perm_singleton_middle
          (List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            (MPFam.correctionIndex
              hleftWeight hrightWeight parent hsupport))
          (ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft)
            (operational_left_supported
              hleftWeight hrightWeight parent hsupport hleft)
            left (left.correction parent right) M N)
          (List.Perm.refl [])
  · simp only [dif_neg hleft, List.nil_append]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      simpa [List.append_assoc] using
        perm_singleton_middle
          (List.replicate
            (left.multiplicity M N * right.multiplicity M N)
            (MPFam.correctionIndex
              hleftWeight hrightWeight parent hsupport))
          (List.Perm.refl [])
          (ih parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright)
            (operational_nested_supported
              hleftWeight hrightWeight parent hsupport hright)
            right (left.correction parent right) M N)
    · simp only [dif_neg hright, List.append_nil]
      exact List.Perm.refl _

/--
Erasing the scheduler-order finite indices recovers the recursive erased-shape
scheduler program literally.
-/
lemma
    key_fin_program
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ) :
    (profiledExpansionScheduler
      hleftWeight hrightWeight O hsupport left right M N).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      (profiledSchedulerProgram
        hleftWeight hrightWeight O hsupport left right M N).trace := by
  refine
    (descends_wellFounded n leftWeight rightWeight).induction
      (C := fun O =>
        ∀ (hsupport :
            IsSupported (n := n) hleftWeight hrightWeight O)
          (left :
            MPFam O.left)
          (right :
            MPFam O.right)
          (M N : ℕ),
          (profiledExpansionScheduler
            hleftWeight hrightWeight O hsupport left right M N).map
              (fun index => (retainedOrbitKey index).erasedShape) =
            (profiledSchedulerProgram
              hleftWeight hrightWeight O hsupport left right M N).trace)
      O ?_ hsupport left right M N
  intro parent ih hsupport left right M N
  rw [
    profiled_expansion_append,
    profiled_scheduler_append,
    List.map_append, List.map_append, List.map_replicate,
    MPFam.retained_key_index,
    ESProgra.trace_append,
    ESProgra.trace_append,
    replicate_erased_program]
  by_cases hleft :
      parent.operationalNestedLeft.weight leftWeight rightWeight < n
  · simp only [dif_pos hleft]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      rw [
        ih parent.operationalNestedLeft
          (parent.nestedLeftDescends
            hleftWeight hrightWeight hleft)
          (operational_left_supported
            hleftWeight hrightWeight parent hsupport hleft)
          left (left.correction parent right) M N,
        ih parent.operationalNestedRight
          (parent.nestedRightDescends
            hleftWeight hrightWeight hright)
          (operational_nested_supported
            hleftWeight hrightWeight parent hsupport hright)
          right (left.correction parent right) M N]
      simp
    · simp only [dif_neg hright, List.map_nil]
      rw [
        ih parent.operationalNestedLeft
          (parent.nestedLeftDescends
            hleftWeight hrightWeight hleft)
          (operational_left_supported
            hleftWeight hrightWeight parent hsupport hleft)
          left (left.correction parent right) M N]
      simp
  · simp only [dif_neg hleft, List.map_nil]
    by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · simp only [dif_pos hright]
      rw [
        ih parent.operationalNestedRight
          (parent.nestedRightDescends
            hleftWeight hrightWeight hright)
          (operational_nested_supported
            hleftWeight hrightWeight parent hsupport hright)
          right (left.correction parent right) M N]
      simp
    · split
      · omega
      · simp [ESProgra.trace_empty]

namespace POBranch

/-- Finite-index scheduler trace attached to one profiled branch. -/
noncomputable def schedulerFinIdx
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  profiledExpansionScheduler
    hleftWeight hrightWeight branch.obstruction branch.support
      branch.left branch.right M N

/-- One profiled branch permutes to its finite-index scheduler trace. -/
lemma idxPermScheduler
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List.Perm
      (branch.indexTrace M N)
      (schedulerFinIdx branch M N) := by
  exact
    profiled_perm_scheduler
      hleftWeight hrightWeight branch.obstruction branch.support
        branch.left branch.right M N

/-- Erasing one profiled finite-index scheduler trace recovers its shape program. -/
lemma key_scheduler_program
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    (schedulerFinIdx branch M N).map
      (fun index => (retainedOrbitKey index).erasedShape) =
      (GRProgra.POBranch.schedulerShapeProgram
        branch M N).trace := by
  exact
    key_fin_program
      hleftWeight hrightWeight branch.obstruction branch.support
        branch.left branch.right M N

end POBranch

namespace IOBranch

/-- Finite-index scheduler trace attached to one raw-source guarded branch. -/
noncomputable def schedulerFinIdx
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
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  POBranch.schedulerFinIdx
    (branch.profiledObstructionBranch raw) M N

/-- One raw-source branch permutes to its finite-index scheduler trace. -/
lemma idxPermScheduler
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
    List.Perm
      (branch.indexTrace raw M N)
      (schedulerFinIdx raw branch M N) := by
  exact
    POBranch.idxPermScheduler
      (branch.profiledObstructionBranch raw) M N

/-- Erasing one raw-source finite-index scheduler trace recovers its shape program. -/
lemma key_scheduler_program
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
    (schedulerFinIdx raw branch M N).map
      (fun index => (retainedOrbitKey index).erasedShape) =
      (GRProgra.IOBranch.schedulerShapeProgram
        raw branch M N).trace := by
  exact
    POBranch.key_scheduler_program
      (branch.profiledObstructionBranch raw) M N

end IOBranch

/--
Finite-index scheduler trace obtained by concatenating the canonical guarded
root grid.
-/
noncomputable def
    guardedIdxFin
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  ((guardedSupportedBranches
    n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
      IOBranch.schedulerFinIdx
        raw branch M N).flatten

/--
The guarded root-first finite-index expansion permutes to the concatenated
finite-index scheduler trace.
-/
lemma
    guarded_perm_scheduler
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List.Perm
      (((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          branch.indexTrace raw M N).flatten)
      (guardedIdxFin
        raw M N) := by
  unfold
    guardedIdxFin
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      exact List.Perm.refl []
  | cons branch branches ih =>
      simp only [List.map_cons, List.flatten_cons]
      exact
        List.Perm.append
          (IOBranch.idxPermScheduler
            raw branch M N)
          ih

/--
Erasing the guarded finite-index scheduler trace recovers the existing
recursive erased-shape scheduler program literally.
-/
lemma
    key_erased_program
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    (guardedIdxFin
      raw M N).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      (guardedSchedulerProgram
        raw M N).trace := by
  unfold
    guardedIdxFin
  unfold
    guardedSchedulerProgram
  rw [
    ESProgra.traceSchedulerConcat]
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        List.flatMap_cons]
      rw [
        IOBranch.key_scheduler_program,
        ih]

end
  FISchedu
end TCTex
end Submission

/-!
# Finite-index scalar recurrences for guarded scheduler traces

The guarded raw-source scheduler retains exact polynomial-orbit indices.  After
fixing one retained index, every supported obstruction branch contributes its
left nested count, its repeated correction-root count, and its right nested
count.  This file records that scalar recurrence and rewrites the complete
canonical guarded scheduler count as a finite sum of branch counts.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  IMRec

open
  RRPkt
open
  RRPkt.POObstru
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  FISchedu

/-- Multiplicity of one retained index in one supported profiled scheduler trace. -/
noncomputable def
    profiledSchedulerCount
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  (profiledExpansionScheduler
    hleftWeight hrightWeight O hsupport left right M N).count index

/--
One supported profiled branch contributes its two nested counts and the
matching repeated correction-root multiplicity.
-/
lemma
    profiled_scheduler_count
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    profiledSchedulerCount
        hleftWeight hrightWeight O hsupport left right M N index =
      (if hleft :
          O.operationalNestedLeft.weight leftWeight rightWeight < n then
        profiledSchedulerCount
          hleftWeight hrightWeight O.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight O hsupport hleft)
          left (left.correction O right) M N index
      else
        0) +
      (if
        MPFam.correctionIndex
            hleftWeight hrightWeight O hsupport =
          index then
        left.multiplicity M N * right.multiplicity M N
      else
        0) +
      (if hright :
          O.operationalNestedRight.weight leftWeight rightWeight < n then
        profiledSchedulerCount
          hleftWeight hrightWeight O.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight O hsupport hright)
          right (left.correction O right) M N index
      else
        0) := by
  rw [
    profiledSchedulerCount,
    profiled_expansion_append,
    List.count_append, List.count_append, List.count_replicate]
  simp only [
    profiledSchedulerCount,
    beq_iff_eq]
  split <;> split <;> split <;> rfl

namespace IOBranch

/-- Multiplicity of one retained index in one raw-source guarded scheduler branch. -/
noncomputable def schedulerIndexCount
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  (FISchedu.IOBranch.schedulerFinIdx
    raw branch M N).count index

/-- The scalar finite-index recurrence specialized to a raw-source guarded branch. -/
lemma scheduler_index_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    schedulerIndexCount raw branch M N index =
      (if hleft :
          branch.obstruction.operationalNestedLeft.weight
              leftWeight rightWeight < n then
        profiledSchedulerCount
          hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight branch.obstruction branch.support hleft)
          (raw.multiplicityProfileFamily branch.leftIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          M N index
      else
        0) +
      (if
        MPFam.correctionIndex
            hleftWeight hrightWeight branch.obstruction branch.support =
          index then
        (raw.multiplicityProfileFamily branch.leftIndex).multiplicity
              M N *
          (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
              M N
      else
        0) +
      (if hright :
          branch.obstruction.operationalNestedRight.weight
              leftWeight rightWeight < n then
        profiledSchedulerCount
          hleftWeight hrightWeight branch.obstruction.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight branch.obstruction branch.support hright)
          (raw.multiplicityProfileFamily branch.rightIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          M N index
      else
        0) := by
  exact
    profiled_scheduler_count
      hleftWeight hrightWeight branch.obstruction branch.support
        (raw.multiplicityProfileFamily branch.leftIndex)
        (raw.multiplicityProfileFamily branch.rightIndex)
        M N index

end IOBranch

/-- Finite sum of exact retained-index counts over the canonical guarded root grid. -/
noncomputable def
    guardedSchedulerSum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerIndexCount
          raw branch M N index).sum

/-- The complete canonical guarded scheduler count is its finite branch-count sum. -/
lemma
    count_guarded_retained
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (guardedIdxFin
      raw M N).count index =
      guardedSchedulerSum
        raw M N index := by
  unfold
    guardedIdxFin
  unfold
    guardedSchedulerSum
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.flatten_cons, List.count_append,
        List.sum_cons,
        IOBranch.schedulerIndexCount,
        ih]

end
  IMRec
end TCTex
end Submission

/-!
# Summed scalar recurrences for guarded scheduler traces

The exact retained-index scheduler count is a finite sum of branch counts.
Each branch count, in turn, is the sum of its left nested count, repeated
correction-root multiplicity, and right nested count.  This file records the
fully expanded scalar sum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  IMRec

open
  RRPkt
open
  RRPkt.POObstru
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  FISchedu

namespace IOBranch

/--
Scalar recurrence value of one raw-source guarded branch at one retained
polynomial-orbit index.
-/
noncomputable def schedulerIdxValue
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  (if hleft :
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n then
    profiledSchedulerCount
      hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
      (operational_left_supported
        hleftWeight hrightWeight branch.obstruction branch.support hleft)
      (raw.multiplicityProfileFamily branch.leftIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      M N index
  else
    0) +
  (if
    MPFam.correctionIndex
        hleftWeight hrightWeight branch.obstruction branch.support =
      index then
    (raw.multiplicityProfileFamily branch.leftIndex).multiplicity
          M N *
      (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
          M N
  else
    0) +
  (if hright :
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n then
    profiledSchedulerCount
      hleftWeight hrightWeight branch.obstruction.operationalNestedRight
      (operational_nested_supported
        hleftWeight hrightWeight branch.obstruction branch.support hright)
      (raw.multiplicityProfileFamily branch.rightIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      M N index
  else
    0)

/-- A raw-source branch count is its explicit scalar recurrence value. -/
lemma scheduler_recurrence_value
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    schedulerIndexCount raw branch M N index =
      schedulerIdxValue raw branch M N index := by
  unfold schedulerIdxValue
  exact scheduler_index_count raw branch M N index

end IOBranch

/--
Sum of the explicit scalar recurrence values over the canonical guarded
raw-source root grid.
-/
noncomputable def
    guardedSchedulerRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerIdxValue
          raw branch M N index).sum

/-- The finite branch-count sum is the sum of explicit branch recurrences. -/
lemma
    guarded_sum_recurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    guardedSchedulerSum
        raw M N index =
      guardedSchedulerRecurrence
        raw M N index := by
  unfold
    guardedSchedulerSum
  unfold
    guardedSchedulerRecurrence
  apply congrArg List.sum
  apply List.map_congr_left
  intro branch _hbranch
  exact
    IOBranch.scheduler_recurrence_value
      raw branch M N index

/-- The full guarded scheduler trace count is the summed scalar recurrence. -/
lemma
    count_recurrence_sum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (FISchedu.guardedIdxFin
      raw M N).count index =
      guardedSchedulerRecurrence
        raw M N index := by
  rw [
    count_guarded_retained,
    guarded_sum_recurrence]

end
  IMRec
end TCTex
end Submission

/-!
# Additive decomposition of guarded raw-source recurrence sums

The scalar recurrence sum separates into three algebraic contributions: left
nested collector counts, matching correction-root products, and right nested
collector counts.  This file records that decomposition and its empty-grid
base cases.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  IMRec

open
  RRPkt
open
  RRPkt.POObstru
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  PGSrc
open
  ESIdx

namespace IOBranch

/-- Left nested contribution of one raw-source guarded branch. -/
noncomputable def schedulerNestedValue
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  if hleft :
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n then
    profiledSchedulerCount
      hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
      (operational_left_supported
        hleftWeight hrightWeight branch.obstruction branch.support hleft)
      (raw.multiplicityProfileFamily branch.leftIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      M N index
  else
    0

/-- Matching correction-root product contribution of one raw-source branch. -/
noncomputable def schedulerFinRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  if
    MPFam.correctionIndex
        hleftWeight hrightWeight branch.obstruction branch.support =
      index then
    (raw.multiplicityProfileFamily branch.leftIndex).multiplicity
          M N *
      (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
          M N
  else
    0

/-- Right nested contribution of one raw-source guarded branch. -/
noncomputable def schedulerRecurrenceValue
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  if hright :
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n then
    profiledSchedulerCount
      hleftWeight hrightWeight branch.obstruction.operationalNestedRight
      (operational_nested_supported
        hleftWeight hrightWeight branch.obstruction branch.support hright)
      (raw.multiplicityProfileFamily branch.rightIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      M N index
  else
    0

/-- One branch recurrence is the sum of its left, root-product, and right terms. -/
lemma scheduler_idx_nested
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    schedulerIdxValue raw branch M N index =
      schedulerNestedValue raw branch M N index +
        schedulerFinRecurrence raw branch M N index +
          schedulerRecurrenceValue raw branch M N index := by
  rfl

end IOBranch

/-- Global left nested contribution over the canonical guarded root grid. -/
noncomputable def
    idxNestedRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerNestedValue
          raw branch M N index).sum

/-- Global matching correction-root product contribution. -/
noncomputable def
    idxRecurrenceSum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerFinRecurrence
          raw branch M N index).sum

/-- Global right nested contribution over the canonical guarded root grid. -/
noncomputable def
    guardedRecurrenceSum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    ℕ :=
  ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerRecurrenceValue
          raw branch M N index).sum

/--
The full scalar recurrence sum is the sum of its left nested, root-product,
and right nested contributions.
-/
lemma
    guarded_idx_nested
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    guardedSchedulerRecurrence
        raw M N index =
      idxNestedRecurrence
          raw M N index +
        idxRecurrenceSum
            raw M N index +
          guardedRecurrenceSum
            raw M N index := by
  unfold
    guardedSchedulerRecurrence
  unfold
    idxNestedRecurrence
  unfold
    idxRecurrenceSum
  unfold
    guardedRecurrenceSum
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [
        IOBranch.scheduler_idx_nested,
        ih]
      omega

/-- Exact scheduler count in decomposed recurrence-sum form. -/
lemma
    count_guarded_nested
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (FISchedu.guardedIdxFin
      raw M N).count index =
      idxNestedRecurrence
          raw M N index +
        idxRecurrenceSum
            raw M N index +
          guardedRecurrenceSum
            raw M N index := by
  rw [
    count_recurrence_sum,
    guarded_idx_nested]

/-- Below twice the principal Hall-pair weight, the left nested sum vanishes. -/
lemma
    guarded_idx_left
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hhigh : n ≤ 2 * (leftWeight + rightWeight)) :
    idxNestedRecurrence
        raw M N index =
      0 := by
  unfold
    idxNestedRecurrence
  rw [
    guarded_supported_sum
      hleftWeight hrightWeight hhigh]
  rfl

/-- Below twice the principal Hall-pair weight, the root-product sum vanishes. -/
lemma
    guarded_idx_sum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hhigh : n ≤ 2 * (leftWeight + rightWeight)) :
    idxRecurrenceSum
        raw M N index =
      0 := by
  unfold
    idxRecurrenceSum
  rw [
    guarded_supported_sum
      hleftWeight hrightWeight hhigh]
  rfl

/-- Below twice the principal Hall-pair weight, the right nested sum vanishes. -/
lemma
    guarded_source_idx
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hhigh : n ≤ 2 * (leftWeight + rightWeight)) :
    guardedRecurrenceSum
        raw M N index =
      0 := by
  unfold
    guardedRecurrenceSum
  rw [
    guarded_supported_sum
      hleftWeight hrightWeight hhigh]
  rfl

/-- Below twice the principal Hall-pair weight, the recurrence sum vanishes. -/
lemma
    guarded_idx_recurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hhigh : n ≤ 2 * (leftWeight + rightWeight)) :
    guardedSchedulerRecurrence
        raw M N index =
      0 := by
  unfold
    guardedSchedulerRecurrence
  rw [
    guarded_supported_sum
      hleftWeight hrightWeight hhigh]
  rfl

/-- Below twice the principal Hall-pair weight, the scheduler count vanishes. -/
lemma
    count_guarded_sum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hhigh : n ≤ 2 * (leftWeight + rightWeight)) :
    (FISchedu.guardedIdxFin
      raw M N).count index =
      0 := by
  rw [
    count_recurrence_sum,
    guarded_idx_recurrence
      raw M N index hhigh]

/-- Through cutoff four, positive source weights force the recurrence sum to vanish. -/
lemma
    guarded_idx_four
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hhigh : n ≤ 4) :
    guardedSchedulerRecurrence
        raw M N index =
      0 := by
  apply
    guarded_idx_recurrence
      raw M N index
  omega

end
  IMRec
end TCTex
end Submission

/-!
# Homogeneous packet profiles for guarded raw-source recurrence sums

Every recursively expanded raw-source branch already carries one homogeneous
signed-block formula packet for each retained polynomial-orbit index.  Its
root-first trace permutes to scheduler order.  Summing those packets over the
canonical guarded root grid therefore realizes the complete explicit scalar
recurrence sum as a homogeneous packet evaluation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  IMRec

open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  MPAlg
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  FISchedu

namespace IOBranch

/--
Homogeneous packet counting one retained index in the scheduler-order
expansion of one guarded raw-source branch.
-/
noncomputable def schedulerIdxProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  (branch.profiledObstructionBranch raw)
    |>.profiledIndexFamily
    |>.kernel
    |>.profiles index

/-- The branch packet evaluates to the exact scheduler-order branch count. -/
lemma value_scheduler_cast
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerIdxProfile raw branch index).value
        (M : ℤ) (N : ℤ) =
      (schedulerIndexCount raw branch M N index : ℤ) := by
  rw [schedulerIdxProfile]
  rw [
    (branch.profiledObstructionBranch raw)
      |>.profiledIndexFamily
      |>.kernel
      |>.profiles_nat_count]
  exact_mod_cast
    (FISchedu.IOBranch.idxPermScheduler
      raw branch M N).count_eq index

/-- The branch packet also evaluates to the explicit one-branch recurrence. -/
lemma scheduler_cast_recurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerIdxProfile raw branch index).value
        (M : ℤ) (N : ℤ) =
      (schedulerIdxValue raw branch M N index : ℤ) := by
  rw [
    value_scheduler_cast,
    scheduler_recurrence_value]

end IOBranch

/--
Homogeneous packet counting one retained index in the complete guarded
raw-source scheduler recurrence sum.
-/
noncomputable def
    schedulerRecurrenceProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  FPkt.sum
    ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerIdxProfile
          raw branch index)

/--
The global recurrence-sum packet evaluates to the complete explicit scalar
recurrence sum.
-/
lemma
    cast_recurrence_sum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerRecurrenceProfile
      raw index).value (M : ℤ) (N : ℤ) =
      (guardedSchedulerRecurrence
        raw M N index : ℤ) := by
  unfold
    schedulerRecurrenceProfile
  unfold
    guardedSchedulerRecurrence
  rw [FPkt.value_sum]
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add]
      rw [
        IOBranch.scheduler_cast_recurrence,
        ih]

/-- The same packet evaluates to the complete scheduler-order trace count. -/
lemma
    guarded_cast_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerRecurrenceProfile
      raw index).value (M : ℤ) (N : ℤ) =
      ((guardedIdxFin
        raw M N).count index : ℤ) := by
  rw [
    cast_recurrence_sum,
    count_recurrence_sum]

end
  IMRec
end TCTex
end Submission

/-!
# Additive packet decomposition of guarded raw-source recurrence sums

The scalar scheduler recurrence separates into left nested, repeated
correction-root, and right nested contributions.  Each contribution is itself
represented by a homogeneous signed-block formula packet.  This file exposes
those packets branchwise and after summing the canonical guarded root grid.

The root-product packet is the symbolic repeated-block term: its profile is
compiled directly by `correctionReplicate`, so its evaluation is the product
of the two parent multiplicity packets at the matching correction index.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  IMRec

open
  RRPkt
open
  RRPkt.POObstru
open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  RIRecurs
open
  MPAlg
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  FISchedu

namespace IOBranch

/-- Packet for the surviving left nested contribution of one guarded branch. -/
noncomputable def schedulerNestedProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  if hleft :
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n then
    (profiledOrbitExpansion
      hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
      (operational_left_supported
        hleftWeight hrightWeight branch.obstruction branch.support hleft)
      (raw.multiplicityProfileFamily branch.leftIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex)))
      |>.kernel
      |>.profiles index
  else
    FPkt.zero
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree

/-- Packet for the repeated correction-root product contribution. -/
noncomputable def schedulerIdxRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  (((raw.multiplicityProfileFamily branch.leftIndex).correction
      branch.obstruction
      (raw.multiplicityProfileFamily branch.rightIndex))
    |>.correctionReplicate
      hleftWeight hrightWeight branch.obstruction branch.support)
    |>.kernel
    |>.profiles index

/-- Packet for the surviving right nested contribution of one guarded branch. -/
noncomputable def schedulerNestedRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  if hright :
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n then
    (profiledOrbitExpansion
      hleftWeight hrightWeight branch.obstruction.operationalNestedRight
      (operational_nested_supported
        hleftWeight hrightWeight branch.obstruction branch.support hright)
      (raw.multiplicityProfileFamily branch.rightIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex)))
      |>.kernel
      |>.profiles index
  else
    FPkt.zero
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree

/-- The left nested packet evaluates to its scalar scheduler recurrence term. -/
lemma scheduler_ordered_cast
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerNestedProfile
      raw branch index).value (M : ℤ) (N : ℤ) =
      (schedulerNestedValue
        raw branch M N index : ℤ) := by
  unfold schedulerNestedProfile
  unfold schedulerNestedValue
  by_cases hleft :
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n
  · simp only [dif_pos hleft]
    rw [
      (profiledOrbitExpansion
        hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
        (operational_left_supported
          hleftWeight hrightWeight branch.obstruction branch.support hleft)
        (raw.multiplicityProfileFamily branch.leftIndex)
        ((raw.multiplicityProfileFamily branch.leftIndex).correction
          branch.obstruction
          (raw.multiplicityProfileFamily branch.rightIndex)))
        |>.kernel
        |>.profiles_nat_count]
    exact_mod_cast
      (profiled_perm_scheduler
        hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
        (operational_left_supported
          hleftWeight hrightWeight branch.obstruction branch.support hleft)
        (raw.multiplicityProfileFamily branch.leftIndex)
        ((raw.multiplicityProfileFamily branch.leftIndex).correction
          branch.obstruction
          (raw.multiplicityProfileFamily branch.rightIndex))
        M N).count_eq index
  · simp only [dif_neg hleft, FPkt.value_zero, Int.cast_ofNat_Int]

/-- The root-product packet evaluates to the matching parent product term. -/
lemma scheduler_fin_cast
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerIdxRecurrence
      raw branch index).value (M : ℤ) (N : ℤ) =
      (schedulerFinRecurrence
        raw branch M N index : ℤ) := by
  unfold schedulerIdxRecurrence
  unfold schedulerFinRecurrence
  rw [
    (((raw.multiplicityProfileFamily branch.leftIndex).correction
      branch.obstruction
      (raw.multiplicityProfileFamily branch.rightIndex))
      |>.correctionReplicate
        hleftWeight hrightWeight branch.obstruction branch.support)
      |>.kernel
      |>.profiles_nat_count,
    MPFam.trace_correctionReplicate,
    List.count_replicate]
  simp only [beq_iff_eq]
  by_cases hindex :
      MPFam.correctionIndex
          hleftWeight hrightWeight branch.obstruction branch.support =
        index
  · simp only [hindex, MPFam.correction]
  · simp only [hindex, if_false]

/-- The right nested packet evaluates to its scalar scheduler recurrence term. -/
lemma scheduler_nat_cast
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerNestedRecurrence
      raw branch index).value (M : ℤ) (N : ℤ) =
      (schedulerRecurrenceValue
        raw branch M N index : ℤ) := by
  unfold schedulerNestedRecurrence
  unfold schedulerRecurrenceValue
  by_cases hright :
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n
  · simp only [dif_pos hright]
    rw [
      (profiledOrbitExpansion
        hleftWeight hrightWeight branch.obstruction.operationalNestedRight
        (operational_nested_supported
          hleftWeight hrightWeight branch.obstruction branch.support hright)
        (raw.multiplicityProfileFamily branch.rightIndex)
        ((raw.multiplicityProfileFamily branch.leftIndex).correction
          branch.obstruction
          (raw.multiplicityProfileFamily branch.rightIndex)))
        |>.kernel
        |>.profiles_nat_count]
    exact_mod_cast
      (profiled_perm_scheduler
        hleftWeight hrightWeight branch.obstruction.operationalNestedRight
        (operational_nested_supported
          hleftWeight hrightWeight branch.obstruction branch.support hright)
        (raw.multiplicityProfileFamily branch.rightIndex)
        ((raw.multiplicityProfileFamily branch.leftIndex).correction
          branch.obstruction
          (raw.multiplicityProfileFamily branch.rightIndex))
        M N).count_eq index
  · simp only [dif_neg hright, FPkt.value_zero, Int.cast_ofNat_Int]

/-- Packet-level sum of the three one-branch scheduler recurrence terms. -/
noncomputable def schedulerDecomposedRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  FPkt.add
    (FPkt.add
      (schedulerNestedProfile raw branch index)
      (schedulerIdxRecurrence raw branch index))
    (schedulerNestedRecurrence raw branch index)

/-- The decomposed one-branch packet evaluates to the complete recurrence. -/
lemma decomposed_recurrence_cast
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerDecomposedRecurrence
      raw branch index).value (M : ℤ) (N : ℤ) =
      (schedulerIdxValue raw branch M N index : ℤ) := by
  rw [
    schedulerDecomposedRecurrence,
    FPkt.value_add,
    FPkt.value_add,
    scheduler_ordered_cast,
    scheduler_fin_cast,
    scheduler_nat_cast,
    ← Int.natCast_add,
    ← Int.natCast_add,
    ← scheduler_idx_nested]

/--
The recursively compiled branch packet and its visible three-part scheduler
decomposition agree on all natural multiplicity inputs.
-/
lemma scheduler_decomposed_recurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerIdxProfile raw branch index).value
        (M : ℤ) (N : ℤ) =
      (schedulerDecomposedRecurrence
        raw branch index).value (M : ℤ) (N : ℤ) := by
  rw [
    scheduler_cast_recurrence,
    decomposed_recurrence_cast]

end IOBranch

/-- Global packet sum of all left nested scheduler recurrence terms. -/
noncomputable def
    guardedIdxRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  FPkt.sum
    ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerNestedProfile
          raw branch index)

/-- Global packet sum of all repeated correction-root product terms. -/
noncomputable def
    finRecurrenceProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  FPkt.sum
    ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerIdxRecurrence
          raw branch index)

/-- Global packet sum of all right nested scheduler recurrence terms. -/
noncomputable def
    idxRecurrenceProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  FPkt.sum
    ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.schedulerNestedRecurrence
          raw branch index)

/-- The global left nested packet evaluates to the scalar left nested sum. -/
lemma
    guarded_cast_sum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (guardedIdxRecurrence
      raw index).value (M : ℤ) (N : ℤ) =
      (idxNestedRecurrence
        raw M N index : ℤ) := by
  unfold
    guardedIdxRecurrence
  unfold
    idxNestedRecurrence
  rw [FPkt.value_sum]
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add]
      rw [
        IOBranch.scheduler_ordered_cast,
        ih]

/-- The global root-product packet evaluates to the scalar root-product sum. -/
lemma
    value_guarded_cast
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (finRecurrenceProfile
      raw index).value (M : ℤ) (N : ℤ) =
      (idxRecurrenceSum
        raw M N index : ℤ) := by
  unfold
    finRecurrenceProfile
  unfold
    idxRecurrenceSum
  rw [FPkt.value_sum]
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add]
      rw [
        IOBranch.scheduler_fin_cast,
        ih]

/-- The global right nested packet evaluates to the scalar right nested sum. -/
lemma
    value_cast_sum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (idxRecurrenceProfile
      raw index).value (M : ℤ) (N : ℤ) =
      (guardedRecurrenceSum
        raw M N index : ℤ) := by
  unfold
    idxRecurrenceProfile
  unfold
    guardedRecurrenceSum
  rw [FPkt.value_sum]
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add]
      rw [
        IOBranch.scheduler_nat_cast,
        ih]

/-- Visible global packet sum of left nested, root-product, and right nested terms. -/
noncomputable def
    idxDecomposedRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      (retainedOrbitKey index).erasedShape.pairLeftDegree
      (retainedOrbitKey index).erasedShape.pairRightDegree :=
  FPkt.add
    (FPkt.add
      (guardedIdxRecurrence
        raw index)
      (finRecurrenceProfile
        raw index))
    (idxRecurrenceProfile
      raw index)

/-- The visible global three-part packet evaluates to the full recurrence sum. -/
lemma
    decomposed_cast_recurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (idxDecomposedRecurrence
      raw index).value (M : ℤ) (N : ℤ) =
      (guardedSchedulerRecurrence
        raw M N index : ℤ) := by
  rw [
    idxDecomposedRecurrence,
    FPkt.value_add,
    FPkt.value_add,
    guarded_cast_sum,
    value_guarded_cast,
    value_cast_sum,
    ← Int.natCast_add,
    ← Int.natCast_add,
    ← guarded_idx_nested]

/--
The existing global recurrence packet and its visible three-part scheduler
decomposition agree on all natural multiplicity inputs.
-/
lemma
    decomposed_recurrence_profile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerRecurrenceProfile
      raw index).value (M : ℤ) (N : ℤ) =
      (idxDecomposedRecurrence
        raw index).value (M : ℤ) (N : ℤ) := by
  rw [
    cast_recurrence_sum,
    decomposed_cast_recurrence]

end
  IMRec
end TCTex
end Submission

/-!
# A finite-index profile kernel for guarded raw-source scheduler traces

The homogeneous recurrence-sum packet for each retained orbit index assembles
into the generic finite-index multiplicity profile interface for the complete
guarded raw-source scheduler trace.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  PKBounda

open
  MPAlg
open
  RITrace
open
  ESIdx
open
  IMRec
open
  FISchedu

/--
The complete guarded raw-source scheduler trace has a homogeneous
finite-index multiplicity profile.
-/
noncomputable def
    guardedIdxMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    IMProfa
      (guardedIdxFin
        raw) where
  profiles :=
    schedulerRecurrenceProfile
      raw
  profiles_nat_count M N index :=
    guarded_cast_count
      raw M N index

/--
Bundle the complete guarded raw-source scheduler trace with its homogeneous
finite-index multiplicity profile.
-/
noncomputable def
    schedulerProfiledFamily
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    PIFam n leftWeight rightWeight where
  trace :=
    guardedIdxFin
      raw
  kernel :=
    guardedIdxMult
      raw

@[simp]
lemma
    finIdxFamily
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    (schedulerProfiledFamily
      raw).trace M N =
      guardedIdxFin
        raw M N := by
  rfl

@[simp]
lemma
    profilesIdxFamily
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (schedulerProfiledFamily
      raw).kernel.profiles index =
      schedulerRecurrenceProfile
        raw index := by
  rfl

end
  PKBounda
end TCTex
end Submission

/-!
# Erased-shape scheduler profiles from guarded recurrence-sum packets

The guarded scheduler trace has homogeneous packets for every retained
polynomial-orbit index.  Summing those packets over equal erased Hall shapes
and transporting across the scheduler erasure theorem gives homogeneous
profiles for the recursive erased-shape scheduler program itself.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  FEProgra

open
  CRLayer
open
  RITrace
open
  ESIdx
open
  ISLift
open
  PKBounda
open
  FISchedu
open
  GRProgra
open
  SEAlg
open
  RTProgra

/--
Erase retained polynomial-orbit indices from the guarded scheduler trace
family while summing packets over equal erased Hall shapes.
-/
noncomputable def
    guardedSchedulerProfiled
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    PEFam :=
  profiledErasedFamily
    (schedulerProfiledFamily
      raw)

@[simp]
lemma
    guardedErasedFamily
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    (guardedSchedulerProfiled
      raw).trace M N =
      (guardedIdxFin
        raw M N).map fun index =>
          (retainedOrbitKey index).erasedShape := by
  rw [
    guardedSchedulerProfiled,
    profiled_erased_family,
    finIdxFamily]

/--
The recursive erased-shape scheduler program has homogeneous shape
multiplicity profiles obtained from the guarded recurrence-sum packets.
-/
noncomputable def
    guardedProgramMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EMProf
      (fun M N =>
        (guardedSchedulerProgram
          raw M N).trace) :=
  (guardedSchedulerProfiled
    raw).kernel.of_trace_eq fun M N => by
      rw [
        guardedErasedFamily]
      exact
        key_erased_program
          raw M N

/--
Evaluation of the erased-shape scheduler-program packet is its exact shape
multiplicity.
-/
lemma
    profiles_cast_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    ((guardedProgramMult
      raw).profiles word).value (M : ℤ) (N : ℤ) =
      (((guardedSchedulerProgram
        raw M N).trace.count word : ℕ) : ℤ) := by
  exact
    (guardedProgramMult
      raw).profiles_nat_count M N word

/--
A comparison between the canonical scheduler program and the endpoint
collector program transports the recurrence-sum packets to a profiled
realization of the endpoint program.
-/
noncomputable def
    endpointProfiledRecurrence
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight) :
    EPRealiz
      layer where
  family := {
    trace :=
      fun M N =>
        (endpointErasedProgram layer M N).trace
    kernel :=
      (guardedProgramMult
        (multiplicityProfileShape
          decomposition.raw)).permTransport decomposition.program_trace_perm }
  trace_eq _M _N :=
    rfl

/--
The recurrence-sum packet route compiles a recursive scheduler-program
comparison directly to endpoint shape-fiber interpolation.
-/
noncomputable def
    endpointInterpolationRecurrence
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight) :=
  (endpointProfiledRecurrence
    decomposition).fiberProfileInterpolation
      hleftWeight hrightWeight decomposition.raw

end
  FEProgra
end TCTex
end Submission

/-!
# Claim 5 from guarded recurrence-sum packet profiles

The guarded recursive recurrence sum supplies homogeneous packets for the
endpoint erased-shape scheduler program.  Once the remaining all-integral
signed recollection law is given, those packets feed the existing Claim 5
coordinate-polynomial constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open
  FPInterp
open
  CRLayer
open
  CFSubsti
open
  FEProgra
open
  GRProgra

namespace
  PCBridgea

/--
The remaining signed extension after guarded recurrence-sum packets have
been transported to endpoint interpolation.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      RCDecompa
        layer (by simp) (by simp)) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d)
    (endpointInterpolationRecurrence
      decomposition)

/--
The truncated signed recollection law for endpoint packets compiled from
guarded recurrence sums.
-/
def SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      RCDecompa
        layer (by simp) (by simp)) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((EFInterp.truncNaturalPacket.{u}
        (d := d)
        (endpointInterpolationRecurrence
          decomposition)).packets.map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/-- The truncated signed recollection law supplies the all-integral lift. -/
def allLiftSatisfies
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      RCDecompa
        layer (by simp) (by simp))
    (hlistEval : SatisfiesTruncEval.{u} (d := d) decomposition) :
    AILift.{u} (d := d) decomposition where
  listEval_eq :=
    hlistEval

/-- The all-integral lift recovers the truncated signed recollection law. -/
lemma satisfies_trunc_all
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      RCDecompa
        layer (by simp) (by simp))
    (lift : AILift.{u} (d := d) decomposition) :
    SatisfiesTruncEval.{u} (d := d) decomposition :=
  lift.listEval_eq

/-- The two signed-extension interfaces agree. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      RCDecompa
        layer (by simp) (by simp)) :
    SatisfiesTruncEval.{u} (d := d) decomposition ↔
      AILift.{u} (d := d) decomposition :=
  ⟨allLiftSatisfies decomposition,
    satisfies_trunc_all decomposition⟩

end
  PCBridgea

namespace TSInput

open
  PCBridgea

/--
Guarded recurrence-sum packets, their signed lift, singleton recollections,
and graded Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem
    guardedRecurrenceLift
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
      RCDecompa
        layer (by simp) (by simp))
    (lift :
      AILift.{u} (d := d) decomposition)
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
  input.fiberInterpolationLift
    hn H hH
      (endpointInterpolationRecurrence
        decomposition)
      lift hsourceSupported factorNormalization hinputWeight

/--
The direct truncated signed recollection law is an equivalent Claim 5
constructor input for guarded recurrence-sum packets.
-/
theorem
    coordinateGuardedRecurrence
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
      RCDecompa
        layer (by simp) (by simp))
    (hlistEval :
      SatisfiesTruncEval.{u} (d := d) decomposition)
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
  input.guardedRecurrenceLift
    hn H hH decomposition
      (allLiftSatisfies decomposition hlistEval)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Weighted formulas from guarded recurrence-sum packets

The guarded scheduler recurrence sum has already been packaged as one
homogeneous signed-block packet for every retained polynomial-orbit index.
This file substitutes arbitrary parent formulas into those packets.  The
resulting formula types retain the exact weighted Hall degree.

Erasing orbit indices and transporting across the endpoint-program comparison
gives the same formula interface for scheduler-program and endpoint-program
shape multiplicities.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CFSubsti
open
  CRLayer
open
  RITrace
open
  ESIdx
open
  RTProgra
open
  IMRec
open
  FEProgra
open
  FISchedu
open
  GRProgra
open
  SEAlg

namespace
  PFSubstib

/--
Substitute arbitrary parent formulas into the complete guarded recurrence-sum
packet for one retained polynomial-orbit index.
-/
noncomputable def
    schedulerRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree) :
    WBForm H ι
      ((retainedOrbitKey index).erasedShape.pairLeftDegree *
          leftFormulaWeight +
        (retainedOrbitKey index).erasedShape.pairRightDegree *
          rightFormulaWeight) :=
  (schedulerRecurrenceProfile
    raw index).toFormula normalizer left right hleft hright

/--
The substituted per-index formula evaluates to the underlying homogeneous
recurrence-sum packet.
-/
@[simp]
lemma
    sourceRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (schedulerRecurrenceFormula
      raw index normalizer left right hleft hright).eval e =
      (schedulerRecurrenceProfile
        raw index).value (left.eval e) (right.eval e) := by
  rw [
    schedulerRecurrenceFormula,
    HFPkt.eval_toFormula]

/--
At natural parent multiplicities, the substituted per-index formula evaluates
to the complete explicit scalar recurrence sum.
-/
lemma
    formula_recurrence_sum
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (schedulerRecurrenceFormula
      raw index normalizer left right hleft hright).eval e =
      (guardedSchedulerRecurrence
        raw M N index : ℤ) := by
  rw [
    sourceRecurrenceFormula,
    hleftEval,
    hrightEval,
    cast_recurrence_sum]

/--
Substitute arbitrary parent formulas into the erased-shape profile for the
recursive scheduler program.
-/
noncomputable def
    guardedMultFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  ((guardedProgramMult
    raw).profiles word).toFormula normalizer left right hleft hright

/--
At natural parent multiplicities, the erased-shape scheduler formula evaluates
to the exact occurrence count in the recursive scheduler program.
-/
lemma
    mult_formula_count
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (guardedMultFormula
      raw word normalizer left right hleft hright).eval e =
      (((guardedSchedulerProgram
        raw M N).trace.count word : ℕ) : ℤ) := by
  rw [
    guardedMultFormula,
    HFPkt.eval_toFormula,
    hleftEval,
    hrightEval]
  exact
    profiles_cast_count
      raw M N word

/--
Substitute arbitrary parent formulas into the endpoint-program shape profile
obtained from a guarded scheduler-program comparison.
-/
noncomputable def
    endpointMultRecurrence
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  (((endpointProfiledRecurrence
    decomposition).family.kernel.profiles word).toFormula
      normalizer left right hleft hright)

/--
At natural parent multiplicities, the transported endpoint-program formula
evaluates to the selected endpoint correction-shape multiplicity.
-/
lemma
    endpoint_formula_count
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (endpointMultRecurrence
      decomposition word normalizer left right hleft hright).eval e =
      ((selectedErasedShape layer M N).count word :
        ℤ) := by
  rw [
    endpointMultRecurrence,
    HFPkt.eval_toFormula,
    hleftEval,
    hrightEval,
    (endpointProfiledRecurrence
      decomposition).family.kernel.profiles_nat_count,
    (endpointProfiledRecurrence
      decomposition).trace_eq M N,
    endpoint_erased_program]

/--
The weighted budget recorded by every erased-shape formula is its literal
Hall-pair word weight.
-/
lemma erased_shape_formula
    (word : CWord HPAtom)
    (leftFormulaWeight rightFormulaWeight : ℕ) :
    word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight =
      word.weight (HPAtom.weight leftFormulaWeight rightFormulaWeight) := by
  rw [CWord.pair_atom_degree]

end
  PFSubstib

end TCTex
end Submission

/-!
# Low-cutoff Claim 5 forwarding from guarded recurrence-sum packets

Through cutoff four, the recursive scheduler-program comparison is already
available.  This file specializes the guarded recurrence-sum packet route to
that range and exposes its endpoint interpolation and Claim 5 constructors.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  FEProgra
open
  PCBridgea
open
  GRProgra
open
  FIProf

namespace
  OLBridge

/--
Through cutoff four, the recurrence-sum packet route reaches endpoint
interpolation from any retained raw shape-fiber profile kernel.
-/
noncomputable def
    fiberInterpolationRecurrence
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :=
  endpointInterpolationRecurrence
    (recNFour
      layer hhigh raw)

/-- Remaining all-integral lift for the cutoff-four recurrence-sum route. -/
abbrev AllNFour
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    Prop :=
  AILift.{u} (d := d)
    (recNFour
      layer hhigh raw)

/--
Direct truncated signed recollection law for the cutoff-four recurrence-sum
route.
-/
abbrev SatisfiesNFour
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    Prop :=
  SatisfiesTruncEval.{u} (d := d)
    (recNFour
      layer hhigh raw)

/-- The two cutoff-four signed-extension interfaces agree. -/
theorem satisfies_all_lift
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    SatisfiesNFour.{u} (d := d) layer hhigh raw ↔
      AllNFour.{u} (d := d) layer hhigh raw :=
  satisfies_trunc_lift
    (recNFour
      layer hhigh raw)

end
  OLBridge

namespace TSInput

open
  OLBridge

/--
Through cutoff four, guarded recurrence-sum packets and their signed lift
construct the Claim 5 coordinate polynomials.
-/
theorem
    recurrenceNLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (lift :
      AllNFour.{u} (d := d) layer hhigh raw)
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
  input.guardedRecurrenceLift
    hn H hH
      (recNFour
        layer hhigh raw)
      lift hsourceSupported factorNormalization hinputWeight

/--
Through cutoff four, the direct truncated signed recollection law is an
equivalent Claim 5 constructor input.
-/
theorem
    recurrenceNFour
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (hlistEval :
      SatisfiesNFour.{u} (d := d) layer hhigh raw)
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
  input.coordinateGuardedRecurrence
    hn H hH
      (recNFour
        layer hhigh raw)
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Weighted formulas for the decomposed guarded recurrence sum

The packet-level scheduler recurrence has visible left nested, repeated
correction-root, and right nested contributions.  Substituting arbitrary
parent formulas into those packets produces integer-valued Hall-binomial
formulas with the exact retained-index weighted budget.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CFSubsti
open
  RITrace
open
  ESIdx
open
  IMRec
open
  PFSubstib

namespace
  DFSubsti

/-- Formula for the global left nested recurrence contribution. -/
noncomputable def
    guardedIdxFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree) :
    WBForm H ι
      ((retainedOrbitKey index).erasedShape.pairLeftDegree *
          leftFormulaWeight +
        (retainedOrbitKey index).erasedShape.pairRightDegree *
          rightFormulaWeight) :=
  (guardedIdxRecurrence
    raw index).toFormula normalizer left right hleft hright

/-- Formula for the global repeated correction-root product contribution. -/
noncomputable def
    guardedFinFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree) :
    WBForm H ι
      ((retainedOrbitKey index).erasedShape.pairLeftDegree *
          leftFormulaWeight +
        (retainedOrbitKey index).erasedShape.pairRightDegree *
          rightFormulaWeight) :=
  (finRecurrenceProfile
    raw index).toFormula normalizer left right hleft hright

/-- Formula for the global right nested recurrence contribution. -/
noncomputable def
    guardedNestedRecurrence
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree) :
    WBForm H ι
      ((retainedOrbitKey index).erasedShape.pairLeftDegree *
          leftFormulaWeight +
        (retainedOrbitKey index).erasedShape.pairRightDegree *
          rightFormulaWeight) :=
  (idxRecurrenceProfile
    raw index).toFormula normalizer left right hleft hright

/-- Formula for the visible three-part global scheduler recurrence. -/
noncomputable def
    idxDecomposedFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree) :
    WBForm H ι
      ((retainedOrbitKey index).erasedShape.pairLeftDegree *
          leftFormulaWeight +
        (retainedOrbitKey index).erasedShape.pairRightDegree *
          rightFormulaWeight) :=
  (idxDecomposedRecurrence
    raw index).toFormula normalizer left right hleft hright

/-- The left nested formula evaluates to its homogeneous packet. -/
@[simp]
lemma
    recurrenceSumFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedIdxFormula
      raw index normalizer left right hleft hright).eval e =
      (guardedIdxRecurrence
        raw index).value (left.eval e) (right.eval e) := by
  rw [
    guardedIdxFormula,
    HFPkt.eval_toFormula]

/-- The root-product formula evaluates to its homogeneous packet. -/
@[simp]
lemma
    evalRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedFinFormula
      raw index normalizer left right hleft hright).eval e =
      (finRecurrenceProfile
        raw index).value (left.eval e) (right.eval e) := by
  rw [
    guardedFinFormula,
    HFPkt.eval_toFormula]

/-- The right nested formula evaluates to its homogeneous packet. -/
@[simp]
lemma
    finRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedNestedRecurrence
      raw index normalizer left right hleft hright).eval e =
      (idxRecurrenceProfile
        raw index).value (left.eval e) (right.eval e) := by
  rw [
    guardedNestedRecurrence,
    HFPkt.eval_toFormula]

/-- The decomposed recurrence formula evaluates to its homogeneous packet. -/
@[simp]
lemma
    finDecomposedFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (idxDecomposedFormula
      raw index normalizer left right hleft hright).eval e =
      (idxDecomposedRecurrence
        raw index).value (left.eval e) (right.eval e) := by
  rw [
    idxDecomposedFormula,
    HFPkt.eval_toFormula]

/-- At natural parent multiplicities, the left nested formula is its scalar sum. -/
lemma
    eval_guarded_formula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (guardedIdxFormula
      raw index normalizer left right hleft hright).eval e =
      (idxNestedRecurrence
        raw M N index : ℤ) := by
  rw [
    recurrenceSumFormula,
    hleftEval,
    hrightEval,
    guarded_cast_sum]

/-- At natural parent multiplicities, the root formula is its scalar product sum. -/
lemma
    guarded_root_formula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (guardedFinFormula
      raw index normalizer left right hleft hright).eval e =
      (idxRecurrenceSum
        raw M N index : ℤ) := by
  rw [
    evalRecurrenceFormula,
    hleftEval,
    hrightEval,
    value_guarded_cast]

/-- At natural parent multiplicities, the right nested formula is its scalar sum. -/
lemma
    guarded_sum_formula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (guardedNestedRecurrence
      raw index normalizer left right hleft hright).eval e =
      (guardedRecurrenceSum
        raw M N index : ℤ) := by
  rw [
    finRecurrenceFormula,
    hleftEval,
    hrightEval,
    value_cast_sum]

/-- At natural parent multiplicities, the recombined formula is the recurrence sum. -/
lemma
    decomposed_formula_recurrence
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (idxDecomposedFormula
      raw index normalizer left right hleft hright).eval e =
      (guardedSchedulerRecurrence
        raw M N index : ℤ) := by
  rw [
    finDecomposedFormula,
    hleftEval,
    hrightEval,
    decomposed_cast_recurrence]

/--
The existing recurrence-sum formula and the visible three-part formula agree
whenever their parent formulas evaluate to natural multiplicities.
-/
lemma
    decomposed_recurrence_formula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (schedulerRecurrenceFormula
      raw index normalizer left right hleft hright).eval e =
      (idxDecomposedFormula
        raw index normalizer left right hleft hright).eval e := by
  rw [
    formula_recurrence_sum
      raw index normalizer left right hleft hright e M N hleftEval hrightEval,
    decomposed_formula_recurrence
      raw index normalizer left right hleft hright e M N hleftEval hrightEval]

end
  DFSubsti

end TCTex
end Submission

/-!
# Vocabulary-indexed weighted endpoint formulas through cutoff four

Endpoint interpolation uses only the finite retained erased-shape vocabulary.
Membership in that vocabulary already proves both Hall-pair bidegrees
positive.  This file removes those routine positivity arguments from the
weighted recurrence-sum formula interface and then specializes the result
through cutoff four, where the recursive scheduler-program comparison is
automatic.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  FIProf
open
  CWSkelet
open
  PFSubstib
open
  GRProgra
open
  SEAlg

namespace
  IVLow

/--
For one retained vocabulary word, substitute arbitrary parent formulas into
the endpoint correction-shape profile obtained from a guarded recurrence-sum
packet comparison.
-/
noncomputable def
    endpointVocabRecurrence
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight) :
    WBForm H ι
      (word.1.pairLeftDegree * leftFormulaWeight +
        word.1.pairRightDegree * rightFormulaWeight) :=
  endpointMultRecurrence
    decomposition word.1 normalizer left right
      (bidegree_positive_vocabulary word.2).1
      (bidegree_positive_vocabulary word.2).2

/--
At natural parent multiplicities, the vocabulary-indexed endpoint formula
evaluates to the selected correction-shape count.
-/
lemma
    endpoint_vocab_count
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (endpointVocabRecurrence
      decomposition word normalizer left right).eval e =
      ((selectedErasedShape layer M N).count word.1 :
        ℤ) := by
  exact
    endpoint_formula_count
      decomposition word.1 normalizer left right
        (bidegree_positive_vocabulary word.2).1
        (bidegree_positive_vocabulary word.2).2
        e M N hleftEval hrightEval

/--
Through cutoff four, the recursive scheduler-program comparison automa
produces one exact weighted endpoint multiplicity formula for every retained
vocabulary word.
-/
noncomputable def
    endpointVocabularyFour
    {d n leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight) :
    WBForm H ι
      (word.1.pairLeftDegree * leftFormulaWeight +
        word.1.pairRightDegree * rightFormulaWeight) :=
  endpointVocabRecurrence
    (recNFour
      layer hhigh raw)
    word normalizer left right

/--
The cutoff-four vocabulary formula evaluates to the exact selected endpoint
correction-shape count.
-/
lemma
    endpoint_four_count
    {d n leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H)
    (M N : ℕ)
    (hleftEval : left.eval e = (M : ℤ))
    (hrightEval : right.eval e = (N : ℤ)) :
    (endpointVocabularyFour
      layer hhigh raw word normalizer left right).eval e =
      ((selectedErasedShape layer M N).count word.1 :
        ℤ) := by
  exact
    endpoint_vocab_count
      (recNFour
        layer hhigh raw)
      word normalizer left right e M N hleftEval hrightEval

/--
The exact target budget of each vocabulary-indexed formula is the literal
weighted Hall-word degree.
-/
lemma vocabulary_formula_word
    {n leftWeight rightWeight : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (leftFormulaWeight rightFormulaWeight : ℕ) :
    word.1.pairLeftDegree * leftFormulaWeight +
        word.1.pairRightDegree * rightFormulaWeight =
      word.1.weight
        (HPAtom.weight leftFormulaWeight rightFormulaWeight) :=
  erased_shape_formula
    word.1 leftFormulaWeight rightFormulaWeight

end
  IVLow

end TCTex
end Submission

/-!
# Symbolic multiplication law for repeated correction-root packets

The repeated correction-root part of the scheduler recurrence is stronger than
its natural-count specialization suggests.  At arbitrary integral source
values, a matching root packet evaluates to the product of its two parent
packets, and a nonmatching root packet evaluates to zero.  Summing the guarded
root grid therefore gives a finite symbolic sum of matching parent products.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RRPkt
open
  RRPkt.POObstru
open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  RIRecurs
open
  MPAlg
open
  OCGrid
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  IMRec
open
  DFSubsti

namespace
  RPSym

/--
An arbitrary-value replicate profile is the selected packet at its selected
index and the zero packet at every other index.
-/
lemma value_replicate_arbitrary
    {n leftWeight rightWeight : ℕ}
    (selected :
      RetainedOrbitIndex n leftWeight rightWeight)
    (multiplicity : ℕ → ℕ → ℕ)
    (profile :
      HFPkt
        (retainedOrbitKey selected).erasedShape.pairLeftDegree
        (retainedOrbitKey selected).erasedShape.pairRightDegree)
    (hprofile :
      ∀ (M N : ℕ),
        profile.value (M : ℤ) (N : ℤ) =
          (multiplicity M N : ℤ))
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (left right : ℤ) :
    ((IMProfa.replicate
      selected multiplicity profile hprofile).profiles index).value left right =
      if selected = index then
        profile.value left right
      else
        0 := by
  classical
  by_cases hindex : index = selected
  · subst index
    simp [IMProfa.replicate]
  · simp [IMProfa.replicate,
      hindex, Ne.symm hindex]

/-- A correction-family packet evaluates to the product of its parent packets. -/
@[simp]
lemma value_packet_arbitrary
    (O : POObstru)
    (left :
      MPFam O.left)
    (right :
      MPFam O.right)
    (leftValue rightValue : ℤ) :
    ((left.correction O right).packet).value leftValue rightValue =
      left.packet.value leftValue rightValue *
        right.packet.value leftValue rightValue := by
  rw [
    MPFam.correction,
    cast_homogeneous_degrees,
    FPkt.value_multiply]

/--
The repeated correction-root family retains its correction packet exactly at
the selected correction index.
-/
lemma profiles_replicate_arbitrary
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport :
      IsSupported (n := n) hleftWeight hrightWeight O)
    (profile :
      MPFam O.correction)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    ((profile.correctionReplicate
      hleftWeight hrightWeight O hsupport).kernel.profiles index).value
        leftValue rightValue =
      if
        MPFam.correctionIndex
            hleftWeight hrightWeight O hsupport =
          index then
        profile.packet.value leftValue rightValue
      else
        0 := by
  rw [MPFam.correctionReplicate]
  rw [
    PIFam.replicate,
    value_replicate_arbitrary,
    cast_homogeneous_degrees]

/--
One guarded repeated-root packet is either the product of its parent packets
or zero, according to whether its correction index is the requested index.
-/
lemma
    scheduler_recurrence_arbitrary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    (IOBranch.schedulerIdxRecurrence
      raw branch index).value leftValue rightValue =
      if
        MPFam.correctionIndex
            hleftWeight hrightWeight branch.obstruction branch.support =
          index then
        (raw.multiplicityProfileFamily
            branch.leftIndex).packet.value leftValue rightValue *
          (raw.multiplicityProfileFamily
            branch.rightIndex).packet.value leftValue rightValue
      else
        0 := by
  rw [
    IOBranch.schedulerIdxRecurrence,
    profiles_replicate_arbitrary,
    value_packet_arbitrary]
  rfl

/--
The global repeated-root packet is a finite symbolic sum of matching parent
packet products over the guarded root grid.
-/
lemma
    finRecurrenceArbitrary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    (finRecurrenceProfile
      raw index).value leftValue rightValue =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          if
            MPFam.correctionIndex
                hleftWeight hrightWeight branch.obstruction branch.support =
              index then
            (raw.multiplicityProfileFamily
                branch.leftIndex).packet.value leftValue rightValue *
              (raw.multiplicityProfileFamily
                branch.rightIndex).packet.value leftValue rightValue
          else
            0).sum := by
  unfold
    finRecurrenceProfile
  rw [FPkt.value_sum]
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [
        scheduler_recurrence_arbitrary,
        ih]

/--
After arbitrary parent-formula substitution, the repeated-root formula remains
the finite symbolic sum of matching parent-packet products.
-/
lemma
    fin_formula_products
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedFinFormula
      raw index normalizer left right hleft hright).eval e =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          if
            MPFam.correctionIndex
                hleftWeight hrightWeight branch.obstruction branch.support =
              index then
            (raw.multiplicityProfileFamily
                branch.leftIndex).packet.value (left.eval e) (right.eval e) *
              (raw.multiplicityProfileFamily
                branch.rightIndex).packet.value (left.eval e) (right.eval e)
          else
            0).sum := by
  rw [
    evalRecurrenceFormula,
    finRecurrenceArbitrary]

/--
The visible recurrence formula is additively decomposed at arbitrary parent
formula values.
-/
lemma
    eval_guarded_nested
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (idxDecomposedFormula
      raw index normalizer left right hleft hright).eval e =
      (guardedIdxFormula
        raw index normalizer left right hleft hright).eval e +
        (guardedFinFormula
          raw index normalizer left right hleft hright).eval e +
          (guardedNestedRecurrence
            raw index normalizer left right hleft hright).eval e := by
  rw [
    finDecomposedFormula,
    idxDecomposedRecurrence,
    FPkt.value_add,
    FPkt.value_add,
    recurrenceSumFormula,
    evalRecurrenceFormula,
    finRecurrenceFormula]

/--
The visible recurrence formula exposes its repeated-root contribution as the
finite sum of matching symbolic parent-packet products.
-/
lemma
    products_add_nested
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (idxDecomposedFormula
      raw index normalizer left right hleft hright).eval e =
      (guardedIdxFormula
        raw index normalizer left right hleft hright).eval e +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if
              MPFam.correctionIndex
                  hleftWeight hrightWeight branch.obstruction branch.support =
                index then
              (raw.multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                (raw.multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          (guardedNestedRecurrence
            raw index normalizer left right hleft hright).eval e := by
  rw [
    eval_guarded_nested,
    fin_formula_products]

end
  RPSym

end TCTex
end Submission

/-!
# Unrestricted semantic equivalence of recurrence packet decompositions

The recursively compiled orbit packet is root-first, while the scheduler
recurrence presentation is left-nested, root, then right-nested.  Their packet
evaluations agree at arbitrary integral source values by commutativity and
associativity of addition.  This removes the natural-specialization boundary
from the comparison between the monolithic and visible recurrence formulas.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  RIRecurs
open
  MPAlg
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  IMRec
open
  DFSubsti
open
  RPSym
open
  PFSubstib

namespace
  PDSem

/-- Arbitrary-value packet evaluation respects profiled trace concatenation. -/
lemma profiles_append_arbitrary
    {n leftWeight rightWeight : ℕ}
    (left right : PIFam n leftWeight rightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    ((left.append right).kernel.profiles index).value leftValue rightValue =
      (left.kernel.profiles index).value leftValue rightValue +
        (right.kernel.profiles index).value leftValue rightValue := by
  rw [
    PIFam.append,
    IMProfa.append,
    FPkt.value_add]

/-- The zero profiled trace family has zero arbitrary-value packet evaluation. -/
lemma value_profiles_arbitrary
    {n leftWeight rightWeight : ℕ}
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    ((PIFam.zero :
      PIFam n leftWeight rightWeight).kernel.profiles
        index).value leftValue rightValue =
      0 := by
  rw [
    PIFam.zero,
    IMProfa.zero,
    FPkt.value_zero]

/-- Arbitrary-value packet evaluation commutes with a dependent family guard. -/
lemma profiles_dite_arbitrary
    {n leftWeight rightWeight : ℕ}
    (condition : Prop)
    [Decidable condition]
    (positive : condition → PIFam n leftWeight rightWeight)
    (negative : PIFam n leftWeight rightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    (((if h : condition then positive h else negative).kernel.profiles
      index).value leftValue rightValue) =
      if h : condition then
        ((positive h).kernel.profiles index).value leftValue rightValue
      else
        (negative.kernel.profiles index).value leftValue rightValue := by
  cases ‹Decidable condition› <;> rfl

/--
The root-first recursively compiled branch packet and its visible
left-root-right scheduler packet agree at arbitrary integral source values.
-/
lemma
    decomposed_recurrence_arbitrary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    (IOBranch.schedulerIdxProfile
      raw branch index).value leftValue rightValue =
      (IOBranch.schedulerDecomposedRecurrence
        raw branch index).value leftValue rightValue := by
  rw [
    IOBranch.schedulerIdxProfile,
    POBranch.profiledIndexFamily,
    profiledOrbitExpansion,
    profiles_append_arbitrary,
    profiles_append_arbitrary,
    IOBranch.schedulerDecomposedRecurrence,
    FPkt.value_add,
    FPkt.value_add]
  unfold
    IOBranch.schedulerNestedProfile
  unfold
    IOBranch.schedulerIdxRecurrence
  unfold
    IOBranch.schedulerNestedRecurrence
  dsimp only [
    IOBranch.profiledObstructionBranch]
  rw [
    profiles_dite_arbitrary,
    profiles_dite_arbitrary]
  by_cases hleft :
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n
  <;> by_cases hright :
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n
  <;> simp_all only [dif_pos, value_profiles_arbitrary,
    FPkt.value_zero, dif_neg (fun h : False => h)]
  <;> ring

/--
After summing the guarded root grid, the monolithic recurrence packet and
visible left-root-right packet remain equal at arbitrary integral values.
-/
lemma
    fin_recurrence_arbitrary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    (schedulerRecurrenceProfile
      raw index).value leftValue rightValue =
      (idxDecomposedRecurrence
        raw index).value leftValue rightValue := by
  unfold
    schedulerRecurrenceProfile
  unfold
    idxDecomposedRecurrence
  unfold
    guardedIdxRecurrence
  unfold
    finRecurrenceProfile
  unfold
    idxRecurrenceProfile
  rw [
    FPkt.value_sum,
    FPkt.value_add,
    FPkt.value_add,
    FPkt.value_sum,
    FPkt.value_sum,
    FPkt.value_sum]
  induction
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight) with
  | nil =>
      rfl
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [
        decomposed_recurrence_arbitrary,
        ih,
        IOBranch.schedulerDecomposedRecurrence,
        FPkt.value_add,
        FPkt.value_add]
      ring

/--
The monolithic and visible weighted recurrence formulas agree after arbitrary
parent-formula substitution, without a natural-value hypothesis.
-/
lemma
    guarded_recurrence_arbitrary
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft :
      0 <
        (retainedOrbitKey index).erasedShape.pairLeftDegree)
    (hright :
      0 <
        (retainedOrbitKey index).erasedShape.pairRightDegree)
    (e : ι → HEFam H) :
    (schedulerRecurrenceFormula
      raw index normalizer left right hleft hright).eval e =
      (idxDecomposedFormula
        raw index normalizer left right hleft hright).eval e := by
  rw [
    sourceRecurrenceFormula,
    finDecomposedFormula,
    fin_recurrence_arbitrary]

end
  PDSem

end TCTex
end Submission

/-!
# Erased-shape aggregation of symbolic repeated correction-root packets

The repeated correction-root contribution is indexed first by retained
polynomial-orbit keys.  Claim 5 ultimately asks for Hall-word coordinates.
This file sums the symbolic root-product packets over all finite orbit indices
with one erased Hall shape and compiles the aggregate packet to a weighted
integer-valued formula.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  IMRec
open
  DFSubsti
open
  RPSym

namespace
  PEShape

/--
Transport one global repeated-root packet to a requested erased Hall shape,
using zero for orbit indices with another shape.
-/
noncomputable def
    guardedIdxShape
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  if hshape : (retainedOrbitKey index).erasedShape = word then
    hshape ▸
      finRecurrenceProfile
        raw index
  else
    FPkt.zero word.pairLeftDegree word.pairRightDegree

/-- Arbitrary-value evaluation of one shape-filtered repeated-root packet. -/
@[simp]
lemma
    valueGuardedShape
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    (guardedIdxShape
      raw word index).value leftValue rightValue =
      if (retainedOrbitKey index).erasedShape = word then
        (finRecurrenceProfile
          raw index).value leftValue rightValue
      else
        0 := by
  classical
  by_cases hshape :
      (retainedOrbitKey index).erasedShape = word
  · subst word
    simp [
      guardedIdxShape]
  · simp [
      guardedIdxShape,
      hshape]

/-- Sum repeated-root packets over all retained orbit indices with one Hall shape. -/
noncomputable def
    guardedIdxProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  FPkt.finsetSum Finset.univ fun index =>
    guardedIdxShape
      raw word index

/--
The Hall-word repeated-root packet evaluates to the finite sum of matching
finite-index repeated-root packets.
-/
lemma
    valueRecurrenceArbitrary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (guardedIdxProfile
      raw word).value leftValue rightValue =
      ∑ index : RetainedOrbitIndex n leftWeight rightWeight,
        if (retainedOrbitKey index).erasedShape = word then
          (finRecurrenceProfile
            raw index).value leftValue rightValue
        else
          0 := by
  rw [
    guardedIdxProfile,
    FPkt.value_finsetSum]
  simp_rw [
    valueGuardedShape]

/--
Expanding the per-index root packets exposes the Hall-word contribution as a
finite sum of matching symbolic parent-packet products.
-/
lemma
    value_arbitrary_products
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (guardedIdxProfile
      raw word).value leftValue rightValue =
      ∑ index : RetainedOrbitIndex n leftWeight rightWeight,
        if (retainedOrbitKey index).erasedShape = word then
          ((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              if
                MPFam.correctionIndex
                    hleftWeight hrightWeight branch.obstruction branch.support =
                  index then
                (raw.multiplicityProfileFamily
                    branch.leftIndex).packet.value leftValue rightValue *
                  (raw.multiplicityProfileFamily
                    branch.rightIndex).packet.value leftValue rightValue
              else
                0).sum
        else
          0 := by
  rw [
    valueRecurrenceArbitrary]
  apply Finset.sum_congr rfl
  intro index _hindex
  by_cases hshape : (retainedOrbitKey index).erasedShape = word
  · rw [
      if_pos hshape,
      if_pos hshape,
      finRecurrenceArbitrary]
  · rw [if_neg hshape, if_neg hshape]

/-- Weighted Hall-binomial formula for one Hall-word repeated-root contribution. -/
noncomputable def
    erasedRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  (guardedIdxProfile
    raw word).toFormula normalizer left right hleft hright

/--
After arbitrary parent-formula substitution, the Hall-word repeated-root
formula remains the finite sum of matching symbolic parent-packet products.
-/
lemma
    erased_formula_products
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (erasedRecurrenceFormula
      raw word normalizer left right hleft hright).eval e =
      ∑ index : RetainedOrbitIndex n leftWeight rightWeight,
        if (retainedOrbitKey index).erasedShape = word then
          ((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              if
                MPFam.correctionIndex
                    hleftWeight hrightWeight branch.obstruction branch.support =
                  index then
                (raw.multiplicityProfileFamily
                    branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                  (raw.multiplicityProfileFamily
                    branch.rightIndex).packet.value (left.eval e) (right.eval e)
              else
                0).sum
        else
          0 := by
  rw [
    erasedRecurrenceFormula,
    HFPkt.eval_toFormula,
    value_arbitrary_products]

end
  PEShape

end TCTex
end Submission

/-!
# Branch-level collapse of erased-shape repeated-root formulas

Every guarded obstruction branch emits its repeated correction root at one
finite orbit index.  Summing over orbit indices with a prescribed erased Hall
shape therefore collapses to a sum over exactly those guarded branches whose
correction word has that shape.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RRPkt
open
  RRPkt.POObstru
open
  CFSubsti
open
  RITrace
open
  RIRecurs
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  PEShape

namespace
  ESCollap

/--
Summing a scalar supported only at one correction index and filtered by erased
shape returns that scalar exactly when the correction shape matches.
-/
lemma
    finset_matching_if
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hsupport : IsSupported (n := n) hleftWeight hrightWeight O)
    (word : CWord HPAtom)
    (value : ℤ) :
    (∑ index : RetainedOrbitIndex n leftWeight rightWeight,
      if (retainedOrbitKey index).erasedShape = word then
        if
          MPFam.correctionIndex
              hleftWeight hrightWeight O hsupport =
            index then
          value
        else
          0
      else
        0) =
      if O.correction.erasedShape = word then value else 0 := by
  classical
  let selected :=
    MPFam.correctionIndex
      hleftWeight hrightWeight O hsupport
  by_cases hshape : O.correction.erasedShape = word
  · rw [if_pos hshape]
    rw [Fintype.sum_eq_single selected]
    · simp [selected,
        MPFam.retained_key_index,
        hshape]
    · intro index hne
      simp [selected, Ne.symm hne]
  · rw [if_neg hshape]
    apply Finset.sum_eq_zero
    intro index _hindex
    by_cases hindex : selected = index
    · subst index
      simp [selected,
        MPFam.retained_key_index,
        hshape]
    · simp [selected, hindex]

/--
Interchanging the finite orbit-index sum with a guarded branch list collapses
each branch to its correction-shape test.
-/
lemma
    finset_matching_shape
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branches :
      List (IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight))
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (∑ index : RetainedOrbitIndex n leftWeight rightWeight,
      if (retainedOrbitKey index).erasedShape = word then
        (branches.map fun branch =>
          if
            MPFam.correctionIndex
                hleftWeight hrightWeight branch.obstruction branch.support =
              index then
            (raw.multiplicityProfileFamily
                branch.leftIndex).packet.value leftValue rightValue *
              (raw.multiplicityProfileFamily
                branch.rightIndex).packet.value leftValue rightValue
          else
            0).sum
      else
        0) =
      (branches.map fun branch =>
        if branch.obstruction.correction.erasedShape = word then
          (raw.multiplicityProfileFamily
              branch.leftIndex).packet.value leftValue rightValue *
            (raw.multiplicityProfileFamily
              branch.rightIndex).packet.value leftValue rightValue
        else
          0).sum := by
  induction branches with
  | nil =>
      simp
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [show
        (∑ index : RetainedOrbitIndex n leftWeight rightWeight,
          if (retainedOrbitKey index).erasedShape = word then
            (if
              MPFam.correctionIndex
                  hleftWeight hrightWeight branch.obstruction branch.support =
                index then
              (raw.multiplicityProfileFamily
                  branch.leftIndex).packet.value leftValue rightValue *
                (raw.multiplicityProfileFamily
                  branch.rightIndex).packet.value leftValue rightValue
            else
              0) +
              (branches.map fun next =>
                if
                  MPFam.correctionIndex
                      hleftWeight hrightWeight next.obstruction next.support =
                    index then
                  (raw.multiplicityProfileFamily
                      next.leftIndex).packet.value leftValue rightValue *
                    (raw.multiplicityProfileFamily
                      next.rightIndex).packet.value leftValue rightValue
                else
                  0).sum
          else
            0) =
          (∑ index : RetainedOrbitIndex n leftWeight rightWeight,
            if (retainedOrbitKey index).erasedShape = word then
              if
                MPFam.correctionIndex
                    hleftWeight hrightWeight branch.obstruction branch.support =
                  index then
                (raw.multiplicityProfileFamily
                    branch.leftIndex).packet.value leftValue rightValue *
                  (raw.multiplicityProfileFamily
                    branch.rightIndex).packet.value leftValue rightValue
              else
                0
            else
              0) +
            (∑ index : RetainedOrbitIndex n leftWeight rightWeight,
              if (retainedOrbitKey index).erasedShape = word then
                (branches.map fun next =>
                  if
                    MPFam.correctionIndex
                        hleftWeight hrightWeight next.obstruction next.support =
                      index then
                    (raw.multiplicityProfileFamily
                        next.leftIndex).packet.value leftValue rightValue *
                      (raw.multiplicityProfileFamily
                        next.rightIndex).packet.value leftValue rightValue
                  else
                    0).sum
              else
                0) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro index _hindex
        by_cases hshape :
            (retainedOrbitKey index).erasedShape = word
        · simp [hshape]
        · simp [hshape]]
      rw [
        finset_matching_if,
        ih]

/--
The Hall-word repeated-root packet is the sum of parent-packet products over
exactly the guarded branches with that correction Hall word.
-/
lemma
    matching_branch_products
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (guardedIdxProfile
      raw word).value leftValue rightValue =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          if branch.obstruction.correction.erasedShape = word then
            (raw.multiplicityProfileFamily
                branch.leftIndex).packet.value leftValue rightValue *
              (raw.multiplicityProfileFamily
                branch.rightIndex).packet.value leftValue rightValue
          else
            0).sum := by
  rw [
    value_arbitrary_products,
    finset_matching_shape]

/--
After arbitrary formula substitution, the Hall-word repeated-root formula is
the sum of matching guarded-branch parent-packet products.
-/
lemma
    guarded_matching_products
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (erasedRecurrenceFormula
      raw word normalizer left right hleft hright).eval e =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          if branch.obstruction.correction.erasedShape = word then
            (raw.multiplicityProfileFamily
                branch.leftIndex).packet.value (left.eval e) (right.eval e) *
              (raw.multiplicityProfileFamily
                branch.rightIndex).packet.value (left.eval e) (right.eval e)
          else
            0).sum := by
  rw [
    erasedRecurrenceFormula,
    HFPkt.eval_toFormula,
    matching_branch_products]

end
  ESCollap

end TCTex
end Submission

/-!
# Hall-word aggregation of the decomposed recurrence packet

Finite orbit indices retain enough information for symbolic recollection, but
Claim 5 is expressed in Hall-word coordinates.  This file gives a generic
erased-shape aggregator for arbitrary finite-index packet families and applies
it to the visible left-root-right scheduler recurrence.

The resulting Hall-word packet is evaluation-equivalent to the existing
monolithic scheduler shape packet at arbitrary integral source values.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  ESIdx
open
  IMRec
open
  PDSem
open
  FEProgra
open
  PEShape
open
  SEAlg

namespace
  DEShape

/--
Transport one packet from an arbitrary finite-index packet family to a
requested erased Hall shape, using zero at indices with another shape.
-/
noncomputable def profileErasedShape
    {n leftWeight rightWeight : ℕ}
    (profiles :
      ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
        HFPkt
          (retainedOrbitKey index).erasedShape.pairLeftDegree
          (retainedOrbitKey index).erasedShape.pairRightDegree)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  if hshape : (retainedOrbitKey index).erasedShape = word then
    hshape ▸ profiles index
  else
    FPkt.zero word.pairLeftDegree word.pairRightDegree

/-- Arbitrary-value evaluation of a shape-filtered finite-index packet. -/
@[simp]
lemma value_erased_shape
    {n leftWeight rightWeight : ℕ}
    (profiles :
      ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
        HFPkt
          (retainedOrbitKey index).erasedShape.pairLeftDegree
          (retainedOrbitKey index).erasedShape.pairRightDegree)
    (word : CWord HPAtom)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (leftValue rightValue : ℤ) :
    (profileErasedShape
      profiles word index).value leftValue rightValue =
      if (retainedOrbitKey index).erasedShape = word then
        (profiles index).value leftValue rightValue
      else
        0 := by
  classical
  by_cases hshape :
      (retainedOrbitKey index).erasedShape = word
  · subst word
    simp [profileErasedShape]
  · simp [profileErasedShape, hshape]

/-- Sum an arbitrary finite-index packet family over one erased Hall shape. -/
noncomputable def familyErasedProfile
    {n leftWeight rightWeight : ℕ}
    (profiles :
      ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
        HFPkt
          (retainedOrbitKey index).erasedShape.pairLeftDegree
          (retainedOrbitKey index).erasedShape.pairRightDegree)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  FPkt.finsetSum Finset.univ
    (profileErasedShape profiles word)

/-- Arbitrary-value evaluation of erased-shape aggregation. -/
lemma value_erased_profile
    {n leftWeight rightWeight : ℕ}
    (profiles :
      ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
        HFPkt
          (retainedOrbitKey index).erasedShape.pairLeftDegree
          (retainedOrbitKey index).erasedShape.pairRightDegree)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (familyErasedProfile
      profiles word).value leftValue rightValue =
      ∑ index : RetainedOrbitIndex n leftWeight rightWeight,
        if (retainedOrbitKey index).erasedShape = word then
          (profiles index).value leftValue rightValue
        else
          0 := by
  rw [
    familyErasedProfile,
    FPkt.value_finsetSum]
  simp_rw [value_erased_shape]

/-- Pointwise arbitrary-value equivalence survives erased-shape aggregation. -/
lemma value_erased_congr
    {n leftWeight rightWeight : ℕ}
    (leftProfiles rightProfiles :
      ∀ index : RetainedOrbitIndex n leftWeight rightWeight,
        HFPkt
          (retainedOrbitKey index).erasedShape.pairLeftDegree
          (retainedOrbitKey index).erasedShape.pairRightDegree)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ)
    (hprofiles :
      ∀ index,
        (leftProfiles index).value leftValue rightValue =
          (rightProfiles index).value leftValue rightValue) :
    (familyErasedProfile
      leftProfiles word).value leftValue rightValue =
      (familyErasedProfile
        rightProfiles word).value leftValue rightValue := by
  rw [
    value_erased_profile,
    value_erased_profile]
  apply Finset.sum_congr rfl
  intro index _hindex
  by_cases hshape : (retainedOrbitKey index).erasedShape = word
  · rw [if_pos hshape, if_pos hshape, hprofiles index]
  · rw [if_neg hshape, if_neg hshape]

/-- Hall-word packet for the global left nested recurrence contribution. -/
noncomputable def
    nestedRecurrenceProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  familyErasedProfile
    (guardedIdxRecurrence
      raw) word

/-- Hall-word packet for the global right nested recurrence contribution. -/
noncomputable def
    guardedRecurrenceProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  familyErasedProfile
    (idxRecurrenceProfile
      raw) word

/-- Hall-word packet for the complete visible left-root-right recurrence. -/
noncomputable def
    decomposedRecurrenceProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  familyErasedProfile
    (idxDecomposedRecurrence
      raw) word

/--
The complete Hall-word decomposed recurrence packet evaluates as its left
nested, repeated-root, and right nested Hall-word contributions.
-/
lemma
    value_guarded_nested
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (decomposedRecurrenceProfile
      raw word).value leftValue rightValue =
      (nestedRecurrenceProfile
        raw word).value leftValue rightValue +
        (guardedIdxProfile
          raw word).value leftValue rightValue +
          (guardedRecurrenceProfile
            raw word).value leftValue rightValue := by
  unfold
    decomposedRecurrenceProfile
  unfold
    nestedRecurrenceProfile
  unfold
    guardedRecurrenceProfile
  rw [
    value_erased_profile,
    value_erased_profile,
    valueRecurrenceArbitrary,
    value_erased_profile,
    ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _hindex
  by_cases hshape : (retainedOrbitKey index).erasedShape = word
  · simp [
      hshape,
      idxDecomposedRecurrence,
      FPkt.value_add]
  · simp [hshape]

/--
The monolithic and visible decomposed Hall-word packets agree at arbitrary
integral source values.
-/
lemma
    value_recurrence_arbitrary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (familyErasedProfile
      (schedulerRecurrenceProfile
        raw) word).value leftValue rightValue =
      (decomposedRecurrenceProfile
        raw word).value leftValue rightValue := by
  apply value_erased_congr
  intro index
  exact
    fin_recurrence_arbitrary
      raw index leftValue rightValue

/--
The existing erased-shape scheduler-program packet is definitionally the
Hall-word aggregate of its monolithic finite-index recurrence packets.
-/
lemma
    profiles_guarded_profile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    (guardedProgramMult
      raw).profiles word =
      familyErasedProfile
        (schedulerRecurrenceProfile
          raw) word := by
  rfl

/--
Consequently the existing scheduler-program Hall-word packet evaluates as the
visible decomposed Hall-word recurrence packet at arbitrary integral values.
-/
lemma
    profiles_recurrence_arbitrary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    ((guardedProgramMult
      raw).profiles word).value leftValue rightValue =
      (decomposedRecurrenceProfile
        raw word).value leftValue rightValue := by
  rw [
    profiles_guarded_profile,
    value_recurrence_arbitrary]

end
  DEShape

end TCTex
end Submission

/-!
# Weighted Hall-word formulas for the decomposed scheduler recurrence

The guarded scheduler shape profile is evaluation-equivalent to a visible
left-root-right recurrence packet.  This file compiles that Hall-word packet
to an integer-valued Hall-binomial formula and exposes the repeated-root
contribution as a sum over matching guarded obstruction branches.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  DEShape
open
  PFSubstib
open
  ESCollap

namespace
  SFSubsti

/-- Weighted Hall-binomial formula for one Hall-word left nested contribution. -/
noncomputable def
    guardedNestedFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  (nestedRecurrenceProfile
    raw word).toFormula normalizer left right hleft hright

/-- Evaluation of the weighted Hall-word left nested formula. -/
@[simp]
lemma
    guardedRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedNestedFormula
      raw word normalizer left right hleft hright).eval e =
      (nestedRecurrenceProfile
        raw word).value (left.eval e) (right.eval e) := by
  rw [
    guardedNestedFormula,
    HFPkt.eval_toFormula]

/-- Weighted Hall-binomial formula for one Hall-word right nested contribution. -/
noncomputable def
    idxRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  (guardedRecurrenceProfile
    raw word).toFormula normalizer left right hleft hright

/-- Evaluation of the weighted Hall-word right nested formula. -/
@[simp]
lemma
    nestedRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (idxRecurrenceFormula
      raw word normalizer left right hleft hright).eval e =
      (guardedRecurrenceProfile
        raw word).value (left.eval e) (right.eval e) := by
  rw [
    idxRecurrenceFormula,
    HFPkt.eval_toFormula]

/-- Weighted Hall-binomial formula for one complete Hall-word recurrence. -/
noncomputable def
    guardedDecomposedRecurrence
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  (decomposedRecurrenceProfile
    raw word).toFormula normalizer left right hleft hright

/-- Evaluation of the weighted complete Hall-word recurrence formula. -/
@[simp]
lemma
    decomposedRecurrenceFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedDecomposedRecurrence
      raw word normalizer left right hleft hright).eval e =
      (decomposedRecurrenceProfile
        raw word).value (left.eval e) (right.eval e) := by
  rw [
    guardedDecomposedRecurrence,
    HFPkt.eval_toFormula]

/--
The complete Hall-word formula is its two nested contributions plus the sum
of parent-packet products over matching guarded repeated-root branches.
-/
lemma
    guarded_products_nested
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedDecomposedRecurrence
      raw word normalizer left right hleft hright).eval e =
      (guardedNestedFormula
        raw word normalizer left right hleft hright).eval e +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word then
              (raw.multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                (raw.multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          (idxRecurrenceFormula
            raw word normalizer left right hleft hright).eval e := by
  rw [
    decomposedRecurrenceFormula,
    value_guarded_nested,
    matching_branch_products,
    guardedRecurrenceFormula,
    nestedRecurrenceFormula]

/--
The pre-existing scheduler shape formula and the visible decomposed Hall-word
formula agree under arbitrary parent-formula substitutions.
-/
lemma
    recurrence_formula_arbitrary
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedMultFormula
      raw word normalizer left right hleft hright).eval e =
      (guardedDecomposedRecurrence
        raw word normalizer left right hleft hright).eval e := by
  rw [
    guardedMultFormula,
    HFPkt.eval_toFormula,
    decomposedRecurrenceFormula]
  exact
    profiles_recurrence_arbitrary
      raw word (left.eval e) (right.eval e)

/--
The existing scheduler shape formula therefore has a direct visible
left-root-right expansion at arbitrary parent-formula substitutions.
-/
lemma
    program_products_nested
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedMultFormula
      raw word normalizer left right hleft hright).eval e =
      (guardedNestedFormula
        raw word normalizer left right hleft hright).eval e +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word then
              (raw.multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                (raw.multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          (idxRecurrenceFormula
            raw word normalizer left right hleft hright).eval e := by
  rw [
    recurrence_formula_arbitrary,
    guarded_products_nested]

end
  SFSubsti

end TCTex
end Submission

/-!
# Branchwise Hall-word aggregation of recursive nested recurrence packets

The visible Hall-word recurrence separates into left nested, repeated-root,
and right nested contributions.  The repeated-root coordinate is already an
explicit sum of parent-packet products.  This file distributes Hall-word
aggregation over the guarded branch list for the two nested contributions,
making their recursive branch structure visible as well.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  IMRec
open
  DEShape
open
  ESCollap

namespace
  SNBranch

/--
Filtering a finite-index sum after summing branch values is the same as
summing the filtered finite-index contribution of each branch.
-/
lemma finset_if_list
    {ι α : Type}
    [Fintype ι]
    (branches : List α)
    (condition : ι → Prop)
    [DecidablePred condition]
    (value : α → ι → ℤ) :
    (∑ index : ι,
      if condition index then
        (branches.map fun branch => value branch index).sum
      else
        0) =
      (branches.map fun branch =>
        ∑ index : ι, if condition index then value branch index else 0).sum := by
  classical
  induction branches with
  | nil =>
      simp
  | cons branch branches ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [show
        (∑ index : ι,
          if condition index then
            value branch index +
              (branches.map fun next => value next index).sum
          else
            0) =
          (∑ index : ι,
            if condition index then value branch index else 0) +
            ∑ index : ι,
              if condition index then
                (branches.map fun next => value next index).sum
              else
                0 by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro index _hindex
        by_cases hcondition : condition index
        · simp [hcondition]
        · simp [hcondition]]
      rw [ih]

/-- Hall-word packet for one guarded branch's surviving left nested recollection. -/
noncomputable def
    idxRecurrenceBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  familyErasedProfile
    (IOBranch.schedulerNestedProfile
      raw branch) word

/-- Evaluation of one guarded branch's Hall-word left nested packet. -/
lemma
    nestedRecurrenceBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (idxRecurrenceBranch
      raw branch word).value leftValue rightValue =
      ∑ index : RetainedOrbitIndex n leftWeight rightWeight,
        if (retainedOrbitKey index).erasedShape = word then
          (IOBranch.schedulerNestedProfile
            raw branch index).value leftValue rightValue
        else
          0 := by
  rw [
    idxRecurrenceBranch,
    value_erased_profile]

/-- Hall-word packet for one guarded branch's surviving right nested recollection. -/
noncomputable def
    guardedRecurrenceBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  familyErasedProfile
    (IOBranch.schedulerNestedRecurrence
      raw branch) word

/-- Evaluation of one guarded branch's Hall-word right nested packet. -/
lemma
    recurrenceBranchProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (guardedRecurrenceBranch
      raw branch word).value leftValue rightValue =
      ∑ index : RetainedOrbitIndex n leftWeight rightWeight,
        if (retainedOrbitKey index).erasedShape = word then
          (IOBranch.schedulerNestedRecurrence
            raw branch index).value leftValue rightValue
        else
          0 := by
  rw [
    guardedRecurrenceBranch,
    value_erased_profile]

/--
The global Hall-word left nested contribution is the sum of the branchwise
Hall-word recursive left nested packets.
-/
lemma
    sum_branch_profiles
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (nestedRecurrenceProfile
      raw word).value leftValue rightValue =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (idxRecurrenceBranch
            raw branch word).value leftValue rightValue).sum := by
  rw [
    nestedRecurrenceProfile,
    value_erased_profile]
  unfold
    guardedIdxRecurrence
  simp_rw [FPkt.value_sum]
  simp_rw [List.map_map]
  rw [finset_if_list]
  simp_rw [
    nestedRecurrenceBranch]
  simp [Function.comp_apply]

/--
The global Hall-word right nested contribution is the sum of the branchwise
Hall-word recursive right nested packets.
-/
lemma
    value_branch_profiles
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (guardedRecurrenceProfile
      raw word).value leftValue rightValue =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (guardedRecurrenceBranch
            raw branch word).value leftValue rightValue).sum := by
  rw [
    guardedRecurrenceProfile,
    value_erased_profile]
  unfold
    idxRecurrenceProfile
  simp_rw [FPkt.value_sum]
  simp_rw [List.map_map]
  rw [finset_if_list]
  simp_rw [
    recurrenceBranchProfile]
  simp [Function.comp_apply]

/--
The full Hall-word recurrence is a sum of recursive left branch packets,
matching repeated-root parent products, and recursive right branch packets.
-/
lemma
    guarded_branch_profiles
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    (decomposedRecurrenceProfile
      raw word).value leftValue rightValue =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (idxRecurrenceBranch
            raw branch word).value leftValue rightValue).sum +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word then
              (raw.multiplicityProfileFamily
                  branch.leftIndex).packet.value leftValue rightValue *
                (raw.multiplicityProfileFamily
                  branch.rightIndex).packet.value leftValue rightValue
            else
              0).sum +
          ((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              (guardedRecurrenceBranch
                raw branch word).value leftValue rightValue).sum := by
  rw [
    value_guarded_nested,
    sum_branch_profiles,
    matching_branch_products,
    value_branch_profiles]

end
  SNBranch

end TCTex
end Submission

/-!
# Endpoint Hall-word formulas for the decomposed scheduler recurrence

Transporting the guarded scheduler shape profiles to the endpoint collector
program preserves the packet vector.  Thus the endpoint-facing formula used
by the Claim 5 route inherits the visible left-root-right Hall-word expansion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  DEShape
open
  SFSubsti
open
  PFSubstib
open
  GRProgra

namespace
  EFSubsti

/--
The endpoint-facing Hall-word formula used by the Claim 5 route evaluates as
the visible decomposed scheduler formula under arbitrary substitutions.
-/
lemma
    endpoint_recurrence_arbitrary
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (endpointMultRecurrence
      decomposition word normalizer left right hleft hright).eval e =
      (guardedDecomposedRecurrence
        (multiplicityProfileShape
          decomposition.raw)
        word normalizer left right hleft hright).eval e := by
  rw [
    endpointMultRecurrence,
    HFPkt.eval_toFormula,
    decomposedRecurrenceFormula]
  exact
    profiles_recurrence_arbitrary
      (multiplicityProfileShape
        decomposition.raw)
      word (left.eval e) (right.eval e)

/--
The endpoint-facing Hall-word formula has the explicit left nested,
matching repeated-root branch product, and right nested expansion.
-/
lemma
    endpoint_products_nested
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (endpointMultRecurrence
      decomposition word normalizer left right hleft hright).eval e =
      (guardedNestedFormula
        (multiplicityProfileShape
          decomposition.raw)
        word normalizer left right hleft hright).eval e +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word then
              ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          (idxRecurrenceFormula
            (multiplicityProfileShape
              decomposition.raw)
            word normalizer left right hleft hright).eval e := by
  rw [
    endpoint_recurrence_arbitrary,
    guarded_products_nested]

end
  EFSubsti

end TCTex
end Submission

/-!
# Strict descent for surviving branchwise Hall-word recurrence packets

The operational collector retains a nested left or right branch only while
its weighted degree remains below the cutoff.  Every retained child has
strictly larger weighted Hall degree than its parent, hence strictly smaller
cutoff defect.  This file exposes those termination facts at the branchwise
Hall-word packet interface.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


open
  RRPkt
open
  RRPkt.POObstru
open
  CFAlg
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  IMRec
open
  DEShape
open
  SNBranch

namespace
  NBDescen

/-- A left nested Hall-word branch packet vanishes outside the cutoff. -/
lemma
    value_not_cutoff
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ)
    (hcutoff :
      ¬branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n) :
    (idxRecurrenceBranch
      raw branch word).value leftValue rightValue =
      0 := by
  rw [
    nestedRecurrenceBranch]
  apply Finset.sum_eq_zero
  intro index _hindex
  by_cases hshape :
      (retainedOrbitKey index).erasedShape = word
  · rw [if_pos hshape]
    simp only [
      IOBranch.schedulerNestedProfile,
      dif_neg hcutoff, FPkt.value_zero]
  · rw [if_neg hshape]

/-- A right nested Hall-word branch packet vanishes outside the cutoff. -/
lemma
    value_guarded_cutoff
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ)
    (hcutoff :
      ¬branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n) :
    (guardedRecurrenceBranch
      raw branch word).value leftValue rightValue =
      0 := by
  rw [
    recurrenceBranchProfile]
  apply Finset.sum_eq_zero
  intro index _hindex
  by_cases hshape :
      (retainedOrbitKey index).erasedShape = word
  · rw [if_pos hshape]
    simp only [
      IOBranch.schedulerNestedRecurrence,
      dif_neg hcutoff, FPkt.value_zero]
  · rw [if_neg hshape]

/--
A nonzero left nested Hall-word branch packet comes from a surviving child:
its weight grows strictly, remains below the cutoff, and its cutoff defect
strictly descends.
-/
lemma
    guarded_ne_zero
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ)
    (hnonzero :
      (idxRecurrenceBranch
        raw branch word).value leftValue rightValue ≠ 0) :
    branch.obstruction.weight leftWeight rightWeight <
        branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight ∧
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n ∧
      Descends n leftWeight rightWeight
        branch.obstruction.operationalNestedLeft branch.obstruction := by
  have hcutoff :
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n := by
    by_contra hcutoff
    exact
      hnonzero
        (value_not_cutoff
          raw branch word leftValue rightValue hcutoff)
  exact
    ⟨branch.obstruction.weight_operational_left
        hleftWeight hrightWeight,
      hcutoff,
      branch.obstruction.nestedLeftDescends
        hleftWeight hrightWeight hcutoff⟩

/--
A nonzero right nested Hall-word branch packet comes from a surviving child:
its weight grows strictly, remains below the cutoff, and its cutoff defect
strictly descends.
-/
lemma
    guarded_idx_value
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ)
    (hnonzero :
      (guardedRecurrenceBranch
        raw branch word).value leftValue rightValue ≠ 0) :
    branch.obstruction.weight leftWeight rightWeight <
        branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight ∧
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n ∧
      Descends n leftWeight rightWeight
        branch.obstruction.operationalNestedRight branch.obstruction := by
  have hcutoff :
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n := by
    by_contra hcutoff
    exact
      hnonzero
        (value_guarded_cutoff
          raw branch word leftValue rightValue hcutoff)
  exact
    ⟨branch.obstruction.weight_operational_nested
        hleftWeight hrightWeight,
      hcutoff,
      branch.obstruction.nestedRightDescends
        hleftWeight hrightWeight hcutoff⟩

end
  NBDescen

end TCTex
end Submission

/-!
# Vocabulary-indexed endpoint recurrence expansions through cutoff four

Retained erased-shape vocabulary membership supplies the two positive Hall
bidegrees required by formula substitution.  This file forwards the explicit
endpoint left-root-right recurrence expansion through that vocabulary
interface and its automatic cutoff-four specialization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  FIProf
open
  CFSubsti
open
  CWSkelet
open
  RITrace
open
  PGSrc
open
  ISLift
open
  EFSubsti
open
  SFSubsti
open
  IVLow
open
  GRProgra

namespace
  EVLow

/--
For a retained vocabulary word, the endpoint-facing formula has the explicit
left nested, matching repeated-root branch product, and right nested
expansion without separately supplied Hall-bidegree positivity proofs.
-/
lemma
    recurrence_products_nested
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H) :
    (endpointVocabRecurrence
      decomposition word normalizer left right).eval e =
      (guardedNestedFormula
        (multiplicityProfileShape
          decomposition.raw)
        word.1 normalizer left right
          (bidegree_positive_vocabulary word.2).1
          (bidegree_positive_vocabulary word.2).2).eval e +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word.1 then
              ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          (idxRecurrenceFormula
            (multiplicityProfileShape
              decomposition.raw)
            word.1 normalizer left right
              (bidegree_positive_vocabulary word.2).1
              (bidegree_positive_vocabulary word.2).2).eval e := by
  rw [
    endpointVocabRecurrence]
  exact
    endpoint_products_nested
      decomposition word.1 normalizer left right
        (bidegree_positive_vocabulary word.2).1
        (bidegree_positive_vocabulary word.2).2
        e

/--
Through cutoff four, every retained vocabulary formula automa has the
visible left-root-right recurrence expansion.
-/
lemma
    n_products_nested
    {d n leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H) :
    (endpointVocabularyFour
      layer hhigh raw word normalizer left right).eval e =
      (guardedNestedFormula
        (multiplicityProfileShape raw)
        word.1 normalizer left right
          (bidegree_positive_vocabulary word.2).1
          (bidegree_positive_vocabulary word.2).2).eval e +
        ((guardedSupportedBranches
          n 1 1 (by simp) (by simp)).map fun branch =>
            if branch.obstruction.correction.erasedShape = word.1 then
              ((multiplicityProfileShape
                  raw).multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                ((multiplicityProfileShape
                  raw).multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          (idxRecurrenceFormula
            (multiplicityProfileShape
              raw)
            word.1 normalizer left right
              (bidegree_positive_vocabulary word.2).1
              (bidegree_positive_vocabulary word.2).2).eval e := by
  rw [
    endpointVocabularyFour]
  exact
    recurrence_products_nested
      (recNFour
        layer hhigh raw)
      word normalizer left right e

end
  EVLow

end TCTex
end Submission

/-!
# Weighted formulas for branchwise recursive Hall-word recurrence packets

The branchwise Hall-word recurrence has recursive left and right nested
packets around an explicit repeated-root parent-product sum.  This file
compiles the nested branch packets to weighted Hall-binomial formulas and
forwards the fully recursive expansion to the endpoint-facing formula.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  EFSubsti
open
  SFSubsti
open
  SNBranch
open
  PFSubstib
open
  GRProgra

namespace
  BFSubsti

/-- Weighted formula for one guarded branch's recursive left nested Hall-word packet. -/
noncomputable def
    idxBranchFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  (idxRecurrenceBranch
    raw branch word).toFormula normalizer left right hleft hright

/-- Evaluation of one recursive left nested Hall-word branch formula. -/
@[simp]
lemma
    nestedBranchFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (idxBranchFormula
      raw branch word normalizer left right hleft hright).eval e =
      (idxRecurrenceBranch
        raw branch word).value (left.eval e) (right.eval e) := by
  rw [
    idxBranchFormula,
    HFPkt.eval_toFormula]

/-- Weighted formula for one guarded branch's recursive right nested Hall-word packet. -/
noncomputable def
    guardedBranchFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree) :
    WBForm H ι
      (word.pairLeftDegree * leftFormulaWeight +
        word.pairRightDegree * rightFormulaWeight) :=
  (guardedRecurrenceBranch
    raw branch word).toFormula normalizer left right hleft hright

/-- Evaluation of one recursive right nested Hall-word branch formula. -/
@[simp]
lemma
    recurrenceBranchFormula
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedBranchFormula
      raw branch word normalizer left right hleft hright).eval e =
      (guardedRecurrenceBranch
        raw branch word).value (left.eval e) (right.eval e) := by
  rw [
    guardedBranchFormula,
    HFPkt.eval_toFormula]

/--
The complete Hall-word formula is a sum of recursive left branch formulas,
matching repeated-root parent products, and recursive right branch formulas.
-/
lemma
    guarded_branch_formulas
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (guardedDecomposedRecurrence
      raw word normalizer left right hleft hright).eval e =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (idxBranchFormula
            raw branch word normalizer left right hleft hright).eval e).sum +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word then
              (raw.multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                (raw.multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          ((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              (guardedBranchFormula
                raw branch word normalizer left right hleft hright).eval e).sum := by
  rw [
    decomposedRecurrenceFormula,
    guarded_branch_profiles]
  simp_rw [
    nestedBranchFormula,
    recurrenceBranchFormula]

/--
The endpoint-facing Hall-word formula used by the Claim 5 route inherits the
fully recursive branchwise expansion.
-/
lemma
    endpoint_branch_formulas
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H) :
    (endpointMultRecurrence
      decomposition word normalizer left right hleft hright).eval e =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (idxBranchFormula
            (multiplicityProfileShape
              decomposition.raw)
            branch word normalizer left right hleft hright).eval e).sum +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word then
              ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          ((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              (guardedBranchFormula
                (multiplicityProfileShape
                  decomposition.raw)
                branch word normalizer left right hleft hright).eval e).sum := by
  rw [
    endpoint_recurrence_arbitrary,
    guarded_branch_formulas]

end
  BFSubsti

end TCTex
end Submission

/-!
# Strict descent for surviving recursive Hall-word branch formulas

The branchwise Hall-binomial formulas evaluate through their underlying
Hall-word packets.  Consequently, every nonzero recursive left or right
formula evaluation carries the same bounded cutoff-defect descent certificate.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RRPkt
open
  RRPkt.POObstru
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  NBDescen
open
  BFSubsti

namespace
  FSDescen

/--
A nonzero recursive left branch formula evaluation comes from a surviving
child with strict weighted-degree growth and strict cutoff-defect descent.
-/
lemma
    guarded_survival_ne
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      (idxBranchFormula
        raw branch word normalizer left right hleft hright).eval e ≠ 0) :
    branch.obstruction.weight leftWeight rightWeight <
        branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight ∧
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n ∧
      Descends n leftWeight rightWeight
        branch.obstruction.operationalNestedLeft branch.obstruction := by
  rw [
    nestedBranchFormula] at hnonzero
  exact
    guarded_ne_zero
      raw branch word (left.eval e) (right.eval e) hnonzero

/--
A nonzero recursive right branch formula evaluation comes from a surviving
child with strict weighted-degree growth and strict cutoff-defect descent.
-/
lemma
    guarded_idx_survival
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      (guardedBranchFormula
        raw branch word normalizer left right hleft hright).eval e ≠ 0) :
    branch.obstruction.weight leftWeight rightWeight <
        branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight ∧
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n ∧
      Descends n leftWeight rightWeight
        branch.obstruction.operationalNestedRight branch.obstruction := by
  rw [
    recurrenceBranchFormula] at hnonzero
  exact
    guarded_idx_value
      raw branch word (left.eval e) (right.eval e) hnonzero

end
  FSDescen

end TCTex
end Submission

/-!
# Vocabulary-indexed recursive endpoint recurrence expansions through cutoff four

Retained erased-shape vocabulary membership supplies the two positive Hall
bidegrees required by formula substitution.  This file forwards the fully
recursive branchwise endpoint expansion through that vocabulary interface and
its automatic cutoff-four specialization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  FIProf
open
  CFSubsti
open
  CWSkelet
open
  RITrace
open
  PGSrc
open
  ISLift
open
  EVLow
open
  BFSubsti
open
  IVLow
open
  GRProgra

namespace
  NVLow

/--
For a retained vocabulary word, the endpoint formula is a sum of recursive
left branch formulas, matching repeated-root parent products, and recursive
right branch formulas without separately supplied Hall-bidegree positivity
proofs.
-/
lemma
    packet_branch_formulas
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H) :
    (endpointVocabRecurrence
      decomposition word normalizer left right).eval e =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (idxBranchFormula
            (multiplicityProfileShape
              decomposition.raw)
            branch word.1 normalizer left right
              (bidegree_positive_vocabulary word.2).1
              (bidegree_positive_vocabulary word.2).2).eval e).sum +
        ((guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
            if branch.obstruction.correction.erasedShape = word.1 then
              ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                ((multiplicityProfileShape
                  decomposition.raw).multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          ((guardedSupportedBranches
            n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
              (guardedBranchFormula
                (multiplicityProfileShape
                  decomposition.raw)
                branch word.1 normalizer left right
                  (bidegree_positive_vocabulary word.2).1
                  (bidegree_positive_vocabulary word.2).2).eval e).sum :=
                    by
  rw [
    endpointVocabRecurrence]
  exact
    endpoint_branch_formulas
      decomposition word.1 normalizer left right
        (bidegree_positive_vocabulary word.2).1
        (bidegree_positive_vocabulary word.2).2
        e

/--
Through cutoff four, every retained vocabulary formula automa has the
fully recursive branchwise recurrence expansion.
-/
lemma
    four_branch_formulas
    {d n leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H) :
    (endpointVocabularyFour
      layer hhigh raw word normalizer left right).eval e =
      ((guardedSupportedBranches
        n 1 1 (by simp) (by simp)).map fun branch =>
          (idxBranchFormula
            (multiplicityProfileShape raw)
            branch word.1 normalizer left right
              (bidegree_positive_vocabulary word.2).1
              (bidegree_positive_vocabulary word.2).2).eval e).sum +
        ((guardedSupportedBranches
          n 1 1 (by simp) (by simp)).map fun branch =>
            if branch.obstruction.correction.erasedShape = word.1 then
              ((multiplicityProfileShape
                  raw).multiplicityProfileFamily
                  branch.leftIndex).packet.value (left.eval e) (right.eval e) *
                ((multiplicityProfileShape
                  raw).multiplicityProfileFamily
                  branch.rightIndex).packet.value (left.eval e) (right.eval e)
            else
              0).sum +
          ((guardedSupportedBranches
            n 1 1 (by simp) (by simp)).map fun branch =>
              (guardedBranchFormula
                (multiplicityProfileShape
                  raw)
                branch word.1 normalizer left right
                  (bidegree_positive_vocabulary word.2).1
                  (bidegree_positive_vocabulary word.2).2).eval e).sum :=
                    by
  rw [
    endpointVocabularyFour]
  exact
    packet_branch_formulas
      (recNFour
        layer hhigh raw)
      word normalizer left right e

end
  NVLow

end TCTex
end Submission

/-!
# Descent witnesses for nonzero recursive Hall-word branch sums

The visible recursive endpoint formula sums left and right nested formulas
over the finite guarded branch list.  A nonzero side sum contains a nonzero
branch formula, hence an explicit child obstruction with bounded
cutoff-defect descent.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RRPkt
open
  RRPkt.POObstru
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  BFSubsti
open
  FSDescen

namespace
  SDSum

/-- A nonzero finite integer sum contains a nonzero summand. -/
lemma ne_list_sum
    {α : Type}
    (items : List α)
    (value : α → ℤ)
    (hnonzero : (items.map value).sum ≠ 0) :
    ∃ item ∈ items, value item ≠ 0 := by
  induction items with
  | nil =>
      simp at hnonzero
  | cons item items ih =>
      by_cases hitem : value item = 0
      · simp only [List.map_cons, List.sum_cons, hitem, zero_add] at hnonzero
        rcases ih hnonzero with ⟨next, hnext, hnextValue⟩
        exact ⟨next, by simp [hnext], hnextValue⟩
      · exact ⟨item, by simp, hitem⟩

/--
A nonzero sum of recursive left branch formulas exposes a guarded child with
strict weighted-degree growth and strict cutoff-defect descent.
-/
lemma
    branch_survival_certificate
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (idxBranchFormula
            raw branch word normalizer left right hleft hright).eval e).sum ≠ 0) :
    ∃ branch ∈
        guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight,
      branch.obstruction.weight leftWeight rightWeight <
          branch.obstruction.operationalNestedLeft.weight
            leftWeight rightWeight ∧
        branch.obstruction.operationalNestedLeft.weight
            leftWeight rightWeight < n ∧
        Descends n leftWeight rightWeight
          branch.obstruction.operationalNestedLeft branch.obstruction := by
  rcases
      ne_list_sum
        (guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight)
        (fun branch =>
          (idxBranchFormula
            raw branch word normalizer left right hleft hright).eval e)
        hnonzero with
    ⟨branch, hbranch, hbranchValue⟩
  exact
    ⟨branch, hbranch,
      guarded_survival_ne
        raw branch word normalizer left right hleft hright e hbranchValue⟩

/--
A nonzero sum of recursive right branch formulas exposes a guarded child with
strict weighted-degree growth and strict cutoff-defect descent.
-/
lemma
    recurrence_branch_survival
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          (guardedBranchFormula
            raw branch word normalizer left right hleft hright).eval e).sum ≠ 0) :
    ∃ branch ∈
        guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight,
      branch.obstruction.weight leftWeight rightWeight <
          branch.obstruction.operationalNestedRight.weight
            leftWeight rightWeight ∧
        branch.obstruction.operationalNestedRight.weight
            leftWeight rightWeight < n ∧
        Descends n leftWeight rightWeight
          branch.obstruction.operationalNestedRight branch.obstruction := by
  rcases
      ne_list_sum
        (guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight)
        (fun branch =>
          (guardedBranchFormula
            raw branch word normalizer left right hleft hright).eval e)
        hnonzero with
    ⟨branch, hbranch, hbranchValue⟩
  exact
    ⟨branch, hbranch,
      guarded_idx_survival
        raw branch word normalizer left right hleft hright e hbranchValue⟩

/--
A nonzero matching repeated-root product sum exposes a guarded correction
branch with the requested erased shape and a nonzero parent-packet product.
-/
lemma
    guarded_matching_branch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ)
    (hnonzero :
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          if branch.obstruction.correction.erasedShape = word then
            (raw.multiplicityProfileFamily
                branch.leftIndex).packet.value leftValue rightValue *
              (raw.multiplicityProfileFamily
                branch.rightIndex).packet.value leftValue rightValue
          else
            0).sum ≠ 0) :
    ∃ branch ∈
        guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight,
      branch.obstruction.correction.erasedShape = word ∧
        (raw.multiplicityProfileFamily
            branch.leftIndex).packet.value leftValue rightValue *
          (raw.multiplicityProfileFamily
            branch.rightIndex).packet.value leftValue rightValue ≠ 0 := by
  rcases
      ne_list_sum
        (guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight)
        (fun branch =>
          if branch.obstruction.correction.erasedShape = word then
            (raw.multiplicityProfileFamily
                branch.leftIndex).packet.value leftValue rightValue *
              (raw.multiplicityProfileFamily
                branch.rightIndex).packet.value leftValue rightValue
          else
            0)
        hnonzero with
    ⟨branch, hbranch, hbranchValue⟩
  by_cases hshape : branch.obstruction.correction.erasedShape = word
  · exact ⟨branch, hbranch, hshape, by simpa only [if_pos hshape] using hbranchValue⟩
  · simp only [if_neg hshape, ne_eq, not_true_eq_false] at hbranchValue

end
  SDSum

end TCTex
end Submission

/-!
# Termination budget for recursive Hall-word formula support

Every surviving recursive Hall-word formula branch chooses an operational
left or right child whose weighted degree remains below the cutoff.  This file
packages those choices as guarded support steps and proves that a path of such
choices has length bounded by the initial cutoff defect.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RRPkt
open
  RRPkt.POObstru
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  BFSubsti
open
  FSDescen

namespace
  ESTermin

/--
One recursive support move chooses a nested child whose weighted degree
remains strictly below the collector cutoff.
-/
inductive GNSuppor
    (n leftWeight rightWeight : ℕ) :
    POObstru → POObstru → Prop
  | left
      (parent : POObstru)
      (hcutoff :
        parent.operationalNestedLeft.weight leftWeight rightWeight < n) :
      GNSuppor n leftWeight rightWeight
        parent.operationalNestedLeft parent
  | right
      (parent : POObstru)
      (hcutoff :
        parent.operationalNestedRight.weight leftWeight rightWeight < n) :
      GNSuppor n leftWeight rightWeight
        parent.operationalNestedRight parent

namespace GNSuppor

/-- Every guarded support child remains below the collector cutoff. -/
lemma child_weight_cutoff
    {n leftWeight rightWeight : ℕ}
    {child parent : POObstru}
    (step : GNSuppor n leftWeight rightWeight child parent) :
    child.weight leftWeight rightWeight < n := by
  cases step with
  | left parent hcutoff =>
      exact hcutoff
  | right parent hcutoff =>
      exact hcutoff

/-- Every guarded support step strictly raises weighted Hall degree. -/
lemma parent_weight_child
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {child parent : POObstru}
    (step : GNSuppor n leftWeight rightWeight child parent) :
    parent.weight leftWeight rightWeight <
      child.weight leftWeight rightWeight := by
  cases step with
  | left parent _hcutoff =>
      exact parent.weight_operational_left hleftWeight hrightWeight
  | right parent _hcutoff =>
      exact parent.weight_operational_nested hleftWeight hrightWeight

/-- Every guarded support step strictly lowers cutoff defect. -/
lemma descends
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {child parent : POObstru}
    (step : GNSuppor n leftWeight rightWeight child parent) :
    Descends n leftWeight rightWeight child parent := by
  cases step with
  | left parent hcutoff =>
      exact
        parent.nestedLeftDescends
          hleftWeight hrightWeight hcutoff
  | right parent hcutoff =>
      exact
        parent.nestedRightDescends
          hleftWeight hrightWeight hcutoff

end GNSuppor

/--
A recursive support path records the successive nested obstructions after
its starting obstruction.  Repeated-root product support is terminal and
therefore contributes no further step.
-/
inductive GNPath
    (n leftWeight rightWeight : ℕ) :
    POObstru → List POObstru → Prop
  | nil (parent : POObstru) :
      GNPath n leftWeight rightWeight parent []
  | cons
      {parent child : POObstru}
      {tail : List POObstru}
      (step : GNSuppor n leftWeight rightWeight child parent)
      (path : GNPath n leftWeight rightWeight child tail) :
      GNPath n leftWeight rightWeight parent (child :: tail)

namespace GNPath

/--
The number of recursive nested choices is bounded by the starting
obstruction's remaining cutoff defect.
-/
lemma length_le_defect
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {parent : POObstru}
    {children : List POObstru}
    (path :
      GNPath n leftWeight rightWeight parent children) :
    children.length ≤ parent.defect n leftWeight rightWeight := by
  induction path with
  | nil parent =>
      simp
  | @cons parent child tail step path ih =>
      have hdescends := step.descends hleftWeight hrightWeight
      unfold Descends at hdescends
      simp only [List.length_cons]
      omega

/--
When the starting obstruction lies within the cutoff, the recursive path
length plus its starting weighted degree fits inside the cutoff.
-/
lemma length_add_cutoff
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {parent : POObstru}
    {children : List POObstru}
    (hparentWeight :
      parent.weight leftWeight rightWeight ≤ n)
    (path :
      GNPath n leftWeight rightWeight parent children) :
    children.length + parent.weight leftWeight rightWeight ≤ n := by
  have hbound := path.length_le_defect hleftWeight hrightWeight
  unfold defect at hbound
  omega

end GNPath

/--
A nonzero recursive left branch formula supplies one guarded recursive
support step.
-/
lemma
    guarded_idx_zero
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      (idxBranchFormula
        raw branch word normalizer left right hleft hright).eval e ≠ 0) :
    GNSuppor n leftWeight rightWeight
      branch.obstruction.operationalNestedLeft branch.obstruction := by
  exact
    GNSuppor.left branch.obstruction
      (guarded_survival_ne
        raw branch word normalizer left right hleft hright e hnonzero).2.1

/--
A nonzero recursive right branch formula supplies one guarded recursive
support step.
-/
lemma
    guarded_idx_ne
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      (guardedBranchFormula
        raw branch word normalizer left right hleft hright).eval e ≠ 0) :
    GNSuppor n leftWeight rightWeight
      branch.obstruction.operationalNestedRight branch.obstruction := by
  exact
    GNSuppor.right branch.obstruction
      (guarded_idx_survival
        raw branch word normalizer left right hleft hright e hnonzero).2.1

end
  ESTermin

end TCTex
end Submission

/-!
# Endpoint support trichotomy for recursive Hall-word formulas

The endpoint Hall-word formula is the sum of recursive left branches,
matching repeated-root parent products, and recursive right branches.  This
file packages the support alternatives for those three visible summands and
shows that every nonzero endpoint evaluation lies in one of them.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RRPkt
open
  RRPkt.POObstru
open
  CRLayer
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  BFSubsti
open
  SDSum
open
  PFSubstib
open
  GRProgra

namespace
  SESuppor

/-- A recursive left formula sum has a surviving descending branch. -/
def RecurrenceSurvivalCertificate
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (_raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (_normalizer : WBForm.RCNormal H ι)
    (_left : WBForm H ι leftFormulaWeight)
    (_right : WBForm H ι rightFormulaWeight)
    (_hleft : 0 < word.pairLeftDegree)
    (_hright : 0 < word.pairRightDegree)
    (_e : ι → HEFam H) :
    Prop :=
  ∃ branch ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight,
    branch.obstruction.weight leftWeight rightWeight <
        branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight ∧
      branch.obstruction.operationalNestedLeft.weight
          leftWeight rightWeight < n ∧
      Descends n leftWeight rightWeight
        branch.obstruction.operationalNestedLeft branch.obstruction

/-- A repeated-root formula sum has a matching branch with nonzero product. -/
def GuardedMatchingBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (leftValue rightValue : ℤ) :
    Prop :=
  ∃ branch ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight,
    branch.obstruction.correction.erasedShape = word ∧
      (raw.multiplicityProfileFamily
          branch.leftIndex).packet.value leftValue rightValue *
        (raw.multiplicityProfileFamily
          branch.rightIndex).packet.value leftValue rightValue ≠ 0

/-- A recursive right formula sum has a surviving descending branch. -/
def BranchSurvivalCertificate
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (_raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (_normalizer : WBForm.RCNormal H ι)
    (_left : WBForm H ι leftFormulaWeight)
    (_right : WBForm H ι rightFormulaWeight)
    (_hleft : 0 < word.pairLeftDegree)
    (_hright : 0 < word.pairRightDegree)
    (_e : ι → HEFam H) :
    Prop :=
  ∃ branch ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight,
    branch.obstruction.weight leftWeight rightWeight <
        branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight ∧
      branch.obstruction.operationalNestedRight.weight
          leftWeight rightWeight < n ∧
      Descends n leftWeight rightWeight
        branch.obstruction.operationalNestedRight branch.obstruction

/-- If a sum of three integers is nonzero, at least one summand is nonzero. -/
lemma ne_or_add
    (left root right : ℤ)
    (hnonzero : left + root + right ≠ 0) :
    left ≠ 0 ∨ root ≠ 0 ∨ right ≠ 0 := by
  by_cases hleft : left = 0
  · by_cases hroot : root = 0
    · right
      right
      intro hright
      exact hnonzero (by simp [hleft, hroot, hright])
    · exact Or.inr (Or.inl hroot)
  · exact Or.inl hleft

/--
Every nonzero endpoint Hall-word formula evaluation has visible support:
a descending recursive left child, a matching repeated-root parent product,
or a descending recursive right child.
-/
lemma
    recurrenceImpTrichotomy
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      (endpointMultRecurrence
        decomposition word normalizer left right hleft hright).eval e ≠ 0) :
    RecurrenceSurvivalCertificate
        (multiplicityProfileShape
          decomposition.raw)
        word normalizer left right hleft hright e ∨
      GuardedMatchingBranch
          (multiplicityProfileShape
            decomposition.raw)
          word (left.eval e) (right.eval e) ∨
        BranchSurvivalCertificate
          (multiplicityProfileShape
            decomposition.raw)
          word normalizer left right hleft hright e := by
  rw [
    endpoint_branch_formulas] at hnonzero
  rcases ne_or_add _ _ _ hnonzero with
    hleftSum | hrootSum | hrightSum
  · left
    exact
      branch_survival_certificate
        (multiplicityProfileShape
          decomposition.raw)
        word normalizer left right hleft hright e hleftSum
  · right
    left
    exact
      guarded_matching_branch
        (multiplicityProfileShape
          decomposition.raw)
        word (left.eval e) (right.eval e) hrootSum
  · right
    right
    exact
      recurrence_branch_survival
        (multiplicityProfileShape
          decomposition.raw)
        word normalizer left right hleft hright e hrightSum

end
  SESuppor

end TCTex
end Submission

/-!
# Recursive-step-or-terminal support for endpoint Hall-word formulas

The endpoint support trichotomy has two recursive cases and one repeated-root
product case.  This file combines the two recursive cases into one guarded
support-step predicate, leaving the repeated-root product as the terminal
alternative consumed by a symbolic Hall collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RRPkt
open
  CRLayer
open
  CFSubsti
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  SESuppor
open
  ESTermin
open
  PFSubstib
open
  GRProgra

namespace
  STTricho

/--
One endpoint formula has recursive nested support when one guarded branch
supplies either a left or a right nested support step.
-/
def GuardedRecurrenceBranch
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop :=
  ∃ branch ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight,
    GNSuppor n leftWeight rightWeight
        branch.obstruction.operationalNestedLeft branch.obstruction ∨
      GNSuppor n leftWeight rightWeight
        branch.obstruction.operationalNestedRight branch.obstruction

/-- A surviving left formula branch supplies recursive endpoint support. -/
lemma nested_recurrence_branch
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (support :
      RecurrenceSurvivalCertificate
        raw word normalizer left right hleft hright e) :
    GuardedRecurrenceBranch
      n leftWeight rightWeight hleftWeight hrightWeight := by
  rcases support with
    ⟨branch, hbranch, _hweight, hcutoff, _hdescends⟩
  exact
    ⟨branch, hbranch,
      Or.inl (GNSuppor.left branch.obstruction hcutoff)⟩

/-- A surviving right formula branch supplies recursive endpoint support. -/
lemma guarded_recurrence_branch
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (support :
      BranchSurvivalCertificate
        raw word normalizer left right hleft hright e) :
    GuardedRecurrenceBranch
      n leftWeight rightWeight hleftWeight hrightWeight := by
  rcases support with
    ⟨branch, hbranch, _hweight, hcutoff, _hdescends⟩
  exact
    ⟨branch, hbranch,
      Or.inr (GNSuppor.right branch.obstruction hcutoff)⟩

/--
Every nonzero endpoint Hall-word formula evaluation either supplies one
guarded recursive support step or stops at a matching repeated-root product.
-/
lemma
    endpointMatchingBranch
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word : CWord HPAtom)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (hleft : 0 < word.pairLeftDegree)
    (hright : 0 < word.pairRightDegree)
    (e : ι → HEFam H)
    (hnonzero :
      (endpointMultRecurrence
        decomposition word normalizer left right hleft hright).eval e ≠ 0) :
    GuardedRecurrenceBranch
        n leftWeight rightWeight hleftWeight hrightWeight ∨
      GuardedMatchingBranch
        (multiplicityProfileShape
          decomposition.raw)
        word (left.eval e) (right.eval e) := by
  rcases
      recurrenceImpTrichotomy
        decomposition word normalizer left right hleft hright e hnonzero with
    hleftSupport | hrootSupport | hrightSupport
  · left
    exact
      nested_recurrence_branch
        (multiplicityProfileShape
          decomposition.raw)
        word normalizer left right hleft hright e hleftSupport
  · exact Or.inr hrootSupport
  · left
    exact
      guarded_recurrence_branch
        (multiplicityProfileShape
          decomposition.raw)
        word normalizer left right hleft hright e hrightSupport

end
  STTricho

end TCTex
end Submission

/-!
# Vocabulary-indexed endpoint support trichotomy through cutoff four

Retained erased-shape vocabulary membership supplies the positive Hall
bidegrees required by formula substitution.  This file forwards the endpoint
support trichotomy through that automatic positivity interface and its
cutoff-four specialization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  FIProf
open
  CFSubsti
open
  CWSkelet
open
  ISLift
open
  SESuppor
open
  IVLow
open
  GRProgra

namespace
  SVLow

/--
Every nonzero retained-vocabulary endpoint formula evaluation has visible
support without separately supplied Hall-bidegree positivity proofs.
-/
lemma
    vocabImpTrichotomy
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H)
    (hnonzero :
      (endpointVocabRecurrence
        decomposition word normalizer left right).eval e ≠ 0) :
    RecurrenceSurvivalCertificate
        (multiplicityProfileShape
          decomposition.raw)
        word.1 normalizer left right
          (bidegree_positive_vocabulary word.2).1
          (bidegree_positive_vocabulary word.2).2
          e ∨
      GuardedMatchingBranch
          (multiplicityProfileShape
            decomposition.raw)
          word.1 (left.eval e) (right.eval e) ∨
        BranchSurvivalCertificate
          (multiplicityProfileShape
            decomposition.raw)
          word.1 normalizer left right
            (bidegree_positive_vocabulary word.2).1
            (bidegree_positive_vocabulary word.2).2
            e := by
  rw [
    endpointVocabRecurrence] at hnonzero
  exact
    recurrenceImpTrichotomy
      decomposition word.1 normalizer left right
        (bidegree_positive_vocabulary word.2).1
        (bidegree_positive_vocabulary word.2).2
        e hnonzero

/--
Through cutoff four, every nonzero retained-vocabulary endpoint formula
evaluation automa has visible recursive support.
-/
lemma
    endpointImpTrichotomy
    {d n leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H)
    (hnonzero :
      (endpointVocabularyFour
        layer hhigh raw word normalizer left right).eval e ≠ 0) :
    RecurrenceSurvivalCertificate
        (multiplicityProfileShape raw)
        word.1 normalizer left right
          (bidegree_positive_vocabulary word.2).1
          (bidegree_positive_vocabulary word.2).2
          e ∨
      GuardedMatchingBranch
          (multiplicityProfileShape raw)
          word.1 (left.eval e) (right.eval e) ∨
        BranchSurvivalCertificate
          (multiplicityProfileShape raw)
          word.1 normalizer left right
            (bidegree_positive_vocabulary word.2).1
            (bidegree_positive_vocabulary word.2).2
            e := by
  rw [endpointVocabularyFour] at hnonzero
  exact
    vocabImpTrichotomy
      (recNFour
        layer hhigh raw)
      word normalizer left right e hnonzero

end
  SVLow

end TCTex
end Submission

/-!
# Vocabulary-indexed recursive-step-or-terminal support through cutoff four

Retained erased-shape vocabulary membership supplies the positive Hall
bidegrees required by endpoint formula substitution.  This file forwards the
recursive-step-or-terminal support facade through that interface and its
cutoff-four specialization.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CRLayer
open
  FIProf
open
  CFSubsti
open
  CWSkelet
open
  ISLift
open
  SESuppor
open
  STTricho
open
  IVLow
open
  GRProgra

namespace
  TVLow

/--
Every nonzero retained-vocabulary endpoint formula evaluation either supplies
one guarded recursive support step or stops at a matching repeated-root
product.
-/
lemma
    vocabMatchingBranch
    {d n leftWeight rightWeight leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      RCDecompa
        layer hleftWeight hrightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H)
    (hnonzero :
      (endpointVocabRecurrence
        decomposition word normalizer left right).eval e ≠ 0) :
    GuardedRecurrenceBranch
        n leftWeight rightWeight hleftWeight hrightWeight ∨
      GuardedMatchingBranch
        (multiplicityProfileShape
          decomposition.raw)
        word.1 (left.eval e) (right.eval e) := by
  rw [
    endpointVocabRecurrence] at hnonzero
  exact
    endpointMatchingBranch
      decomposition word.1 normalizer left right
        (bidegree_positive_vocabulary word.2).1
        (bidegree_positive_vocabulary word.2).2
        e hnonzero

/--
Through cutoff four, every nonzero retained-vocabulary endpoint formula
evaluation either supplies one guarded recursive support step or stops at a
matching repeated-root product.
-/
lemma
    fourMatchingBranch
    {d n leftFormulaWeight rightFormulaWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftFormulaWeight)
    (right : WBForm H ι rightFormulaWeight)
    (e : ι → HEFam H)
    (hnonzero :
      (endpointVocabularyFour
        layer hhigh raw word normalizer left right).eval e ≠ 0) :
    GuardedRecurrenceBranch n 1 1 (by simp) (by simp) ∨
      GuardedMatchingBranch
        (multiplicityProfileShape raw)
        word.1 (left.eval e) (right.eval e) := by
  rw [endpointVocabularyFour] at hnonzero
  exact
    vocabMatchingBranch
      (recNFour
        layer hhigh raw)
      word normalizer left right e hnonzero

end
  TVLow

end TCTex
end Submission

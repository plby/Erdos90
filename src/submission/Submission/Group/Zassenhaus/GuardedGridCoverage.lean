import Submission.Group.Zassenhaus.SchedulePrograms
import Submission.Group.Zassenhaus.ErasedShapePrograms
import Submission.Group.Zassenhaus.EndpointShapeInterpolation
import Submission.Group.Zassenhaus.InverseUniversalClosure

/-!
# Guarded-grid coverage for concrete retained corrections

The canonical guarded polynomial-orbit grid enumerates retained parent-index
pairs whose recursive correction packets stay inside the finite vocabulary and
whose root correction lies below the cutoff.  The concrete endpoint scheduler
stores the actual crossed parents that emitted each retained correction.

This file connects the two descriptions.  Every concrete endpoint crossing has
retained parent keys, determines a canonical guarded-grid branch, and is
recovered exactly by forgetting that branch's finite indices.

The remaining arbitrary-cutoff collector theorem is therefore a multiplicity
and coalescing statement: no support-direction gap remains between actual
endpoint crossings and the guarded symbolic grid.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace CGCovera

open
  HACoeff
open
  RRPkt
open
  ROSuppor
open
  ROAggreg
open
  ROTransi
open
  CRAlign
open
  CRIndexa
open
  CRSuppor
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  CFCollec
open
  CRLayer
open
  CCAggreg
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  UCVocabu
open
  RITrace
open
  OEBounda
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  UOVocabu
open
  URVocabu

/--
Every below-cutoff concrete term generated from the inverse raw source has its
exact polynomial-orbit key in the retained finite vocabulary.
-/
lemma poly_orbit_key
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {term :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length}
    (hterm :
      CGFrom (inverseDecoratedTerms M N) term)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight term < n) :
    polynomialOrbitKey term.family.recipe ∈
      retainedOrbitVocabulary n leftWeight rightWeight := by
  rcases
      recipe_correction_inverse
        hleftWeight hrightWeight hterm hweight with
    ⟨recipe, hrecipe, hkey⟩
  rw [← hkey]
  exact
    key_vocabulary_recipes
      hrecipe

/--
Both parents of every actual retained endpoint crossing have retained finite
polynomial-orbit indices.
-/
lemma parents_poly_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length}
    (hcrossing :
      crossing ∈
        (endpointScheduleProgram
          layer M N).program.crossings) :
    polynomialOrbitKey crossing.1.family.recipe ∈
        retainedOrbitVocabulary n leftWeight rightWeight ∧
      polynomialOrbitKey crossing.2.family.recipe ∈
        retainedOrbitVocabulary n leftWeight rightWeight := by
  have hparents :=
    inverse_schedule_program
      layer M N hcrossing
  have hrootWeight :=
    (endpointScheduleProgram
      layer M N).program.weight_correction_crossings hcrossing
  have hleftCutoff :
      decoratedFamilyWeight leftWeight rightWeight crossing.1 < n := by
    rw [decorated_family_correction] at hrootWeight
    omega
  have hrightCutoff :
      decoratedFamilyWeight leftWeight rightWeight crossing.2 < n := by
    rw [decorated_family_correction] at hrootWeight
    omega
  exact
    ⟨poly_orbit_key
        hleftWeight hrightWeight hparents.1 hleftCutoff,
      poly_orbit_key
        hleftWeight hrightWeight hparents.2 hrightCutoff⟩

/--
Canonical guarded-grid branch represented by one actual retained endpoint
crossing.
-/
noncomputable def guardedGridCrossing
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
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
        (endpointScheduleProgram
          layer M N).program.crossings) :
    IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight where
  leftIndex :=
    indexOrbitKey
      ⟨polynomialOrbitKey crossing.1.family.recipe,
        (parents_poly_program
          layer hleftWeight hrightWeight M N hcrossing).1⟩
  rightIndex :=
    indexOrbitKey
      ⟨polynomialOrbitKey crossing.2.family.recipe,
        (parents_poly_program
          layer hleftWeight hrightWeight M N hcrossing).2⟩
  support := by
    simpa [concreteCrossingObstruction,
      crossingRecipeObstruction, polynomialOrbitObstruction] using
      supported_crossing_program
        layer hleftWeight hrightWeight M N hcrossing

/-- Forgetting finite indices recovers the concrete crossing obstruction exactly. -/
@[simp]
lemma obstruction_grid_crossing
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
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
        (endpointScheduleProgram
          layer M N).program.crossings) :
    (guardedGridCrossing
      layer hleftWeight hrightWeight M N crossing hcrossing).obstruction =
        concreteCrossingObstruction crossing := by
  simp [guardedGridCrossing,
    IOBranch.obstruction,
    concreteCrossingObstruction,
    crossingRecipeObstruction, polynomialOrbitObstruction]

/-- Every concrete endpoint crossing branch occurs in the canonical guarded grid. -/
lemma gridBranchBranches
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
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
        (endpointScheduleProgram
          layer M N).program.crossings) :
    guardedGridCrossing
        layer hleftWeight hrightWeight M N crossing hcrossing ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight := by
  let branch :=
    guardedGridCrossing
      layer hleftWeight hrightWeight M N crossing hcrossing
  have hroot :
      branch.obstruction.weight leftWeight rightWeight < n := by
    rw [show branch.obstruction =
        concreteCrossingObstruction crossing from
      obstruction_grid_crossing
        layer hleftWeight hrightWeight M N crossing hcrossing]
    rw [crossing_orbit_obstruction]
    exact
      (endpointScheduleProgram
        layer M N).program.weight_correction_crossings hcrossing
  exact
    mk_supported_branches
      branch.leftIndex branch.rightIndex branch.support hroot

/--
Ordered guarded-grid branches selected by the literal concrete endpoint
crossings.
-/
noncomputable def endpointGridBranches
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight) :=
  (endpointScheduleProgram
    layer M N).program.crossings.attach.map fun crossing =>
      guardedGridCrossing
        layer hleftWeight hrightWeight M N crossing.1 crossing.2

/-- Every selected concrete branch is a member of the canonical guarded grid. -/
lemma guarded_grid_branches
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight}
    (hbranch :
      branch ∈
        endpointGridBranches
          layer hleftWeight hrightWeight M N) :
    branch ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight := by
  rcases List.mem_map.mp hbranch with ⟨crossing, _hcrossing, rfl⟩
  exact
    gridBranchBranches
      layer hleftWeight hrightWeight M N crossing.1 crossing.2

/--
Forgetting selected guarded branches recovers the ordered literal endpoint
obstruction list exactly.
-/
lemma obstruction_generated_branches
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (endpointGridBranches
      layer hleftWeight hrightWeight M N).map
        IOBranch.obstruction =
      polynomialOrbitObstructions
        (endpointScheduleProgram
          layer M N).program := by
  unfold endpointGridBranches
  unfold polynomialOrbitObstructions
  rw [List.map_map]
  calc
    _ =
        (endpointScheduleProgram
          layer M N).program.crossings.attach.map fun crossing =>
            concreteCrossingObstruction crossing.1 := by
      apply List.map_congr_left
      intro crossing _hcrossing
      exact
        obstruction_grid_crossing
          layer hleftWeight hrightWeight M N crossing.1 crossing.2
    _ = _ := by
      simpa only [List.map_map, Function.comp_apply] using
        congrArg
          (List.map concreteCrossingObstruction)
          (List.attach_map_subtype_val
            (endpointScheduleProgram
              layer M N).program.crossings)

/--
Every actual endpoint obstruction is represented by a canonical guarded-grid
branch with exactly that obstruction.
-/
lemma guarded_supported_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {obstruction : POObstru}
    (hobstruction :
      obstruction ∈
        polynomialOrbitObstructions
          (endpointScheduleProgram
            layer M N).program) :
    ∃ branch ∈
        guardedSupportedBranches
          n leftWeight rightWeight hleftWeight hrightWeight,
      branch.obstruction = obstruction := by
  rw [←
    obstruction_generated_branches
      layer hleftWeight hrightWeight M N] at hobstruction
  rcases List.mem_map.mp hobstruction with
    ⟨branch, hbranch, rfl⟩
  exact
    ⟨branch,
      guarded_grid_branches
        layer hleftWeight hrightWeight M N hbranch,
      rfl⟩

/--
Correction-root finite index selected by the profiled polynomial-orbit
expansion compiler for one guarded branch.
-/
noncomputable def
    guardedGridBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RetainedOrbitIndex n leftWeight rightWeight :=
  MPFam.correctionIndex
    hleftWeight hrightWeight branch.obstruction branch.support

/-- Decoding a guarded branch's compiler-selected root index recovers its correction key. -/
@[simp]
lemma
    key_branch_index
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      IOBranch
        n leftWeight rightWeight hleftWeight hrightWeight) :
    retainedOrbitKey (guardedGridBranch branch) =
      branch.obstruction.correction := by
  exact
    MPFam.retained_key_index
      hleftWeight hrightWeight branch.obstruction branch.support

/--
Ordered correction-root finite-index trace selected by the profiled compiler
from the literal concrete endpoint branches.
-/
noncomputable def
    endpointGeneratedBranch
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  (endpointGridBranches
    layer hleftWeight hrightWeight M N).map fun branch =>
      guardedGridBranch branch

/--
Decoding the compiler-selected concrete branch roots recovers the ordered
literal endpoint root-key trace exactly.
-/
lemma
    key_grid_branch
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (endpointGeneratedBranch
      layer hleftWeight hrightWeight M N).map
        retainedOrbitKey =
      endpointGeneratedKeys
        layer M N := by
  unfold
    endpointGeneratedBranch
  rw [List.map_map]
  calc
    _ =
        (endpointGridBranches
          layer hleftWeight hrightWeight M N).map fun branch =>
            branch.obstruction.correction := by
      apply List.map_congr_left
      intro branch _hbranch
      exact
        key_branch_index
          branch
    _ =
        ((endpointGridBranches
          layer hleftWeight hrightWeight M N).map
            IOBranch.obstruction).map
              POObstru.correction := by
      rw [List.map_map]
      apply List.map_congr_left
      intro branch _hbranch
      rfl
    _ =
        (polynomialOrbitObstructions
          (endpointScheduleProgram
            layer M N).program).map
              POObstru.correction := by
      rw [
        obstruction_generated_branches]
    _ =
        endpointGeneratedKeys
          layer M N := by
      rfl

/-- Mapping an injective function over lists remains injective. -/
lemma listMap_injective
    {α β : Type*}
    (f : α → β)
    (hf : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro left
  induction left with
  | nil =>
      intro right hright
      cases right with
      | nil =>
          rfl
      | cons head tail =>
          simp at hright
  | cons head tail ih =>
      intro right hright
      cases right with
      | nil =>
          simp at hright
      | cons next rest =>
          simp only [List.map_cons, List.cons.injEq] at hright
          rw [hf hright.1, ih hright.2]

/--
The correction-root indices selected by concrete guarded branches are exactly
the literal endpoint root indices encoded earlier.
-/
lemma
    endpoint_guarded_idx
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    endpointGeneratedBranch
        layer hleftWeight hrightWeight M N =
      endpointGeneratedConcrete
        layer hleftWeight hrightWeight M N := by
  apply listMap_injective retainedOrbitKey
    orbit_key_injective
  rw [
    key_grid_branch,
    key_generated_concrete]

end CGCovera
end TCTex
end Submission

/-!
# Finite-index recursive packets for concrete retained corrections

Every actual retained endpoint crossing has a fully supported recipe-free
operational packet.  This file encodes those packets independently, preserving
their endpoint order and their packet boundaries, and then flattens them into
one finite-index recursive expansion trace.

Decoding the flattened trace recovers the ordered flattened list of complete
recipe-free recursive packets exactly.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  CRIndex

open
  RRPkt
open
  RRPkt.POObstru
open
  ROAggreg
open
  CRAlign
open
  CRSuppor
open
  CPProven
open
  CRLayer
open
  RITrace
open
  RIRecurs

/--
Ordered complete recipe-free key packets rooted at the actual retained
endpoint crossings.
-/
def endpointRecursiveKeys
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (List POKey) :=
  (polynomialOrbitObstructions
      (endpointScheduleProgram
        layer M N).program).map fun obstruction =>
    obstruction.retainedKeys (n := n) hleftWeight hrightWeight

/--
Encode every complete actual endpoint recursive packet separately, preserving
the packet boundary list.
-/
noncomputable def
  endpointRecursiveTraces
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (List (RetainedOrbitIndex n leftWeight rightWeight)) :=
  (polynomialOrbitObstructions
      (endpointScheduleProgram
        layer M N).program).attach.map fun obstruction =>
    retainedIndexTrace (n := n) hleftWeight hrightWeight obstruction.1
      (supported_schedule_program
        layer hleftWeight hrightWeight M N obstruction.2)

/-- Decoding each finite-index packet recovers the ordered recipe-free packet list. -/
lemma keyRecTraces
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (endpointRecursiveTraces
      layer hleftWeight hrightWeight M N).map
        (List.map retainedOrbitKey) =
      endpointRecursiveKeys
        layer hleftWeight hrightWeight M N := by
  unfold
    endpointRecursiveTraces
  unfold endpointRecursiveKeys
  rw [List.map_map]
  calc
    _ =
        (polynomialOrbitObstructions
          (endpointScheduleProgram
            layer M N).program).attach.map fun obstruction =>
              obstruction.1.retainedKeys
                (n := n) hleftWeight hrightWeight := by
      apply List.map_congr_left
      intro obstruction _hobstruction
      exact
        key_retained_trace
          hleftWeight hrightWeight obstruction.1 _
    _ = _ := by
      simpa only [List.map_map, Function.comp_apply] using
        congrArg
          (List.map fun obstruction =>
            obstruction.retainedKeys (n := n) hleftWeight hrightWeight)
          (List.attach_map_subtype_val
            (polynomialOrbitObstructions
              (endpointScheduleProgram
                layer M N).program))

/-- Flatten the complete actual endpoint recursive packets into one index trace. -/
noncomputable def
  endpointGeneratedRecursive
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  (endpointRecursiveTraces
    layer hleftWeight hrightWeight M N).flatten

/--
Decoding the flattened finite-index recursive expansion recovers the flattened
ordered recipe-free packet list exactly.
-/
lemma key_generated_recursive
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (endpointGeneratedRecursive
      layer hleftWeight hrightWeight M N).map retainedOrbitKey =
      (endpointRecursiveKeys
        layer hleftWeight hrightWeight M N).flatten := by
  unfold
    endpointGeneratedRecursive
  rw [List.map_flatten,
    keyRecTraces]

end CRIndex
end TCTex
end Submission

/-!
# Guarded orbit expansions against generated concrete collector programs

The provenance-certified endpoint schedule retains the two actual parents of
every selected correction and proves that they are generated from the inverse
raw source.  The concrete guarded-grid coverage boundary places every one of
those crossings inside the canonical symbolic grid.

The remaining arbitrary-cutoff collector theorem is now stated against that
literal provenance-certified program: after raw-source multiplicity packets
are installed, the guarded symbolic scheduler-order program permutes to the
erasure of the generated concrete schedule.  This file compiles that single
coalescing obligation to the endpoint interpolation package consumed by the
power-coordinate pipeline.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace GGProgra

open
  HACoeff
open
  CGCovera
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  CFCollec
open
  CRLayer
open
  FIProf
open
  ISLift
open
  PGSrc
open
  RTProgra
open
  GGErased
open
  GRProgra
open
  SEAlg

/--
Erasing the provenance-certified generated endpoint program recovers the
literal selected retained-correction shape trace.
-/
lemma programEndpointSchedule
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ((endpointScheduleProgram
      layer M N).program.shapeTraceProgram).trace =
        selectedErasedShape layer M N := by
  rw [
    RSPrograa.trace_erased_shape,
    (endpointScheduleProgram
      layer M N).correctionTrace_eq]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/--
Induction-ready arbitrary-cutoff boundary: the canonical guarded symbolic
program permutes to the provenance-certified concrete endpoint schedule.

The remaining proof is concentrated in `generated_concrete_perm`.
Every node on the concrete side is already known to be represented by a
canonical guarded-grid branch.
-/
structure
    GCDecompa
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  generated_concrete_perm :
    ∀ M N,
      List.Perm
        (guardedSchedulerProgram
          (multiplicityProfileShape
            raw)
          M N).trace
        ((endpointScheduleProgram
          layer M N).program.shapeTraceProgram).trace

namespace
  GCDecompa

/--
Forget concrete parent witnesses and retain the erased-shape guarded-grid
decomposition consumed by the existing endpoint compiler.
-/
noncomputable def
    guardedErasedDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecompa
        layer hleftWeight hrightWeight) :
    GEDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  shape_trace_perm M N := by
    rw [←
      programEndpointSchedule
        layer M N]
    exact
      (keyErasedScheduler
        (multiplicityProfileShape
          decomposition.raw)
        M N).trans
        (decomposition.generated_concrete_perm M N)

/--
Compile the single generated-concrete-program comparison to the selected
endpoint finite-index shape-fiber profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecompa
        layer hleftWeight hrightWeight) :=
  decomposition.guardedErasedDecomp
    |>.selectedFullFiber

/--
Compile the generated-concrete-program comparison directly to the endpoint
interpolation object consumed by the power-coordinate pipeline.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecompa
        layer hleftWeight hrightWeight) :=
  decomposition.guardedErasedDecomp
    |>.fiberProfileInterpolation

end
  GCDecompa

/--
Through cutoff four, the generated provenance-certified concrete program and
the guarded symbolic program both emit the empty correction-shape trace.
-/
noncomputable def
    genDecompFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GCDecompa
      layer (by simp) (by simp) where
  raw :=
    raw
  generated_concrete_perm M N := by
    unfold
      guardedSchedulerProgram
    rw [
      branches_nil_four
        (by simp) (by simp) hhigh]
    have htrace :=
      programEndpointSchedule
        layer M N
    rw [
      selected_nil_four
        layer hhigh M N] at htrace
    simp [htrace]

/--
Through cutoff four, the provenance-certified generated-program route reaches
the endpoint interpolation object consumed by the power-coordinate pipeline.
-/
noncomputable def
    fiberInterpolationProgram
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :=
  (genDecompFour
    layer hhigh raw)
      |>.fiberProfileInterpolation

end GGProgra
end TCTex
end Submission

/-!
# Generic guarded-grid coverage for synchronized concrete schedules

The guarded-grid coverage theorem for retained corrections was originally
specialized to one compiler-selected endpoint program.  The support argument
only uses two local facts about a concrete crossing:

* both parents are generated from the inverse-raw source;
* the emitted correction lies strictly below the cutoff.

This file factors out that local theorem and compiles any concrete schedule
with inverse-raw crossing provenance into canonical guarded-grid branches.
Applying the compiler to the synchronized endpoint certificate connects the
actual cutoff-full occurrence run directly to guarded polynomial-orbit roots.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  EGCovera

universe u

open
  HACoeff
open
  RCSuppor
open
  RRPkt
open
  RRPkt.POObstru
open
  ROSuppor
open
  BRPkt
open
  BRPkt.RObstru
open
  ROAggreg
open
  ROTransi
open
  BRSpec
open
  CRAlign
open
  CRIndexa
open
  CGCovera
open
  CRSuppor
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
  CCAggreg
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  UCVocabu
open
  RITrace
open
  RIRecurs
open
  ESIdx
open
  PGSrc
open
  URVocabu
open
  RTProgra

/--
The complete recursive packet rooted at a concrete crossing is supported by
the retained orbit vocabulary whenever its two parents have inverse-raw
provenance and its emitted correction lies below cutoff.
-/
lemma supported_crossing_poly
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
    IsSupported (n := n) hleftWeight hrightWeight
      (concreteCrossingObstruction crossing) := by
  have hleftCutoff :
      decoratedFamilyWeight leftWeight rightWeight crossing.1 < n := by
    rw [decorated_family_correction] at hrootWeight
    omega
  have hrightCutoff :
      decoratedFamilyWeight leftWeight rightWeight crossing.2 < n := by
    rw [decorated_family_correction] at hrootWeight
    omega
  rcases
      recipe_key_generated
        hleftWeight hrightWeight
        (sourceRecipes := sourceRecipes n leftWeight rightWeight)
        (fun sourceTerm hsourceTerm hsourceWeight =>
          key_decorated_terms
            hleftWeight hrightWeight hsourceTerm hsourceWeight)
        hparents.1 hleftCutoff with
    ⟨leftRecipe, hleftRecipe, hleftKey⟩
  rcases
      recipe_key_generated
        hleftWeight hrightWeight
        (sourceRecipes := sourceRecipes n leftWeight rightWeight)
        (fun sourceTerm hsourceTerm hsourceWeight =>
          key_decorated_terms
            hleftWeight hrightWeight hsourceTerm hsourceWeight)
        hparents.2 hrightCutoff with
    ⟨rightRecipe, hrightRecipe, hrightKey⟩
  let recipeObstruction : RObstru := {
    left := leftRecipe
    right := rightRecipe
  }
  have hleftRecipeWeight :
      weightedWordWeight leftWeight rightWeight leftRecipe =
        decoratedFamilyWeight leftWeight rightWeight crossing.1 := by
    rw [decoratedFamilyWeight, ← weight_orbit_key,
      ← weight_orbit_key, hleftKey]
  have hrightRecipeWeight :
      weightedWordWeight leftWeight rightWeight rightRecipe =
        decoratedFamilyWeight leftWeight rightWeight crossing.2 := by
    rw [decoratedFamilyWeight, ← weight_orbit_key,
      ← weight_orbit_key, hrightKey]
  have hleftRecipeClosure :
      leftRecipe ∈
        correctionClosure (sourceRecipes n leftWeight rightWeight)
          (weightedWordWeight leftWeight rightWeight leftRecipe) := by
    rw [hleftRecipeWeight]
    exact hleftRecipe
  have hrightRecipeClosure :
      rightRecipe ∈
        correctionClosure (sourceRecipes n leftWeight rightWeight)
          (weightedWordWeight leftWeight rightWeight rightRecipe) := by
    rw [hrightRecipeWeight]
    exact hrightRecipe
  have horbit :
      polynomialOrbitObstruction recipeObstruction =
        concreteCrossingObstruction crossing := by
    simp [recipeObstruction, concreteCrossingObstruction,
      crossingRecipeObstruction, polynomialOrbitObstruction,
      hleftKey, hrightKey]
  have hrecipeRoot :
      recipeObstruction.weight leftWeight rightWeight < n := by
    rw [← weight_orbit_obstruction, horbit,
      crossing_orbit_obstruction]
    exact hrootWeight
  rw [← horbit]
  intro key hkey
  apply
    poly_orbit_keys
      hleftWeight hrightWeight recipeObstruction
      hleftRecipeClosure hrightRecipeClosure hrecipeRoot
  rw [retained_orbit_keys]
  exact hkey

/--
The parents of any provenance-certified retained crossing have keys in the
finite retained orbit vocabulary.
-/
lemma parents_vocabulary_generated
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
    polynomialOrbitKey crossing.1.family.recipe ∈
        retainedOrbitVocabulary n leftWeight rightWeight ∧
      polynomialOrbitKey crossing.2.family.recipe ∈
        retainedOrbitVocabulary n leftWeight rightWeight := by
  have hleftCutoff :
      decoratedFamilyWeight leftWeight rightWeight crossing.1 < n := by
    rw [decorated_family_correction] at hrootWeight
    omega
  have hrightCutoff :
      decoratedFamilyWeight leftWeight rightWeight crossing.2 < n := by
    rw [decorated_family_correction] at hrootWeight
    omega
  exact
    ⟨poly_orbit_key
        hleftWeight hrightWeight hparents.1 hleftCutoff,
      poly_orbit_key
        hleftWeight hrightWeight hparents.2 hrightCutoff⟩

/--
Canonical guarded-grid branch represented by one crossing of an arbitrary
inverse-raw provenance-certified concrete schedule.
-/
noncomputable def guardedBranchCrossing
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hcrossing : crossing ∈ program.crossings) :
    IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight where
  leftIndex :=
    indexOrbitKey
      ⟨polynomialOrbitKey crossing.1.family.recipe,
        (parents_vocabulary_generated
          hleftWeight hrightWeight crossing
            (hgenerated crossing hcrossing)
              (program.weight_correction_crossings hcrossing)).1⟩
  rightIndex :=
    indexOrbitKey
      ⟨polynomialOrbitKey crossing.2.family.recipe,
        (parents_vocabulary_generated
          hleftWeight hrightWeight crossing
            (hgenerated crossing hcrossing)
              (program.weight_correction_crossings hcrossing)).2⟩
  support := by
    simpa [concreteCrossingObstruction,
      crossingRecipeObstruction, polynomialOrbitObstruction] using
      supported_crossing_poly
        hleftWeight hrightWeight crossing
          (hgenerated crossing hcrossing)
            (program.weight_correction_crossings hcrossing)

/-- Forgetting finite indices recovers the concrete crossing obstruction. -/
@[simp]
lemma obstruction_branch_crossing
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hcrossing : crossing ∈ program.crossings) :
    (guardedBranchCrossing
      hleftWeight hrightWeight program hgenerated crossing hcrossing).obstruction =
        concreteCrossingObstruction crossing := by
  simp [guardedBranchCrossing,
    IOBranch.obstruction,
    concreteCrossingObstruction,
    crossingRecipeObstruction, polynomialOrbitObstruction]

/-- Every provenance-certified concrete crossing occurs in the guarded grid. -/
lemma guardedBranchBranches
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hcrossing : crossing ∈ program.crossings) :
    guardedBranchCrossing
        hleftWeight hrightWeight program hgenerated crossing hcrossing ∈
      guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight := by
  let branch :=
    guardedBranchCrossing
      hleftWeight hrightWeight program hgenerated crossing hcrossing
  have hroot :
      branch.obstruction.weight leftWeight rightWeight < n := by
    rw [show branch.obstruction =
        concreteCrossingObstruction crossing from
      obstruction_branch_crossing
        hleftWeight hrightWeight program hgenerated crossing hcrossing]
    rw [crossing_orbit_obstruction]
    exact program.weight_correction_crossings hcrossing
  exact
    mk_supported_branches
      branch.leftIndex branch.rightIndex branch.support hroot

/-- Ordered guarded branches selected by an arbitrary provenance schedule. -/
noncomputable def generatedGuardedBranches
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program) :
    List (IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight) :=
  program.crossings.attach.map fun crossing =>
    guardedBranchCrossing
      hleftWeight hrightWeight program hgenerated crossing.1 crossing.2

/-- The generic guarded branches decode to the schedule obstruction list. -/
lemma obstruction_guarded_branches
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program) :
    (generatedGuardedBranches
      hleftWeight hrightWeight program hgenerated).map
        IOBranch.obstruction =
      polynomialOrbitObstructions program := by
  unfold generatedGuardedBranches
  unfold polynomialOrbitObstructions
  rw [List.map_map]
  calc
    _ =
        program.crossings.attach.map fun crossing =>
          concreteCrossingObstruction crossing.1 := by
      apply List.map_congr_left
      intro crossing _hcrossing
      exact
        obstruction_branch_crossing
          hleftWeight hrightWeight program hgenerated crossing.1 crossing.2
    _ = _ := by
      simpa only [List.map_map, Function.comp_apply] using
        congrArg
          (List.map concreteCrossingObstruction)
          (List.attach_map_subtype_val program.crossings)

/-- Ordered compiler-selected guarded root indices for a provenance schedule. -/
noncomputable def generatedGuardedBranch
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  (generatedGuardedBranches
    hleftWeight hrightWeight program hgenerated).map fun branch =>
      guardedGridBranch
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) branch

/--
Erasing the generic guarded root-index trace recovers the concrete schedule's
literal erased-shape trace.
-/
lemma key_branch_program
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program) :
    ((generatedGuardedBranch
      hleftWeight hrightWeight program hgenerated).map fun index =>
        (retainedOrbitKey index).erasedShape) =
      program.shapeTraceProgram.trace := by
  unfold generatedGuardedBranch
  rw [List.map_map]
  calc
    _ =
        (generatedGuardedBranches
          hleftWeight hrightWeight program hgenerated).map fun branch =>
            branch.obstruction.correction.erasedShape := by
      apply List.map_congr_left
      intro branch _hbranch
      simp only [Function.comp_apply]
      rw [key_branch_index
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)]
    _ =
        ((generatedGuardedBranches
          hleftWeight hrightWeight program hgenerated).map
            IOBranch.obstruction).map
              (fun obstruction => obstruction.correction.erasedShape) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro branch _hbranch
      rfl
    _ =
        (polynomialOrbitObstructions program).map
          (fun obstruction => obstruction.correction.erasedShape) := by
      rw [obstruction_guarded_branches]
    _ = program.shapeTraceProgram.trace := by
      rw [
        RSPrograa.mapcor_erase_polyo,
        RSPrograa.trace_erased_shape]

/--
The synchronized endpoint certificate therefore carries a direct guarded-grid
root-index encoding of its own concrete correction program.
-/
noncomputable def
  synchronizedGridBranch
    {n leftWeight rightWeight : ℕ}
    {layer :
      CRLayer.NRLayer
        n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  generatedGuardedBranch
    hleftWeight hrightWeight certificate.program certificate.crossings_generated

/--
Erasing synchronized guarded roots recovers the correction-program trace
carried by the same endpoint occurrence certificate.
-/
lemma key_endpoint_program
    {n leftWeight rightWeight : ℕ}
    {layer :
      CRLayer.NRLayer
        n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ((synchronizedGridBranch
      certificate hleftWeight hrightWeight).map fun index =>
        (retainedOrbitKey index).erasedShape) =
      certificate.program.shapeTraceProgram.trace :=
  key_branch_program
    hleftWeight hrightWeight certificate.program certificate.crossings_generated

end
  EGCovera
end TCTex
end Submission

/-!
# Multiplicity coalescing for generated concrete collector programs

The guarded symbolic scheduler and the provenance-certified concrete endpoint
program were previously compared by a permutation of erased-shape traces.
Endpoint coordinates depend only on Hall-shape multiplicities.  This file
rephrases the remaining arbitrary-cutoff theorem as the corresponding family
of count identities.

The symbolic side is the flattened recursive expansion of the canonical
guarded root grid.  The concrete side is the ordered compiler-selected root
trace attached to the actual retained endpoint crossings.  Adapters in both
directions prove that this multiplicity-coalescing formulation is exactly
equivalent to the generated-program permutation boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace PMCoales

open
  CRIndexa
open
  CGCovera
open
  GGProgra
open
  CRProgra
open
  CPProven
open
  CRLayer
open
  FIProf
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  GRProgra

/--
Shape-erased recursive expansion emitted by the canonical guarded root grid.
-/
noncomputable def
    guardedExpansionErased
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List (CWord HPAtom) :=
  (((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        branch.indexTrace
          (multiplicityProfileShape
            raw)
          M N).flatten).map fun index =>
            (retainedOrbitKey index).erasedShape

/--
Shape-erased compiler-selected roots attached to the actual endpoint
crossings.
-/
noncomputable def
    endpointGridBranch
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (CWord HPAtom) :=
  (endpointGeneratedBranch
    layer hleftWeight hrightWeight M N).map fun index =>
      (retainedOrbitKey index).erasedShape

/--
The recursive guarded expansion permutes to its scheduler-order program.
-/
lemma
    idxSchedulerProgram
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ) :
    List.Perm
      (guardedExpansionErased
        raw M N)
      (guardedSchedulerProgram
        (multiplicityProfileShape raw)
        M N).trace := by
  exact
    keyErasedScheduler
      (multiplicityProfileShape raw)
      M N

/--
The concrete crossing-root trace is exactly the trace of the erased generated
endpoint schedule.
-/
lemma
    endpoint_guarded_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    endpointGridBranch
        layer hleftWeight hrightWeight M N =
      ((endpointScheduleProgram
        layer M N).program.shapeTraceProgram).trace := by
  rw [
    endpointGridBranch,
    endpoint_guarded_idx,
    key_endpoint_generated,
    ←
      programEndpointSchedule]

/--
Induction-ready multiplicity formulation of the arbitrary-cutoff theorem.

For each Hall shape, the recursively expanded guarded root grid has the same
multiplicity as the compiler-selected roots attached to the actual endpoint
crossings.
-/
structure
    GCDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  expanded_root_count :
    ∀ M N word,
      (guardedExpansionErased
        raw M N).count word =
      (endpointGridBranch
        layer hleftWeight hrightWeight M N).count word

namespace
  GCDecomp

/--
Turn Hall-shape count identities into the generated concrete-program
permutation boundary.
-/
noncomputable def
    polyComparisonDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecomp
        layer hleftWeight hrightWeight) :
    GCDecompa
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  generated_concrete_perm M N := by
    classical
    rw [List.perm_iff_count]
    intro word
    rw [←
      (idxSchedulerProgram
        decomposition.raw M N).count_eq word]
    rw [←
      endpoint_guarded_program
        layer hleftWeight hrightWeight M N]
    exact decomposition.expanded_root_count M N word

/--
Compile multiplicity coalescing directly to the endpoint interpolation object
consumed by the power-coordinate pipeline.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecomp
        layer hleftWeight hrightWeight) :=
  decomposition.polyComparisonDecomp
    |>.fiberProfileInterpolation

end
  GCDecomp

namespace
  GCDecompa

/--
Recover Hall-shape multiplicity coalescing from the generated concrete-program
permutation boundary.
-/
noncomputable def
    guardedCoalescingDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecompa
        layer hleftWeight hrightWeight) :
    GCDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  expanded_root_count M N word := by
    rw [
      (idxSchedulerProgram
        decomposition.raw M N).count_eq word]
    rw [
      endpoint_guarded_program
        layer hleftWeight hrightWeight M N]
    exact (decomposition.generated_concrete_perm M N).count_eq word

end
  GCDecompa

/--
Through cutoff four, multiplicity coalescing is available from the empty
guarded grid and empty generated concrete schedule.
-/
noncomputable def
    multCoalescingFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
  GCDecomp
      layer (by simp) (by simp) :=
  GCDecompa.guardedCoalescingDecomp
    (genDecompFour
      layer hhigh raw)

end
  PMCoales
end TCTex
end Submission

/-!
# Finite-index recurrences for generated concrete schedules

The generated concrete schedule previously exposed its correction-root trace
only as a flat map over stored parent crossings.  Exact symbolic Hall
collection needs the constructor equations before polynomial-orbit indices are
erased to Hall shapes.

This file factors the root index attached to one generated parent pair and
proves the `empty`, `append`, and `retained` equations for an arbitrary
inverse-raw provenance-certified concrete schedule.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  ITRec

open
  HACoeff
open
  RRPkt
open
  ROAggreg
open
  ROTransi
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
  CFCollec.DFTerm
open
  CCAggreg
open
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  RITrace
open
  ESIdx
open
  ISLift

/--
Canonical guarded branch attached directly to one inverse-raw generated parent
pair.  Unlike the schedule-facing constructor, this definition does not retain
an ambient schedule or a membership proof.
-/
noncomputable def gridBranchParents
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
    IOBranch
      n leftWeight rightWeight hleftWeight hrightWeight where
  leftIndex :=
    indexOrbitKey
      ⟨polynomialOrbitKey crossing.1.family.recipe,
        (parents_vocabulary_generated
          hleftWeight hrightWeight crossing hparents hrootWeight).1⟩
  rightIndex :=
    indexOrbitKey
      ⟨polynomialOrbitKey crossing.2.family.recipe,
        (parents_vocabulary_generated
          hleftWeight hrightWeight crossing hparents hrootWeight).2⟩
  support := by
    simpa [concreteCrossingObstruction,
      crossingRecipeObstruction, polynomialOrbitObstruction] using
      supported_crossing_poly
        hleftWeight hrightWeight crossing hparents hrootWeight

/-- Forgetting the direct guarded branch recovers the concrete obstruction. -/
@[simp]
lemma obstruction_grid_parents
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
    (gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight).obstruction =
        concreteCrossingObstruction crossing := by
  simp [gridBranchParents,
    IOBranch.obstruction,
    concreteCrossingObstruction,
    crossingRecipeObstruction, polynomialOrbitObstruction]

/-- Compiler-selected correction-root index attached directly to one pair. -/
noncomputable def guardedGridParents
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
    RetainedOrbitIndex n leftWeight rightWeight :=
  guardedGridBranch
    (gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight)

/-- Decoding a direct generated-parent root recovers the concrete correction key. -/
@[simp]
lemma key_generated_parents
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
    retainedOrbitKey
        (guardedGridParents
          hleftWeight hrightWeight crossing hparents hrootWeight) =
      (concreteCrossingObstruction crossing).correction := by
  unfold guardedGridParents
  rw [key_branch_index]
  rw [obstruction_grid_parents]

/--
The schedule-facing branch is propositionally the direct generated-parent
branch.  This removes ambient schedule proof terms from recurrence equations.
-/
lemma branch_crossing_parents
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program)
    (crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length)
    (hcrossing : crossing ∈ program.crossings) :
    guardedBranchCrossing
        hleftWeight hrightWeight program hgenerated crossing hcrossing =
      gridBranchParents
        hleftWeight hrightWeight crossing
          (hgenerated crossing hcrossing)
          (program.weight_correction_crossings hcrossing) := by
  rfl

/--
The generic concrete root-index trace is the ordered direct root-index map over
its stored crossings.
-/
lemma generated_branch_attach
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program) :
    generatedGuardedBranch
        hleftWeight hrightWeight program hgenerated =
      program.crossings.attach.map fun crossing =>
        guardedGridParents
          hleftWeight hrightWeight crossing.1
            (hgenerated crossing.1 crossing.2)
            (program.weight_correction_crossings crossing.2) := by
  unfold generatedGuardedBranch
  unfold generatedGuardedBranches
  rw [List.map_map]
  apply List.map_congr_left
  intro crossing _hcrossing
  rfl

/--
Decoding the generated concrete root-index trace recovers the ordered
polynomial-orbit correction roots of the stored parent crossings.
-/
lemma key_generated_branch
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N) program) :
    (generatedGuardedBranch
      hleftWeight hrightWeight program hgenerated).map
        retainedOrbitKey =
      (polynomialOrbitObstructions program).map
        POObstru.correction := by
  unfold generatedGuardedBranch
  rw [List.map_map]
  calc
    _ =
        (generatedGuardedBranches
          hleftWeight hrightWeight program hgenerated).map fun branch =>
            branch.obstruction.correction := by
      apply List.map_congr_left
      intro branch _hbranch
      simp only [Function.comp_apply]
      rw [key_branch_index]
    _ =
        ((generatedGuardedBranches
          hleftWeight hrightWeight program hgenerated).map
            IOBranch.obstruction).map
              POObstru.correction := by
      rw [List.map_map]
      rfl
    _ =
        (polynomialOrbitObstructions program).map
          POObstru.correction := by
      rw [obstruction_guarded_branches]

/-- Restrict generated crossing provenance to the left side of an append. -/
lemma crossings_left_append
    {M N K n leftWeight rightWeight : ℕ}
    {source : List (DFTerm M N K)}
    {left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hgenerated :
      CGFroma source
        (RSPrograa.append left right)) :
    CGFroma source left := by
  intro crossing hcrossing
  exact hgenerated crossing (List.mem_append_left _ hcrossing)

/-- Restrict generated crossing provenance to the right side of an append. -/
lemma crossings_generated_append
    {M N K n leftWeight rightWeight : ℕ}
    {source : List (DFTerm M N K)}
    {left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hgenerated :
      CGFroma source
        (RSPrograa.append left right)) :
    CGFroma source right := by
  intro crossing hcrossing
  exact hgenerated crossing (List.mem_append_right _ hcrossing)

/-- Restrict generated crossing provenance to the left child of a retained node. -/
lemma crossings_generated_left
    {M N K n leftWeight rightWeight : ℕ}
    {source : List (DFTerm M N K)}
    {left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    {crossedLeft crossedRight : DFTerm M N K}
    {hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n}
    (hgenerated :
      CGFroma source
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    CGFroma source left := by
  intro crossing hcrossing
  exact hgenerated crossing
    (List.mem_append_left _
      (List.mem_append_left _ hcrossing))

/-- Restrict generated crossing provenance to the right child of a retained node. -/
lemma crossings_generated_retained
    {M N K n leftWeight rightWeight : ℕ}
    {source : List (DFTerm M N K)}
    {left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    {crossedLeft crossedRight : DFTerm M N K}
    {hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n}
    (hgenerated :
      CGFroma source
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    CGFroma source right := by
  intro crossing hcrossing
  exact hgenerated crossing
    (List.mem_append_right _ hcrossing)

/-- Recover the generated-parent proofs stored at the root of a retained node. -/
lemma generated_parents_retained
    {M N K n leftWeight rightWeight : ℕ}
    {source : List (DFTerm M N K)}
    {left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    {crossedLeft crossedRight : DFTerm M N K}
    {hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n}
    (hgenerated :
      CGFroma source
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    CGFrom source crossedLeft ∧
      CGFrom source crossedRight := by
  apply hgenerated (crossedLeft, crossedRight)
  change
    (crossedLeft, crossedRight) ∈
      left.crossings ++ [(crossedLeft, crossedRight)] ++ right.crossings
  simp

/-- The empty generated concrete schedule has an empty root-index trace. -/
@[simp]
lemma generated_branch_empty
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    generatedGuardedBranch
        hleftWeight hrightWeight
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N)
            (K := (inverseLabelledCollection M N).factors.length)
            n leftWeight rightWeight)
        (CGFroma.empty _) =
      [] := by
  rw [
    generated_branch_attach]
  rfl

/-- Generated root-index traces distribute over schedule concatenation. -/
lemma generated_branch_append
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right)) :
    generatedGuardedBranch
        hleftWeight hrightWeight
        (RSPrograa.append left right)
        hgenerated =
      generatedGuardedBranch
          hleftWeight hrightWeight left
          (crossings_left_append hgenerated) ++
      generatedGuardedBranch
          hleftWeight hrightWeight right
          (crossings_generated_append hgenerated) := by
  apply listMap_injective retainedOrbitKey
    orbit_key_injective
  rw [
    List.map_append,
    key_generated_branch,
    key_generated_branch,
    key_generated_branch]
  simp [polynomialOrbitObstructions,
    RSPrograa.crossings]

/--
A retained concrete crossing emits its left child trace, one direct root index,
and its right child trace.
-/
lemma generated_guarded_branch
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
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
    (hgenerated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)) :
    generatedGuardedBranch
        hleftWeight hrightWeight
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        hgenerated =
      generatedGuardedBranch
          hleftWeight hrightWeight left
          (crossings_generated_left hgenerated) ++
        [guardedGridParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
            (generated_parents_retained hgenerated) hweight] ++
      generatedGuardedBranch
          hleftWeight hrightWeight right
          (crossings_generated_retained hgenerated) := by
  apply listMap_injective retainedOrbitKey
    orbit_key_injective
  rw [
    List.map_append, List.map_append,
    key_generated_branch,
    key_generated_branch,
    key_generated_branch]
  simp only [List.map_singleton]
  rw [
    key_generated_parents]
  simp [polynomialOrbitObstructions,
    RSPrograa.crossings]

end
  ITRec
end TCTex
end Submission

/-!
# Branchwise multiplicity equations for generated concrete collector programs

The generated-program multiplicity boundary compares counts of two erased
shape traces.  This file normalizes both sides:

* the guarded recursive expansion count is a finite sum of branch counts;
* the concrete crossing-root count is the cardinality of the selected
  crossing branches whose correction has the requested Hall shape.

The remaining arbitrary-cutoff collector theorem is therefore one explicit
branchwise scalar identity for every Hall shape and every pair of block
multiplicities.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace PBMult

open
  CGCovera
open
  PMCoales
open
  CRLayer
open
  FIProf
open
  RITrace
open
  PGSrc
open
  ESIdx
open
  ISLift
open
  SEAlg

/--
Counting a mapped flattened packet list is the sum of the mapped packet
counts.
-/
lemma count_flatten_sum
    {α β γ : Type*}
    [DecidableEq γ]
    (entries : List α)
    (packet : α → List β)
    (erase : β → γ)
    (value : γ) :
    ((((entries.map packet).flatten).map erase).count value) =
      (entries.map fun entry => ((packet entry).map erase).count value).sum := by
  induction entries with
  | nil =>
      rfl
  | cons entry entries ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        List.count_append, List.sum_cons, ih]

/--
Finite sum of erased-shape counts contributed by the recursively expanded
canonical guarded branches.
-/
noncomputable def
    guardedBranchSum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    ℕ :=
  ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        ((branch.indexTrace
          (multiplicityProfileShape
            raw)
          M N).map fun index =>
            (retainedOrbitKey index).erasedShape).count word
    ).sum

/--
The flattened guarded recursive expansion count is its finite sum of branch
counts.
-/
lemma
    count_guarded_erased
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (guardedExpansionErased
      raw M N).count word =
      guardedBranchSum
        raw M N word := by
  exact
    count_flatten_sum
      (guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight)
      (fun branch =>
        branch.indexTrace
          (multiplicityProfileShape
            raw)
          M N)
      (fun index => (retainedOrbitKey index).erasedShape)
      word

/--
Number of actual endpoint crossing branches whose retained correction root
has the requested erased Hall shape.
-/
noncomputable def
    branchFiberCardinality
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    ℕ :=
  ((endpointGridBranches
    layer hleftWeight hrightWeight M N).filter fun branch =>
      decide (branch.obstruction.correction.erasedShape = word)).length

/--
The concrete compiler-selected root count is the filtered cardinality of
actual endpoint crossing branches.
-/
lemma
    count_fiber_cardinality
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (endpointGridBranch
      layer hleftWeight hrightWeight M N).count word =
      branchFiberCardinality
        layer hleftWeight hrightWeight M N word := by
  unfold
    endpointGridBranch
  unfold
    endpointGeneratedBranch
  rw [List.map_map]
  rw [show
    (endpointGridBranches
      layer hleftWeight hrightWeight M N).map
        ((fun index => (retainedOrbitKey index).erasedShape) ∘
          fun branch => guardedGridBranch branch) =
      (endpointGridBranches
        layer hleftWeight hrightWeight M N).map
          (fun branch => branch.obstruction.correction.erasedShape) by
    apply List.map_congr_left
    intro branch _hbranch
    simp only [Function.comp_apply,
      key_branch_index]]
  unfold
    branchFiberCardinality
  exact
    count_length_filter
      (fun branch => branch.obstruction.correction.erasedShape)
      word
      (endpointGridBranches
        layer hleftWeight hrightWeight M N)

/--
Scalar induction target for the arbitrary-cutoff Hall collector.

For each Hall shape, the finite sum of recursively expanded canonical guarded
branch contributions equals the number of actual endpoint crossing roots of
that shape.
-/
structure
    GMDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  branch_fiber_cardinality :
    ∀ M N word,
      guardedBranchSum
          raw M N word =
        branchFiberCardinality
          layer hleftWeight hrightWeight M N word

namespace
  GMDecomp

/--
Compile branchwise scalar identities to generated-program multiplicity
coalescing.
-/
noncomputable def
    guardedCoalescingDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GMDecomp
        layer hleftWeight hrightWeight) :
    GCDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  expanded_root_count M N word := by
    rw [
      count_guarded_erased,
      count_fiber_cardinality]
    exact decomposition.branch_fiber_cardinality M N word

/--
Compile branchwise scalar identities directly to endpoint interpolation.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GMDecomp
        layer hleftWeight hrightWeight) :=
  decomposition.guardedCoalescingDecomp
    |>.fiberProfileInterpolation

end
  GMDecomp

namespace
  GCDecomp

/--
Recover the explicit branchwise scalar identities from generated-program
multiplicity coalescing.
-/
noncomputable def
    guardedMultDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecomp
        layer hleftWeight hrightWeight) :
    GMDecomp
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  branch_fiber_cardinality M N word := by
    rw [←
      count_guarded_erased]
    rw [←
      count_fiber_cardinality]
    exact decomposition.expanded_root_count M N word

end
  GCDecomp

/--
Through cutoff four, the explicit branchwise scalar identities hold.
-/
noncomputable def
    branchwiseNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GMDecomp
      layer (by simp) (by simp) :=
  GCDecomp.guardedMultDecomp
    (multCoalescingFour
      layer hhigh raw)

end
  PBMult
end TCTex
end Submission

/-!
# Generated-parent alignment for nested polynomial-orbit crossings

The guarded raw-source branch attached to a concrete generated crossing has
two operational obstruction children.  This file identifies them with the
literal concrete child crossings used by the recursive collector and records
the inherited inverse-raw provenance and cutoff guards.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace NCAligna

open HACoeff
open
  RRPkt.POObstru
open
  CRAlign
open
  ITRec
open
  CNAlign
open CFCollec
open OCClos
open OCClos.DFTerm
open OCPartit
open
  RITrace
open
  ISLift

/-- Concrete parent pair used by the nested-left operational branch. -/
def nestedLeftCrossing
    {M N K : ℕ}
    (crossing : DFTerm M N K × DFTerm M N K) :
    DFTerm M N K × DFTerm M N K :=
  (crossing.1, crossing.1.correction crossing.2)

/-- Concrete parent pair used by the nested-right operational branch. -/
def nestedRightCrossing
    {M N K : ℕ}
    (crossing : DFTerm M N K × DFTerm M N K) :
    DFTerm M N K × DFTerm M N K :=
  (crossing.2, crossing.1.correction crossing.2)

/-- Inverse-raw provenance is closed under the nested-left child crossing. -/
lemma nested_left_generated
    {M N K : ℕ}
    {source : List (DFTerm M N K)}
    (crossing : DFTerm M N K × DFTerm M N K)
    (hparents :
      CGFrom source crossing.1 ∧
        CGFrom source crossing.2) :
    CGFrom source (nestedLeftCrossing crossing).1 ∧
      CGFrom source (nestedLeftCrossing crossing).2 := by
  exact
    ⟨hparents.1,
      CGFrom.correction hparents.1 hparents.2⟩

/-- Inverse-raw provenance is closed under the nested-right child crossing. -/
lemma nested_crossing_generated
    {M N K : ℕ}
    {source : List (DFTerm M N K)}
    (crossing : DFTerm M N K × DFTerm M N K)
    (hparents :
      CGFrom source crossing.1 ∧
        CGFrom source crossing.2) :
    CGFrom source (nestedRightCrossing crossing).1 ∧
      CGFrom source (nestedRightCrossing crossing).2 := by
  exact
    ⟨hparents.2,
      CGFrom.correction hparents.1 hparents.2⟩

/-- The generated-parent branch's nested-left obstruction is concrete. -/
@[simp]
lemma obstruction_branch_parents
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
    (gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight).obstruction.operationalNestedLeft =
        concreteCrossingObstruction (nestedLeftCrossing crossing) := by
  rw [obstruction_grid_parents]
  exact
    operational_nested_crossing
      crossing.1 crossing.2

/-- The generated-parent branch's nested-right obstruction is concrete. -/
@[simp]
lemma operational_branch_parents
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
    (gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight).obstruction.operationalNestedRight =
        concreteCrossingObstruction (nestedRightCrossing crossing) := by
  rw [obstruction_grid_parents]
  exact
    operational_concrete_obstruction
      crossing.1 crossing.2

/-- The generated-parent nested-left guard is the explicit concrete guard. -/
@[simp]
lemma branch_generated_parents
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
    (gridBranchParents
      hleftWeight hrightWeight crossing hparents
        hrootWeight).obstruction.operationalNestedLeft.weight
        leftWeight rightWeight =
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction (crossing.1.correction crossing.2)) := by
  rw [
    obstruction_branch_parents]
  simp [nestedLeftCrossing]

/-- The generated-parent nested-right guard is the explicit concrete guard. -/
@[simp]
lemma grid_branch_parents
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
    (gridBranchParents
      hleftWeight hrightWeight crossing hparents
        hrootWeight).obstruction.operationalNestedRight.weight
        leftWeight rightWeight =
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.2.correction (crossing.1.correction crossing.2)) := by
  rw [
    operational_branch_parents]
  simp [nestedRightCrossing]

/--
The nested-left guarded branch reuses the parent's left raw-source index.
-/
lemma generated_parents_crossing
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
    (hnestedWeight :
      decoratedFamilyWeight leftWeight rightWeight
        ((nestedLeftCrossing crossing).1.correction
          (nestedLeftCrossing crossing).2) < n) :
    (gridBranchParents
      hleftWeight hrightWeight
      (nestedLeftCrossing crossing)
      (nested_left_generated crossing hparents)
      hnestedWeight).leftIndex =
        (gridBranchParents
          hleftWeight hrightWeight crossing hparents hrootWeight).leftIndex := by
  apply orbit_key_injective
  simp [gridBranchParents, nestedLeftCrossing]

/--
The nested-left guarded branch uses the parent's correction-root index as its
right raw-source index.
-/
lemma parents_nested_crossing
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
    (hnestedWeight :
      decoratedFamilyWeight leftWeight rightWeight
        ((nestedLeftCrossing crossing).1.correction
          (nestedLeftCrossing crossing).2) < n) :
    (gridBranchParents
      hleftWeight hrightWeight
      (nestedLeftCrossing crossing)
      (nested_left_generated crossing hparents)
      hnestedWeight).rightIndex =
        guardedGridParents
          hleftWeight hrightWeight crossing hparents hrootWeight := by
  apply orbit_key_injective
  simp [gridBranchParents, nestedLeftCrossing]

/--
The nested-right guarded branch reuses the parent's right raw-source index.
-/
lemma grid_parents_crossing
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
    (hnestedWeight :
      decoratedFamilyWeight leftWeight rightWeight
        ((nestedRightCrossing crossing).1.correction
          (nestedRightCrossing crossing).2) < n) :
    (gridBranchParents
      hleftWeight hrightWeight
      (nestedRightCrossing crossing)
      (nested_crossing_generated crossing hparents)
      hnestedWeight).leftIndex =
        (gridBranchParents
          hleftWeight hrightWeight crossing hparents hrootWeight).rightIndex := by
  apply orbit_key_injective
  simp [gridBranchParents, nestedRightCrossing]

/--
The nested-right guarded branch uses the parent's correction-root index as its
right raw-source index.
-/
lemma branch_parents_crossing
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
    (hnestedWeight :
      decoratedFamilyWeight leftWeight rightWeight
        ((nestedRightCrossing crossing).1.correction
          (nestedRightCrossing crossing).2) < n) :
    (gridBranchParents
      hleftWeight hrightWeight
      (nestedRightCrossing crossing)
      (nested_crossing_generated crossing hparents)
      hnestedWeight).rightIndex =
        guardedGridParents
          hleftWeight hrightWeight crossing hparents hrootWeight := by
  apply orbit_key_injective
  simp [gridBranchParents, nestedRightCrossing]

end NCAligna
end TCTex
end Submission

/-!
# Scalar recurrences for guarded polynomial-orbit branches

The branchwise multiplicity boundary leaves a finite sum of recursive guarded
branch contributions.  This file exposes the scalar recurrence for one
contribution: a supported orbit obstruction contributes its repeated root
block, followed by the two higher-weight nested obstruction contributions
whose strict cutoff guards succeed.

This is the induction rule needed to compare symbolic repeated-block
collection with the cardinality of actual concrete endpoint crossings.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace PBRec

open
  RRPkt
open
  RRPkt.POObstru
open
  PBMult
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

/--
Multiplicity of one erased Hall shape in a recursively expanded supported
polynomial-orbit obstruction.
-/
noncomputable def
    profiledErasedCount
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
    (word : CWord HPAtom) :
    ℕ :=
  ((profiledOrbitExpansion
    hleftWeight hrightWeight O hsupport left right).trace M N |>.map
      fun index => (retainedOrbitKey index).erasedShape).count word

/--
One supported recursive branch contributes its repeated correction root plus
the two surviving higher-weight nested branches.
-/
lemma profiled_erased_count
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
    (word : CWord HPAtom) :
    profiledErasedCount
        hleftWeight hrightWeight O hsupport left right M N word =
      (if O.correction.erasedShape = word then
        left.multiplicity M N * right.multiplicity M N
      else
        0) +
      (if hleft :
          O.operationalNestedLeft.weight leftWeight rightWeight < n then
        profiledErasedCount
          hleftWeight hrightWeight O.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight O hsupport hleft)
          left (left.correction O right) M N word
      else
        0) +
      (if hright :
          O.operationalNestedRight.weight leftWeight rightWeight < n then
        profiledErasedCount
          hleftWeight hrightWeight O.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight O hsupport hright)
          right (left.correction O right) M N word
      else
        0) := by
  rw [profiledErasedCount,
    trace_profiled_expansion,
    List.map_append, List.map_append, List.count_append, List.count_append,
    List.map_replicate,
    MPFam.retained_key_index]
  by_cases hroot : O.correction.erasedShape = word
  · subst word
    split <;> split <;>
      simp [profiledErasedCount, *]
  · split <;> split <;>
      simp [profiledErasedCount,
        List.count_replicate, *]

namespace POBranch

/--
Multiplicity of one erased Hall shape in one profiled obstruction branch.
-/
noncomputable def erasedShapeCount
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    ℕ :=
  profiledErasedCount
    hleftWeight hrightWeight branch.obstruction branch.support
      branch.left branch.right M N word

/--
The scalar recurrence specialized to a packaged profiled branch.
-/
lemma erased_shape_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (branch :
      POBranch
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    POBranch.erasedShapeCount
        branch M N word =
      (if branch.obstruction.correction.erasedShape = word then
        branch.left.multiplicity M N * branch.right.multiplicity M N
      else
        0) +
      (if hleft :
          branch.obstruction.operationalNestedLeft.weight
              leftWeight rightWeight < n then
        profiledErasedCount
          hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight branch.obstruction branch.support hleft)
          branch.left
          (branch.left.correction branch.obstruction branch.right)
          M N word
      else
        0) +
      (if hright :
          branch.obstruction.operationalNestedRight.weight
              leftWeight rightWeight < n then
        profiledErasedCount
          hleftWeight hrightWeight branch.obstruction.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight branch.obstruction branch.support hright)
          branch.right
          (branch.left.correction branch.obstruction branch.right)
          M N word
      else
        0) := by
  exact
    profiled_erased_count
      hleftWeight hrightWeight branch.obstruction branch.support
        branch.left branch.right M N word

end POBranch

namespace IOBranch

/--
Multiplicity of one erased Hall shape in a recursively expanded raw-source
guarded branch.
-/
noncomputable def erasedShapeCount
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
    (word : CWord HPAtom) :
    ℕ :=
  POBranch.erasedShapeCount
    (branch.profiledObstructionBranch raw) M N word

/--
The raw-source branch count is exactly the mapped finite-index trace count
used in the branchwise finite sum.
-/
lemma erased_count_key
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
    (word : CWord HPAtom) :
    IOBranch.erasedShapeCount
        raw branch M N word =
      ((branch.indexTrace raw M N).map fun index =>
        (retainedOrbitKey index).erasedShape).count word := by
  rfl

/--
The scalar recurrence specialized to a raw-source guarded branch.
-/
lemma erased_shape_count
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
    (word : CWord HPAtom) :
    IOBranch.erasedShapeCount
        raw branch M N word =
      (if branch.obstruction.correction.erasedShape = word then
        (raw.multiplicityProfileFamily branch.leftIndex).multiplicity M N *
          (raw.multiplicityProfileFamily branch.rightIndex).multiplicity M N
      else
        0) +
      (if hleft :
          branch.obstruction.operationalNestedLeft.weight
              leftWeight rightWeight < n then
        profiledErasedCount
          hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
          (operational_left_supported
            hleftWeight hrightWeight branch.obstruction branch.support hleft)
          (raw.multiplicityProfileFamily branch.leftIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          M N word
      else
        0) +
      (if hright :
          branch.obstruction.operationalNestedRight.weight
              leftWeight rightWeight < n then
        profiledErasedCount
          hleftWeight hrightWeight branch.obstruction.operationalNestedRight
          (operational_nested_supported
            hleftWeight hrightWeight branch.obstruction branch.support hright)
          (raw.multiplicityProfileFamily branch.rightIndex)
          ((raw.multiplicityProfileFamily branch.leftIndex).correction
            branch.obstruction
            (raw.multiplicityProfileFamily branch.rightIndex))
          M N word
      else
        0) := by
  exact
    POBranch.erased_shape_count
      (branch.profiledObstructionBranch raw) M N word

end IOBranch

/--
The branchwise guarded-grid sum is the sum of the scalar raw-source branch
counts governed by the recurrence above.
-/
lemma
    guarded_idx_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    guardedBranchSum
        raw M N word =
      ((guardedSupportedBranches
        n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
          IOBranch.erasedShapeCount
            (multiplicityProfileShape
              raw)
            branch M N word).sum := by
  rfl

end
  PBRec
end TCTex
end Submission

/-!
# Scalar recurrences for concrete retained-correction schedules

The symbolic guarded branches satisfy a root-plus-two-nested-branches scalar
recurrence.  The provenance-certified concrete endpoint schedule has the
matching recursive shape on the collector side.  This file equips every
concrete schedule program with its erased-shape multiplicity, proves the
constructor recurrences, and identifies that multiplicity with a filtered
count of stored concrete parent crossings.

At the endpoint, the filtered crossing-root cardinality used by the branchwise
coalescing boundary is exactly this recursively defined concrete schedule
multiplicity.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace RMRec

open
  HACoeff
open
  CRAlign
open
  PBMult
open
  PMCoales
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
  CRLayer
open
  OCPartit
open
  RTProgra
open
  SEAlg

namespace RSPrograa

/--
Multiplicity of one erased Hall shape in a concrete retained-correction
schedule.
-/
def erasedShapeMultiplicity
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    (word : CWord HPAtom) :
    ℕ :=
  program.shapeTraceProgram.trace.count word

/-- The empty concrete schedule has zero shape multiplicity. -/
@[simp]
lemma erased_multiplicity_empty
    {M N K n leftWeight rightWeight : ℕ}
    (word : CWord HPAtom) :
    erasedShapeMultiplicity
        (RSPrograa.empty :
          RSPrograa
            (M := M) (N := N) (K := K) n leftWeight rightWeight)
        word =
      0 := by
  rfl

/-- Concrete schedule concatenation adds shape multiplicities. -/
@[simp]
lemma erased_multiplicity_append
    {M N K n leftWeight rightWeight : ℕ}
    (left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    (word : CWord HPAtom) :
    erasedShapeMultiplicity
        (RSPrograa.append left right)
        word =
      erasedShapeMultiplicity left word +
        erasedShapeMultiplicity right word := by
  simp [erasedShapeMultiplicity,
    RSPrograa.shapeTraceProgram,
    ESProgra.trace_append,
    List.count_append]

/--
A retained concrete crossing contributes its left schedule, one root, and its
right schedule.
-/
@[simp]
lemma erased_multiplicity_retained
    {M N K n leftWeight rightWeight : ℕ}
    (left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    (crossedLeft crossedRight : DFTerm M N K)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n)
    (word : CWord HPAtom) :
    erasedShapeMultiplicity
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        word =
      erasedShapeMultiplicity left word +
        ([((concreteCrossingObstruction
          (crossedLeft, crossedRight)).correction.erasedShape)].count word) +
        erasedShapeMultiplicity right word := by
  simp [erasedShapeMultiplicity,
    RSPrograa.shapeTraceProgram,
    ESProgra.trace_retained,
    List.count_append,
    List.count_cons,
    ROAggreg.polynomialOrbitKey]
  omega

/--
Concrete schedule multiplicity is the filtered cardinality of stored parent
crossings whose retained correction root has the requested erased shape.
-/
lemma erased_filter_crossings
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    (word : CWord HPAtom) :
    erasedShapeMultiplicity program word =
      (program.crossings.filter fun crossing =>
        decide
          ((concreteCrossingObstruction
            crossing).correction.erasedShape = word)).length := by
  unfold erasedShapeMultiplicity
  rw [←
    RSPrograa.mapcor_erase_polyo]
  unfold polynomialOrbitObstructions
  rw [List.map_map]
  simpa only [Function.comp_apply] using
    count_length_filter
      (fun crossing =>
        (concreteCrossingObstruction
          crossing).correction.erasedShape)
      word program.crossings

end RSPrograa

/--
The endpoint crossing-root cardinality in the branchwise symbolic boundary is
the erased-shape multiplicity of the provenance-certified recursive concrete
schedule.
-/
lemma
    endpoint_guarded_mult
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    branchFiberCardinality
        layer hleftWeight hrightWeight M N word =
      RSPrograa.erasedShapeMultiplicity
        (endpointScheduleProgram
          layer M N).program
        word := by
  rw [←
    count_fiber_cardinality]
  rw [
    endpoint_guarded_program]
  rfl

/--
Endpoint crossing-root cardinality is equivalently the filtered cardinality
of the parent crossings stored by the provenance-certified concrete schedule.
-/
lemma
    endpoint_filter_crossings
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    branchFiberCardinality
        layer hleftWeight hrightWeight M N word =
      (((endpointScheduleProgram
        layer M N).program.crossings.filter fun crossing =>
          decide
            ((concreteCrossingObstruction
              crossing).correction.erasedShape = word)).length) := by
  rw [
    endpoint_guarded_mult,
    RSPrograa.erased_filter_crossings]

end
  RMRec
end TCTex
end Submission

/-!
# Induction kernel for symbolic-to-concrete retained-correction multiplicities

The symbolic guarded-grid side is a finite sum of recursively expanded raw
branches.  The concrete collector side is the erased-shape multiplicity of its
provenance-certified recursive schedule.  Both sides now have explicit
root-plus-nested-branches recurrences.

This file isolates the remaining arbitrary-cutoff theorem as their direct
scalar comparison.  Supplying that induction kernel compiles immediately to
the branchwise coalescing decomposition and hence to endpoint interpolation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace MIKern

open
  PBRec
open
  PBMult
open
  RMRec
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  CRLayer
open
  FIProf
open
  PGSrc
open
  ISLift

/--
Finite sum of the recurrence-governed erased-shape multiplicities of all
canonical guarded raw-source branches.
-/
noncomputable def
    guardedBranchRecurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    ℕ :=
  ((guardedSupportedBranches
      n leftWeight rightWeight hleftWeight hrightWeight).map fun branch =>
        IOBranch.erasedShapeCount
          (multiplicityProfileShape
            raw)
          branch M N word).sum

/--
The branchwise finite-index sum is exactly the sum of the scalar branch
recurrences.
-/
lemma
    guarded_idx_erased
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    guardedBranchSum
        raw M N word =
      guardedBranchRecurrence
        raw M N word := by
  exact
    guarded_idx_count
      raw M N word

/--
Direct scalar induction target for the arbitrary-cutoff symbolic Hall
collector.

For every input multiplicity pair and Hall shape, the sum of recurrence-governed
symbolic raw branches equals the erased-shape multiplicity of the concrete
provenance schedule emitted by the cutoff-full collector.
-/
structure
    GMInduct
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  branch_schedule_multiplicity :
    ∀ M N word,
      guardedBranchRecurrence
          raw M N word =
        RSPrograa.erasedShapeMultiplicity
          (endpointScheduleProgram
            layer M N).program
          word

namespace
  GMInduct

/--
Compile the direct recurrence induction kernel to the branchwise scalar
coalescing decomposition.
-/
noncomputable def
    guardedMultDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMInduct
        layer hleftWeight hrightWeight) :
    GMDecomp
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_fiber_cardinality M N word := by
    rw [
      guarded_idx_erased,
      endpoint_guarded_mult]
    exact kernel.branch_schedule_multiplicity M N word

/--
Compile the direct recurrence induction kernel to endpoint interpolation.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMInduct
        layer hleftWeight hrightWeight) :=
  kernel.guardedMultDecomp
    |>.fiberProfileInterpolation

end
  GMInduct

namespace
  GMDecomp

/--
Recover the direct recurrence induction kernel from branchwise scalar
coalescing.
-/
noncomputable def
    scheduleMultInduction
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GMDecomp
        layer hleftWeight hrightWeight) :
    GMInduct
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  branch_schedule_multiplicity M N word := by
    rw [←
      guarded_idx_erased]
    rw [←
      endpoint_guarded_mult]
    exact decomposition.branch_fiber_cardinality M N word

end
  GMDecomp

/--
Through cutoff four, the direct recurrence induction kernel holds.
-/
noncomputable def
    inductionNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GMInduct
      layer (by simp) (by simp) :=
  GMDecomp.scheduleMultInduction
    (branchwiseNFour
      layer hhigh raw)

end
  MIKern
end TCTex
end Submission

/-!
# Recursive compilation relations for concrete retained-correction schedules

The traced cutoff-full collector relations live in `Prop`, so Lean does not
permit eliminating a derivation directly into a schedule program in `Type`.
Nevertheless, the derivations expose the exact recursive shape of the concrete
schedule.  This file records that shape as constructor-level compilation
relations in `Prop`.

Every traced insertion and collection derivation admits a recursively compiled
schedule.  A compiled schedule emits exactly the retained corrections recorded
by its derivation, and therefore its erased-shape multiplicity is exactly the
corresponding correction-trace count.  At the selected natural endpoint this
gives a concrete schedule with an explicit recursive compilation witness,
rather than only an existentially selected trace witness.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  PRCompb

open
  HACoeff
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
  OCPartit
open
  RTProgra
open
  SEAlg

namespace RSPrograa

/--
Constructor-level compilation of one traced cutoff insertion into a concrete
retained-correction schedule.
-/
inductive CompilesInsertsCorrections
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    {L R corrections : List (DFTerm M N K)} →
      {A : DFTerm M N K} →
        CICorrec
          n leftWeight rightWeight L A R corrections →
          RSPrograa
            (M := M) (N := N) (K := K) n leftWeight rightWeight →
            Prop where
  | nil
      (A : DFTerm M N K) :
      CompilesInsertsCorrections
        n leftWeight rightWeight
        (.nil A)
        .empty
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hBA : B.decorated.collectorLe A.decorated) :
      CompilesInsertsCorrections
        n leftWeight rightWeight
        (.append P B A hBA)
        .empty
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
          n leftWeight rightWeight Q A R rightCorrections)
      {left right :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight}
      (hleft :
        CompilesInsertsCorrections
          n leftWeight rightWeight hcorrection left)
      (hright :
        CompilesInsertsCorrections
          n leftWeight rightWeight hinsert right) :
      CompilesInsertsCorrections
        n leftWeight rightWeight
        (.retained P B A hAB hweight hcorrection hinsert)
        (.retained left B A hweight right)
  | residual
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.collectorBefore B.decorated)
      (hweight :
        n ≤ decoratedFamilyWeight leftWeight rightWeight (B.correction A))
      {R corrections : List (DFTerm M N K)}
      (hinsert :
        CICorrec
          n leftWeight rightWeight P A R corrections)
      {program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight}
      (hprogram :
        CompilesInsertsCorrections
          n leftWeight rightWeight hinsert program) :
      CompilesInsertsCorrections
        n leftWeight rightWeight
        (.residual P B A hAB hweight hinsert)
        program

/--
Constructor-level compilation of one traced cutoff collection into a concrete
retained-correction schedule.
-/
inductive CompilesCollectsCorrections
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) :
    {L R corrections : List (DFTerm M N K)} →
      CCCorrec
        n leftWeight rightWeight L R corrections →
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight →
          Prop where
  | nil :
      CompilesCollectsCorrections
        n leftWeight rightWeight
        .nil
        .empty
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
          n leftWeight rightWeight C A R insertCorrections)
      {collectProgram insertProgram :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight}
      (hcollectProgram :
        CompilesCollectsCorrections
          n leftWeight rightWeight hcollect collectProgram)
      (hinsertProgram :
        CompilesInsertsCorrections
          n leftWeight rightWeight hinsert insertProgram) :
      CompilesCollectsCorrections
        n leftWeight rightWeight
        (.retained P A hweight hcollect hinsert)
        (.append collectProgram insertProgram)
  | residual
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hweight :
        n ≤ decoratedFamilyWeight leftWeight rightWeight A)
      {C corrections : List (DFTerm M N K)}
      (hcollect :
        CCCorrec
          n leftWeight rightWeight P C corrections)
      {program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight}
      (hprogram :
        CompilesCollectsCorrections
          n leftWeight rightWeight hcollect program) :
      CompilesCollectsCorrections
        n leftWeight rightWeight
        (.residual P A hweight hcollect)
        program

/-- Every traced insertion derivation admits a constructor-level compilation. -/
lemma compiles_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    ∃ program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight,
      CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program := by
  induction hinsert with
  | nil A =>
      exact ⟨.empty, .nil A⟩
  | append P B A hBA =>
      exact ⟨.empty, .append P B A hBA⟩
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      rcases ihcorrection with ⟨left, hleft⟩
      rcases ihinsert with ⟨right, hright⟩
      exact
        ⟨.retained left B A hweight right,
          .retained P B A hAB hweight hcorrection hinsert hleft hright⟩
  | residual P B A hAB hweight hinsert ihinsert =>
      rcases ihinsert with ⟨program, hprogram⟩
      exact
        ⟨program, .residual P B A hAB hweight hinsert hprogram⟩

/-- Every traced collection derivation admits a constructor-level compilation. -/
lemma compiles_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    ∃ program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight,
      CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program := by
  induction hcollect with
  | nil =>
      exact ⟨.empty, .nil⟩
  | retained P A hweight hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨collectProgram, hcollectProgram⟩
      rcases
          compiles_inserts_corrections hinsert with
        ⟨insertProgram, hinsertProgram⟩
      exact
        ⟨.append collectProgram insertProgram,
          .retained P A hweight hcollect hinsert
            hcollectProgram hinsertProgram⟩
  | residual P A hweight hcollect ihcollect =>
      rcases ihcollect with ⟨program, hprogram⟩
      exact
        ⟨program, .residual P A hweight hcollect hprogram⟩

/-- A recursively compiled insertion schedule emits its recorded corrections. -/
lemma correction_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      CompilesInsertsCorrections
        n leftWeight rightWeight
        (L := L) (R := R) (corrections := corrections) (A := A)
        hinsert
        program) :
    program.correctionTrace = corrections := by
  induction hcompile with
  | nil A =>
      rfl
  | append P B A hBA =>
      rfl
  | retained P B A hAB hweight hcorrection hinsert
      hleft hright ihleft ihright =>
      simp [ihleft, ihright]
  | residual P B A hAB hweight hinsert hprogram ihprogram =>
      exact ihprogram

/-- A recursively compiled collection schedule emits its recorded corrections. -/
lemma correction_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      CompilesCollectsCorrections
        n leftWeight rightWeight
        (L := L) (R := R) (corrections := corrections)
        hcollect
        program) :
    program.correctionTrace = corrections := by
  induction hcompile with
  | nil =>
      rfl
  | retained P A hweight hcollect hinsert
      hcollectProgram hinsertProgram ihcollect =>
      simp [ihcollect,
        correction_inserts_corrections
          hinsertProgram]
  | residual P A hweight hcollect hprogram ihprogram =>
      exact ihprogram

/--
Multiplicity in a recursively compiled insertion schedule is the erased-shape
count of the retained correction trace recorded by the derivation.
-/
lemma mult_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program)
    (word : CWord HPAtom) :
    erasedShapeMultiplicity program word =
      (erasedShapeTrace corrections).count word := by
  unfold erasedShapeMultiplicity
  rw [trace_erased_shape,
    correction_inserts_corrections
      hcompile]

/--
Multiplicity in a recursively compiled collection schedule is the erased-shape
count of the retained correction trace recorded by the derivation.
-/
lemma mult_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program)
    (word : CWord HPAtom) :
    erasedShapeMultiplicity program word =
      (erasedShapeTrace corrections).count word := by
  unfold erasedShapeMultiplicity
  rw [trace_erased_shape,
    correction_collects_corrections
      hcompile]

end RSPrograa

/--
One selected endpoint schedule together with its constructor-level recursive
compilation witness.
-/
structure RecursivelyCompiledConcrete
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) where
  program :
    RSPrograa
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      n leftWeight rightWeight
  compiles :
    RSPrograa.CompilesCollectsCorrections
        n leftWeight rightWeight
        (endpointCorrectionInventory layer M N
          |>.family_collects_corrections)
        program

/-- Select a recursively compiled concrete endpoint schedule. -/
noncomputable def recursivelyCompiledConcrete
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    RecursivelyCompiledConcrete
      layer M N :=
  let hcollect :=
    (endpointCorrectionInventory layer M N)
      |>.family_collects_corrections
  let hexists :=
    RSPrograa.compiles_collects_corrections
      hcollect
  {
    program := Classical.choose hexists
    compiles := Classical.choose_spec hexists
  }

/-- The recursively compiled endpoint schedule emits the selected inventory. -/
lemma endpoint_recursively_compiled
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    (recursivelyCompiledConcrete
      layer M N).program.correctionTrace =
        (endpointCorrectionInventory layer M N).corrections :=
  RSPrograa.correction_collects_corrections
      (recursivelyCompiledConcrete
        layer M N).compiles

/--
The recursively compiled endpoint schedule has the selected retained
correction erased-shape trace.
-/
lemma endpointRecursivelyProgram
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    (recursivelyCompiledConcrete
      layer M N).program.shapeTraceProgram.trace =
        selectedErasedShape layer M N := by
  rw [
    RSPrograa.trace_erased_shape,
    endpoint_recursively_compiled]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/--
The recursively compiled endpoint schedule and the earlier provenance-selected
endpoint schedule agree after erased-shape projection.
-/
lemma recursively_compiled_generated
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    (recursivelyCompiledConcrete
      layer M N).program.shapeTraceProgram.trace =
        (endpointScheduleProgram
          layer M N).program.shapeTraceProgram.trace := by
  rw [
    endpointRecursivelyProgram,
    RSPrograa.trace_erased_shape,
    (endpointScheduleProgram
      layer M N).correctionTrace_eq]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/--
Endpoint multiplicity can be computed from a schedule carrying an explicit
constructor-level recursive compilation witness.
-/
lemma recursively_compiled_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    RSPrograa.erasedShapeMultiplicity
        (recursivelyCompiledConcrete
          layer M N).program word =
      (selectedErasedShape layer M N).count word := by
  rw [←
    endpointRecursivelyProgram]
  rfl

end
  PRCompb
end TCTex
end Submission

/-!
# Claim 5 from the generated-concrete schedule multiplicity induction kernel

The symbolic-to-concrete scalar induction kernel supplies endpoint recipe-shape
fiber interpolation.  At root weights, an all-integral signed lift of those
packets and the existing local factor-normalization hypothesis construct the
Claim 5 coordinate polynomials.

This file states that downstream constructor directly.  It also restates the
all-integral lift as the corresponding truncated signed recollection law.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open
  MIKern
open
  FPInterp
open
  CRLayer
open
  CFSubsti

namespace
  MIKern
namespace
  GMInduct

/--
The remaining signed extension needed after symbolic-to-concrete multiplicity
coalescing.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GMInduct
        layer (by simp) (by simp)) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d) kernel.fiberProfileInterpolation

/--
The remaining signed recollection law for the packets obtained from the
symbolic-to-concrete multiplicity induction kernel.
-/
def SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GMInduct
        layer (by simp) (by simp)) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((EFInterp.truncNaturalPacket.{u}
        (d := d)
        kernel.fiberProfileInterpolation).packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
The truncated signed recollection law supplies the all-integral lift.
-/
def allLiftSatisfies
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GMInduct
        layer (by simp) (by simp))
    (hlistEval :
      GMInduct.SatisfiesTruncEval.{u}
        (d := d) kernel) :
    GMInduct.AILift.{u}
      (d := d) kernel where
  listEval_eq :=
    hlistEval

/--
The all-integral lift recovers the truncated signed recollection law.
-/
lemma satisfies_trunc_all
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GMInduct
        layer (by simp) (by simp))
    (lift :
      GMInduct.AILift.{u}
        (d := d) kernel) :
    GMInduct.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  lift.listEval_eq

/--
For the multiplicity induction kernel, the remaining signed extension is
exactly its truncated signed recollection law.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GMInduct
        layer (by simp) (by simp)) :
    GMInduct.SatisfiesTruncEval.{u}
        (d := d) kernel ↔
      GMInduct.AILift.{u}
        (d := d) kernel :=
  ⟨kernel.allLiftSatisfies,
    kernel.satisfies_trunc_all⟩

end
  GMInduct
end
  MIKern

namespace TSInput

/--
The generated-concrete schedule multiplicity induction kernel, its signed
lift, singleton recollections, and graded Hall bases construct the Claim 5
coordinate polynomials.
-/
theorem
    generatedInductionLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GMInduct
        layer (by simp) (by simp))
    (lift :
      GMInduct.AILift.{u}
        (d := d) kernel)
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
    hn H hH kernel.fiberProfileInterpolation
      lift hsourceSupported factorNormalization hinputWeight

/--
The direct truncated signed recollection law is an equivalent constructor
input for the Claim 5 coordinate polynomials.
-/
theorem
    coordInductionTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GMInduct
        layer (by simp) (by simp))
    (hlistEval :
      GMInduct.SatisfiesTruncEval.{u}
        (d := d) kernel)
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
  input.generatedInductionLift
    hn H hH kernel
      (kernel.allLiftSatisfies hlistEval)
        hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Structural coalescing for symbolic and concrete retained-correction schedules

The scalar induction kernel compares the multiplicity of every Hall shape in
the guarded symbolic scheduler with the corresponding multiplicity in the
concrete cutoff-full collector schedule.  This file supplies a recursive
language for proving that comparison.

The structural coalescing relation permits constructorwise recursion together
with the harmless append normalizations needed to reconcile differently
grouped scheduler blocks.  Every rule preserves trace multiplicities.  A
structural coalescing proof against the provenance-certified endpoint schedule
therefore compiles directly to the scalar induction kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  RPCoales

open
  HACoeff
open
  PBMult
open
  MIKern
open
  RMRec
open
  PMCoales
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CPProven
open
  CRLayer
open
  FIProf
open
  OCPartit
open
  PGSrc
open
  ISLift
open
  RTProgra
open
  RTProgra.ESProgra
open
  GGErased
open
  GRProgra
open
  REProgra
open
  SEAlg

namespace EMCoales

/--
Recursive multiplicity-preserving rewrites between erased scheduler programs.

The retained constructor is respected recursively.  The append laws permit
independent scheduler blocks to be regrouped, reordered, and stripped of empty
blocks.  Splitting a retained node exposes its singleton root block, which is
the form emitted by the symbolic repeated-root scheduler.
-/
inductive Rel :
    ESProgra →
      ESProgra → Prop
  | refl
      (program : ESProgra) :
      Rel program program
  | symm
      {left right : ESProgra}
      (h : Rel left right) :
      Rel right left
  | trans
      {first middle last : ESProgra}
      (hfirst : Rel first middle)
      (hlast : Rel middle last) :
      Rel first last
  | append
      {left left' right right' : ESProgra}
      (hleft : Rel left left')
      (hright : Rel right right') :
      Rel
        (ESProgra.append left right)
        (ESProgra.append left' right')
  | retained
      {left left' right right' : ESProgra}
      (shape : CWord HPAtom)
      (hleft : Rel left left')
      (hright : Rel right right') :
      Rel
        (ESProgra.retained left shape right)
        (ESProgra.retained left' shape right')
  | append_empty_left
      (program : ESProgra) :
      Rel
        (ESProgra.append
          ESProgra.empty program)
        program
  | append_empty_right
      (program : ESProgra) :
      Rel
        (ESProgra.append program
          ESProgra.empty)
        program
  | append_assoc
      (first middle last : ESProgra) :
      Rel
        (ESProgra.append
          (ESProgra.append first middle)
          last)
        (ESProgra.append first
          (ESProgra.append middle last))
  | append_comm
      (left right : ESProgra) :
      Rel
        (ESProgra.append left right)
        (ESProgra.append right left)
  | retained_split
      (left right : ESProgra)
      (shape : CWord HPAtom) :
      Rel
        (ESProgra.retained left shape right)
        (ESProgra.append left
          (ESProgra.append
            (ESProgra.retained
              ESProgra.empty shape
              ESProgra.empty)
            right))

namespace Rel

/-- Structural coalescing preserves the multiset of emitted Hall shapes. -/
lemma trace_perm
    {left right : ESProgra}
    (h : Rel left right) :
    List.Perm left.trace right.trace := by
  induction h with
  | refl program =>
      exact List.Perm.refl program.trace
  | symm h ih =>
      exact ih.symm
  | trans hfirst hlast ihfirst ihlast =>
      exact ihfirst.trans ihlast
  | append hleft hright ihleft ihright =>
      simpa only [trace_append] using List.Perm.append ihleft ihright
  | retained shape hleft hright ihleft ihright =>
      simpa only [trace_retained] using
        List.Perm.append
          (List.Perm.append ihleft (List.Perm.refl [shape]))
          ihright
  | append_empty_left program =>
      simpa only [trace_append, trace_empty, List.nil_append] using
        List.Perm.refl program.trace
  | append_empty_right program =>
      simpa only [trace_append, trace_empty, List.append_nil] using
        List.Perm.refl program.trace
  | append_assoc first middle last =>
      simpa only [trace_append, List.append_assoc] using
        List.Perm.refl (first.trace ++ middle.trace ++ last.trace)
  | append_comm left right =>
      simpa only [trace_append] using
        (List.perm_append_comm :
          List.Perm (left.trace ++ right.trace) (right.trace ++ left.trace))
  | retained_split left right shape =>
      simpa only [trace_append, trace_retained, trace_empty, List.nil_append,
        List.append_nil, List.append_assoc] using
          List.Perm.refl (left.trace ++ [shape] ++ right.trace)

/-- Structural coalescing preserves each individual Hall-shape multiplicity. -/
lemma count_eq
    {left right : ESProgra}
    (h : Rel left right)
    (word : CWord HPAtom) :
    left.trace.count word = right.trace.count word :=
  h.trace_perm.count_eq word

/-- Pointwise structural coalescing lifts through scheduler concatenation. -/
lemma schedulerConcat
    {left right : List ESProgra}
    (h : List.Forall₂ Rel left right) :
    Rel
      (ESProgra.schedulerConcat left)
      (ESProgra.schedulerConcat right) := by
  induction h with
  | nil =>
      exact Rel.refl
        ESProgra.empty
  | cons hhead htail ih =>
      exact Rel.append hhead ih

/-- A program with empty trace structurally coalesces to the empty program. -/
lemma empty_nil
    (program : ESProgra)
    (htrace : program.trace = []) :
    Rel program
      ESProgra.empty := by
  induction program with
  | empty =>
      exact Rel.refl
        ESProgra.empty
  | append left right ihleft ihright =>
      have hchildren :
          left.trace = [] ∧ right.trace = [] := by
        simpa only [trace_append, List.append_eq_nil_iff] using htrace
      exact
        (Rel.append
          (ihleft hchildren.1) (ihright hchildren.2)).trans
            (Rel.append_empty_left
              ESProgra.empty)
  | retained left shape right ihleft ihright =>
      simp only [trace_retained, List.append_eq_nil_iff,
        List.cons_ne_nil, and_false] at htrace
      exact htrace.1.elim

/-- The empty program structurally coalesces to every program with empty trace. -/
lemma empty_trace_nil
    (program : ESProgra)
    (htrace : program.trace = []) :
    Rel ESProgra.empty
      program :=
  (empty_nil program htrace).symm

end Rel

end EMCoales

/--
The symbolic scheduler structurally coalesces with a concrete retained
correction schedule when it coalesces with the schedule's shape erasure.
-/
def MCSched
    {M N K n leftWeight rightWeight : ℕ}
    (symbolic : ESProgra)
    (concrete :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    Prop :=
  EMCoales.Rel symbolic
    concrete.shapeTraceProgram

namespace MCSched

open EMCoales

/-- Every concrete schedule structurally coalesces with its own erasure. -/
lemma of_erasure
    {M N K n leftWeight rightWeight : ℕ}
    (concrete :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    MCSched
      concrete.shapeTraceProgram concrete :=
  Rel.refl concrete.shapeTraceProgram

/-- The empty symbolic and concrete schedules structurally coalesce. -/
lemma empty
    {M N K n leftWeight rightWeight : ℕ} :
    MCSched
      ESProgra.empty
      (RSPrograa.empty :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight) := by
  exact Rel.refl
    ESProgra.empty

/-- Structurally coalescing symbolic blocks lift across concrete append. -/
lemma append
    {M N K n leftWeight rightWeight : ℕ}
    {symbolicLeft symbolicRight : ESProgra}
    {concreteLeft concreteRight :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hleft :
      MCSched
        symbolicLeft concreteLeft)
    (hright :
      MCSched
        symbolicRight concreteRight) :
    MCSched
      (ESProgra.append
        symbolicLeft symbolicRight)
      (RSPrograa.append
        concreteLeft concreteRight) := by
  exact Rel.append hleft hright

/-- A symbolic retained root aligns with one concrete retained crossing. -/
lemma retained
    {M N K n leftWeight rightWeight : ℕ}
    {symbolicLeft symbolicRight : ESProgra}
    {concreteLeft concreteRight :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (crossedLeft crossedRight :
      DFTerm M N K)
    (hweight :
      decoratedFamilyWeight
        leftWeight rightWeight (crossedLeft.correction crossedRight) < n)
    (hleft :
      MCSched
        symbolicLeft concreteLeft)
    (hright :
      MCSched
        symbolicRight concreteRight) :
    MCSched
      (ESProgra.retained symbolicLeft
        (crossedLeft.correction crossedRight).family.recipe.erasedShape
        symbolicRight)
      (RSPrograa.retained concreteLeft
        crossedLeft crossedRight hweight concreteRight) := by
  exact Rel.retained
    (crossedLeft.correction crossedRight).family.recipe.erasedShape
      hleft hright

/-- Normalize the symbolic side before aligning it with a concrete schedule. -/
lemma normalize_left
    {M N K n leftWeight rightWeight : ℕ}
    {symbolic symbolic' : ESProgra}
    {concrete :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hnormalize :
      EMCoales.Rel
        symbolic symbolic')
    (hcoalesce :
      MCSched
        symbolic' concrete) :
    MCSched
      symbolic concrete :=
  hnormalize.trans hcoalesce

/-- Structural alignment with a concrete schedule preserves Hall-shape counts. -/
lemma count_erased_multiplicity
    {M N K n leftWeight rightWeight : ℕ}
    {symbolic : ESProgra}
    {concrete :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcoalesce :
      MCSched
        symbolic concrete)
    (word : CWord HPAtom) :
    symbolic.trace.count word =
      RSPrograa.erasedShapeMultiplicity
        concrete word :=
  hcoalesce.count_eq word

end MCSched

/--
Constructor-level arbitrary-cutoff target.

Instead of postulating a family of endpoint cardinality equalities, this
kernel asks for a recursive structural coalescing derivation between the
symbolic scheduler program and the provenance-certified concrete collector
schedule.
-/
structure
    GSCoales
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  program_coalesces_schedule :
    ∀ M N,
      MCSched
        (guardedSchedulerProgram
          (multiplicityProfileShape
            raw)
          M N)
        (endpointScheduleProgram
          layer M N).program

namespace
  GSCoales

/--
Compile constructor-level structural coalescing to the scalar schedule
multiplicity induction kernel.
-/
noncomputable def
    scheduleMultInduction
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSCoales
        layer hleftWeight hrightWeight) :
    GMInduct
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_schedule_multiplicity M N word := by
    rw [←
      guarded_idx_erased]
    rw [←
      count_guarded_erased]
    rw [
      (idxSchedulerProgram
        kernel.raw M N).count_eq word]
    exact
      (kernel.program_coalesces_schedule M N)
        |>.count_erased_multiplicity word

/-- Compile constructor-level structural coalescing directly to interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSCoales
        layer hleftWeight hrightWeight) :=
  kernel.scheduleMultInduction
    |>.fiberProfileInterpolation

end
  GSCoales

/-- Through cutoff four, the constructor-level structural kernel is available. -/
noncomputable def
    coalescingNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GSCoales
      layer (by simp) (by simp) where
  raw :=
    raw
  program_coalesces_schedule M N := by
    have hconcrete :
        ((endpointScheduleProgram
          layer M N).program.shapeTraceProgram).trace = [] := by
      rw [
        GGProgra.programEndpointSchedule,
        selected_nil_four
          layer hhigh M N]
    unfold
      guardedSchedulerProgram
    rw [
      branches_nil_four
        (by simp) (by simp) hhigh]
    exact
      EMCoales.Rel.empty_trace_nil
        _ hconcrete

end
  RPCoales
end TCTex
end Submission

/-!
# Provenance and occurrence synchronization for recursively compiled schedules

The constructor-level compilation relation remembers how a traced cutoff-full
collector derivation builds its concrete retained-correction schedule.  This
file proves that recursive compilation preserves generated-parent provenance
and packages a selected endpoint schedule with:

* its constructor-level compilation witness;
* inverse-raw provenance for every retained concrete crossing;
* the cutoff-aware occurrence run from the same endpoint collector derivation.

This is the concrete collector object needed for an arbitrary-cutoff symbolic
Hall collector induction.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  RCProven

universe u

open scoped commutatorElement

open
  HACoeff
open
  CRProgra
open
  CPProven
open
  TOSync
open
  PRCompb
open
  PRCompb.RSPrograa
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
  OCClos
open
  OCClos.DFTerm
open
  OCPartit
open
  PTOcc
open
  PCBridge

namespace RSPrograa

/--
Every crossing in a recursively compiled insertion schedule is generated from
any common source containing the input list and inserted term.
-/
lemma crossings_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {source L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      CompilesInsertsCorrections
        n leftWeight rightWeight hinsert program)
    (hL : ∀ term ∈ L, CGFrom source term)
    (hA : CGFrom source A) :
    CGFroma source program := by
  induction hcompile generalizing source with
  | nil A =>
      exact CGFroma.empty source
  | append P B A hBA =>
      exact CGFroma.empty source
  | retained P B A hAB hweight hcorrection hinsert
      hleft hright ihleft ihright =>
      have hP :
          ∀ term ∈ P, CGFrom source term := by
        intro term hterm
        exact hL term (List.mem_append_left [B] hterm)
      have hB :
          CGFrom source B :=
        hL B (by simp)
      have hBA :
          CGFrom source (B.correction A) :=
        CGFrom.correction hB hA
      have hQ :
          ∀ term ∈ _, CGFrom source term :=
        FVSuppor.DFTerm.correction_cutoff_inserts
          hcorrection.cutoffInserts hP hBA
      exact
        CGFroma.retained
          (ihleft hP hBA) hB hA (ihright hQ hA)
  | residual P B A hAB hweight hinsert hprogram ihprogram =>
      have hP :
          ∀ term ∈ P, CGFrom source term := by
        intro term hterm
        exact hL term (List.mem_append_left [B] hterm)
      exact ihprogram hP hA

/--
Every crossing in a recursively compiled collection schedule is generated from
the original source list.
-/
lemma crossings_compiles_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hcompile :
      CompilesCollectsCorrections
        n leftWeight rightWeight hcollect program) :
    CGFroma L program := by
  induction hcompile with
  | nil =>
      exact CGFroma.empty []
  | retained P A hweight hcollect hinsert
      hcollectProgram hinsertProgram ihcollect =>
      have hcollect' :
          CGFroma (P ++ [A]) _ :=
        ihcollect.mono fun term hterm =>
          List.mem_append_left [A] hterm
      have hC := fun term hterm => by
        exact
          (FVSuppor.DFTerm.correction_cutoff_collects
            hcollect.cutoffCollects term hterm).mono fun next hnext =>
              List.mem_append_left [A] hnext
      have hA :
          CGFrom (P ++ [A]) A :=
        CGFrom.source (by simp)
      exact
        CGFroma.append hcollect'
          (crossings_inserts_corrections
            hinsertProgram hC hA)
  | residual P A hweight hcollect hprogram ihprogram =>
      exact
        ihprogram.mono fun term hterm =>
          List.mem_append_left [A] hterm

end RSPrograa

/--
A selected endpoint concrete schedule carrying its constructor-level recursive
compilation witness and inverse-raw crossing provenance.
-/
structure ERCompil
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) where
  program :
    RSPrograa
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      n leftWeight rightWeight
  compiles :
    RSPrograa.CompilesCollectsCorrections
      n leftWeight rightWeight
      (endpointCorrectionInventory layer M N
        |>.family_collects_corrections)
      program
  correctionTrace_eq :
    program.correctionTrace =
      (endpointCorrectionInventory layer M N).corrections
  crossings_generated :
    CGFroma (inverseDecoratedTerms M N) program

/-- Select the recursively compiled endpoint schedule with provenance. -/
noncomputable def
    endpointRecursivelyCompiled
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ERCompil
      layer M N :=
  let hcollect :=
    (endpointCorrectionInventory layer M N)
      |>.family_collects_corrections
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

namespace
  ERCompil

/-- Forget recursive compilation while retaining endpoint provenance. -/
noncomputable def endpointGeneratedProgram
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    (schedule :
      ERCompil
        layer M N) :
    EndpointGeneratedProgram layer M N where
  program :=
    schedule.program
  correctionTrace_eq :=
    schedule.correctionTrace_eq
  crossings_generated :=
    schedule.crossings_generated

end
  ERCompil

/--
A selected endpoint certificate carrying recursive compilation, inverse-raw
provenance, and a cutoff-aware occurrence run from the same traced collector
derivation.
-/
structure
    RCOcc
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G) where
  program :
    RSPrograa
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      n leftWeight rightWeight
  compiles :
    RSPrograa.CompilesCollectsCorrections
      n leftWeight rightWeight
      (endpointCorrectionInventory layer M N
        |>.family_collects_corrections)
      program
  correctionTrace_eq :
    program.correctionTrace =
      (endpointCorrectionInventory layer M N).corrections
  crossings_generated :
    CGFroma (inverseDecoratedTerms M N) program
  rewrites :
    TORwa
      (collapsedEvaluatedFactors x y (inverseDecoratedTerms M N))
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors)

namespace
  RCOcc

/--
Construct the enhanced endpoint certificate from the actual traced endpoint
collector derivation.
-/
noncomputable def natural_recollect_layer
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
    RCOcc
      layer M N x y :=
  let hcollect :=
    (endpointCorrectionInventory layer M N)
      |>.family_collects_corrections
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
    rewrites :=
      DFTerm.CCollec.truncatedOccurrenceRewrites
        hleftWeight hrightWeight hx hy hbot hcollect.cutoffCollects
  }

/-- Forget recursive compilation while retaining the synchronized endpoint run. -/
noncomputable def endpointOccurrenceCertificate
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      RCOcc
        layer M N x y) :
    EOCert
      layer M N x y where
  program :=
    certificate.program
  correctionTrace_eq :=
    certificate.correctionTrace_eq
  crossings_generated :=
    certificate.crossings_generated
  rewrites :=
    certificate.rewrites

/--
Adjoining the powered parents to the enhanced certificate gives the concrete
natural parent-pair collection run.
-/
lemma parent_endpoint_rewrites
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      RCOcc
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
        [y ^ N, x ^ M]) :=
  certificate.endpointOccurrenceCertificate
    |>.parent_endpoint_rewrites
      hleftWeight hrightWeight hx hy hbot

/--
At root weights in the free lower-central truncation, the recursively compiled
enhanced endpoint certificate is unconditional.
-/
noncomputable def rootNaturalRecollection
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    RCOcc
      layer M N x y :=
  natural_recollect_layer layer M N x y
    (by omega) (by omega) (by simp) (by simp)
      SCFactor.trunc_last_bot

end
  RCOcc

end
  RCProven
end TCTex
end Submission

/-!
# Flat retained-root normal forms for structural coalescing

The structural coalescing calculus splits each recursive retained node into
its left schedule, singleton root block, and right schedule.  This file
iterates that local rewrite: every erased scheduler program coalesces to a
flat scheduler concatenation of singleton retained-root blocks.

Concrete schedules inherit the same normal form after erasure.  The remaining
arbitrary-cutoff comparison can therefore be posed between two flat root
programs while retaining a constructor-level route back to the scalar
induction kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  CNForm

open
  RPCoales
open
  CRProgra
open
  CPProven
open
  CRLayer
open
  FIProf
open
  ISLift
open
  RTProgra
open
  RTProgra.ESProgra
open
  GRProgra
open
  REProgra

namespace EFForm

open EMCoales

/-- Singleton scheduler block carrying one retained Hall-shape root. -/
def singletonRootProgram
    (shape : CWord HPAtom) :
    ESProgra :=
  ESProgra.retained
    ESProgra.empty shape
    ESProgra.empty

/-- Flatten a recursive scheduler program to its singleton retained-root blocks. -/
def flatRootProgram
    (program : ESProgra) :
    ESProgra :=
  ESProgra.schedulerConcat
    (program.trace.map singletonRootProgram)

/--
Two separately concatenated normalized block lists coalesce to the
concatenation of the combined block list.
-/
lemma append_scheduler_concat
    (left right : List ESProgra) :
    Rel
      (ESProgra.append
        (ESProgra.schedulerConcat left)
        (ESProgra.schedulerConcat right))
      (ESProgra.schedulerConcat
        (left ++ right)) := by
  induction left with
  | nil =>
      simpa only [ESProgra.schedulerConcat,
        List.nil_append] using
          Rel.append_empty_left
            (ESProgra.schedulerConcat right)
  | cons head tail ih =>
      simpa only [ESProgra.schedulerConcat,
        List.cons_append] using
          (Rel.append_assoc head
            (ESProgra.schedulerConcat tail)
            (ESProgra.schedulerConcat right)
          ).trans
            (Rel.append (Rel.refl head) ih)

/-- A singleton retained root coalesces to its one-block scheduler concatenation. -/
lemma singleton_scheduler_concat
    (shape : CWord HPAtom) :
    Rel
      (singletonRootProgram shape)
      (ESProgra.schedulerConcat
        [singletonRootProgram shape]) := by
  simpa only [ESProgra.schedulerConcat] using
    (Rel.append_empty_right (singletonRootProgram shape)).symm

/-- Every erased scheduler program structurally coalesces to its flat root form. -/
theorem flat_program
    (program : ESProgra) :
    Rel program (flatRootProgram program) := by
  induction program with
  | empty =>
      exact Rel.refl ESProgra.empty
  | append left right ihleft ihright =>
      unfold flatRootProgram
      rw [trace_append, List.map_append]
      exact
        (Rel.append ihleft ihright).trans
          (append_scheduler_concat
            (left.trace.map singletonRootProgram)
            (right.trace.map singletonRootProgram))
  | retained left shape right ihleft ihright =>
      unfold flatRootProgram
      rw [trace_retained, List.map_append, List.map_append]
      refine (Rel.retained_split left right shape).trans ?_
      refine
        (Rel.append ihleft
          (Rel.append
            (singleton_scheduler_concat shape)
            ihright)).trans ?_
      refine
        (Rel.append (Rel.refl _)
          (append_scheduler_concat
            [singletonRootProgram shape]
            (right.trace.map singletonRootProgram))).trans ?_
      simpa only [List.map_cons, List.map_nil, List.singleton_append,
        List.append_assoc] using
          append_scheduler_concat
            (left.trace.map singletonRootProgram)
            ([singletonRootProgram shape] ++
              right.trace.map singletonRootProgram)

/-- Flat-root normalization preserves every Hall-shape multiplicity. -/
lemma count_flat_program
    (program : ESProgra)
    (word : CWord HPAtom) :
    (flatRootProgram program).trace.count word =
      program.trace.count word :=
  (flat_program program).count_eq word |>.symm

end EFForm

namespace MCSched

open EFForm
open EMCoales

/--
The flat singleton-root normal form of a concrete schedule's erasure
structurally coalesces with the original concrete schedule.
-/
lemma flat_program_erasure
    {M N K n leftWeight rightWeight : ℕ}
    (concrete :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    MCSched
      (flatRootProgram concrete.shapeTraceProgram) concrete :=
  (flat_program concrete.shapeTraceProgram).symm.trans
    (RPCoales.MCSched.of_erasure
      concrete)

end MCSched

open EFForm
open EMCoales

/--
Flat-root normal-form arbitrary-cutoff target.

The symbolic scheduler and concrete collector are normalized independently.
Only the coalescing comparison between their flat singleton-root programs
remains.
-/
structure
    GFCoales
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  flat_programs_coalesce :
    ∀ M N,
      Rel
        (flatRootProgram
          (guardedSchedulerProgram
            (multiplicityProfileShape
              raw)
            M N))
        (flatRootProgram
          (endpointScheduleProgram
            layer M N).program.shapeTraceProgram)

namespace
  GFCoales

/--
Compile flat-root coalescing to the recursive structural coalescing kernel.
-/
noncomputable def
    guardedScheduleCoalescing
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GFCoales
        layer hleftWeight hrightWeight) :
    GSCoales
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  program_coalesces_schedule M N :=
    (flat_program
      (guardedSchedulerProgram
        (multiplicityProfileShape
          kernel.raw)
        M N)).trans
      ((kernel.flat_programs_coalesce M N).trans
        (flat_program
          (endpointScheduleProgram
            layer M N).program.shapeTraceProgram).symm)

/-- Compile flat-root coalescing directly to endpoint interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GFCoales
        layer hleftWeight hrightWeight) :=
  kernel.guardedScheduleCoalescing
    |>.fiberProfileInterpolation

end
  GFCoales

namespace
  GSCoales

/-- Normalize a recursive structural coalescing kernel to flat root programs. -/
noncomputable def
    guardedFlatCoalescing
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSCoales
        layer hleftWeight hrightWeight) :
    GFCoales
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  flat_programs_coalesce M N :=
    (flat_program
      (guardedSchedulerProgram
        (multiplicityProfileShape
          kernel.raw)
        M N)).symm.trans
      ((kernel.program_coalesces_schedule M N).trans
        (flat_program
          (endpointScheduleProgram
            layer M N).program.shapeTraceProgram))

end
  GSCoales

/-- Through cutoff four, flat-root structural coalescing is available. -/
noncomputable def
    flatNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GFCoales
      layer (by simp) (by simp) :=
  GSCoales.guardedFlatCoalescing
    (coalescingNFour
      layer hhigh raw)

end
  CNForm
end TCTex
end Submission

/-!
# Claim 5 from constructor-level concrete-schedule structural coalescing

The structural coalescing kernel is the constructor-level input for the
arbitrary-cutoff symbolic Hall collector.  This file compiles that input
directly to the Claim 5 coordinate-polynomial package.

The remaining signed lift is inherited from the scalar multiplicity kernel
produced by structural coalescing.  It is equivalently the corresponding
truncated signed recollection law.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  MIKern
open
  RPCoales
open
  CRLayer
open
  CFSubsti

namespace
  RPCoales
namespace
  GSCoales

/-- Signed extension inherited from the scalar kernel compiled by coalescing. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GSCoales
        layer (by simp) (by simp)) :
    Prop :=
  GMInduct.AILift.{u}
    (d := d)
    kernel.scheduleMultInduction

/--
Truncated signed recollection law inherited from the scalar kernel compiled by
coalescing.
-/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GSCoales
        layer (by simp) (by simp)) :
    Prop :=
  GMInduct.SatisfiesTruncEval.{u}
    (d := d)
    kernel.scheduleMultInduction

/--
For constructor-level structural coalescing, the remaining signed lift is
exactly the inherited truncated signed recollection law.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GSCoales
        layer (by simp) (by simp)) :
    GSCoales.SatisfiesTruncEval.{u}
        (d := d) kernel ↔
      GSCoales.AILift.{u}
        (d := d) kernel :=
  by
    change
      GMInduct.SatisfiesTruncEval.{u}
          (d := d)
          kernel.scheduleMultInduction ↔
        GMInduct.AILift.{u}
          (d := d)
          kernel.scheduleMultInduction
    exact
      GMInduct.satisfies_trunc_lift
        (d := d)
        kernel.scheduleMultInduction

end
  GSCoales
end
  RPCoales

namespace TSInput

/--
Constructor-level structural coalescing, its signed lift, singleton
recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem
    structuralCoalescingLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GSCoales
        layer (by simp) (by simp))
    (lift :
      GSCoales.AILift.{u}
        (d := d) kernel)
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
  input.generatedInductionLift
    hn H hH
      kernel.scheduleMultInduction
      (show
        GMInduct.AILift.{u}
          (d := d)
          kernel.scheduleMultInduction
        from lift)
      hsourceSupported factorNormalization hinputWeight

/--
The inherited truncated signed recollection law is an equivalent
constructor-level input for the Claim 5 coordinate polynomials.
-/
theorem
    coordCoalescingTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GSCoales
        layer (by simp) (by simp))
    (hlistEval :
      GSCoales.SatisfiesTruncEval.{u}
        (d := d) kernel)
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
  input.coordInductionTrunc
    hn H hH
      kernel.scheduleMultInduction
      (show
        GMInduct.SatisfiesTruncEval.{u}
          (d := d)
          kernel.scheduleMultInduction
        from hlistEval)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Permutation criteria for structural coalescing

The flat-root normal form is a scheduler concatenation of singleton retained
roots.  The structural coalescing calculus can realize every permutation of
those singleton blocks.  Consequently, two erased scheduler programs
structurally coalesce exactly when their Hall-shape traces are permutations.

This file packages the arbitrary-cutoff endpoint obligation as a root-trace
permutation criterion and proves that it is equivalent both to flat structural
coalescing and to the earlier Hall-shape multiplicity criterion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  RPCrit

open
  RPCoales
open
  CNForm
open
  PMCoales
open
  CRProgra
open
  CPProven
open
  CRLayer
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

namespace SPCrit

open EFForm
open EMCoales

/-- A singleton retained-root block emits exactly its designated Hall shape. -/
@[simp]
lemma trace_singleton_program
    (shape : CWord HPAtom) :
    (singletonRootProgram shape).trace = [shape] := by
  rfl

/-- Flat-root normalization leaves the emitted Hall-shape trace unchanged. -/
@[simp]
lemma flat_root_program
    (program : ESProgra) :
    (flatRootProgram program).trace = program.trace := by
  unfold flatRootProgram
  rw [ESProgra.traceSchedulerConcat]
  induction program.trace with
  | nil =>
      rfl
  | cons shape shapes ih =>
      simp only [List.map_cons, List.flatMap_cons,
        trace_singleton_program, ih, List.singleton_append]

/--
Any permutation of scheduler blocks induces a structural coalescing
derivation between their concatenations.
-/
lemma schedulerConcat_perm
    {left right : List ESProgra}
    (hperm : List.Perm left right) :
    Rel
      (ESProgra.schedulerConcat left)
      (ESProgra.schedulerConcat right) := by
  induction hperm with
  | nil =>
      exact Rel.refl ESProgra.empty
  | cons head hperm ih =>
      exact Rel.append (Rel.refl head) ih
  | swap first second tail =>
      simpa only [ESProgra.schedulerConcat] using
        ((Rel.append_assoc first second
            (ESProgra.schedulerConcat tail)
          ).symm.trans
            ((Rel.append (Rel.append_comm first second) (Rel.refl _)).trans
              (Rel.append_assoc second first
                (ESProgra.schedulerConcat tail)))).symm
  | trans hfirst hlast ihfirst ihlast =>
      exact ihfirst.trans ihlast

/--
A permutation of root traces induces structural coalescing between the
corresponding flat-root normal forms.
-/
lemma flat_coalesces_perm
    {left right : ESProgra}
    (hperm : List.Perm left.trace right.trace) :
    Rel (flatRootProgram left) (flatRootProgram right) := by
  unfold flatRootProgram
  exact schedulerConcat_perm (hperm.map singletonRootProgram)

/-- Structural coalescing is complete for trace permutations. -/
lemma coalesces_perm
    {left right : ESProgra}
    (hperm : List.Perm left.trace right.trace) :
    Rel left right :=
  (flat_program left).trans
    ((flat_coalesces_perm hperm).trans
      (flat_program right).symm)

/-- Structural coalescing is exactly permutation of emitted Hall-shape traces. -/
theorem coalesces_trace_perm
    {left right : ESProgra} :
    Rel left right ↔ List.Perm left.trace right.trace :=
  ⟨Rel.trace_perm, coalesces_perm⟩

/--
Equivalently, structural coalescing is exactly pointwise equality of
Hall-shape multiplicities.
-/
theorem coalesces_count
    {left right : ESProgra} :
    Rel left right ↔
      ∀ word : CWord HPAtom,
        left.trace.count word = right.trace.count word := by
  classical
  rw [coalesces_trace_perm, List.perm_iff_count]

end SPCrit

/--
Practical arbitrary-cutoff criterion: the symbolic recursive expansion root
trace permutes to the compiler-selected root trace of the actual endpoint
crossings.
-/
structure
    GPPerm
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  expanded_root_perm :
    ∀ M N,
      List.Perm
        (guardedExpansionErased
          raw M N)
        (endpointGridBranch
          layer hleftWeight hrightWeight M N)

namespace
  GPPerm

open SPCrit

/-- Compile root-trace permutation to flat-root structural coalescing. -/
noncomputable def
    guardedFlatCoalescing
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GPPerm
        layer hleftWeight hrightWeight) :
    GFCoales
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  flat_programs_coalesce M N := by
    apply flat_coalesces_perm
    refine
      (idxSchedulerProgram
        kernel.raw M N).symm.trans ?_
    rw [←
      endpoint_guarded_program]
    exact kernel.expanded_root_perm M N

/-- Compile root-trace permutation directly to the recursive structural kernel. -/
noncomputable def
    guardedScheduleCoalescing
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GPPerm
        layer hleftWeight hrightWeight) :
    GSCoales
      layer hleftWeight hrightWeight :=
  kernel.guardedFlatCoalescing
    |>.guardedScheduleCoalescing

/-- Compile root-trace permutation directly to endpoint interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GPPerm
        layer hleftWeight hrightWeight) :=
  kernel.guardedScheduleCoalescing
    |>.fiberProfileInterpolation

end
  GPPerm

namespace
  GFCoales

open SPCrit

/-- Recover root-trace permutation from flat-root structural coalescing. -/
noncomputable def
    guardedPolyPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GFCoales
        layer hleftWeight hrightWeight) :
    GPPerm
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  expanded_root_perm M N := by
    rw [
      endpoint_guarded_program]
    refine
      (idxSchedulerProgram
        kernel.raw M N).trans ?_
    simpa only [flat_root_program] using
      (kernel.flat_programs_coalesce M N).trace_perm

end
  GFCoales

namespace
  GCDecomp

/-- Hall-shape count coalescing supplies root-trace permutation. -/
noncomputable def
    guardedPolyPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GCDecomp
        layer hleftWeight hrightWeight) :
    GPPerm
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  expanded_root_perm M N := by
    classical
    rw [List.perm_iff_count]
    exact decomposition.expanded_root_count M N

end
  GCDecomp

namespace
  GPPerm

/-- Root-trace permutation recovers Hall-shape count coalescing. -/
noncomputable def
    guardedCoalescingDecomp
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GPPerm
        layer hleftWeight hrightWeight) :
    GCDecomp
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  expanded_root_count M N word :=
    (kernel.expanded_root_perm M N).count_eq word

end
  GPPerm

/-- Through cutoff four, the root-trace permutation criterion holds. -/
noncomputable def
    correctionNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GPPerm
      layer (by simp) (by simp) :=
  GCDecomp.guardedPolyPermutation
    (multCoalescingFour
      layer hhigh raw)

end
  RPCrit
end TCTex
end Submission

/-!
# Root-trace permutation from the guarded finite-index grid

The older guarded-grid boundary compares the recursively expanded finite-index
trace with the literal selected retained-correction finite-index trace.  The
concrete generated-program boundary packages the same selected endpoint
corrections through provenance-certified guarded branches.

After erasing finite orbit indices to Hall shapes, both endpoint encodings are
literally the selected correction shape trace.  Thus the guarded finite-index
permutation compiles directly to the root-trace permutation kernel consumed by
the structural Hall collector.

This implication is intentionally one-way: erased Hall shapes need not recover
finite orbit indices.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  PGBridge

open
  CRIndexa
open
  CGCovera
open
  PMCoales
open
  RPCrit
open
  CRLayer
open
  FIProf
open
  RITrace
open
  PGSrc
open
  SEAlg

/--
The provenance-certified concrete guarded-branch roots erase to the literal
selected retained-correction shape trace.
-/
lemma
    endpoint_guarded_erased
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    endpointGridBranch
        layer hleftWeight hrightWeight M N =
      selectedErasedShape layer M N := by
  unfold
    endpointGridBranch
  rw [
    endpoint_guarded_idx,
    key_endpoint_generated]

namespace
  GIDecomp

/--
Erase the guarded finite-index scheduler theorem to the root-trace permutation
kernel used by the constructor-level structural collector.
-/
noncomputable def
    guardedPolyPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      GIDecomp
        layer hleftWeight hrightWeight) :
    GPPerm
      layer hleftWeight hrightWeight where
  raw :=
    decomposition.raw
  expanded_root_perm M N := by
    unfold
      guardedExpansionErased
    rw [
      endpoint_guarded_erased]
    simpa only [
      key_erased_selected] using
        (decomposition.trace_perm M N).map fun index =>
          (retainedOrbitKey index).erasedShape

end
  GIDecomp

/--
Through cutoff four, the guarded finite-index route supplies the root-trace
permutation kernel directly.
-/
noncomputable def
    gridNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    GPPerm
      layer (by simp) (by simp) :=
  GIDecomp.guardedPolyPermutation
    (guardedNFour
      layer hhigh raw)

end
  PGBridge
end TCTex
end Submission

/-!
# Claim 5 from concrete-schedule root-trace permutation

Root-trace permutation is a compact endpoint condition for the symbolic Hall
collector.  The structural permutation criterion compiles it to constructor-
level coalescing, so it can be fed directly to the Claim 5 coordinate-
polynomial package.

The remaining signed lift is equivalently the corresponding truncated signed
recollection law.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  RPCoales
open
  RPCrit
open
  CRLayer
open
  CFSubsti

namespace
  RPCrit
namespace
  GPPerm

/-- Signed extension inherited from structural coalescing. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp)) :
    Prop :=
  GSCoales.AILift.{u}
    (d := d)
    kernel.guardedScheduleCoalescing

/-- Truncated signed recollection inherited from structural coalescing. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp)) :
    Prop :=
  GSCoales.SatisfiesTruncEval.{u}
    (d := d)
    kernel.guardedScheduleCoalescing

/--
For root-trace permutation, the remaining signed lift is exactly the inherited
truncated signed recollection law.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp)) :
    GPPerm.SatisfiesTruncEval.{u}
        (d := d) kernel ↔
      GPPerm.AILift.{u}
        (d := d) kernel :=
  GSCoales.satisfies_trunc_lift
    (d := d)
    kernel.guardedScheduleCoalescing

end
  GPPerm
end
  RPCrit

namespace TSInput

/--
Root-trace permutation, its signed lift, singleton recollections, and graded
Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem
    generatedPermutationLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (lift :
      GPPerm.AILift.{u}
        (d := d) kernel)
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
  input.structuralCoalescingLift
    hn H hH
      kernel.guardedScheduleCoalescing
      (show
        GSCoales.AILift.{u}
          (d := d)
          kernel.guardedScheduleCoalescing
        from lift)
      hsourceSupported factorNormalization hinputWeight

/--
The inherited truncated signed recollection law is an equivalent root-trace
input for the Claim 5 coordinate polynomials.
-/
theorem
    coordPermutationTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (hlistEval :
      GPPerm.SatisfiesTruncEval.{u}
        (d := d) kernel)
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
  input.coordCoalescingTrunc
    hn H hH
      kernel.guardedScheduleCoalescing
      (show
        GSCoales.SatisfiesTruncEval.{u}
          (d := d)
          kernel.guardedScheduleCoalescing
        from hlistEval)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Structural coalescing criteria for synchronized endpoint schedules

The guarded-grid root compiler now applies directly to the concrete correction
program carried by an endpoint occurrence certificate.  This file connects
that synchronized root trace to the earlier endpoint root trace used by the
power-coordinate pipeline.

The new synchronized permutation kernel carries one actual cutoff-aware
occurrence certificate for every natural input pair.  Its symbolic obligation
is still exactly root-trace permutation.  Adapters in both directions show
that no new multiplicity theorem is hidden in this operational strengthening.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  CPCrit

universe u

open
  HACoeff
open
  RPCoales
open
  RPCrit
open
  PMCoales
open
  EGCovera
open
  CRProgra
open
  CPProven
open
  TOSync
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRLayer
open
  FIProf
open
  RITrace
open
  PTOcc
open
  PCBridge
open
  ISLift
open
  RTProgra
open
  GRProgra
open
  SEAlg

open
  RPCrit.SPCrit
open
  RPCoales.EMCoales

/--
Shape erasure of the guarded-grid roots compiled from one synchronized
endpoint occurrence certificate.
-/
noncomputable def
    synchronizedEndpointErased
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (CWord HPAtom) :=
  (synchronizedGridBranch
    certificate hleftWeight hrightWeight).map fun index =>
      (retainedOrbitKey index).erasedShape

/--
The synchronized guarded roots erase to the trace of the concrete correction
program carried by the same occurrence certificate.
-/
lemma
    synchronized_endpoint_program
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    synchronizedEndpointErased
        certificate hleftWeight hrightWeight =
      certificate.program.shapeTraceProgram.trace := by
  unfold
    synchronizedEndpointErased
  exact
    key_endpoint_program
      certificate hleftWeight hrightWeight

/--
Although the synchronized program remembers its occurrence run, its erased
root trace is the same selected retained-correction shape trace as before.
-/
lemma
    synchronized_endpoint_erased
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    synchronizedEndpointErased
        certificate hleftWeight hrightWeight =
      selectedErasedShape layer M N := by
  rw [
    synchronized_endpoint_program,
    RSPrograa.trace_erased_shape,
    certificate.correctionTrace_eq]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/--
The synchronized and previously selected guarded-root traces agree after
shape erasure.
-/
lemma
    synchronized_endpoint_trace
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    synchronizedEndpointErased
        certificate hleftWeight hrightWeight =
      endpointGridBranch
        layer hleftWeight hrightWeight M N := by
  rw [
    synchronized_endpoint_erased,
    endpoint_guarded_program,
    GGProgra.programEndpointSchedule]

/--
The independently selected endpoint correction program and the synchronized
occurrence program have literally equal erased-shape traces.
-/
lemma
    erased_program_endpoint
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    certificate.program.shapeTraceProgram.trace =
      ((endpointScheduleProgram
        layer M N).program.shapeTraceProgram).trace := by
  rw [←
    synchronized_endpoint_program
      certificate hleftWeight hrightWeight]
  rw [
    synchronized_endpoint_trace
      certificate hleftWeight hrightWeight]
  exact
    endpoint_guarded_program
      layer hleftWeight hrightWeight M N

/--
The synchronized and previously selected endpoint correction programs
structurally coalesce.
-/
lemma
    erasedProgramEndpoint
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    EMCoales.Rel
      certificate.program.shapeTraceProgram
      (endpointScheduleProgram
        layer M N).program.shapeTraceProgram := by
  apply coalesces_perm
  rw [
    erased_program_endpoint
      certificate hleftWeight hrightWeight]

/--
For one synchronized endpoint certificate, recursive symbolic coalescing is
equivalent to permutation of the expanded roots and the synchronized concrete
roots.
-/
theorem
    coalesces_synchronized_perm
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (certificate :
      EOCert
        layer M N x y) :
    EMCoales.Rel
        (guardedSchedulerProgram
          (multiplicityProfileShape raw)
          M N)
        certificate.program.shapeTraceProgram ↔
      List.Perm
        (guardedExpansionErased
          raw M N)
        (synchronizedEndpointErased
          certificate hleftWeight hrightWeight) := by
  rw [coalesces_trace_perm,
    synchronized_endpoint_program]
  constructor
  · intro hperm
    exact
      (idxSchedulerProgram
        raw M N).trans hperm
  · intro hperm
    exact
      (idxSchedulerProgram
        raw M N).symm.trans hperm

/--
Operational strengthening of the root-trace permutation kernel: besides the
symbolic permutation proof, retain synchronized cutoff-aware endpoint
occurrence certificates for every natural input pair.
-/
structure
    GSPerm
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    {G : Type u}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  certificate :
    ∀ M N,
      EOCert
        layer M N x y
  expanded_root_perm :
    ∀ M N,
      List.Perm
        (guardedExpansionErased
          raw M N)
        (synchronizedEndpointErased
          (certificate M N) hleftWeight hrightWeight)

namespace
  GSPerm

/--
Forget the occurrence certificates and recover the root-permutation kernel
already consumed by the polynomial pipeline.
-/
noncomputable def
    guardedPolyPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSPerm
        layer x y hleftWeight hrightWeight) :
    GPPerm
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  expanded_root_perm M N := by
    rw [←
      synchronized_endpoint_trace
        (kernel.certificate M N) hleftWeight hrightWeight]
    exact kernel.expanded_root_perm M N

/-- Compile synchronized root permutation directly to endpoint interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSPerm
        layer x y hleftWeight hrightWeight) :=
  kernel.guardedPolyPermutation
    |>.fiberProfileInterpolation

/--
The synchronized root permutation proof is equivalently a structural
coalescing derivation against the concrete program carried by its occurrence
certificate.
-/
lemma scheduler_coalesces_synchronized
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSPerm
        layer x y hleftWeight hrightWeight)
    (M N : ℕ) :
    EMCoales.Rel
      (guardedSchedulerProgram
        (multiplicityProfileShape
          kernel.raw)
        M N)
      (kernel.certificate M N).program.shapeTraceProgram :=
  (coalesces_synchronized_perm
    hleftWeight hrightWeight kernel.raw (kernel.certificate M N)).2
      (kernel.expanded_root_perm M N)

/-- Recover the raw-source to endpoint cutoff-aware occurrence run. -/
lemma endpoint_occurrence_rewrites
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSPerm
        layer x y hleftWeight hrightWeight)
    (M N : ℕ) :
    TORwa
      (collapsedEvaluatedFactors x y (inverseDecoratedTerms M N))
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors) :=
  (kernel.certificate M N).rewrites

/--
Adjoining the powered parents recovers the concrete natural parent-pair
occurrence run from the synchronized kernel.
-/
lemma parent_endpoint_rewrites
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSPerm
        layer x y hleftWeight hrightWeight)
    (M N : ℕ)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
        [y ^ N, x ^ M]) :=
  (kernel.certificate M N).parent_endpoint_rewrites
    hleftWeight hrightWeight hx hy hbot

/--
For free lower-central truncations at root weights, the synchronized kernel
supplies the concrete powered parent-pair run without additional hypotheses.
-/
lemma parentEndpointTrunc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n}
    (kernel :
      GSPerm
        layer x y (by simp) (by simp))
    (M N : ℕ) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
        [y ^ N, x ^ M]) :=
  kernel.parent_endpoint_rewrites M N
    (by simp) (by simp)
      SCFactor.trunc_last_bot

end
  GSPerm

namespace
  GPPerm

/--
Install synchronized occurrence certificates into an existing root-trace
permutation kernel.
-/
noncomputable def
    guardedSynchronizedPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GPPerm
        layer hleftWeight hrightWeight)
    {G : Type u}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    GSPerm
      layer x y hleftWeight hrightWeight :=
  let certificate M N :=
    EOCert.natural_recollect_layer
      layer M N x y hleftWeight hrightWeight hx hy hbot
  {
    raw := kernel.raw
    certificate := certificate
    expanded_root_perm := by
      intro M N
      rw [
        synchronized_endpoint_trace
          (certificate M N) hleftWeight hrightWeight]
      exact kernel.expanded_root_perm M N
  }

end
  GPPerm

/--
Through cutoff four, the empty-grid root-permutation theorem upgrades to an
occurrence-backed synchronized endpoint kernel in every sufficiently
truncated group.
-/
noncomputable def
    synchronizedNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    {G : Type u}
    [Group G]
    (x y : G)
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    GSPerm
      layer x y (by simp) (by simp) :=
  GPPerm.guardedSynchronizedPermutation
    (correctionNFour
      layer hhigh raw)
    x y (by simp) (by simp) hbot

/--
Through cutoff four, the free lower-central truncation carries an
occurrence-backed synchronized endpoint kernel unconditionally.
-/
noncomputable def
    freeNFour
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    GSPerm
      layer x y (by simp) (by simp) :=
  synchronizedNFour
    layer hhigh raw x y
      SCFactor.trunc_last_bot

end
  CPCrit
end TCTex
end Submission

/-!
# Canonical packet alignment for root-trace signed lifting

The generated concrete-schedule root-trace kernel supplies a natural endpoint
interpolation packet.  The canonical finite correction closure supplies a
fixed coefficient-sum packet with an explicit signed semantic law.

These packets arise from different constructions.  This file isolates the
remaining order-aware comparison as literal packet-list equality and
transports the canonical signed law across that equality.

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
  CFSubsti
open
  CPSplit
open
  CTAssign
open
  GRPolys

namespace
  FPInterp
namespace EFInterp

/--
Literal alignment with the canonical coefficient-sum packet transports the
canonical recipe-product law to an endpoint interpolation packet.
-/
def
    allLiftTrunc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (hpackets :
      packets =
        globalProfilePackets n 1 1)
    (hlistEval :
      SatisfiesRecipeTruncated.{u} d n) :
    EFInterp.AILift.{u}
      (d := d) interpolation where
  listEval_eq left right leftExponent rightExponent := by
    rw [packetsTruncNatural, hpackets]
    simpa only [globalProfilePackets] using
      (satisfies_profile_assignment
        hlistEval left right leftExponent rightExponent)

end EFInterp
end
  FPInterp

namespace
  RPCrit
namespace
  GPPerm

/--
The generated root-trace interpolation packet is literally the canonical
coefficient-sum packet, including order and profile formulas.
-/
def GlobalPacketAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp)) :
    Prop :=
  (EFInterp.truncNaturalPacket.{u}
    (d := d)
    kernel.fiberProfileInterpolation).packets =
      globalProfilePackets n 1 1

/--
Canonical packet alignment and the canonical recipe-product law provide the
signed lift inherited by the root-trace kernel.
-/
def
    allLiftTrunc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (halignment :
      GlobalPacketAlignment.{u} (d := d) kernel)
    (hlistEval :
      SatisfiesRecipeTruncated.{u} d n) :
    GPPerm.AILift.{u}
      (d := d) kernel := by
  change
    EFInterp.AILift.{u}
      (d := d)
      kernel.fiberProfileInterpolation
  apply
    EFInterp.allLiftTrunc
      kernel.fiberProfileInterpolation
      ?_ hlistEval
  simpa only [
    EFInterp.packetsTruncNatural] using
      halignment

/--
The same explicit inputs discharge the truncated signed recollection law used
by the root-trace Claim 5 adapters.
-/
lemma
    satisfies_trunc_recipe
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (halignment :
      GlobalPacketAlignment.{u} (d := d) kernel)
    (hlistEval :
      SatisfiesRecipeTruncated.{u} d n) :
    GPPerm.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  (kernel.satisfies_trunc_lift).mpr
    (kernel.allLiftTrunc
      halignment hlistEval)

end
  GPPerm
end
  RPCrit

end TCTex
end Submission

/-!
# Scalar multiplicity induction for synchronized endpoint schedules

The guarded symbolic expansion is already normalized to a finite sum of
root-plus-nested-branch recurrences.  The synchronized endpoint certificate
carries the actual concrete correction program and its cutoff-aware occurrence
run.  This file identifies the remaining root-permutation theorem with the
direct scalar comparison against that carried concrete program.

Unlike the earlier endpoint induction kernel, this boundary does not compare
against an independently selected concrete schedule.  Its concrete side is
literally the program stored by the occurrence certificate.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  SMInduct

universe u

open
  PBMult
open
  MIKern
open
  RMRec
open
  PMCoales
open
  CPCrit
open
  CRProgra
open
  CPProven
open
  TOSync
open
  CRLayer
open
  FIProf

/--
Counting the synchronized guarded roots is exactly erased-shape multiplicity
in the concrete correction program carried by the same occurrence
certificate.
-/
lemma
    count_synchronized_mult
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom) :
    (synchronizedEndpointErased
      certificate hleftWeight hrightWeight).count word =
      RSPrograa.erasedShapeMultiplicity
        certificate.program word := by
  rw [
    synchronized_endpoint_program]
  rfl

/--
Direct arbitrary-cutoff scalar induction target against synchronized
occurrence certificates.

For every natural input pair and Hall shape, the finite sum of recursively
expanded symbolic guarded branches has the same multiplicity as the actual
concrete correction program carried by the cutoff-aware occurrence run.
-/
structure
    EMInduct
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    {G : Type u}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  certificate :
    ∀ M N,
      EOCert
        layer M N x y
  branch_schedule_multiplicity :
    ∀ M N word,
      guardedBranchRecurrence
          raw M N word =
        RSPrograa.erasedShapeMultiplicity
          (certificate M N).program word

namespace
  EMInduct

/--
Compile synchronized scalar multiplicity induction to synchronized root-trace
permutation while retaining the same occurrence certificates.
-/
noncomputable def
    guardedSynchronizedPermutation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EMInduct
        layer x y hleftWeight hrightWeight) :
    GSPerm
      layer x y hleftWeight hrightWeight where
  raw :=
    kernel.raw
  certificate :=
    kernel.certificate
  expanded_root_perm M N := by
    classical
    rw [List.perm_iff_count]
    intro word
    calc
      (guardedExpansionErased
            kernel.raw M N).count word =
          guardedBranchSum
            kernel.raw M N word :=
        count_guarded_erased
          kernel.raw M N word
      _ =
          guardedBranchRecurrence
            kernel.raw M N word :=
        guarded_idx_erased
          kernel.raw M N word
      _ =
          RSPrograa.erasedShapeMultiplicity
            (kernel.certificate M N).program word :=
        kernel.branch_schedule_multiplicity M N word
      _ =
          (synchronizedEndpointErased
            (kernel.certificate M N) hleftWeight hrightWeight).count word :=
        (count_synchronized_mult
          (kernel.certificate M N) hleftWeight hrightWeight word).symm

/-- Compile synchronized scalar induction directly to endpoint interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EMInduct
        layer x y hleftWeight hrightWeight) :=
  kernel.guardedSynchronizedPermutation
    |>.fiberProfileInterpolation

end
  EMInduct

namespace
  GSPerm

/--
Recover the direct synchronized scalar induction identities from synchronized
root-trace permutation.
-/
noncomputable def
    endpointMultInduction
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GSPerm
        layer x y hleftWeight hrightWeight) :
    EMInduct
      layer x y hleftWeight hrightWeight where
  raw :=
    kernel.raw
  certificate :=
    kernel.certificate
  branch_schedule_multiplicity M N word := by
    calc
      guardedBranchRecurrence
            kernel.raw M N word =
          guardedBranchSum
            kernel.raw M N word :=
        (guarded_idx_erased
          kernel.raw M N word).symm
      _ =
          (guardedExpansionErased
            kernel.raw M N).count word :=
        (count_guarded_erased
          kernel.raw M N word).symm
      _ =
          (synchronizedEndpointErased
            (kernel.certificate M N) hleftWeight hrightWeight).count word :=
        (kernel.expanded_root_perm M N).count_eq word
      _ =
          RSPrograa.erasedShapeMultiplicity
            (kernel.certificate M N).program word :=
        count_synchronized_mult
          (kernel.certificate M N) hleftWeight hrightWeight word

end
  GSPerm

namespace
  GMInduct

/--
Install actual cutoff-aware occurrence certificates into the earlier scalar
induction kernel.  Trace equality transports its multiplicity theorem to the
synchronized concrete programs.
-/
noncomputable def
    endpointMultInduction
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GMInduct
        layer hleftWeight hrightWeight)
    {G : Type u}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    EMInduct
      layer x y hleftWeight hrightWeight :=
  let certificate M N :=
    EOCert.natural_recollect_layer
      layer M N x y hleftWeight hrightWeight hx hy hbot
  {
    raw := kernel.raw
    certificate := certificate
    branch_schedule_multiplicity := by
      intro M N word
      calc
        guardedBranchRecurrence
              kernel.raw M N word =
            RSPrograa.erasedShapeMultiplicity
              (endpointScheduleProgram
                layer M N).program word :=
          kernel.branch_schedule_multiplicity M N word
        _ =
            RSPrograa.erasedShapeMultiplicity
              (certificate M N).program word := by
          unfold RSPrograa.erasedShapeMultiplicity
          rw [
            erased_program_endpoint
              (certificate M N) hleftWeight hrightWeight]
  }

end
  GMInduct

/--
Through cutoff four, the empty-grid scalar induction theorem upgrades to an
occurrence-backed synchronized endpoint induction kernel.
-/
noncomputable def
    synchronizedInductionFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    {G : Type u}
    [Group G]
    (x y : G)
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    EMInduct
      layer x y (by simp) (by simp) :=
  GMInduct.endpointMultInduction
    (inductionNFour
      layer hhigh raw)
    x y (by simp) (by simp) hbot

end
  SMInduct
end TCTex
end Submission

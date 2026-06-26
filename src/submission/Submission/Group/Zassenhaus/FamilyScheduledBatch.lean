import Submission.Group.Zassenhaus.FamilyCollectorSupport
import Submission.Group.Zassenhaus.GuardedGridCoverage
import Submission.Group.Zassenhaus.ErasedShapePrograms
import Submission.Group.Zassenhaus.PolynomialRankedSupport

/-!
# Root multiplicity synchronization for scheduled generated batches

The annotated compatible-grid collector and the guarded raw-source scheduler
have the same retained-root Hall shape.  Their local scalar recurrences differ
only in the multiplicity assigned to that root: the annotated collector uses
the cardinality of one support-compatible correction grid, while the guarded
scheduler uses the product of its two raw-source parent multiplicities.

This file proves the shape alignment and packages the remaining cardinality
identity as the exact local synchronization obligation.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace BRSync

open HACoeff
open
  CRAlign
open
  ITRec
open CFCollec
open
  SRAlign
open CCAggreg
open CCGrida
open OCClos
open OCClos.DFTerm
open OCPartit
open UIComp
open
  ESIdx

namespace UIAvoida

/--
The Hall shape stored by one unrestricted crossing annotation is the concrete
correction shape of the annotated parent pair.
-/
lemma root_shape_erased
    {sourceLeft sourceRight : ℕ}
    {crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length}
    (profile :
      UIAvoida crossing) :
    CWord.commutator profile.leftShape profile.rightShape =
      (crossing.1.correction crossing.2).erasedShape := by
  rw [CCAggreg.DFTerm.erasedShape_corr,
    profile.leftShape_eq, profile.rightShape_eq]

/--
The same annotation shape is the correction shape used by the guarded
polynomial-orbit obstruction attached to the concrete crossing.
-/
lemma root_obstruction_erased
    {sourceLeft sourceRight : ℕ}
    {crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length}
    (profile :
      UIAvoida crossing) :
    CWord.commutator profile.leftShape profile.rightShape =
      (concreteCrossingObstruction crossing).correction.erasedShape := by
  rw [root_shape_erased profile]
  exact
    (concrete_crossing_obstruction
      crossing).symm

end UIAvoida

/--
Local cardinality synchronization for one inverse-raw generated crossing.

The retained-root index and its Hall shape are already canonical.  This field
is the remaining scalar equation needed to identify the annotated
compatible-grid root block with the guarded scheduler root block.
-/
structure GCSync
    {sourceLeft sourceRight n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (profile :
      UIAvoida crossing) where
  grid_parent_mul :
    ∀ M N,
      (compatibleCorrectionGrid
        (profile.left.terms M N)
        (profile.right.terms M N)).length =
      let branch :=
        gridBranchParents
          hleftWeight hrightWeight crossing parents rootWeight
      (raw.multiplicityProfileFamily branch.leftIndex).multiplicity M N *
        (raw.multiplicityProfileFamily branch.rightIndex).multiplicity M N

namespace GCSync

/--
The annotated and guarded scalar root contributions agree for every Hall
shape once the local correction-grid cardinality equation is supplied.
-/
lemma rootContribution_eq
    {sourceLeft sourceRight n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    {crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length}
    {parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2}
    {rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n}
    {profile :
      UIAvoida crossing}
    (synchronization :
      GCSync
        hleftWeight hrightWeight raw crossing parents rootWeight profile)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (if
      CWord.commutator profile.leftShape profile.rightShape = word then
        (compatibleCorrectionGrid
          (profile.left.terms M N)
          (profile.right.terms M N)).length
      else
        0) =
      let branch :=
        gridBranchParents
          hleftWeight hrightWeight crossing parents rootWeight
      if branch.obstruction.correction.erasedShape = word then
        (raw.multiplicityProfileFamily branch.leftIndex).multiplicity M N *
          (raw.multiplicityProfileFamily branch.rightIndex).multiplicity M N
      else
        0 := by
  rw [
    UIAvoida.root_obstruction_erased
      profile,
    synchronization.grid_parent_mul]
  dsimp only
  rw [obstruction_grid_parents]

/--
At the finite-index level, local cardinality synchronization identifies the
two repeated root blocks directly.
-/
lemma replicate_grid_index
    {sourceLeft sourceRight n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    {crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length}
    {parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2}
    {rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n}
    {profile :
      UIAvoida crossing}
    (synchronization :
      GCSync
        hleftWeight hrightWeight raw crossing parents rootWeight profile)
    (M N : ℕ) :
    List.replicate
        (compatibleCorrectionGrid
          (profile.left.terms M N)
          (profile.right.terms M N)).length
        (guardedGridParents
          hleftWeight hrightWeight crossing parents rootWeight) =
      let branch :=
        gridBranchParents
          hleftWeight hrightWeight crossing parents rootWeight
      List.replicate
        ((raw.multiplicityProfileFamily branch.leftIndex).multiplicity M N *
          (raw.multiplicityProfileFamily branch.rightIndex).multiplicity M N)
        (guardedGridParents
          hleftWeight hrightWeight crossing parents rootWeight) := by
  rw [
    synchronization.grid_parent_mul]

end GCSync

end BRSync
end TCTex
end Submission

/-!
# Program-wide root multiplicity synchronization

The local compatible-grid cardinality obligation can be attached uniformly to
every retained crossing in one annotated concrete schedule.  This file
packages that schedule-wide family and records the restriction maps needed by
structural induction on the schedule.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace SRSync

open HACoeff
open
  ITRec
open CRProgra
open
  CRProgra.RSPrograa
open CPProven
open CFCollec
open OCPartit
open BRSync
open UIComp
open
  ESIdx

/--
Local correction-grid cardinality synchronization for every retained crossing
of one annotated generated concrete schedule.
-/
abbrev GeneratedSynchronizationsProgram
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (profiles :
      InhomogeneousAvoidanceProfiles
        program) :=
  ∀ crossing hcrossing,
    GCSync
      hleftWeight hrightWeight raw crossing
        (generated crossing hcrossing)
        (program.weight_correction_crossings hcrossing)
        (profiles crossing hcrossing)

/-- Restrict append synchronization data to the left child. -/
def synchronizationsLeftAppend
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    {left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    {generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right)}
    {profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right)}
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.append left right)
          generated profiles) :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight raw left
        (crossings_left_append generated)
        (profilesLeftAppend profiles) :=
  fun crossing hcrossing =>
    synchronizations crossing (List.mem_append_left _ hcrossing)

/-- Restrict append synchronization data to the right child. -/
def synchronizationsRightAppend
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    {left right :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight}
    {generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.append left right)}
    {profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.append left right)}
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.append left right)
          generated profiles) :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight raw right
        (crossings_generated_append generated)
        (profilesRightAppend profiles) :=
  fun crossing hcrossing =>
    synchronizations crossing (List.mem_append_right _ hcrossing)

/-- Restrict retained-node synchronization data to the left child. -/
def synchronizationsLeftRetained
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
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
    {generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)}
    {profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)}
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          generated profiles) :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight raw left
        (crossings_generated_left generated)
        (profilesLeftRetained profiles) :=
  fun crossing hcrossing =>
    synchronizations crossing
      (List.mem_append_left _
        (List.mem_append_left _ hcrossing))

/-- Restrict retained-node synchronization data to the right child. -/
def synchronizationsRightRetained
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
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
    {generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)}
    {profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)}
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          generated profiles) :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight raw right
        (crossings_generated_retained generated)
        (profilesRightRetained profiles) :=
  fun crossing hcrossing =>
    synchronizations crossing (List.mem_append_right _ hcrossing)

/-- Recover the local synchronization obligation stored at a retained root. -/
def synchronizationRootRetained
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
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
    {generated :
      CGFroma (inverseDecoratedTerms M N)
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)}
    {profiles :
      InhomogeneousAvoidanceProfiles
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)}
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          generated profiles) :
    GCSync
      hleftWeight hrightWeight raw (crossedLeft, crossedRight)
        (generated_parents_retained generated) hweight
        (profileRootRetained profiles) :=
  synchronizations (crossedLeft, crossedRight) (by
    change
      (crossedLeft, crossedRight) ∈
        left.crossings ++ [(crossedLeft, crossedRight)] ++ right.crossings
    simp)

end SRSync
end TCTex
end Submission

/-!
# Root-synchronized erased-shape programs for scheduled generated batches

Local compatible-grid cardinality synchronization identifies not only the
scalar root contribution but the whole repeated erased-shape root program.
This file rewrites the retained-node annotated compiler equation in the
guarded raw-source branch vocabulary while leaving its recursive children
visible.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace SRErased

open HACoeff
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open CCGrida
open OCClos.DFTerm
open OCPartit
open
  SRSync
open BRSync
open UIComp
open
  UIErased
open
  ESIdx
open RTProgra
open
  GRProgra

/--
One synchronized annotation compiles to exactly the repeated root block used
by its guarded raw-source branch.
-/
lemma replicate_program_block
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    {crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length}
    {parents :
      CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms M N) crossing.2}
    {rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n}
    {profile :
      UIAvoida crossing}
    (synchronization :
      GCSync
        hleftWeight hrightWeight raw crossing parents rootWeight profile)
    (sourceLeft sourceRight : ℕ) :
    replicateErasedProgram
        (CWord.commutator profile.leftShape profile.rightShape)
        (compatibleCorrectionGrid
          (profile.left.terms sourceLeft sourceRight)
          (profile.right.terms sourceLeft sourceRight)).length =
      let branch :=
        gridBranchParents
          hleftWeight hrightWeight crossing parents rootWeight
      replicateErasedProgram
        branch.obstruction.correction.erasedShape
        ((raw.multiplicityProfileFamily branch.leftIndex).multiplicity
            sourceLeft sourceRight *
          (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
            sourceLeft sourceRight) := by
  rw [
    UIAvoida.root_obstruction_erased
      profile,
    synchronization.grid_parent_mul]
  dsimp only
  rw [obstruction_grid_parents]

/--
At a retained node, the annotated recursive compiler exposes the same guarded
root block as the symbolic scheduler.  The left and right annotated child
programs remain as the next structural synchronization obligations.
-/
lemma erased_program_block
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          generated profiles)
    (sourceLeft sourceRight : ℕ) :
    erasedProgram
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight =
      let branch :=
        gridBranchParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
            (generated_parents_retained generated) hweight
      ESProgra.append
        (erasedProgram left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight)
        (ESProgra.append
          (replicateErasedProgram
            branch.obstruction.correction.erasedShape
            ((raw.multiplicityProfileFamily branch.leftIndex).multiplicity
                sourceLeft sourceRight *
              (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
                sourceLeft sourceRight))
          (erasedProgram right
            (crossings_generated_retained generated)
            (profilesRightRetained profiles) sourceLeft sourceRight)) := by
  rw [shape_program_retained]
  rw [
    replicate_program_block
      (synchronizationRootRetained synchronizations)]

end SRErased
end TCTex
end Submission

/-!
# Root-synchronized multiplicity recurrence for scheduled generated batches

Once every annotated retained crossing carries its local compatible-grid
cardinality synchronization proof, the annotated schedule recurrence can be
written directly in the guarded raw-source branch vocabulary.  This leaves
the two recursive child multiplicities visible as the remaining induction
terms.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace RMReca

open HACoeff
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open OCPartit
open
  SRSync
open BRSync
open UIComp
open
  UMRec
open
  ESIdx

/--
At one retained node, program-wide root synchronization rewrites the annotated
compatible-grid cardinality to the guarded branch parent-multiplicity product.
-/
lemma erased_program_contribution
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          generated profiles)
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
        (let branch :=
          gridBranchParents
            hleftWeight hrightWeight (crossedLeft, crossedRight)
              (generated_parents_retained generated) hweight
        if branch.obstruction.correction.erasedShape = word then
          (raw.multiplicityProfileFamily branch.leftIndex).multiplicity
              sourceLeft sourceRight *
            (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
              sourceLeft sourceRight
        else
          0) +
        erasedMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight word := by
  rw [erased_program_retained]
  rw [
    GCSync.rootContribution_eq
      (synchronizationRootRetained synchronizations)]

end RMReca
end TCTex
end Submission

/-!
# Structural synchronization with one guarded raw-source branch

The guarded scheduler program for one raw-source branch consists of a nested
left program, a repeated correction-root block, and a nested right program.
After local compatible-grid cardinality synchronization, an annotated crossing
has exactly the same middle block.  This file packages the remaining local
structural obligation as coalescing of the two child programs.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace GBStruct

open HACoeff
open RRPkt
open
  RRPkt.POObstru
open
  RPCoales
open
  ITRec
open CFCollec
open CCGrida
open OCPartit
open
  SRErased
open BRSync
open UIComp
open
  OEBounda
open
  ESIdx
open
  RIRecurs
open RTProgra
open
  GRProgra

/-- Guarded nested-left scheduler program for one raw-source branch. -/
noncomputable def guardedErasedProgram
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
  if hleft :
      branch.obstruction.operationalNestedLeft.weight leftWeight rightWeight < n then
    profiledSchedulerProgram
      hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
      (operational_left_supported
        hleftWeight hrightWeight branch.obstruction branch.support hleft)
      (raw.multiplicityProfileFamily branch.leftIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      M N
  else
    ESProgra.empty

/-- Guarded repeated-root scheduler program for one raw-source branch. -/
noncomputable def guardedShapeProgram
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
  replicateErasedProgram
    branch.obstruction.correction.erasedShape
    ((raw.multiplicityProfileFamily branch.leftIndex).multiplicity M N *
      (raw.multiplicityProfileFamily branch.rightIndex).multiplicity M N)

/-- Guarded nested-right scheduler program for one raw-source branch. -/
noncomputable def guardedNestedProgram
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
  if hright :
      branch.obstruction.operationalNestedRight.weight leftWeight rightWeight < n then
    profiledSchedulerProgram
      hleftWeight hrightWeight branch.obstruction.operationalNestedRight
      (operational_nested_supported
        hleftWeight hrightWeight branch.obstruction branch.support hright)
      (raw.multiplicityProfileFamily branch.rightIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      M N
  else
    ESProgra.empty

/-- Expose the three scheduler-order blocks of one guarded raw-source branch. -/
lemma scheduler_program_append
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
    IOBranch.schedulerShapeProgram
        raw branch M N =
      ESProgra.append
        (guardedErasedProgram raw branch M N)
        (ESProgra.append
          (guardedShapeProgram raw branch M N)
          (guardedNestedProgram raw branch M N)) := by
  rw [
    IOBranch.schedulerShapeProgram,
    POBranch.schedulerShapeProgram,
    profiled_scheduler_append]
  simp only [guardedErasedProgram,
    guardedShapeProgram,
    guardedNestedProgram,
    IOBranch.profiledObstructionBranch]

/--
If annotated child programs coalesce with the two guarded nested programs,
then adjoining the guarded root block yields the whole branch scheduler
program.
-/
lemma coalesces_scheduler_program
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
    (annotatedLeft annotatedRight :
      ESProgra)
    (hleft :
      EMCoales.Rel annotatedLeft
        (guardedErasedProgram raw branch M N))
    (hright :
      EMCoales.Rel annotatedRight
        (guardedNestedProgram raw branch M N)) :
    EMCoales.Rel
      (ESProgra.append annotatedLeft
        (ESProgra.append
          (guardedShapeProgram raw branch M N)
          annotatedRight))
      (IOBranch.schedulerShapeProgram
        raw branch M N) := by
  rw [scheduler_program_append]
  exact
    EMCoales.Rel.append hleft
      (EMCoales.Rel.append
        (EMCoales.Rel.refl _) hright)

/--
For one synchronized concrete crossing, coalescing the two annotated children
with the guarded nested programs is enough to coalesce the complete annotated
crossing program with its guarded raw-source branch scheduler program.
-/
lemma annotated_coalesces_program
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    {crossing :
      DFTerm M N
          (inverseLabelledCollection M N).factors.length ×
        DFTerm M N
          (inverseLabelledCollection M N).factors.length}
    {parents :
      OCClos.DFTerm.CGFrom
          (inverseDecoratedTerms M N) crossing.1 ∧
        OCClos.DFTerm.CGFrom
          (inverseDecoratedTerms M N) crossing.2}
    {rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n}
    {profile :
      UIAvoida crossing}
    (synchronization :
      GCSync
        hleftWeight hrightWeight raw crossing parents rootWeight profile)
    (sourceLeft sourceRight : ℕ)
    (annotatedLeft annotatedRight :
      ESProgra)
    (hleft :
      EMCoales.Rel annotatedLeft
        (guardedErasedProgram raw
          (gridBranchParents
            hleftWeight hrightWeight crossing parents rootWeight)
          sourceLeft sourceRight))
    (hright :
      EMCoales.Rel annotatedRight
        (guardedNestedProgram raw
          (gridBranchParents
            hleftWeight hrightWeight crossing parents rootWeight)
          sourceLeft sourceRight)) :
    EMCoales.Rel
      (ESProgra.append annotatedLeft
        (ESProgra.append
          (replicateErasedProgram
            (CWord.commutator profile.leftShape profile.rightShape)
            (compatibleCorrectionGrid
              (profile.left.terms sourceLeft sourceRight)
              (profile.right.terms sourceLeft sourceRight)).length)
          annotatedRight))
      (IOBranch.schedulerShapeProgram
        raw
        (gridBranchParents
          hleftWeight hrightWeight crossing parents rootWeight)
        sourceLeft sourceRight) := by
  rw [
    replicate_program_block
      synchronization]
  exact
    coalesces_scheduler_program
      raw
      (gridBranchParents
        hleftWeight hrightWeight crossing parents rootWeight)
      sourceLeft sourceRight annotatedLeft annotatedRight hleft hright

end GBStruct
end TCTex
end Submission

/-!
# Concrete guards for scheduled nested raw-source branches

The recursive raw-source scheduler carries synthesized polynomial correction
profiles, so its nested programs are not fresh raw-source branches.  Their
cutoff guards are nevertheless the literal concrete collector guards.  This
file exposes that exact boundary for generated parent crossings.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace NBSync

open HACoeff
open RRPkt
open
  RRPkt.POObstru
open
  NCAligna
open
  RPCoales
open
  ITRec
open CFCollec
open OCClos
open OCClos.DFTerm
open OCPartit
open
  GBStruct
open
  ESIdx
open
  RIRecurs
open RTProgra
open
  GRProgra

/--
Nested-left scheduler program with the literal concrete collector cutoff
guard exposed.  Its right profile remains the synthesized parent-correction
profile, rather than a raw-source profile at the correction-root index.
-/
noncomputable def parentsNestedProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    ESProgra :=
  let branch :=
    gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight
  if hleft :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction (crossing.1.correction crossing.2)) < n then
    profiledSchedulerProgram
      hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
      (operational_left_supported
        hleftWeight hrightWeight branch.obstruction branch.support
          (by
            change
              (gridBranchParents
                hleftWeight hrightWeight crossing hparents
                  hrootWeight).obstruction.operationalNestedLeft.weight
                    leftWeight rightWeight < n
            simpa only [
              branch_generated_parents]
              using hleft))
      (raw.multiplicityProfileFamily branch.leftIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      sourceLeft sourceRight
  else
    ESProgra.empty

/--
Nested-right scheduler program with the literal concrete collector cutoff
guard exposed.  Its right profile remains the synthesized parent-correction
profile, rather than a raw-source profile at the correction-root index.
-/
noncomputable def generatedParentsProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    ESProgra :=
  let branch :=
    gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight
  if hright :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.2.correction (crossing.1.correction crossing.2)) < n then
    profiledSchedulerProgram
      hleftWeight hrightWeight branch.obstruction.operationalNestedRight
      (operational_nested_supported
        hleftWeight hrightWeight branch.obstruction branch.support
          (by
            change
              (gridBranchParents
                hleftWeight hrightWeight crossing hparents
                  hrootWeight).obstruction.operationalNestedRight.weight
                    leftWeight rightWeight < n
            simpa only [
              grid_branch_parents]
              using hright))
      (raw.multiplicityProfileFamily branch.rightIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      sourceLeft sourceRight
  else
    ESProgra.empty

/-- The guarded nested-left scheduler is exactly its concrete-guard view. -/
lemma guarded_generated_parents
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    guardedErasedProgram raw
        (gridBranchParents
          hleftWeight hrightWeight crossing hparents hrootWeight)
        sourceLeft sourceRight =
      parentsNestedProgram
        raw crossing hparents hrootWeight sourceLeft sourceRight := by
  unfold guardedErasedProgram
  unfold parentsNestedProgram
  simp only [
    branch_generated_parents]

/-- The guarded nested-right scheduler is exactly its concrete-guard view. -/
lemma guarded_nested_parents
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    guardedNestedProgram raw
        (gridBranchParents
          hleftWeight hrightWeight crossing hparents hrootWeight)
        sourceLeft sourceRight =
      generatedParentsProgram
        raw crossing hparents hrootWeight sourceLeft sourceRight := by
  unfold guardedNestedProgram
  unfold generatedParentsProgram
  simp only [
    grid_branch_parents]

/--
Rewrite the two local retained-node child synchronization contracts into
their concrete-guard form.
-/
lemma structural_synchronizations_parents
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ)
    (annotatedLeft annotatedRight :
      ESProgra) :
    (EMCoales.Rel annotatedLeft
        (guardedErasedProgram raw
          (gridBranchParents
            hleftWeight hrightWeight crossing hparents hrootWeight)
          sourceLeft sourceRight) ∧
      EMCoales.Rel annotatedRight
        (guardedNestedProgram raw
          (gridBranchParents
            hleftWeight hrightWeight crossing hparents hrootWeight)
          sourceLeft sourceRight)) ↔
      (EMCoales.Rel annotatedLeft
          (parentsNestedProgram
            raw crossing hparents hrootWeight sourceLeft sourceRight) ∧
        EMCoales.Rel annotatedRight
          (generatedParentsProgram
            raw crossing hparents hrootWeight sourceLeft sourceRight)) := by
  rw [
    guarded_generated_parents,
    guarded_nested_parents]

end NBSync
end TCTex
end Submission

/-!
# Structural synchronization at one retained annotated schedule node

The guarded raw-source scheduler and the annotated schedule compiler expose
the same repeated root block after local compatible-grid cardinality
synchronization.  This file packages the retained-node induction step: once
the two annotated children coalesce with the guarded nested branch programs,
the complete annotated retained node coalesces with its raw-source scheduler
branch.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace NSSync

open HACoeff
open
  RPCoales
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open OCPartit
open
  GBStruct
open
  SRErased
open
  SRSync
open UIComp
open
  UIErased
open
  ESIdx
open RTProgra
open
  GRProgra

/--
The retained-node structural induction step.  Root synchronization has
already discharged the middle block, so the only hypotheses are coalescing
for the annotated left and right child programs.
-/
lemma erased_coalesces_scheduler
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          generated profiles)
    (sourceLeft sourceRight : ℕ)
    (hleft :
      EMCoales.Rel
        (erasedProgram left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight)
        (guardedErasedProgram raw
          (gridBranchParents
            hleftWeight hrightWeight (crossedLeft, crossedRight)
            (generated_parents_retained generated) hweight)
          sourceLeft sourceRight))
    (hright :
      EMCoales.Rel
        (erasedProgram right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight)
        (guardedNestedProgram raw
          (gridBranchParents
            hleftWeight hrightWeight (crossedLeft, crossedRight)
            (generated_parents_retained generated) hweight)
          sourceLeft sourceRight)) :
    EMCoales.Rel
      (erasedProgram
        (RSPrograa.retained
          left crossedLeft crossedRight hweight right)
        generated profiles sourceLeft sourceRight)
      (IOBranch.schedulerShapeProgram
        raw
        (gridBranchParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight)
        sourceLeft sourceRight) := by
  rw [
    erased_program_block
      raw left right crossedLeft crossedRight hweight generated profiles
        synchronizations sourceLeft sourceRight]
  exact
    coalesces_scheduler_program
      raw
      (gridBranchParents
        hleftWeight hrightWeight (crossedLeft, crossedRight)
        (generated_parents_retained generated) hweight)
      sourceLeft sourceRight _ _ hleft hright

end NSSync
end TCTex
end Submission

/-!
# Concrete guards for scheduled nested finite-index traces

The recursive raw-source scheduler retains finite polynomial-orbit indices
before erasing them to Hall shapes.  Its nested traces carry synthesized
correction profiles, but their cutoff tests are still the literal concrete
collector guards.  This file exposes that finite-index normal form and checks
that erasing it recovers the existing collector-facing erased-shape programs.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace SISync

open HACoeff
open RRPkt
open
  RRPkt.POObstru
open
  NCAligna
open
  ITRec
open CFCollec
open
  SRAlign
open OCClos
open OCClos.DFTerm
open OCPartit
open
  NBSync
open
  RITrace
open
  RIRecurs
open
  ESIdx
open RTProgra
open
  FISchedu

/--
Nested-left finite-index scheduler trace with the literal concrete collector
cutoff guard exposed.  Its right profile is the synthesized parent-correction
profile.
-/
noncomputable def generatedConcreteParents
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  let branch :=
    gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight
  if hleft :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction (crossing.1.correction crossing.2)) < n then
    profiledExpansionScheduler
      hleftWeight hrightWeight branch.obstruction.operationalNestedLeft
      (operational_left_supported
        hleftWeight hrightWeight branch.obstruction branch.support
          (by
            change
              (gridBranchParents
                hleftWeight hrightWeight crossing hparents
                  hrootWeight).obstruction.operationalNestedLeft.weight
                    leftWeight rightWeight < n
            simpa only [
              branch_generated_parents]
              using hleft))
      (raw.multiplicityProfileFamily branch.leftIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      sourceLeft sourceRight
  else
    []

/--
Nested-right finite-index scheduler trace with the literal concrete collector
cutoff guard exposed.  Its right profile is the synthesized parent-correction
profile.
-/
noncomputable def generatedParentsNested
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  let branch :=
    gridBranchParents
      hleftWeight hrightWeight crossing hparents hrootWeight
  if hright :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.2.correction (crossing.1.correction crossing.2)) < n then
    profiledExpansionScheduler
      hleftWeight hrightWeight branch.obstruction.operationalNestedRight
      (operational_nested_supported
        hleftWeight hrightWeight branch.obstruction branch.support
          (by
            change
              (gridBranchParents
                hleftWeight hrightWeight crossing hparents
                  hrootWeight).obstruction.operationalNestedRight.weight
                    leftWeight rightWeight < n
            simpa only [
              grid_branch_parents]
              using hright))
      (raw.multiplicityProfileFamily branch.rightIndex)
      ((raw.multiplicityProfileFamily branch.leftIndex).correction
        branch.obstruction
        (raw.multiplicityProfileFamily branch.rightIndex))
      sourceLeft sourceRight
  else
    []

/--
The finite-index scheduler recurrence for generated concrete parents uses the
literal concrete nested cutoff guards and emits the concrete root index in its
middle block.
-/
lemma scheduler_idx_parents
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
    IOBranch.schedulerFinIdx
        raw branch inputLeft inputRight =
      generatedConcreteParents
          raw crossing hparents hrootWeight inputLeft inputRight ++
        List.replicate
          ((raw.multiplicityProfileFamily branch.leftIndex).multiplicity
              inputLeft inputRight *
            (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
              inputLeft inputRight)
          (guardedGridParents
            hleftWeight hrightWeight crossing hparents hrootWeight) ++
        generatedParentsNested
          raw crossing hparents hrootWeight inputLeft inputRight := by
  dsimp only
  rw [
    scheduler_parents_append]
  unfold generatedConcreteParents
  unfold generatedParentsNested
  simp only [
    branch_generated_parents,
    grid_branch_parents]

/-- Erasing the collector-facing nested-left finite trace recovers its shape program. -/
lemma key_erased_parents
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    (generatedConcreteParents
      raw crossing hparents hrootWeight sourceLeft sourceRight).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      (parentsNestedProgram
        raw crossing hparents hrootWeight sourceLeft sourceRight).trace := by
  unfold generatedConcreteParents
  unfold parentsNestedProgram
  dsimp only
  split
  · exact
      key_fin_program
        _ _ _ _ _ _ _ _
  · rfl

/-- Erasing the collector-facing nested-right finite trace recovers its shape program. -/
lemma key_parents_nested
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
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
    (sourceLeft sourceRight : ℕ) :
    (generatedParentsNested
      raw crossing hparents hrootWeight sourceLeft sourceRight).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      (generatedParentsProgram
        raw crossing hparents hrootWeight sourceLeft sourceRight).trace := by
  unfold generatedParentsNested
  unfold generatedParentsProgram
  dsimp only
  split
  · exact
      key_fin_program
        _ _ _ _ _ _ _ _
  · rfl

end SISync
end TCTex
end Submission

/-!
# Structural synchronization for guarded scheduler forests

An annotated concrete schedule is a forest: `append` joins independent
components, while a retained root represents one guarded raw-source branch.
After root-cardinality synchronization, the only non-formal obligations at a
retained root are comparison of its two concrete child programs with the two
guarded nested obstruction programs.

This file packages that boundary recursively.  Empty and append nodes are
handled structurally; retained roots are discharged by the local theorem from
the preceding leaf.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace GSStruct

open HACoeff
open
  RPCoales
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open OCPartit
open
  GBStruct
open
  SRSync
open
  NSSync
open UIComp
open
  UIErased
open
  ESIdx
open RTProgra
open
  GRProgra

/--
Compile a provenance-certified concrete schedule forest to the guarded
scheduler program attached to each retained root.
-/
noncomputable def schedulerProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (sourceLeft sourceRight : ℕ) :
    ESProgra :=
  match program with
  | .empty =>
      ESProgra.empty
  | .append left right =>
      ESProgra.append
        (schedulerProgram raw left
          (crossings_left_append generated)
          sourceLeft sourceRight)
        (schedulerProgram raw right
          (crossings_generated_append generated)
          sourceLeft sourceRight)
  | .retained _left crossedLeft crossedRight hweight _right =>
      IOBranch.schedulerShapeProgram
        raw
        (gridBranchParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight)
        sourceLeft sourceRight

/--
At every retained root of a schedule forest, the annotated concrete children
coalesce with the two guarded nested obstruction programs.  Append nodes
carry this obligation recursively for both forest components.
-/
def BranchStructuralSynchronizations
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    Prop :=
  match program with
  | .empty =>
      True
  | .append left right =>
      BranchStructuralSynchronizations raw left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight ∧
        BranchStructuralSynchronizations raw right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight
  | .retained left crossedLeft crossedRight hweight right =>
      let branch :=
        gridBranchParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight
      EMCoales.Rel
          (erasedProgram left
            (crossings_generated_left generated)
            (profilesLeftRetained profiles) sourceLeft sourceRight)
          (guardedErasedProgram raw branch
            sourceLeft sourceRight) ∧
        EMCoales.Rel
          (erasedProgram right
            (crossings_generated_retained generated)
            (profilesRightRetained profiles) sourceLeft sourceRight)
          (guardedNestedProgram raw branch
            sourceLeft sourceRight)

/--
Root-cardinality synchronization and the nested-child contracts compile an
annotated concrete schedule forest to its guarded scheduler forest.
-/
lemma program_coalesces_scheduler
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw program generated profiles)
    (sourceLeft sourceRight : ℕ)
    (hnested :
      BranchStructuralSynchronizations raw program
        generated profiles sourceLeft sourceRight) :
    EMCoales.Rel
      (erasedProgram program generated profiles
        sourceLeft sourceRight)
      (schedulerProgram raw program generated
        sourceLeft sourceRight) := by
  induction program with
  | empty =>
      exact
        EMCoales.Rel.refl
          ESProgra.empty
  | append left right ihleft ihright =>
      exact
        EMCoales.Rel.append
          (ihleft
            (crossings_left_append generated)
            (profilesLeftAppend profiles)
            (synchronizationsLeftAppend synchronizations)
            hnested.1)
          (ihright
            (crossings_generated_append generated)
            (profilesRightAppend profiles)
            (synchronizationsRightAppend synchronizations)
            hnested.2)
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      exact
        erased_coalesces_scheduler
          raw left right crossedLeft crossedRight hweight generated profiles
            synchronizations sourceLeft sourceRight hnested.1 hnested.2

end GSStruct
end TCTex
end Submission

/-!
# Finite-index synchronization for scheduled concrete forests

The finite-index trace of an annotated concrete schedule is a forest of
compatible-grid root blocks.  At a retained node, the symbolic scheduler has
the same repeated concrete root index after local cardinality synchronization.
Its two recursive traces retain synthesized contextual profiles.

This file packages the remaining contextual child equations recursively and
folds them through the concrete schedule forest.  No fresh raw-source child
profile is introduced.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  BISync

open HACoeff
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open OCPartit
open
  SISync
open
  SRSync
open BRSync
open UIComp
open
  UFIdx
open
  RITrace
open
  ESIdx
open
  FISchedu

/--
Compile each retained root of a concrete schedule forest to its contextual
finite-index scheduler trace.
-/
noncomputable def schedulerIndexProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (program :
      RSPrograa
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        n leftWeight rightWeight)
    (generated :
      CGFroma (inverseDecoratedTerms M N) program)
    (sourceLeft sourceRight : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  match program with
  | .empty =>
      []
  | .append left right =>
      schedulerIndexProgram raw left
          (crossings_left_append generated)
          sourceLeft sourceRight ++
        schedulerIndexProgram raw right
          (crossings_generated_append generated)
          sourceLeft sourceRight
  | .retained _left crossedLeft crossedRight hweight _right =>
      IOBranch.schedulerFinIdx
        raw
        (gridBranchParents
          hleftWeight hrightWeight (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight)
        sourceLeft sourceRight

/--
At every retained root of a schedule forest, the annotated concrete child
traces equal the two contextual synthesized-profile scheduler traces.  Append
nodes retain this obligation recursively for both forest components.
-/
def BranchSynchronizationsProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    Prop :=
  match program with
  | .empty =>
      True
  | .append left right =>
      BranchSynchronizationsProgram raw left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight ∧
        BranchSynchronizationsProgram raw right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight
  | .retained left crossedLeft crossedRight hweight right =>
      finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          left
          (crossings_generated_left generated)
          (profilesLeftRetained profiles) sourceLeft sourceRight =
        generatedConcreteParents raw
          (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight
          sourceLeft sourceRight ∧
      finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight =
        generatedParentsNested raw
          (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight
          sourceLeft sourceRight

/--
Root-cardinality synchronization and contextual nested-child synchronization
identify the complete annotated finite-index forest with its guarded symbolic
scheduler forest.
-/
lemma program_guarded_scheduler
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw program generated profiles)
    (sourceLeft sourceRight : ℕ)
    (hnested :
      BranchSynchronizationsProgram raw
        program generated profiles sourceLeft sourceRight) :
    finIdxProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        program generated profiles sourceLeft sourceRight =
      schedulerIndexProgram raw program generated
        sourceLeft sourceRight := by
  induction program with
  | empty =>
      rfl
  | append left right ihleft ihright =>
      rw [index_program_append]
      exact
        congrArg₂ (· ++ ·)
          (ihleft
            (crossings_left_append generated)
            (profilesLeftAppend profiles)
            (synchronizationsLeftAppend synchronizations)
            hnested.1)
          (ihright
            (crossings_generated_append generated)
            (profilesRightAppend profiles)
            (synchronizationsRightAppend synchronizations)
            hnested.2)
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      rw [index_program_retained]
      rw [
        GCSync.replicate_grid_index
          (synchronizationRootRetained synchronizations)]
      rw [hnested.1, hnested.2]
      exact
        (scheduler_idx_parents
          hleftWeight hrightWeight raw (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight
          sourceLeft sourceRight).symm

end BISync
end TCTex
end Submission

/-!
# Guarded scheduler forest alignment for scheduled generated batches

The annotated schedule compiler now coalesces with the guarded scheduler
forest attached to its retained roots.  The universal expansion pipeline uses
the canonical guarded raw-source scheduler instead.  This file isolates the
remaining outer-root alignment and adapts the forest-level theorem into the
existing structural decomposition.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace GFStruct

open HACoeff
open
  RPCoales
open CRProgra
open CPProven
open CFCollec
open FIProf
open OCPartit
open
  GSStruct
open
  SRSync
open UIComp
open UIStruct
open
  ISLift
open RTProgra
open
  GRProgra

/--
Forest-level structural synchronization data.  The retained-root theorem
handles the internal scheduler blocks.  The last field identifies the
resulting forest of outer guarded branches with the canonical raw-source grid.
-/
structure SFStruct
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
  rootSynchronizations :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight
        (multiplicityProfileShape raw)
      program generated profiles
  nestedBranchSynchronizations :
    ∀ M N,
      BranchStructuralSynchronizations
        (multiplicityProfileShape raw)
        program generated profiles M N
  guarded_forest_coalesces :
    ∀ M N,
      EMCoales.Rel
        (schedulerProgram
          (multiplicityProfileShape
            raw)
          program generated M N)
        (guardedSchedulerProgram
          (multiplicityProfileShape
            raw)
          M N)

namespace SFStruct

/--
Compile forest-level synchronization to the structural decomposition consumed
by the universal generated-batch expansion pipeline.
-/
noncomputable def
    scheduledStructuralCoalescing
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFStruct
        hleftWeight hrightWeight raw) :
    SSCoales
      hleftWeight hrightWeight raw where
  sourceLeft :=
    alignment.sourceLeft
  sourceRight :=
    alignment.sourceRight
  program :=
    alignment.program
  generated :=
    alignment.generated
  profiles :=
    alignment.profiles
  programs_coalesce M N :=
    (program_coalesces_scheduler
      (multiplicityProfileShape raw)
      alignment.program alignment.generated alignment.profiles
        alignment.rootSynchronizations M N
        (alignment.nestedBranchSynchronizations M N)).trans
      (alignment.guarded_forest_coalesces M N)

/-- Compile forest-level synchronization directly to universal generated batches. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFStruct
        hleftWeight hrightWeight raw) :=
  alignment.scheduledStructuralCoalescing
    |>.generatedParentsDecomposition

end SFStruct

end GFStruct
end TCTex
end Submission

/-!
# Concrete nested-branch contracts for scheduled programs

The guarded scheduler forest contract can be stated entirely with the
literal concrete cutoff guards of each retained crossing.  This file lifts
the local concrete-guard adapter recursively over concrete schedule forests.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace SBSynca

open HACoeff
open
  RPCoales
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open OCPartit
open
  NBSync
open
  GSStruct
open UIComp
open
  UIErased
open
  ESIdx
open RTProgra

/--
Concrete-guard form of the nested child synchronization contract at every
retained node of a schedule forest.
-/
def StructuralSynchronizationsProgram
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    Prop :=
  match program with
  | .empty =>
      True
  | .append left right =>
      StructuralSynchronizationsProgram raw left
          (crossings_left_append generated)
          (profilesLeftAppend profiles) sourceLeft sourceRight ∧
        StructuralSynchronizationsProgram raw right
          (crossings_generated_append generated)
          (profilesRightAppend profiles) sourceLeft sourceRight
  | .retained left crossedLeft crossedRight hweight right =>
      EMCoales.Rel
          (erasedProgram left
            (crossings_generated_left generated)
            (profilesLeftRetained profiles) sourceLeft sourceRight)
          (parentsNestedProgram raw
            (crossedLeft, crossedRight)
            (generated_parents_retained generated) hweight
            sourceLeft sourceRight) ∧
        EMCoales.Rel
          (erasedProgram right
            (crossings_generated_retained generated)
            (profilesRightRetained profiles) sourceLeft sourceRight)
          (generatedParentsProgram raw
            (crossedLeft, crossedRight)
            (generated_parents_retained generated) hweight
            sourceLeft sourceRight)

/--
The original guarded scheduler forest contract is equivalent to the
collector-facing concrete-guard contract.
-/
lemma branch_structural_synchronizations
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    BranchStructuralSynchronizations raw program
        generated profiles sourceLeft sourceRight ↔
      StructuralSynchronizationsProgram raw
        program generated profiles sourceLeft sourceRight := by
  induction program with
  | empty =>
      rfl
  | append left right ihleft ihright =>
      exact and_congr
        (ihleft
          (crossings_left_append generated)
          (profilesLeftAppend profiles))
        (ihright
          (crossings_generated_append generated)
          (profilesRightAppend profiles))
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      exact
        structural_synchronizations_parents
          raw (crossedLeft, crossedRight)
          (generated_parents_retained generated) hweight
          sourceLeft sourceRight
          (erasedProgram left
            (crossings_generated_left generated)
            (profilesLeftRetained profiles) sourceLeft sourceRight)
          (erasedProgram right
            (crossings_generated_retained generated)
            (profilesRightRetained profiles) sourceLeft sourceRight)

end SBSynca
end TCTex
end Submission

/-!
# Finite-index forest alignment for scheduled generated batches

The annotated concrete schedule and the guarded symbolic scheduler can be
compared before erasing polynomial-orbit indices.  At each retained node,
root multiplicity synchronization identifies the repeated root block and the
contextual child hypotheses identify the two synthesized-profile traces.

This file packages the remaining outer finite-index forest permutation.  Its
erasure supplies the existing scheduler-program decomposition used by the
universal generated-batch Claim 5 pipeline.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace GSForest

open HACoeff
open CRProgra
open CPProven
open CFCollec
open FIProf
open OCPartit
open
  BISync
open SRSync
open UIComp
open UIAlign
open UFIdx
open RITrace
open
  ISLift
open
  FISchedu

/--
Finite-index forest synchronization data stated with the concrete cutoff
guards of retained child crossings.
-/
structure BFAlign
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
  rootSynchronizations :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight
        (multiplicityProfileShape raw)
      program generated profiles
  concreteNestedSynchronizations :
    ∀ M N,
      BranchSynchronizationsProgram
        (multiplicityProfileShape raw)
        program generated profiles M N
  guarded_forest_canonical :
    ∀ M N,
      List.Perm
        (schedulerIndexProgram
          (multiplicityProfileShape
            raw)
          program generated M N)
        (guardedIdxFin
          (multiplicityProfileShape
            raw)
          M N)

namespace BFAlign

/--
Fold the local finite-index synchronization equations through the concrete
schedule forest and compose with the outer canonical scheduler permutation.
-/
lemma program_perm_scheduler
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      BFAlign
        hleftWeight hrightWeight raw)
    (M N : ℕ) :
    List.Perm
      (finIdxProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        alignment.program alignment.generated alignment.profiles M N)
      (guardedIdxFin
        (multiplicityProfileShape raw)
        M N) :=
  (List.Perm.of_eq
      (program_guarded_scheduler
        (multiplicityProfileShape raw)
        alignment.program alignment.generated alignment.profiles
        alignment.rootSynchronizations M N
        (alignment.concreteNestedSynchronizations M N))).trans
    (alignment.guarded_forest_canonical M N)

/--
Erase the stronger finite-index alignment and recover the scheduler-program
decomposition consumed by the generated-batch expansion pipeline.
-/
noncomputable def schedu_sched_decom
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      BFAlign
        hleftWeight hrightWeight raw) :
    SSDecomp
      hleftWeight hrightWeight raw where
  sourceLeft :=
    alignment.sourceLeft
  sourceRight :=
    alignment.sourceRight
  program :=
    alignment.program
  generated :=
    alignment.generated
  profiles :=
    alignment.profiles
  scheduler_program_perm M N := by
    rw [←
      key_shape_program
        alignment.program alignment.generated alignment.profiles M N]
    rw [←
      key_erased_program]
    exact
      (alignment.program_perm_scheduler M N).map
        (fun index => (retainedOrbitKey index).erasedShape)

/-- Compile finite-index forest alignment directly to universal generated batches. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      BFAlign
        hleftWeight hrightWeight raw) :=
  alignment.schedu_sched_decom
    |>.generatedParentsDecomposition

end BFAlign

end GSForest
end TCTex
end Submission

/-!
# Root-synchronized finite-index multiplicity recurrences for scheduled batches

The erased-shape scheduled-batch recurrence already rewrites one compatible-grid
cardinality to the guarded raw-source parent-multiplicity product.  The stronger
finite-index trace retains the concrete polynomial-orbit root selected by that
crossing.  This file records the corresponding scalar rewrite after fixing one
retained orbit index and transports it through a complete concrete schedule
forest.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace RIRec

open HACoeff
open
  ITRec
open CRProgra
open CPProven
open CFCollec
open CCGrida
open OCClos
open OCClos.DFTerm
open OCPartit
open
  BISync
open
  SRSync
open BRSync
open UIComp
open
  UIRec
open
  RITrace
open
  ESIdx

namespace GCSync

/--
After fixing one retained orbit index, local compatible-grid cardinality
synchronization rewrites the annotated repeated-root contribution to the
guarded raw-source parent-multiplicity product.
-/
lemma root_index_contribution
    {sourceLeft sourceRight n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    {crossing :
      DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length ×
        DFTerm sourceLeft sourceRight
          (inverseLabelledCollection sourceLeft sourceRight).factors.length}
    {parents :
      CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.1 ∧
        CGFrom
          (inverseDecoratedTerms sourceLeft sourceRight) crossing.2}
    {rootWeight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) < n}
    {profile :
      UIAvoida crossing}
    (synchronization :
      GCSync
        hleftWeight hrightWeight raw crossing parents rootWeight profile)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    (if
      guardedGridParents
          hleftWeight hrightWeight crossing parents rootWeight =
        index then
      (compatibleCorrectionGrid
        (profile.left.terms M N)
        (profile.right.terms M N)).length
    else
      0) =
      let branch :=
        gridBranchParents
          hleftWeight hrightWeight crossing parents rootWeight
      if
        guardedGridParents
            hleftWeight hrightWeight crossing parents rootWeight =
          index then
        (raw.multiplicityProfileFamily branch.leftIndex).multiplicity
              M N *
          (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
              M N
      else
        0 := by
  rw [
    synchronization.grid_parent_mul]

end GCSync

/--
At one retained node, program-wide root synchronization rewrites the annotated
finite-index compatible-grid cardinality to the guarded branch
parent-multiplicity product.
-/
lemma multiplicity_program_contribution
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw
          (RSPrograa.retained
            left crossedLeft crossedRight hweight right)
          generated profiles)
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
        (let branch :=
          gridBranchParents
            hleftWeight hrightWeight (crossedLeft, crossedRight)
              (generated_parents_retained generated) hweight
        if
          guardedGridParents
              hleftWeight hrightWeight (crossedLeft, crossedRight)
              (generated_parents_retained generated) hweight =
            index then
          (raw.multiplicityProfileFamily branch.leftIndex).multiplicity
                sourceLeft sourceRight *
            (raw.multiplicityProfileFamily branch.rightIndex).multiplicity
                sourceLeft sourceRight
        else
          0) +
        indexMultiplicityProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight) right
          (crossings_generated_retained generated)
          (profilesRightRetained profiles) sourceLeft sourceRight index := by
  rw [index_multiplicity_program]
  rw [
    GCSync.root_index_contribution
      (synchronizationRootRetained synchronizations)]

/--
Root-cardinality and concrete nested-child synchronization identify each
scheduled finite-index multiplicity with the corresponding guarded scheduler
forest count.
-/
lemma multiplicity_program_scheduler
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RMProf
        n leftWeight rightWeight hleftWeight hrightWeight)
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
    (synchronizations :
      GeneratedSynchronizationsProgram
        hleftWeight hrightWeight raw program generated profiles)
    (sourceLeft sourceRight : ℕ)
    (hnested :
      BranchSynchronizationsProgram raw
        program generated profiles sourceLeft sourceRight)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        program generated profiles sourceLeft sourceRight index =
      (schedulerIndexProgram raw program generated
        sourceLeft sourceRight).count index := by
  unfold indexMultiplicityProgram
  rw [
    program_guarded_scheduler
      raw program generated profiles synchronizations sourceLeft sourceRight
        hnested]

end RIRec
end TCTex
end Submission

/-!
# Claim 5 from guarded scheduler forest alignment

Forest-level structural alignment compiles annotated unrestricted generated
batches into the universal guarded raw-source expansion criterion.  This file
composes that route with the signed extension boundary and restates the Claim
5 coordinate-polynomial constructor directly in guarded scheduler forest
vocabulary.

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
open GFStruct

namespace GFStruct

namespace SFStruct

/--
Remaining signed extension after guarded scheduler forest alignment has been
compiled through the universal generated-batch expansion pipeline.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SFStruct
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PCDecomp.AILift.{u}
    (d := d) scheduler
      alignment.generatedParentsDecomposition

/--
Truncated signed recollection law after guarded scheduler forest alignment has
been compiled through the universal generated-batch expansion pipeline.
-/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SFStruct
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PCDecomp.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.generatedParentsDecomposition

/-- For guarded scheduler forest alignment, the two signed extension inputs agree. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SFStruct
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  PCDecomp.satisfies_trunc_lift
    scheduler
      alignment.generatedParentsDecomposition

end SFStruct

end GFStruct

namespace TSInput

open GFStruct

/--
Guarded scheduler forest alignment, its signed lift, singleton recollections,
and graded Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem
    genForestAlignment
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
    (alignment :
      SFStruct
        (by simp) (by simp) scheduler.raw)
    (lift :
      SFStruct.AILift.{u}
        (d := d) scheduler alignment)
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
      alignment.generatedParentsDecomposition
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent constructor input for
the guarded scheduler forest Claim 5 route.
-/
theorem
    scheduledGenForest
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
    (alignment :
      SFStruct
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SFStruct.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
      alignment.generatedParentsDecomposition
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Concrete-guard forest alignment for scheduled generated batches

The forest-level Claim 5 interface can use literal concrete collector guards
at every nested retained branch.  This file adapts that collector-facing
interface to the guarded scheduler forest alignment consumed by the existing
universal expansion pipeline.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace SFStructa

open HACoeff
open
  RPCoales
open CRProgra
open CPProven
open CFCollec
open FIProf
open OCPartit
open
  NBSync
open
  GFStruct
open
  SBSynca
open
  GSStruct
open
  SRSync
open UIComp
open
  ISLift
open RTProgra
open
  GRProgra

/--
Forest-level structural synchronization data stated with the concrete cutoff
guards of retained child crossings.
-/
structure SSAlign
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
  rootSynchronizations :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight
        (multiplicityProfileShape raw)
      program generated profiles
  concreteBranchSynchronizations :
    ∀ M N,
      StructuralSynchronizationsProgram
        (multiplicityProfileShape raw)
        program generated profiles M N
  guarded_forest_coalesces :
    ∀ M N,
      EMCoales.Rel
        (schedulerProgram
          (multiplicityProfileShape
            raw)
          program generated M N)
        (guardedSchedulerProgram
          (multiplicityProfileShape
            raw)
          M N)

namespace SSAlign

/--
Forget the concrete-guard presentation and recover the guarded scheduler
forest alignment consumed by the universal expansion pipeline.
-/
noncomputable def scheduledForestStructural
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSAlign
        hleftWeight hrightWeight raw) :
    SFStruct
      hleftWeight hrightWeight raw where
  sourceLeft :=
    alignment.sourceLeft
  sourceRight :=
    alignment.sourceRight
  program :=
    alignment.program
  generated :=
    alignment.generated
  profiles :=
    alignment.profiles
  rootSynchronizations :=
    alignment.rootSynchronizations
  nestedBranchSynchronizations M N :=
    (branch_structural_synchronizations
      (multiplicityProfileShape raw)
      alignment.program alignment.generated alignment.profiles M N).mpr
        (alignment.concreteBranchSynchronizations M N)
  guarded_forest_coalesces :=
    alignment.guarded_forest_coalesces

/-- Compile concrete-guard forest alignment directly to universal generated batches. -/
noncomputable def
    generatedParentsDecomposition
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSAlign
        hleftWeight hrightWeight raw) :=
  alignment.scheduledForestStructural
    |>.generatedParentsDecomposition

end SSAlign

end SFStructa
end TCTex
end Submission

/-!
# Exact occurrence accounting from scheduled finite-index forest alignment

The flattened annotated batch trace is a useful common middle list.  The
finite-index forest alignment identifies it with the symbolic scheduler.  A
second permutation can identify that same list with the canonical concrete
collector's root-index trace.

This file packages that two-sided comparison and compiles it to the existing
layer-free exact occurrence-accounting kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace IABridge

open HACoeff
open
  ALFree
open
  CLFree
open FIProf
open
  GSForest
open
  BISync
open UFIdx
open
  ISLift

/--
Two-sided finite-index comparison through the flattened annotated generated
batch trace.
-/
structure SFAligna
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  finiteIndexAlignment :
    BFAlign
      hleftWeight hrightWeight raw
  program_perm_root :
    ∀ M N,
      List.Perm
        (finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          finiteIndexAlignment.program finiteIndexAlignment.generated
          finiteIndexAlignment.profiles M N)
        (generatedGridBranch
          (n := n) hleftWeight hrightWeight M N)

namespace SFAligna

/--
The concrete guarded scheduler forest itself permutes to the canonical
concrete collector root-index trace.
-/
lemma guarded_scheduler_perm
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAligna
        hleftWeight hrightWeight raw)
    (M N : ℕ) :
    List.Perm
      (schedulerIndexProgram
        (multiplicityProfileShape raw)
        alignment.finiteIndexAlignment.program
        alignment.finiteIndexAlignment.generated M N)
      (generatedGridBranch
        (n := n) hleftWeight hrightWeight M N) :=
  (List.Perm.of_eq
      (program_guarded_scheduler
        (multiplicityProfileShape raw)
        alignment.finiteIndexAlignment.program
        alignment.finiteIndexAlignment.generated
        alignment.finiteIndexAlignment.profiles
        alignment.finiteIndexAlignment.rootSynchronizations M N
        (alignment.finiteIndexAlignment.concreteNestedSynchronizations
          M N)).symm).trans
    (alignment.program_perm_root M N)

/--
Compile the two-sided annotated-batch comparison to exact scheduler-ordered
finite-index occurrence accounting for the canonical collector.
-/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAligna
        hleftWeight hrightWeight raw) :
    SOAccoun
      (n := n) hleftWeight hrightWeight where
  raw :=
    raw
  scheduler_perm_root M N :=
    (alignment.finiteIndexAlignment.program_perm_scheduler
      M N).symm.trans
        (alignment.program_perm_root M N)

/--
Erase exact occurrence accounting to the layer-free canonical Hall-shape
expansion kernel.
-/
noncomputable def
    guardedShapeExpansion
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAligna
        hleftWeight hrightWeight raw) :=
  alignment.schedulerOccAccounting
    |>.guardedShapeExpansion

end SFAligna

end IABridge
end TCTex
end Submission

/-!
# Claim 5 from finite-index concrete-guard scheduler forest alignment

Finite-index forest alignment erases to universal generated compatible-grid
batches.  Those batches feed the existing signed-extension Claim 5
constructor.  This file records the direct composite interface.

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
open CRLayer
open
  SEAlign
open
  GSForest

namespace GSForest

namespace BFAlign

/-- Remaining signed extension after finite-index forest alignment. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      BFAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PCDecomp.AILift.{u}
    (d := d) scheduler
      alignment.generatedParentsDecomposition

/-- Truncated signed recollection law after finite-index forest alignment. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      BFAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  PCDecomp.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.generatedParentsDecomposition

/-- For finite-index forest alignment, the two signed extension inputs agree. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      BFAlign
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  PCDecomp.satisfies_trunc_lift
    scheduler
      alignment.generatedParentsDecomposition

end BFAlign

end GSForest

namespace TSInput

open
  GSForest

/--
Finite-index concrete-guard scheduler forest alignment and its signed lift
construct the Claim 5 coordinate polynomials.
-/
theorem
    idxAlignmentLift
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
    (alignment :
      BFAlign
        (by simp) (by simp) scheduler.raw)
    (lift :
      BFAlign.AILift.{u}
        (d := d) scheduler alignment)
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
      alignment.generatedParentsDecomposition
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input for finite-index forest alignment.
-/
theorem
    coordFinTrunc
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
    (alignment :
      BFAlign
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      BFAlign.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
      alignment.generatedParentsDecomposition
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from concrete-guard scheduler forest alignment

The collector-facing concrete-guard forest alignment compiles to the guarded
scheduler forest interface and therefore to the Claim 5 coordinate-polynomial
constructor.

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
  SFStructa
open
  GFStruct

namespace SFStructa

namespace SSAlign

/-- Remaining signed extension after concrete-guard forest alignment. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SSAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SFStruct.AILift.{u}
    (d := d) scheduler
      alignment.scheduledForestStructural

/-- Truncated signed recollection law after concrete-guard forest alignment. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SSAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SFStruct.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.scheduledForestStructural

/-- For concrete-guard forest alignment, the two signed extension inputs agree. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SSAlign
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  SFStruct.satisfies_trunc_lift
    scheduler
      alignment.scheduledForestStructural

end SSAlign

end SFStructa

namespace TSInput

open
  SFStructa

/--
Concrete-guard scheduler forest alignment and its signed lift construct the
Claim 5 coordinate polynomials.
-/
theorem
    scheduledSchedulerForest
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
    (alignment :
      SSAlign
        (by simp) (by simp) scheduler.raw)
    (lift :
      SSAlign.AILift.{u}
        (d := d) scheduler alignment)
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
  input.genForestAlignment
    hn H hH scheduler
      alignment.scheduledForestStructural
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input for concrete-guard scheduler forest alignment.
-/
theorem
    scheduledForestAlignment
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
    (alignment :
      SSAlign
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SSAlign.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
  input.scheduledGenForest
    hn H hH scheduler
      alignment.scheduledForestStructural
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Multiplicity criteria for scheduled finite-index forest accounting

The remaining outer scheduled-forest comparisons are permutations of finite
polynomial-orbit index traces.  For proofs by symbolic coefficient
calculation, pointwise multiplicity equalities are a more convenient
interface.  This file packages countwise variants of both outer comparisons
and compiles them back to the permutation-based alignment records.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


open HACoeff
open CRProgra
open CPProven
open CFCollec
open
  CLFree
open FIProf
open OCPartit
open
  GSForest
open
  IABridge
open
  BISync
open SRSync
open UIComp
open UFIdx
open
  RITrace
open
  ISLift
open
  FISchedu

namespace AMCrit

/--
Countwise form of finite-index alignment between a compiled concrete schedule
forest and the canonical symbolic scheduler.
-/
structure SSForest
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
  rootSynchronizations :
    GeneratedSynchronizationsProgram
      hleftWeight hrightWeight
        (multiplicityProfileShape raw)
      program generated profiles
  concreteNestedSynchronizations :
    ∀ M N,
      BranchSynchronizationsProgram
        (multiplicityProfileShape raw)
        program generated profiles M N
  guarded_forest_count :
    ∀ M N index,
      (schedulerIndexProgram
        (multiplicityProfileShape raw)
        program generated M N).count index =
      (guardedIdxFin
        (multiplicityProfileShape raw)
        M N).count index

namespace SSForest

/-- Promote pointwise scheduler multiplicities to a finite-index forest permutation. -/
noncomputable def scheduledSchedulerAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    BFAlign
      hleftWeight hrightWeight raw where
  sourceLeft :=
    alignment.sourceLeft
  sourceRight :=
    alignment.sourceRight
  program :=
    alignment.program
  generated :=
    alignment.generated
  profiles :=
    alignment.profiles
  rootSynchronizations :=
    alignment.rootSynchronizations
  concreteNestedSynchronizations :=
    alignment.concreteNestedSynchronizations
  guarded_forest_canonical M N := by
    classical
    rw [List.perm_iff_count]
    exact alignment.guarded_forest_count M N

end SSForest

end AMCrit

namespace GSForest

open
  AMCrit

namespace BFAlign

/-- Forget a finite-index forest permutation down to pointwise multiplicities. -/
noncomputable def
    scheduledGeneratedForest
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      BFAlign
        hleftWeight hrightWeight raw) :
    SSForest
      hleftWeight hrightWeight raw where
  sourceLeft :=
    alignment.sourceLeft
  sourceRight :=
    alignment.sourceRight
  program :=
    alignment.program
  generated :=
    alignment.generated
  profiles :=
    alignment.profiles
  rootSynchronizations :=
    alignment.rootSynchronizations
  concreteNestedSynchronizations :=
    alignment.concreteNestedSynchronizations
  guarded_forest_count M N index :=
    (alignment.guarded_forest_canonical M N).count_eq index

end BFAlign

end GSForest

namespace AMCrit

/--
Countwise form of the second outer comparison, from annotated generated
batches to the canonical concrete collector root-index trace.
-/
structure
  SFAlign
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  indexMultiplicityAlignment :
    SSForest
      hleftWeight hrightWeight raw
  program_count_root :
    ∀ M N index,
      (finIdxProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        indexMultiplicityAlignment.program
        indexMultiplicityAlignment.generated
        indexMultiplicityAlignment.profiles M N).count index =
      (generatedGridBranch
        (n := n) hleftWeight hrightWeight M N).count index

namespace
  SFAlign

/-- Promote both pointwise comparisons to exact canonical root-index alignment. -/
noncomputable def
    scheduledBatchAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAlign
        hleftWeight hrightWeight raw) :
    SFAligna
      hleftWeight hrightWeight raw where
  finiteIndexAlignment :=
    alignment.indexMultiplicityAlignment
      |>.scheduledSchedulerAlignment
  program_perm_root M N := by
    classical
    rw [List.perm_iff_count]
    exact alignment.program_count_root M N

/-- Compile countwise scheduled accounting directly to exact occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAlign
        hleftWeight hrightWeight raw) :=
  alignment.scheduledBatchAlignment
    |>.schedulerOccAccounting

end SFAlign

end AMCrit

namespace IABridge

open
  AMCrit

namespace SFAligna

/-- Forget exact root-index permutations down to pointwise multiplicities. -/
noncomputable def
    scheduledIdxAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAligna
        hleftWeight hrightWeight raw) :
    SFAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.finiteIndexAlignment
      |>.scheduledGeneratedForest
  program_count_root M N index :=
    (alignment.program_perm_root M N).count_eq
      index

end SFAligna

end IABridge

namespace AMCrit

end AMCrit
end TCTex
end Submission

/-!
# Claim 5 from exact scheduled finite-index occurrence accounting

The strongest scheduled forest interface compares annotated generated batches
both with the symbolic scheduler and with the canonical concrete collector.
It contains the finite-index forest alignment consumed by the Claim 5 route.
This file records the direct forwarding interface.

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
open CRLayer
open
  GSForest
open
  IABridge

namespace IABridge

namespace SFAligna

/-- Remaining signed extension after exact scheduled occurrence accounting. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SFAligna
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  BFAlign.AILift.{u}
    (d := d) scheduler alignment.finiteIndexAlignment

/-- Truncated signed recollection law after exact scheduled occurrence accounting. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SFAligna
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  BFAlign.SatisfiesTruncEval.{u}
    (d := d) scheduler alignment.finiteIndexAlignment

/-- For exact scheduled occurrence accounting, the two signed extension inputs agree. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SFAligna
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  BFAlign.satisfies_trunc_lift
    scheduler alignment.finiteIndexAlignment

end SFAligna

end IABridge

namespace TSInput

open
  IABridge

/--
Exact scheduled finite-index occurrence accounting and its signed lift
construct the Claim 5 coordinate polynomials.
-/
theorem
    coordAlignmentLift
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
    (alignment :
      SFAligna
        (by simp) (by simp) scheduler.raw)
    (lift :
      SFAligna.AILift.{u}
        (d := d) scheduler alignment)
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
  input.idxAlignmentLift
    hn H hH scheduler alignment.finiteIndexAlignment lift hsourceSupported
      factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input for exact scheduled finite-index occurrence accounting.
-/
theorem
    coordRootTrunc
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
    (alignment :
      SFAligna
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SFAligna.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
  input.coordFinTrunc
    hn H hH scheduler alignment.finiteIndexAlignment hlistEval
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Canonical occurrence accounting from scheduled finite-index multiplicities

The generated-batch recurrence is most useful when the second outer
finite-index comparison is stated directly as a scalar formula.  This file
packages that residual formula and compiles it back to the exact canonical
occurrence-accounting kernel.

Together with the constructor equations for `indexMultiplicityProgram`,
the remaining symbolic Hall collector theorem is exposed as a recursive
pointwise multiplicity calculation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace AMCrit

open HACoeff
open
  CLFree
open FIProf
open
  UIRec
open
  ISLift

namespace SSForest

/--
Residual scalar formula for the second outer comparison: the annotated
generated-batch multiplicity is the canonical concrete collector multiplicity.
-/
abbrev SatisfiesMultiplicityFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    Prop :=
  ∀ M N index,
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        alignment.program alignment.generated alignment.profiles M N index =
      (generatedGridBranch
        (n := n) hleftWeight hrightWeight M N).count index

/--
The recurrence-facing scalar formula is definitionally the trace-count field
required by canonical root-index multiplicity alignment.
-/
theorem satisfies_formula_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    alignment.SatisfiesMultiplicityFormula ↔
      ∀ M N index,
        (UFIdx.finIdxProgram
          (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
          alignment.program alignment.generated alignment.profiles M N).count index =
        (generatedGridBranch
          (n := n) hleftWeight hrightWeight M N).count index := by
  rfl

/--
Compile the recurrence-facing scalar formula to the two countwise outer
comparisons.
-/
noncomputable def
    scheduledAlignmentFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula : alignment.SatisfiesMultiplicityFormula) :
    SFAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment
  program_count_root M N index :=
    hformula M N index

/--
Compile the recurrence-facing scalar formula directly to exact canonical
finite-index occurrence accounting.
-/
noncomputable def
    guardedAccountingFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula : alignment.SatisfiesMultiplicityFormula) :=
  (alignment.scheduledAlignmentFormula
      hformula)
    |>.schedulerOccAccounting

end SSForest

namespace
  SFAlign

/-- Recover the recurrence-facing scalar formula from countwise alignment. -/
theorem satisfiesMultiplicityFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAlign
        hleftWeight hrightWeight raw) :
    alignment.indexMultiplicityAlignment.SatisfiesMultiplicityFormula :=
  alignment.program_count_root

end SFAlign

end AMCrit
end TCTex
end Submission

/-!
# Scheduled multiplicities against the canonical scalar local collector

The residual scheduled-batch comparison was previously stated against the
canonical concrete collector root-index trace.  Counting the canonical
generated-source local model gives an equivalent local insertion/collection
interface.  This file records that equivalence and compiles the local formula
directly to exact finite-index occurrence accounting.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace AMCrit

open HACoeff
open
  LMBounda
open
  ILModela
open FIProf
open
  UIRec
open
  ISLift

namespace SSForest

/--
Local-collector form of the residual scalar comparison.  The right side is the
canonical scalar collection evaluator on the literal inverse-raw source.
-/
abbrev SatisfiesIdxMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    Prop :=
  ∀ M N index,
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        alignment.program alignment.generated alignment.profiles M N index =
      (generatedGridModel
        M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
          (inverseDecoratedTerms M N)
          (inverse_generated_source M N)

/--
The canonical trace-count formula and the canonical scalar local-collection
formula are equivalent.
-/
theorem
    satisfies_mult_formula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    alignment.SatisfiesIdxMult ↔
      alignment.SatisfiesMultiplicityFormula := by
  constructor
  · intro hformula M N index
    rw [←
      decorated_branch_idx
        index]
    exact hformula M N index
  · intro hformula M N index
    rw [
      decorated_branch_idx
        index]
    exact hformula M N index

/--
Promote the local-collector scalar formula to both countwise outer
comparisons.
-/
noncomputable def
    scheduledBatchFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesIdxMult) :
    SFAlign
      hleftWeight hrightWeight raw :=
  alignment.scheduledAlignmentFormula
    ((alignment.satisfies_mult_formula).mp
      hformula)

/--
Promote the local-collector scalar formula to exact two-sided finite-index
forest alignment.
-/
noncomputable def
    scheduledForestFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesIdxMult) :=
  alignment.scheduledBatchFormula
      hformula
    |>.scheduledBatchAlignment

/--
Compile the local-collector scalar formula directly to exact canonical
finite-index occurrence accounting.
-/
noncomputable def
    guardedRetainedFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesIdxMult) :=
  alignment.scheduledBatchFormula
      hformula
    |>.schedulerOccAccounting

end SSForest

namespace
  SFAlign

/-- Recover the local-collector scalar formula from canonical countwise alignment. -/
theorem satisfiesCollectionFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAlign
        hleftWeight hrightWeight raw) :
    alignment.indexMultiplicityAlignment.SatisfiesIdxMult :=
  (alignment.indexMultiplicityAlignment.satisfies_mult_formula).mpr
    alignment.satisfiesMultiplicityFormula

end SFAlign

end AMCrit
end TCTex
end Submission

/-!
# Canonical scalar local-collector criterion for scheduled finite-index accounting

The symbolic Hall collector can now target a constructor-facing record.  Its
first field supplies the finite-index scheduler-forest multiplicity alignment;
its second field identifies annotated scheduled-batch multiplicities with the
canonical scalar local collection evaluator on the inverse-raw source.

This packages the local insertion/collection statement and compiles it to the
existing canonical root-index alignment and exact occurrence-accounting
interfaces.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace AMCrit

open HACoeff
open FIProf
open
  ISLift

/--
Constructor-facing local-collector form of the two outer finite-index
multiplicity comparisons.
-/
structure SBForest
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  indexMultiplicityAlignment :
    SSForest
      hleftWeight hrightWeight raw
  multiplicityCollectionFormula :
    indexMultiplicityAlignment.SatisfiesIdxMult

namespace SBForest

/-- Compile local-collector scalar accounting to canonical root-index multiplicity alignment. -/
noncomputable def
    scheduledIdxAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBForest
        hleftWeight hrightWeight raw) :
    SFAlign
      hleftWeight hrightWeight raw :=
  alignment.indexMultiplicityAlignment
    |>.scheduledBatchFormula
      alignment.multiplicityCollectionFormula

/-- Compile local-collector scalar accounting to exact two-sided finite-index alignment. -/
noncomputable def
    scheduledBatchAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBForest
        hleftWeight hrightWeight raw) :=
  alignment.scheduledIdxAlignment
    |>.scheduledBatchAlignment

/-- Compile local-collector scalar accounting directly to exact occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBForest
        hleftWeight hrightWeight raw) :=
  alignment.scheduledIdxAlignment
    |>.schedulerOccAccounting

end SBForest

namespace
  SFAlign

/-- Forget canonical trace-count accounting down to the local scalar collector target. -/
noncomputable def
    scheduledMultAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SFAlign
        hleftWeight hrightWeight raw) :
    SBForest
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  multiplicityCollectionFormula :=
    alignment.satisfiesCollectionFormula

end SFAlign

end AMCrit
end TCTex
end Submission

/-!
# Claim 5 from canonical scalar local-collector multiplicity accounting

The constructor-facing scalar local-collector criterion compiles to exact
scheduled finite-index occurrence accounting.  This file forwards that route to
the existing Claim 5 coordinate-polynomial constructor.

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
open CRLayer
open
  IABridge
open
  AMCrit

namespace AMCrit

namespace SBForest

/-- Remaining signed extension after local-collector multiplicity accounting. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBForest
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SFAligna.AILift.{u}
    (d := d) scheduler
      alignment.scheduledBatchAlignment

/-- Truncated signed recollection law after local-collector multiplicity accounting. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBForest
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SFAligna.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.scheduledBatchAlignment

/-- The two signed extension inputs agree after local-collector accounting. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBForest
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  SFAligna.satisfies_trunc_lift
    scheduler
      alignment.scheduledBatchAlignment

end SBForest

end AMCrit

namespace TSInput

open
  AMCrit

/--
Canonical local-collector multiplicity accounting and its signed lift construct
the Claim 5 coordinate polynomials.
-/
theorem
    scheduledBatchForest
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
    (alignment :
      SBForest
        (by simp) (by simp) scheduler.raw)
    (lift :
      SBForest.AILift.{u}
        (d := d) scheduler alignment)
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
  input.coordAlignmentLift
    hn H hH scheduler
      alignment.scheduledBatchAlignment
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input after local-collector multiplicity accounting.
-/
theorem
    schedulerForestAlignment
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
    (alignment :
      SBForest
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SBForest.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
  input.coordRootTrunc
    hn H hH scheduler
      alignment.scheduledBatchAlignment
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Canonical scheduler criterion for scalar local-collector accounting

Root-cardinality synchronization and concrete nested-child synchronization
identify the annotated generated-batch multiplicity with the guarded scheduler
forest count.  The outer forest alignment then identifies that count with the
canonical guarded raw-source scheduler.

Consequently, the residual local-collector formula can be stated without the
annotated concrete schedule: it is exactly equality between the canonical
guarded scheduler count and the canonical scalar local collection evaluator.
This file packages that reduced constructor target and compiles it to exact
finite-index occurrence accounting.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  AMCrit

open HACoeff
open
  LMBounda
open
  ILModela
open FIProf
open
  AMCrit
open
  RIRec
open
  UIRec
open
  RITrace
open
  ISLift
open
  FISchedu

namespace SSForest

/--
After all forest synchronization fields are supplied, the annotated
generated-batch multiplicity is the canonical guarded raw-source scheduler
multiplicity.
-/
lemma program_scheduler_count
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight) :
    indexMultiplicityProgram
        (hleftWeight := hleftWeight) (hrightWeight := hrightWeight)
        alignment.program alignment.generated alignment.profiles M N index =
      (guardedIdxFin
        (multiplicityProfileShape raw)
        M N).count index := by
  rw [
    multiplicity_program_scheduler
      (multiplicityProfileShape raw)
      alignment.program alignment.generated alignment.profiles
      alignment.rootSynchronizations M N
      (alignment.concreteNestedSynchronizations M N)]
  exact alignment.guarded_forest_count M N index

/--
Reduced canonical-scheduler form of the residual scalar local-collector
comparison.
-/
abbrev SatisfiesSchedulerFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (_alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    Prop :=
  ∀ M N index,
    (guardedIdxFin
      (multiplicityProfileShape raw)
      M N).count index =
      (generatedGridModel
        M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
          (inverseDecoratedTerms M N)
          (inverse_generated_source M N)

/--
Once the synchronized scheduler forest is available, the annotated-schedule
local formula is equivalent to its canonical guarded-scheduler form.
-/
theorem
    satisfies_mult_scheduler
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    alignment.SatisfiesIdxMult ↔
      alignment.SatisfiesSchedulerFormula := by
  constructor
  · intro hformula M N index
    rw [←
      alignment.program_scheduler_count
        M N index]
    exact hformula M N index
  · intro hformula M N index
    rw [
      alignment.program_scheduler_count
        M N index]
    exact hformula M N index

/--
Compile the reduced canonical-scheduler formula directly to exact canonical
finite-index occurrence accounting.
-/
noncomputable def
    guardedSchedulerFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesSchedulerFormula) :=
  alignment.guardedRetainedFormula
    ((alignment.satisfies_mult_scheduler).mpr
      hformula)

end SSForest

/--
Constructor-facing reduced local-collector target.  Its residual field mentions
only the canonical guarded scheduler and canonical scalar source-local
collector.
-/
structure
    SBAlign
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  indexMultiplicityAlignment :
    SSForest
      hleftWeight hrightWeight raw
  canonicalCollectionFormula :
    indexMultiplicityAlignment.SatisfiesSchedulerFormula

namespace
  SBAlign

/-- Compile the reduced target to the annotated-schedule local-collector target. -/
noncomputable def
    scheduledMultAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBAlign
        hleftWeight hrightWeight raw) :
    SBForest
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  multiplicityCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_mult_scheduler).mpr
      alignment.canonicalCollectionFormula

/-- Compile the reduced target directly to exact finite-index occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBAlign
        hleftWeight hrightWeight raw) :=
  alignment.scheduledMultAlignment
    |>.schedulerOccAccounting

end
  SBAlign

namespace
  SBForest

/-- Rewrite the annotated-schedule local-collector target in canonical scheduler form. -/
noncomputable def
    scheduledForestMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBForest
        hleftWeight hrightWeight raw) :
    SBAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  canonicalCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_mult_scheduler).mp
      alignment.multiplicityCollectionFormula

end
  SBForest

end
  AMCrit
end TCTex
end Submission

/-!
# Canonical scheduler branch-sum criterion for scalar local-collector accounting

The canonical guarded scheduler count is a finite sum of exact retained-index
branch counts.  This file rewrites the reduced scheduler local-collector
criterion in that scalar branch-sum form and packages the resulting
constructor-facing target.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  AMCrit

open HACoeff
open
  LMBounda
open
  ILModela
open FIProf
open
  AMCrit
open
  RITrace
open
  ISLift
open
  IMRec

namespace SSForest

/--
Branch-sum form of the residual scalar local-collector comparison.  Every term
is one exact retained-index multiplicity in a guarded raw-source root branch.
-/
abbrev SatisfiesSchedulerBranch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (_alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    Prop :=
  ∀ M N index,
    guardedSchedulerSum
        (multiplicityProfileShape raw)
        M N index =
      (generatedGridModel
        M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
          (inverseDecoratedTerms M N)
          (inverse_generated_source M N)

/--
The canonical guarded-scheduler criterion is equivalent to its exact finite
branch-sum form.
-/
theorem
    satisfies_idx_branch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    alignment.SatisfiesSchedulerFormula ↔
      alignment.SatisfiesSchedulerBranch := by
  constructor
  · intro hformula M N index
    rw [←
      count_guarded_retained]
    exact hformula M N index
  · intro hformula M N index
    rw [
      count_guarded_retained]
    exact hformula M N index

/--
Compile the scalar branch-sum formula directly to exact canonical finite-index
occurrence accounting.
-/
noncomputable def
    branchCollectFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesSchedulerBranch) :=
  alignment.guardedSchedulerFormula
    ((alignment.satisfies_idx_branch).mpr
      hformula)

end SSForest

/--
Constructor-facing scalar branch-sum target.  Its residual field is a finite
sum of explicit guarded raw-source branch multiplicities.
-/
structure
    SBAligna
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  indexMultiplicityAlignment :
    SSForest
      hleftWeight hrightWeight raw
  branchCountFormula :
    indexMultiplicityAlignment.SatisfiesSchedulerBranch

namespace
  SBAligna

/-- Compile the branch-sum target to the canonical guarded-scheduler target. -/
noncomputable def
    scheduledForestMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBAligna
        hleftWeight hrightWeight raw) :
    SBAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  canonicalCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_idx_branch).mpr
      alignment.branchCountFormula

/-- Compile the scalar branch-sum target directly to exact finite-index occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBAligna
        hleftWeight hrightWeight raw) :=
  alignment.scheduledForestMult
    |>.schedulerOccAccounting

end
  SBAligna

namespace
  SBAlign

/-- Rewrite the canonical scheduler target in exact scalar branch-sum form. -/
noncomputable def
    scheduledBatchMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBAlign
        hleftWeight hrightWeight raw) :
    SBAligna
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  branchCountFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_idx_branch).mp
      alignment.canonicalCollectionFormula

end
  SBAlign

end
  AMCrit
end TCTex
end Submission

/-!
# Claim 5 from canonical scheduler-to-local-collector multiplicity accounting

The reduced constructor-facing criterion compares the canonical guarded
scheduler directly with the canonical scalar source-local collector.  This file
forwards that criterion through exact finite-index occurrence accounting to the
existing Claim 5 coordinate-polynomial constructor.

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
open CRLayer

namespace AMCrit

namespace
  SBAlign

/-- Remaining signed extension after reduced scheduler-to-local accounting. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SBForest.AILift.{u}
    (d := d) scheduler
      alignment.scheduledMultAlignment

/-- Truncated signed recollection law after reduced scheduler-to-local accounting. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SBForest.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.scheduledMultAlignment

/-- The two signed extension inputs agree after reduced scheduler-to-local accounting. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBAlign
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  SBForest.satisfies_trunc_lift
    scheduler
      alignment.scheduledMultAlignment

end
  SBAlign

end AMCrit

namespace TSInput

open
  AMCrit

/--
Reduced scheduler-to-local-collector multiplicity accounting and its signed
lift construct the Claim 5 coordinate polynomials.
-/
theorem
    batchForestAlignment
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
    (alignment :
      SBAlign
        (by simp) (by simp) scheduler.raw)
    (lift :
      SBAlign.AILift.{u}
        (d := d) scheduler alignment)
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
  input.scheduledBatchForest
    hn H hH scheduler
      alignment.scheduledMultAlignment
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input after reduced scheduler-to-local-collector multiplicity accounting.
-/
theorem
    forestMultAlignment
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
    (alignment :
      SBAlign
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SBAlign.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
  input.schedulerForestAlignment
    hn H hH scheduler
      alignment.scheduledMultAlignment
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Canonical scheduler recurrence-sum criterion for scalar local accounting

The canonical guarded scheduler multiplicity is the explicit sum of its
one-branch scalar recurrences.  This file packages the corresponding
constructor-facing criterion and compiles it both to standalone recurrence-sum
occurrence accounting and to the existing scheduled canonical-local route.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  AMCrit

open HACoeff
open
  ILModela
open
  LMBounda
open FIProf
open
  AMCrit
open
  RITrace
open
  ISLift
open
  IMRec
open
  SOAccouna
open
  FISchedu

namespace SSForest

/--
Explicit recurrence-sum form of the residual canonical scheduler
local-collector comparison.
-/
abbrev SatisfiesMultFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (_alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    Prop :=
  ∀ M N index,
    guardedSchedulerRecurrence
        (multiplicityProfileShape raw)
        M N index =
      (generatedGridModel
        M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
          (inverseDecoratedTerms M N)
          (inverse_generated_source M N)

/--
The canonical guarded-scheduler local formula is equivalent to its fully
expanded scalar recurrence-sum form.
-/
theorem
    satisfies_scheduler_recurrence
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    alignment.SatisfiesSchedulerFormula ↔
      alignment.SatisfiesMultFormula := by
  constructor
  · intro hformula M N index
    rw [←
      count_recurrence_sum]
    exact hformula M N index
  · intro hformula M N index
    rw [
      count_recurrence_sum]
    exact hformula M N index

/--
Compile the recurrence-sum local formula to the standalone raw-source
recurrence-sum kernel.
-/
noncomputable def
    guardedCollectFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesMultFormula) :
    GICollec
      (n := n) hleftWeight hrightWeight where
  raw := raw
  recurrence_sum_collection := hformula

/--
The recurrence-sum local formula directly reconstructs exact finite-index
occurrence accounting.
-/
noncomputable def
    guardedOccFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesMultFormula) :=
  alignment
    |>.guardedCollectFormula
      hformula
    |>.schedulerOccAccounting

end SSForest

/--
Constructor-facing scheduled forest target whose remaining scalar obligation
is the explicit recurrence sum.
-/
structure
    SMAlign
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  indexMultiplicityAlignment :
    SSForest
      hleftWeight hrightWeight raw
  recurrenceCollectionFormula :
    indexMultiplicityAlignment.SatisfiesMultFormula

namespace
  SMAlign

/--
Compile the recurrence-sum target to the canonical guarded-scheduler
local-collector target.
-/
noncomputable def
    scheduledForestMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SMAlign
        hleftWeight hrightWeight raw) :
    SBAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  canonicalCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_scheduler_recurrence).mpr
      alignment.recurrenceCollectionFormula

/--
Forget the scheduled forest wrapper down to the standalone raw-source
recurrence-sum local-collector kernel.
-/
noncomputable def
    guardedCollectKernel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SMAlign
        hleftWeight hrightWeight raw) :
    GICollec
      (n := n) hleftWeight hrightWeight :=
  alignment.indexMultiplicityAlignment
    |>.guardedCollectFormula
      alignment.recurrenceCollectionFormula

/-- Compile the recurrence-sum target directly to exact occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SMAlign
        hleftWeight hrightWeight raw) :=
  alignment
    |>.guardedCollectKernel
    |>.schedulerOccAccounting

end
  SMAlign

namespace
  SBAlign

/-- Expand the canonical guarded-scheduler local target into recurrence-sum form. -/
noncomputable def
    scheduledRecurrenceAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBAlign
        hleftWeight hrightWeight raw) :
    SMAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  recurrenceCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_scheduler_recurrence).mp
      alignment.canonicalCollectionFormula

end
  SBAlign

end
  AMCrit
end TCTex
end Submission

/-!
# Claim 5 from canonical scheduler branch-sum local accounting

The branch-sum constructor target exposes the canonical guarded scheduler count
as a finite sum of exact retained-index branch multiplicities.  This file
forwards that explicit target through the existing Claim 5 coordinate-polynomial
constructor.

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
open CRLayer

namespace AMCrit

namespace
  SBAligna

/-- Remaining signed extension after branch-sum scheduler-to-local accounting. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBAligna
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SBAlign.AILift.{u}
    (d := d) scheduler
      alignment.scheduledForestMult

/-- Truncated signed recollection law after branch-sum scheduler-to-local accounting. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBAligna
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SBAlign.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.scheduledForestMult

/-- The two signed extension inputs agree after branch-sum scheduler-to-local accounting. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SBAligna
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  SBAlign.satisfies_trunc_lift
    scheduler
      alignment.scheduledForestMult

end
  SBAligna

end AMCrit

namespace TSInput

open
  AMCrit

/--
Branch-sum scheduler-to-local multiplicity accounting and its signed lift
construct the Claim 5 coordinate polynomials.
-/
theorem
    branchMultAlignment
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
    (alignment :
      SBAligna
        (by simp) (by simp) scheduler.raw)
    (lift :
      SBAligna.AILift.{u}
        (d := d) scheduler alignment)
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
  input.batchForestAlignment
    hn H hH scheduler
      alignment.scheduledForestMult
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input after branch-sum scheduler-to-local multiplicity accounting.
-/
theorem
    coordBranchTrunc
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
    (alignment :
      SBAligna
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SBAligna.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
  input.forestMultAlignment
    hn H hH scheduler
      alignment.scheduledForestMult
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Equivalence of canonical scheduler branch sums and recurrence sums

The exact finite branch-count sum and its expanded one-branch recurrence sum
are interchangeable residual collector interfaces.  This file records the
pointwise equivalence and packages conversions between the constructor-facing
scheduled forest records.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  AMCrit

open HACoeff
open FIProf
open
  AMCrit
open
  ISLift
open
  IMRec

namespace SSForest

/--
The finite sum of exact branch counts and the expanded sum of one-branch
scalar recurrences give equivalent residual local-collector formulas.
-/
theorem
    satisfies_scheduler_branch
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    alignment.SatisfiesSchedulerBranch ↔
      alignment.SatisfiesMultFormula := by
  constructor
  · intro hformula M N index
    rw [←
      guarded_sum_recurrence]
    exact hformula M N index
  · intro hformula M N index
    rw [
      guarded_sum_recurrence]
    exact hformula M N index

end SSForest

namespace
  SBAligna

/-- Expand exact branch-count sums into one-branch scalar recurrence sums. -/
noncomputable def
    scheduledRecurrenceAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SBAligna
        hleftWeight hrightWeight raw) :
    SMAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  recurrenceCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_scheduler_branch).mp
      alignment.branchCountFormula

end
  SBAligna

namespace
  SMAlign

/-- Collapse one-branch scalar recurrence sums back to exact branch-count sums. -/
noncomputable def
    scheduledBatchMult
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SMAlign
        hleftWeight hrightWeight raw) :
    SBAligna
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  branchCountFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_scheduler_branch).mpr
      alignment.recurrenceCollectionFormula

end
  SMAlign

/--
Constructor-facing exact branch-count sums and expanded recurrence sums are
equivalent data.
-/
noncomputable def
    scheduledBranchAlignment
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    SBAligna
        hleftWeight hrightWeight raw ≃
      SMAlign
        hleftWeight hrightWeight raw where
  toFun :=
    SBAligna.scheduledRecurrenceAlignment
  invFun :=
    SMAlign.scheduledBatchMult
  left_inv alignment := by
    cases alignment
    congr
  right_inv alignment := by
    cases alignment
    congr

/--
The canonical scheduler-count local interface and its expanded recurrence-sum
interface are equivalent data.
-/
noncomputable def
    scheduledBatchRecurrence
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    SBAlign
        hleftWeight hrightWeight raw ≃
      SMAlign
        hleftWeight hrightWeight raw where
  toFun :=
    SBAlign.scheduledRecurrenceAlignment
  invFun :=
    SMAlign.scheduledForestMult
  left_inv alignment := by
    cases alignment
    congr
  right_inv alignment := by
    cases alignment
    congr

end
  AMCrit
end TCTex
end Submission

/-!
# Scheduled canonical collector criterion from decomposed recurrence sums

The scheduled Claim 5 route can expose its remaining raw-source collector
obligation as three algebraic sums: left nested collector terms, matching
correction-root products, and right nested collector terms.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  AMCrit

open HACoeff
open
  ILModela
open
  LMBounda
open FIProf
open
  AMCrit
open
  RITrace
open
  ISLift
open
  IMRec
open
  DOAccoun

namespace SSForest

/--
Three-way algebraic form of the residual canonical scheduler local-collector
comparison.
-/
abbrev SatisfiesSchedulerDecomposed
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (_alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    Prop :=
  ∀ M N index,
    idxNestedRecurrence
        (multiplicityProfileShape raw)
        M N index +
      idxRecurrenceSum
          (multiplicityProfileShape raw)
          M N index +
        guardedRecurrenceSum
            (multiplicityProfileShape raw)
            M N index =
      (generatedGridModel
        M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
          (inverseDecoratedTerms M N)
          (inverse_generated_source M N)

/--
The scalar recurrence-sum formula and its left/root-product/right
decomposition are equivalent.
-/
theorem
    satisfies_scheduler_decomposed
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw) :
    alignment.SatisfiesMultFormula ↔
      alignment.SatisfiesSchedulerDecomposed := by
  constructor
  · intro hformula M N index
    rw [←
      guarded_idx_nested]
    exact hformula M N index
  · intro hformula M N index
    rw [
      guarded_idx_nested]
    exact hformula M N index

/--
Compile the three-way scalar formula to the standalone decomposed raw-source
kernel.
-/
noncomputable def
    guardedDecomposedFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesSchedulerDecomposed) :
    GIDecompa
      (n := n) hleftWeight hrightWeight where
  raw := raw
  add_product_collection :=
    hformula

/-- The three-way scalar formula directly reconstructs exact occurrence accounting. -/
noncomputable def
    occDecomposedFormula
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SSForest
        hleftWeight hrightWeight raw)
    (hformula :
      alignment.SatisfiesSchedulerDecomposed) :=
  alignment
    |>.guardedDecomposedFormula
      hformula
    |>.schedulerOccAccounting

end SSForest

/--
Constructor-facing scheduled forest target with the residual collector
identity exposed as left nested, root-product, and right nested sums.
-/
structure
    SDAlign
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) where
  indexMultiplicityAlignment :
    SSForest
      hleftWeight hrightWeight raw
  decomposedCollectionFormula :
    indexMultiplicityAlignment.SatisfiesSchedulerDecomposed

namespace
  SDAlign

/-- Collapse the decomposed scheduled target to the scalar recurrence-sum target. -/
noncomputable def
    scheduledRecurrenceAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SDAlign
        hleftWeight hrightWeight raw) :
    SMAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  recurrenceCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_scheduler_decomposed).mpr
      alignment.decomposedCollectionFormula

/-- Forget the scheduled wrapper to the standalone decomposed raw-source kernel. -/
noncomputable def
    guardedDecomposedCollect
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SDAlign
        hleftWeight hrightWeight raw) :
    GIDecompa
      (n := n) hleftWeight hrightWeight :=
  alignment.indexMultiplicityAlignment
    |>.guardedDecomposedFormula
      alignment.decomposedCollectionFormula

/-- Compile the decomposed scheduled target directly to exact occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SDAlign
        hleftWeight hrightWeight raw) :=
  alignment
    |>.guardedDecomposedCollect
    |>.schedulerOccAccounting

end
  SDAlign

namespace
  SMAlign

/-- Expand the scalar recurrence-sum scheduled target into three algebraic sums. -/
noncomputable def
    scheduledDecomposedAlignment
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight}
    (alignment :
      SMAlign
        hleftWeight hrightWeight raw) :
    SDAlign
      hleftWeight hrightWeight raw where
  indexMultiplicityAlignment :=
    alignment.indexMultiplicityAlignment
  decomposedCollectionFormula :=
    (alignment.indexMultiplicityAlignment.satisfies_scheduler_decomposed).mp
      alignment.recurrenceCollectionFormula

end
  SMAlign

/-- Scalar recurrence-sum and decomposed scheduled targets are equivalent data. -/
noncomputable def
    scheduledBatchDecomposed
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    SMAlign
        hleftWeight hrightWeight raw ≃
      SDAlign
        hleftWeight hrightWeight raw where
  toFun :=
    SMAlign.scheduledDecomposedAlignment
  invFun :=
    SDAlign.scheduledRecurrenceAlignment
  left_inv alignment := by
    cases alignment
    congr
  right_inv alignment := by
    cases alignment
    congr

end
  AMCrit
end TCTex
end Submission

/-!
# Claim 5 from canonical scheduler recurrence-sum local accounting

The recurrence-sum constructor target exposes the canonical guarded scheduler
count as the finite sum of its exact one-branch scalar recurrences.  This file
forwards that explicit target through the existing Claim 5
coordinate-polynomial constructor.

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
open CRLayer

namespace
  AMCrit

namespace
  SMAlign

/-- Remaining signed extension after recurrence-sum scheduler-to-local accounting. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SMAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SBAlign.AILift.{u}
    (d := d) scheduler
      alignment.scheduledForestMult

/-- Truncated signed recollection law after recurrence-sum scheduler-to-local accounting. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SMAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SBAlign.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.scheduledForestMult

/--
The two signed extension inputs agree after recurrence-sum scheduler-to-local
accounting.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SMAlign
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  SBAlign.satisfies_trunc_lift
    scheduler
      alignment.scheduledForestMult

end
  SMAlign

end
  AMCrit

namespace TSInput

open
  AMCrit

/--
Recurrence-sum scheduler-to-local multiplicity accounting and its signed lift
construct the Claim 5 coordinate polynomials.
-/
theorem
    recurrenceMultAlignment
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
    (alignment :
      SMAlign
        (by simp) (by simp) scheduler.raw)
    (lift :
      SMAlign.AILift.{u}
        (d := d) scheduler alignment)
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
  input.batchForestAlignment
    hn H hH scheduler
      alignment.scheduledForestMult
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input after recurrence-sum scheduler-to-local multiplicity accounting.
-/
theorem
    coordRecurrenceTrunc
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
    (alignment :
      SMAlign
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SMAlign.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
  input.forestMultAlignment
    hn H hH scheduler
      alignment.scheduledForestMult
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from decomposed canonical scheduler recurrence sums

The final constructor-facing collector obligation is exposed as the sum of
left nested terms, matching correction-root products, and right nested terms.
This file forwards that algebraic interface through the existing Claim 5
coordinate-polynomial constructor.

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
open CRLayer

namespace
  AMCrit

namespace
  SDAlign

/-- Remaining signed extension after decomposed recurrence-sum accounting. -/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SDAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SMAlign.AILift.{u}
    (d := d) scheduler
      alignment.scheduledRecurrenceAlignment

/-- Truncated signed recollection law after decomposed recurrence-sum accounting. -/
abbrev SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SDAlign
        (by simp) (by simp) scheduler.raw) :
    Prop :=
  SMAlign.SatisfiesTruncEval.{u}
    (d := d) scheduler
      alignment.scheduledRecurrenceAlignment

/-- The signed extension inputs agree after decomposed recurrence-sum accounting. -/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (scheduler :
      GPPerm
        layer (by simp) (by simp))
    (alignment :
      SDAlign
        (by simp) (by simp) scheduler.raw) :
    SatisfiesTruncEval.{u} (d := d) scheduler alignment ↔
      AILift.{u} (d := d) scheduler alignment :=
  SMAlign.satisfies_trunc_lift
    scheduler
      alignment.scheduledRecurrenceAlignment

end
  SDAlign

end
  AMCrit

namespace TSInput

open
  AMCrit

/--
Decomposed recurrence-sum accounting and its signed lift construct the Claim 5
coordinate polynomials.
-/
theorem
    decomposedMultAlignment
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
    (alignment :
      SDAlign
        (by simp) (by simp) scheduler.raw)
    (lift :
      SDAlign.AILift.{u}
        (d := d) scheduler alignment)
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
  input.recurrenceMultAlignment
    hn H hH scheduler
      alignment.scheduledRecurrenceAlignment
      lift hsourceSupported factorNormalization hinputWeight

/--
The truncated signed recollection law is an equivalent Claim 5 constructor
input after decomposed recurrence-sum accounting.
-/
theorem
    coordDecomposedTrunc
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
    (alignment :
      SDAlign
        (by simp) (by simp) scheduler.raw)
    (hlistEval :
      SDAlign.SatisfiesTruncEval.{u}
        (d := d) scheduler alignment)
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
  input.coordRecurrenceTrunc
    hn H hH scheduler
      alignment.scheduledRecurrenceAlignment
      hlistEval hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

import Towers.Group.Zassenhaus.GuardedGridCoverage
import Towers.Group.Zassenhaus.OrderedRetainedLaw
import Towers.Group.Zassenhaus.RestrictedFullCollector

/-!
# Root-trace Claim 5 from retained occurrence scheduling

The generated concrete-schedule root-trace kernel solves the polynomial-counting
side of the cutoff-full collector.  Independently, a retained-transversal
occurrence schedule and an operational order transport solve the signed
collection side.  This file joins those constructions at their minimal common
interface: literal equality between the root-trace interpolation packet and the
sorted retained-transversal packet.

The resulting compiler supplies the signed root-trace lift, the complete
quantified Claim 5 input, and the weight-controlled Hall-coordinate degree
bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  RPCrit
open
  FPInterp
open
  OOSched
open
  SOAlign
open
  CRLayer
open
  PTOcc

namespace
  RPCrit
namespace
  GPPerm

/--
The endpoint interpolation packet compiled from root-trace permutation is
literally the sorted retained-transversal packet, including order and profiles.
-/
def OrderedCoefficientAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp)) :
    Prop :=
  (EFInterp.truncNaturalPacket.{u}
    (d := d)
    kernel.fiberProfileInterpolation).packets =
      profileRecollectionPackets n

/--
Packet alignment, an all-integral retained occurrence schedule, and operational
retained-order transport supply the signed lift inherited by the root-trace
kernel.
-/
def
    liftOccTransport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (halignment :
      OrderedCoefficientAlignment.{u}
        (d := d) kernel)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n) :
    GPPerm.AILift.{u}
      (d := d) kernel := by
  change
    EFInterp.AILift.{u}
      (d := d)
      kernel.fiberProfileInterpolation
  exact
    allLiftAlignment
      kernel.fiberProfileInterpolation
      (by
        simpa only [
          EFInterp.packetsTruncNatural] using
            halignment)
      (occ_transport_schedule
        orderedTransport schedule)

/--
The same operational inputs discharge the signed list-evaluation law consumed
by the root-trace Claim 5 adapters.
-/
lemma
    trunc_occ_transport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (halignment :
      OrderedCoefficientAlignment.{u}
        (d := d) kernel)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n) :
    GPPerm.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  (kernel.satisfies_trunc_lift).mpr
    (kernel.liftOccTransport
      halignment schedule orderedTransport)

end
  GPPerm
end
  RPCrit

/--
Root-trace permutation, retained packet alignment, retained occurrence
scheduling, operational order transport, and intrinsic residual recollections
construct the complete quantified Claim 5 power input.
-/
theorem
    forall_transversal_builders
    {d n : ℕ}
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
    (halignment :
      GPPerm.OrderedCoefficientAlignment.{u}
        (d := d) kernel)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuild
            (n := n) (inputWeight := inputWeight) hn H hH) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight :=
  coord_collect_builders
    hn H hH kernel
      (kernel.trunc_occ_transport
        halignment schedule orderedTransport)
      lowWeightSource lowWeightSupported builders

/--
The same operational root-trace package yields the weight-controlled polynomial
degree bound for every Hall coordinate of a power.
-/
theorem
    transversal_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      GPPerm
        layer (by simp) (by simp))
    (halignment :
      GPPerm.OrderedCoefficientAlignment.{u}
        (d := d) kernel)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuild
            (n := n) (inputWeight := inputWeight) hn H hH)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    IVMost
      (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
      (s / r) := by
  exact
    integer_valued_most
      hn H hH
        (forall_transversal_builders
          hn H hH kernel halignment schedule orderedTransport
            lowWeightSource lowWeightSupported builders)
        u hu hr hs hsn i

end TCTex
end Towers

/-!
# Scalar recurrences for recursively compiled concrete schedules

The concrete cutoff-full collector and the guarded symbolic orbit expansion
both have a root-plus-recursive-branches multiplicity shadow.  Since the traced
collector derivations live in `Prop`, their scalar shadow is also best recorded
as an inductive relation rather than as a proof-eliminating function.

This file defines the insertion and collection multiplicity relations, proves
existence and uniqueness, identifies their values with recursively compiled
schedule multiplicities, and packages the remaining arbitrary-cutoff theorem
as a direct statement that the symbolic guarded recurrence sum satisfies the
endpoint collector recurrence.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  CMRec

universe u

open
  HACoeff
open
  MIKern
open
  RMRec
open
  RMRec.RSPrograa
open
  SMInduct
open
  CRProgra
open
  CPProven
open
  PRCompb
open
  PRCompb.RSPrograa
open
  RCProven
open
  RCProven.RCOcc
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
  FIProf
open
  OCPartit
open
  RTProgra

namespace DFTerm

/--
Scalar erased-shape multiplicity recurrence for one traced cutoff insertion.
-/
inductive CutoffInsertsMultiplicity
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    {L R corrections : List (DFTerm M N K)} →
      {A : DFTerm M N K} →
        CICorrec
          n leftWeight rightWeight L A R corrections →
          ℕ → Prop where
  | nil
      (A : DFTerm M N K) :
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word
        (.nil A)
        0
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hBA : B.decorated.collectorLe A.decorated) :
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word
        (.append P B A hBA)
        0
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
      {leftMultiplicity rightMultiplicity : ℕ}
      (hleft :
        CutoffInsertsMultiplicity
          n leftWeight rightWeight word hcorrection leftMultiplicity)
      (hright :
        CutoffInsertsMultiplicity
          n leftWeight rightWeight word hinsert rightMultiplicity) :
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word
        (.retained P B A hAB hweight hcorrection hinsert)
        (leftMultiplicity +
          [((B.correction A).family.recipe.erasedShape)].count word +
            rightMultiplicity)
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
      {multiplicity : ℕ}
      (hmultiplicity :
        CutoffInsertsMultiplicity
          n leftWeight rightWeight word hinsert multiplicity) :
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word
        (.residual P B A hAB hweight hinsert)
        multiplicity

/--
Scalar erased-shape multiplicity recurrence for one traced cutoff collection.
-/
inductive CutoffCollectsMultiplicity
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    {L R corrections : List (DFTerm M N K)} →
      CCCorrec
        n leftWeight rightWeight L R corrections →
        ℕ → Prop where
  | nil :
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word
        .nil
        0
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
      {collectMultiplicity insertMultiplicity : ℕ}
      (hcollectMultiplicity :
        CutoffCollectsMultiplicity
          n leftWeight rightWeight word hcollect collectMultiplicity)
      (hinsertMultiplicity :
        CutoffInsertsMultiplicity
          n leftWeight rightWeight word hinsert insertMultiplicity) :
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word
        (.retained P A hweight hcollect hinsert)
        (collectMultiplicity + insertMultiplicity)
  | residual
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      (hweight :
        n ≤ decoratedFamilyWeight leftWeight rightWeight A)
      {C corrections : List (DFTerm M N K)}
      (hcollect :
        CCCorrec
          n leftWeight rightWeight P C corrections)
      {multiplicity : ℕ}
      (hmultiplicity :
        CutoffCollectsMultiplicity
          n leftWeight rightWeight word hcollect multiplicity) :
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word
        (.residual P A hweight hcollect)
        multiplicity

/-- Every traced insertion has an erased-shape multiplicity recurrence value. -/
lemma inserts_erased_multiplicity
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (word : CWord HPAtom)
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    ∃ multiplicity,
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word hinsert multiplicity := by
  induction hinsert with
  | nil A =>
      exact ⟨0, .nil A⟩
  | append P B A hBA =>
      exact ⟨0, .append P B A hBA⟩
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      rcases ihcorrection with ⟨leftMultiplicity, hleft⟩
      rcases ihinsert with ⟨rightMultiplicity, hright⟩
      exact
        ⟨leftMultiplicity +
            [((B.correction A).family.recipe.erasedShape)].count word +
              rightMultiplicity,
          .retained P B A hAB hweight hcorrection hinsert hleft hright⟩
  | residual P B A hAB hweight hinsert ihinsert =>
      rcases ihinsert with ⟨multiplicity, hmultiplicity⟩
      exact
        ⟨multiplicity,
          .residual P B A hAB hweight hinsert hmultiplicity⟩

/-- Every traced collection has an erased-shape multiplicity recurrence value. -/
lemma collects_erased_multiplicity
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    (word : CWord HPAtom)
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    ∃ multiplicity,
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word hcollect multiplicity := by
  induction hcollect with
  | nil =>
      exact ⟨0, .nil⟩
  | retained P A hweight hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨collectMultiplicity, hcollectMultiplicity⟩
      rcases
          inserts_erased_multiplicity
            word hinsert with
        ⟨insertMultiplicity, hinsertMultiplicity⟩
      exact
        ⟨collectMultiplicity + insertMultiplicity,
          .retained P A hweight hcollect hinsert
            hcollectMultiplicity hinsertMultiplicity⟩
  | residual P A hweight hcollect ihcollect =>
      rcases ihcollect with ⟨multiplicity, hmultiplicity⟩
      exact
        ⟨multiplicity, .residual P A hweight hcollect hmultiplicity⟩

/--
The insertion recurrence value is the count in its literal retained-correction
shape trace.
-/
lemma count_inserts_mult
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {multiplicity : ℕ}
    (hmultiplicity :
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word hinsert multiplicity) :
    multiplicity =
      (erasedShapeTrace corrections).count word := by
  induction hmultiplicity with
  | nil A =>
      rfl
  | append P B A hBA =>
      rfl
  | retained P B A hAB hweight hcorrection hinsert
      hleft hright ihleft ihright =>
      simp [erasedShapeTrace, List.count_append,
        List.count_cons, ihleft, ihright]
      omega
  | residual P B A hAB hweight hinsert hmultiplicity ihmultiplicity =>
      exact ihmultiplicity

/--
The collection recurrence value is the count in its literal retained-correction
shape trace.
-/
lemma count_collects_mult
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {multiplicity : ℕ}
    (hmultiplicity :
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word hcollect multiplicity) :
    multiplicity =
      (erasedShapeTrace corrections).count word := by
  induction hmultiplicity with
  | nil =>
      rfl
  | retained P A hweight hcollect hinsert
      hcollectMultiplicity hinsertMultiplicity ihcollect =>
      simp [erasedShapeTrace, List.count_append,
        ihcollect,
        count_inserts_mult
          hinsertMultiplicity]
  | residual P A hweight hcollect hmultiplicity ihmultiplicity =>
      exact ihmultiplicity

/-- The insertion recurrence value is unique. -/
lemma cutoff_inserts_multiplicity
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections}
    {left right : ℕ}
    (hleft :
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word hinsert left)
    (hright :
      CutoffInsertsMultiplicity
        n leftWeight rightWeight word hinsert right) :
    left = right := by
  rw [
    count_inserts_mult
      hleft,
    count_inserts_mult
      hright]

/-- The collection recurrence value is unique. -/
lemma cutoff_collects_multiplicity
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections}
    {left right : ℕ}
    (hleft :
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word hcollect left)
    (hright :
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word hcollect right) :
    left = right := by
  rw [
    count_collects_mult
      hleft,
    count_collects_mult
      hright]

end DFTerm

open DFTerm

namespace RSPrograa

/--
For a recursively compiled insertion schedule, the scalar collector recurrence
holds exactly at the schedule's erased-shape multiplicity.
-/
lemma inserts_mult_compiles
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
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
    (multiplicity : ℕ) :
    CutoffInsertsMultiplicity
        n leftWeight rightWeight word hinsert multiplicity ↔
      multiplicity = erasedShapeMultiplicity program word := by
  constructor
  · intro hmultiplicity
    rw [
      DFTerm.count_inserts_mult
        hmultiplicity,
      ← mult_inserts_corrections
        hcompile word]
  · intro hmultiplicity
    rcases
        DFTerm.inserts_erased_multiplicity
          word hinsert with
      ⟨recurrenceMultiplicity, hrecurrence⟩
    have hrecurrenceMultiplicity :
        recurrenceMultiplicity = erasedShapeMultiplicity program word := by
      rw [
        DFTerm.count_inserts_mult
          hrecurrence,
        ← mult_inserts_corrections
          hcompile word]
    rw [← hrecurrenceMultiplicity.trans hmultiplicity.symm]
    exact hrecurrence

/--
For a recursively compiled collection schedule, the scalar collector
recurrence holds exactly at the schedule's erased-shape multiplicity.
-/
lemma collects_mult_compiles
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
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
    (multiplicity : ℕ) :
    CutoffCollectsMultiplicity
        n leftWeight rightWeight word hcollect multiplicity ↔
      multiplicity = erasedShapeMultiplicity program word := by
  constructor
  · intro hmultiplicity
    rw [
      DFTerm.count_collects_mult
        hmultiplicity,
      ← mult_collects_corrections
        hcompile word]
  · intro hmultiplicity
    rcases
        DFTerm.collects_erased_multiplicity
          word hcollect with
      ⟨recurrenceMultiplicity, hrecurrence⟩
    have hrecurrenceMultiplicity :
        recurrenceMultiplicity = erasedShapeMultiplicity program word := by
      rw [
        DFTerm.count_collects_mult
          hrecurrence,
        ← mult_collects_corrections
          hcompile word]
    rw [← hrecurrenceMultiplicity.trans hmultiplicity.symm]
    exact hrecurrence

end RSPrograa

/--
Constructor-level arbitrary-cutoff target against the synchronized endpoint
collector.

For each natural input pair and Hall shape, the symbolic guarded branch sum is
itself certified by the scalar recurrence of the actual traced endpoint
collector derivation.
-/
structure
    EMRec
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
      RCOcc
        layer M N x y
  satisfies_endpoint_collector :
    ∀ M N word,
      CutoffCollectsMultiplicity
        n leftWeight rightWeight word
        (endpointCorrectionInventory layer M N
          |>.family_collects_corrections)
        (guardedBranchRecurrence
          raw M N word)

namespace
  EMRec

/--
Compile the constructor-level endpoint recurrence kernel to the synchronized
scalar multiplicity kernel consumed by the root-permutation pipeline.
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
      EMRec
        layer x y hleftWeight hrightWeight) :
    EMInduct
      layer x y hleftWeight hrightWeight where
  raw :=
    kernel.raw
  certificate M N :=
    (kernel.certificate M N)
      |>.endpointOccurrenceCertificate
  branch_schedule_multiplicity M N word := by
    exact
      (RSPrograa.collects_mult_compiles
          (kernel.certificate M N).compiles
          (guardedBranchRecurrence
            kernel.raw M N word)).mp
        (kernel.satisfies_endpoint_collector
          M N word)

/-- Compile the constructor-level recurrence directly to endpoint interpolation. -/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {G : Type u}
    [Group G]
    {x y : G}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EMRec
        layer x y hleftWeight hrightWeight) :=
  kernel.endpointMultInduction
    |>.fiberProfileInterpolation

end
  EMRec

namespace
  GMInduct

/--
Upgrade an earlier scalar induction kernel to the constructor-certified
endpoint collector recurrence.  The enhanced occurrence certificate and the
earlier selected endpoint schedule emit the same retained correction inventory.
-/
noncomputable def
    guardedMultRecurrence
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
    EMRec
      layer x y hleftWeight hrightWeight :=
  let certificate M N :=
    RCOcc.natural_recollect_layer
      layer M N x y hleftWeight hrightWeight hx hy hbot
  {
    raw := kernel.raw
    certificate := certificate
    satisfies_endpoint_collector := by
      intro M N word
      apply
        (RSPrograa.collects_mult_compiles
          (certificate M N).compiles
          (guardedBranchRecurrence
            kernel.raw M N word)).mpr
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
            RSPrograa.trace_erased_shape,
            (endpointScheduleProgram
              layer M N).correctionTrace_eq,
            RSPrograa.trace_erased_shape,
            (certificate M N).correctionTrace_eq]
  }

end
  GMInduct

/--
Through cutoff four, the symbolic guarded sum satisfies the constructor-level
endpoint collector recurrence while retaining the synchronized occurrence run.
-/
noncomputable def
    recursivelyNFour
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
    EMRec
      layer x y (by simp) (by simp) :=
  GMInduct.guardedMultRecurrence
    (inductionNFour
      layer hhigh raw)
    x y (by simp) (by simp) hbot

end
  CMRec
end TCTex
end Towers

/-!
# Claim 5 from synchronized endpoint occurrence certificates

The synchronized endpoint root-permutation kernel retains actual cutoff-aware
occurrence certificates while compiling to the earlier root-permutation
kernel.  This file exposes the resulting direct route to the quantified
power-coordinate polynomial package and its degree bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u v


open
  RPCrit
open
  CPCrit
open
  OOSched
open
  CRLayer
open
  PTOcc

namespace
  CPCrit
namespace
  GSPerm

/--
Ordered retained-packet alignment inherited by an occurrence-backed
synchronized root-permutation kernel.
-/
abbrev OrderedCoefficientAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {G : Type v}
    [Group G]
    {x y : G}
    (kernel :
      GSPerm
        layer x y (by simp) (by simp)) :
    Prop :=
  GPPerm.OrderedCoefficientAlignment.{u}
    (d := d)
    kernel.guardedPolyPermutation

/--
Retained occurrence scheduling and ordered transport supply the signed
list-evaluation law inherited by the synchronized kernel.
-/
lemma
    trunc_occ_transport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {G : Type v}
    [Group G]
    {x y : G}
    (kernel :
      GSPerm
        layer x y (by simp) (by simp))
    (halignment :
      OrderedCoefficientAlignment.{u}
        (d := d) kernel)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n) :
    GPPerm.SatisfiesTruncEval.{u}
      (d := d)
      kernel.guardedPolyPermutation :=
  kernel.guardedPolyPermutation
    |>.trunc_occ_transport
      halignment schedule orderedTransport

end
  GSPerm
end
  CPCrit

/--
An occurrence-backed synchronized root-trace permutation kernel, retained
packet alignment, retained scheduling, order transport, and residual-source
builders construct the complete quantified Claim 5 power input.
-/
theorem
    forall_synchronized_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {G : Type v}
    [Group G]
    {x y : G}
    (kernel :
      GSPerm
        layer x y (by simp) (by simp))
    (halignment :
      GSPerm.OrderedCoefficientAlignment.{u}
        (d := d) kernel)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuild
            (n := n) (inputWeight := inputWeight) hn H hH) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight :=
  forall_transversal_builders
    hn H hH
      kernel.guardedPolyPermutation
      halignment schedule orderedTransport
      lowWeightSource lowWeightSupported builders

/--
The occurrence-backed synchronized package yields the weight-controlled
integer-valued polynomial degree bound for every Hall coordinate of a power.
-/
theorem
    synchronized_collect_builders
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    {G : Type v}
    [Group G]
    {x y : G}
    (kernel :
      GSPerm
        layer x y (by simp) (by simp))
    (halignment :
      GSPerm.OrderedCoefficientAlignment.{u}
        (d := d) kernel)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TSBuild
            (n := n) (inputWeight := inputWeight) hn H hH)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    IVMost
      (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
      (s / r) :=
  transversal_collect_builders
    hn H hH
      kernel.guardedPolyPermutation
      halignment schedule orderedTransport
      lowWeightSource lowWeightSupported builders
      u hu hr hs hsn i

end TCTex
end Towers

/-!
# Local scalar models for recursively compiled retained-correction schedules

The constructor-level scalar recurrence is the right target for an
arbitrary-cutoff symbolic Hall collector proof, but an endpoint recurrence
certificate is still inconvenient to construct directly.  A symbolic
collector naturally assigns scalar values to input lists and insertion
problems, then proves one equation for each local collector constructor.

This file packages that proof interface.  Any pair of proof-free scalar
evaluators satisfying the local insertion and collection equations folds
through every traced collector derivation.  In particular, a local model for
the inverse-raw endpoint source compiles to the existing scalar induction
kernel and hence to endpoint interpolation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  RLModel

universe u

open
  HACoeff
open
  MIKern
open
  RMRec
open
  CRProgra
open
  CPProven
open
  PRCompb
open
  CMRec
open
  CMRec.DFTerm
open
  RCProven
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
  FIProf
open
  OCPartit
open
  RTProgra

/--
A proof-free scalar interpretation of the retained-correction collector.

The evaluator values depend only on the current list and inserted term.  The
fields assert the local equations needed at each actual traced collector
constructor.  This is the interface a symbolic Hall collector can satisfy by
weight induction.
-/
structure EMModel
    {M N K n leftWeight rightWeight : ℕ}
    (word : CWord HPAtom) where
  insertion :
    List (DFTerm M N K) →
      DFTerm M N K →
        ℕ
  collection :
    List (DFTerm M N K) →
      ℕ
  insertion_nil :
    ∀ A : DFTerm M N K,
      insertion [] A = 0
  insertion_append :
    ∀ (P : List (DFTerm M N K))
        (B A : DFTerm M N K),
      B.decorated.collectorLe A.decorated →
        insertion (P ++ [B]) A = 0
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
                  insertion P (B.correction A) +
                    [((B.correction A).family.recipe.erasedShape)].count word +
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
    collection [] = 0
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
                collection P + insertion C A
  collection_residual :
    ∀ (P : List (DFTerm M N K))
        (A : DFTerm M N K),
      n ≤ decoratedFamilyWeight leftWeight rightWeight A →
        ∀ {C corrections : List (DFTerm M N K)},
          CCCorrec
              n leftWeight rightWeight P C corrections →
            collection (P ++ [A]) =
              collection P

namespace EMModel

/--
The local insertion equations fold through every traced insertion derivation.
-/
lemma inserts_multiplicity_insertion
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (model :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    CutoffInsertsMultiplicity
      n leftWeight rightWeight word hinsert (model.insertion L A) := by
  induction hinsert with
  | nil A =>
      rw [model.insertion_nil A]
      exact .nil A
  | append P B A hBA =>
      rw [model.insertion_append P B A hBA]
      exact .append P B A hBA
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      rw [model.insertion_retained P B A hAB hweight hcorrection hinsert]
      exact
        .retained P B A hAB hweight hcorrection hinsert
          ihcorrection ihinsert
  | residual P B A hAB hweight hinsert ihinsert =>
      rw [model.insertion_residual P B A hAB hweight hinsert]
      exact .residual P B A hAB hweight hinsert ihinsert

/--
The local collection equations fold through every traced collection
derivation.
-/
lemma collects_multiplicity_collection
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (model :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    CutoffCollectsMultiplicity
      n leftWeight rightWeight word hcollect (model.collection L) := by
  induction hcollect with
  | nil =>
      rw [model.collection_nil]
      exact .nil
  | retained P A hweight hcollect hinsert ihcollect =>
      rw [model.collection_retained P A hweight hcollect hinsert]
      exact
        .retained P A hweight hcollect hinsert ihcollect
          (model.inserts_multiplicity_insertion
            hinsert)
  | residual P A hweight hcollect ihcollect =>
      rw [model.collection_residual P A hweight hcollect]
      exact .residual P A hweight hcollect ihcollect

/--
A local insertion model computes the literal retained-correction shape count.
-/
lemma insertion_count_erased
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (model :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    model.insertion L A =
      (erasedShapeTrace corrections).count word :=
  DFTerm.count_inserts_mult
    (model.inserts_multiplicity_insertion
      hinsert)

/--
A local collection model computes the literal retained-correction shape count.
-/
lemma collection_count_erased
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (model :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    model.collection L =
      (erasedShapeTrace corrections).count word :=
  DFTerm.count_collects_mult
    (model.collects_multiplicity_collection
      hcollect)

/--
Any two local models agree on every traced insertion problem.
-/
lemma insertion_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (left right :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    left.insertion L A =
      right.insertion L A :=
  DFTerm.cutoff_inserts_multiplicity
    (left.inserts_multiplicity_insertion
      hinsert)
    (right.inserts_multiplicity_insertion
      hinsert)

/--
Any two local models agree on every traced collection problem.
-/
lemma collection_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (left right :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    left.collection L =
      right.collection L :=
  DFTerm.cutoff_collects_multiplicity
    (left.collects_multiplicity_collection
      hcollect)
    (right.collects_multiplicity_collection
      hcollect)

/--
Against a recursively compiled insertion schedule, a local model computes its
erased-shape multiplicity.
-/
lemma insertion_multiplicity_compiles
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (model :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
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
    model.insertion L A =
      RSPrograa.erasedShapeMultiplicity
        program word :=
  (RSPrograa.inserts_mult_compiles
      hcompile (model.insertion L A)).mp
    (model.inserts_multiplicity_insertion
      hinsert)

/--
Against a recursively compiled collection schedule, a local model computes
its erased-shape multiplicity.
-/
lemma collection_multiplicity_compiles
    {M N K n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (model :
      EMModel
        (M := M) (N := N) (K := K)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word)
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
    model.collection L =
      RSPrograa.erasedShapeMultiplicity
        program word :=
  (RSPrograa.collects_mult_compiles
      hcompile (model.collection L)).mp
    (model.collects_multiplicity_collection
      hcollect)

end EMModel

/--
Local-equation form of the arbitrary-cutoff scalar Hall collector target.

For each natural input pair and erased Hall shape, the symbolic side supplies
a local scalar collector model.  It remains only to identify the guarded
symbolic sum with that model on the inverse-raw source list.
-/
structure
    PMModel
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  localModel :
    ∀ M N word,
      EMModel
        (M := M) (N := N)
        (K := (inverseLabelledCollection M N).factors.length)
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        word
  branch_sum_collection :
    ∀ M N word,
      guardedBranchRecurrence
          raw M N word =
        (localModel M N word).collection
          (inverseDecoratedTerms M N)

namespace
  PMModel

/--
Compile local symbolic collector equations to the direct scalar endpoint
induction kernel.
-/
noncomputable def
    scheduleMultInduction
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      PMModel
        layer hleftWeight hrightWeight) :
    GMInduct
      layer hleftWeight hrightWeight where
  raw :=
    kernel.raw
  branch_schedule_multiplicity M N word := by
    calc
      guardedBranchRecurrence
            kernel.raw M N word =
          (kernel.localModel M N word).collection
            (inverseDecoratedTerms M N) :=
        kernel.branch_sum_collection M N word
      _ =
          (erasedShapeTrace
            (endpointCorrectionInventory layer M N).corrections).count
              word :=
        (kernel.localModel M N word)
          |>.collection_count_erased
            (endpointCorrectionInventory layer M N
              |>.family_collects_corrections)
      _ =
          RSPrograa.erasedShapeMultiplicity
            (endpointScheduleProgram
              layer M N).program word := by
        unfold RSPrograa.erasedShapeMultiplicity
        rw [
          RSPrograa.trace_erased_shape,
          (endpointScheduleProgram
            layer M N).correctionTrace_eq]

/--
Compile local symbolic collector equations directly to endpoint
interpolation.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      PMModel
        layer hleftWeight hrightWeight) :=
  kernel.scheduleMultInduction
    |>.fiberProfileInterpolation

/--
Compile local symbolic collector equations to the occurrence-synchronized
constructor-level endpoint recurrence kernel in a matching nilpotent target.
-/
noncomputable def
    guardedMultRecurrence
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      PMModel
        layer hleftWeight hrightWeight)
    {G : Type u}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    EMRec
      layer x y hleftWeight hrightWeight :=
  CMRec.GMInduct.guardedMultRecurrence
    kernel.scheduleMultInduction
    x y hx hy hbot

end
  PMModel

end
  RLModel
end TCTex
end Towers

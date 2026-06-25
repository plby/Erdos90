import Towers.Group.Zassenhaus.RetainedProgramBoundary
import Towers.Group.Zassenhaus.BlockRecipe
import Towers.Group.Zassenhaus.CompatiblePacketRouting
import Towers.Group.Zassenhaus.RetainedHistoryFibers
import Towers.Group.Zassenhaus.InverseRaw
import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary
import Towers.Group.Zassenhaus.SelectedProfileAlgebra

/-!
# Concrete retained-correction schedule programs

The cutoff-full collector records retained corrections in its literal recursive
insertion order.  The erased-shape operational program forgets the concrete
crossing that emitted each retained correction.  This file keeps that crossing:
every retained node stores its two concrete parents and the strict cutoff proof
for their correction.

Traced cutoff insertion and collection derivations compile directly to these
concrete programs.  Erasing the compiled endpoint program recovers both the
selected correction-shape trace and the previously selected erased-shape
program trace.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace CRProgra

open
  HACoeff
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

/--
Concrete recursive schedule of retained cutoff-full corrections.  A retained
node remembers the crossed parents and certifies that its emitted correction is
strictly below the quotient cutoff.
-/
inductive RSPrograa
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ) where
  | empty :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight
  | append
      (left right :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight) :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight
  | retained
      (left :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight)
      (crossedLeft crossedRight : DFTerm M N K)
      (hweight :
        decoratedFamilyWeight leftWeight rightWeight
          (crossedLeft.correction crossedRight) < n)
      (right :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight) :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight

namespace RSPrograa

/-- Literal concrete correction trace emitted by one schedule program. -/
def correctionTrace
    {M N K n leftWeight rightWeight : ℕ} :
    RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight →
      List (DFTerm M N K)
  | .empty =>
      []
  | .append left right =>
      left.correctionTrace ++ right.correctionTrace
  | .retained left crossedLeft crossedRight _hweight right =>
      left.correctionTrace ++
        [crossedLeft.correction crossedRight] ++
          right.correctionTrace

/-- Ordered concrete parent crossings retained by one schedule program. -/
def crossings
    {M N K n leftWeight rightWeight : ℕ} :
    RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight →
      List (DFTerm M N K × DFTerm M N K)
  | .empty =>
      []
  | .append left right =>
      left.crossings ++ right.crossings
  | .retained left crossedLeft crossedRight _hweight right =>
      left.crossings ++ [(crossedLeft, crossedRight)] ++ right.crossings

/-- Erase concrete crossing witnesses while retaining the recursive schedule. -/
def shapeTraceProgram
    {M N K n leftWeight rightWeight : ℕ} :
    RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight →
      ESProgra
  | .empty =>
      .empty
  | .append left right =>
      .append left.shapeTraceProgram right.shapeTraceProgram
  | .retained left crossedLeft crossedRight _hweight right =>
      .retained left.shapeTraceProgram
        (crossedLeft.correction crossedRight).family.recipe.erasedShape
        right.shapeTraceProgram

@[simp]
lemma correctionTrace_empty
    {M N K n leftWeight rightWeight : ℕ} :
    (RSPrograa.empty :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight).correctionTrace =
      [] := by
  rfl

@[simp]
lemma correctionTrace_append
    {M N K n leftWeight rightWeight : ℕ}
    (left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    (RSPrograa.append left right).correctionTrace =
      left.correctionTrace ++ right.correctionTrace := by
  rfl

@[simp]
lemma correctionTrace_retained
    {M N K n leftWeight rightWeight : ℕ}
    (left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    (crossedLeft crossedRight : DFTerm M N K)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n) :
    (RSPrograa.retained
      left crossedLeft crossedRight hweight right).correctionTrace =
        left.correctionTrace ++
          [crossedLeft.correction crossedRight] ++
            right.correctionTrace := by
  rfl

/--
Applying the concrete correction constructor to the ordered crossing list
recovers the literal emitted correction trace.
-/
lemma map_correction_crossings
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    program.crossings.map (fun crossing =>
      crossing.1.correction crossing.2) =
        program.correctionTrace := by
  induction program with
  | empty =>
      rfl
  | append left right ihleft ihright =>
      simp [crossings, ihleft, ihright]
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      simp [crossings, ihleft, ihright]

/-- Every concrete correction emitted by a schedule program lies below cutoff. -/
lemma weight_correction_trace
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    {term : DFTerm M N K}
    (hterm : term ∈ program.correctionTrace) :
    decoratedFamilyWeight leftWeight rightWeight term < n := by
  induction program with
  | empty =>
      simp at hterm
  | append left right ihleft ihright =>
      simp only [correctionTrace_append, List.mem_append] at hterm
      rcases hterm with hterm | hterm
      · exact ihleft hterm
      · exact ihright hterm
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      simp only [correctionTrace_retained, List.mem_append,
        List.mem_singleton] at hterm
      rcases hterm with (hterm | hterm) | hterm
      · exact ihleft hterm
      · subst term
        exact hweight
      · exact ihright hterm

/-- Every listed concrete parent crossing emits a correction below cutoff. -/
lemma weight_correction_crossings
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    {crossing : DFTerm M N K × DFTerm M N K}
    (hcrossing : crossing ∈ program.crossings) :
    decoratedFamilyWeight leftWeight rightWeight
      (crossing.1.correction crossing.2) < n := by
  apply program.weight_correction_trace
  rw [← program.map_correction_crossings]
  exact List.mem_map.mpr ⟨crossing, hcrossing, rfl⟩

/--
Erasing a concrete schedule program emits exactly the erased shapes of its
concrete correction trace.
-/
lemma trace_erased_shape
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    program.shapeTraceProgram.trace =
      erasedShapeTrace program.correctionTrace := by
  induction program with
  | empty =>
      rfl
  | append left right ihleft ihright =>
      simp [shapeTraceProgram, erasedShapeTrace,
        ihleft, ihright]
  | retained left crossedLeft crossedRight hweight right ihleft ihright =>
      simp [shapeTraceProgram, erasedShapeTrace,
        ihleft, ihright]

end RSPrograa

/--
Every traced cutoff insertion derivation admits a concrete recursive retained
correction schedule.
-/
lemma concrete_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections) :
    ∃ program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight,
      program.correctionTrace = corrections := by
  induction hinsert with
  | nil A =>
      exact ⟨.empty, rfl⟩
  | append P B A hBA =>
      exact ⟨.empty, rfl⟩
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      rcases ihcorrection with ⟨left, hleft⟩
      rcases ihinsert with ⟨right, hright⟩
      refine ⟨.retained left B A hweight right, ?_⟩
      simp [hleft, hright]
  | residual P B A hAB hweight hinsert ihinsert =>
      exact ihinsert

/--
Every traced cutoff collection derivation admits a concrete recursive
retained-correction schedule.
-/
lemma concrete_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    ∃ program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight,
      program.correctionTrace = corrections := by
  induction hcollect with
  | nil =>
      exact ⟨.empty, rfl⟩
  | retained P A hweight hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨collectProgram, hcollectProgram⟩
      rcases
          concrete_inserts_corrections
            hinsert with
        ⟨insertProgram, hinsertProgram⟩
      refine ⟨.append collectProgram insertProgram, ?_⟩
      simp [hcollectProgram, hinsertProgram]
  | residual P A hweight hcollect ihcollect =>
      exact ihcollect

/--
Canonical concrete schedule program compiled from the selected endpoint
inventory.
-/
noncomputable def endpointConcreteProgram
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    RSPrograa
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      n leftWeight rightWeight :=
  Classical.choose
    (concrete_collects_corrections
      (endpointCorrectionInventory layer M
        N).family_collects_corrections)

/-- The canonical endpoint program emits exactly the selected concrete inventory. -/
lemma endpoint_concrete_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    (endpointConcreteProgram layer M N).correctionTrace =
      (endpointCorrectionInventory layer M N).corrections := by
  exact
    Classical.choose_spec
      (concrete_collects_corrections
        (endpointCorrectionInventory layer M
          N).family_collects_corrections)

/--
The selected endpoint correction inventory is the ordered image of its
retained concrete parent crossings.
-/
lemma crossings_endpoint_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    (endpointConcreteProgram layer M N).crossings.map
        (fun crossing => crossing.1.correction crossing.2) =
      (endpointCorrectionInventory layer M N).corrections := by
  rw [
    RSPrograa.map_correction_crossings,
    endpoint_concrete_program]

/--
Erasing the canonical concrete endpoint program recovers the literal selected
retained-correction shape trace.
-/
lemma program_endpoint_schedule
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ((endpointConcreteProgram layer M N)
        |>.shapeTraceProgram).trace =
      selectedErasedShape layer M N := by
  rw [
    RSPrograa.trace_erased_shape,
    endpoint_concrete_program]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/--
The canonical concrete endpoint compiler and the earlier existentially selected
shape program emit the same erased-shape trace.
-/
lemma trace_erased_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    ((endpointConcreteProgram layer M N)
        |>.shapeTraceProgram).trace =
      (endpointErasedProgram layer M N).trace := by
  rw [
    program_endpoint_schedule,
    endpoint_erased_program]

end CRProgra
end TCTex
end Towers

/-!
# Concrete retained-correction polynomial-orbit alignment

The cutoff-full collector records concrete retained parent crossings.  The
recipe-free polynomial-orbit recursion records the corresponding symbolic
obstructions.  This file identifies the local root emitted by those two
descriptions and lifts the identification over a concrete schedule program.

In particular, every concrete endpoint correction shape is the erased root of
a polynomial-orbit obstruction with the same strict weighted cutoff guard.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace CRAlign

open
  HACoeff
open
  RRPkt
open
  RRPkt.POObstru
open
  BRPkt
open
  ROAggreg
open
  ROTransi
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CFCollec
open
  CRLayer
open
  CCAggreg
open
  OCPartit
open
  RTProgra
open
  SEAlg

/-- Recipe obstruction obtained by forgetting the concrete labels of one crossing. -/
def crossingRecipeObstruction
    {M N K : ℕ}
    (crossing :
      DFTerm M N K × DFTerm M N K) :
    RObstru where
  left :=
    crossing.1.family.recipe
  right :=
    crossing.2.family.recipe

/-- Recipe-free polynomial-orbit obstruction attached to one concrete crossing. -/
def concreteCrossingObstruction
    {M N K : ℕ}
    (crossing :
      DFTerm M N K × DFTerm M N K) :
    POObstru :=
  polynomialOrbitObstruction
    (crossingRecipeObstruction crossing)

@[simp]
lemma correction_crossing_obstruction
    {M N K : ℕ}
    (crossing :
      DFTerm M N K × DFTerm M N K) :
    (concreteCrossingObstruction crossing).correction =
      polynomialOrbitKey
        (crossing.1.correction crossing.2).family.recipe := by
  simp [concreteCrossingObstruction,
    crossingRecipeObstruction, DFTerm.correction,
    RObstru.correction]

@[simp]
lemma concrete_crossing_obstruction
    {M N K : ℕ}
    (crossing :
      DFTerm M N K × DFTerm M N K) :
    (concreteCrossingObstruction crossing).correction.erasedShape =
      (crossing.1.correction crossing.2).erasedShape := by
  rw [correction_crossing_obstruction]
  exact
    (DFTerm.erased_shape_family
      (crossing.1.correction crossing.2)).symm

@[simp]
lemma crossing_orbit_obstruction
    {M N K leftWeight rightWeight : ℕ}
    (crossing :
      DFTerm M N K × DFTerm M N K) :
    (concreteCrossingObstruction crossing).weight
        leftWeight rightWeight =
      decoratedFamilyWeight leftWeight rightWeight
        (crossing.1.correction crossing.2) := by
  simp [concreteCrossingObstruction,
    crossingRecipeObstruction, DFTerm.correction,
    RObstru.weight, decoratedFamilyWeight, Nat.add_mul]
  omega

/-- Ordered polynomial-orbit obstruction roots attached to one concrete program. -/
def polynomialOrbitObstructions
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    List POObstru :=
  program.crossings.map concreteCrossingObstruction

/--
The erased roots of the attached recipe-free obstructions are exactly the
erased-shape trace emitted by the concrete schedule program.
-/
lemma RSPrograa.mapcor_erase_polyo
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    (polynomialOrbitObstructions program).map
        (fun obstruction => obstruction.correction.erasedShape) =
      program.shapeTraceProgram.trace := by
  rw [
    RSPrograa.trace_erased_shape,
    ← RSPrograa.map_correction_crossings]
  simp [polynomialOrbitObstructions, erasedShapeTrace,
    polynomialOrbitKey, List.map_map]

/-- Every attached polynomial-orbit obstruction root lies below cutoff. -/
lemma RSPrograa.weight_mempo_orbit
    {M N K n leftWeight rightWeight : ℕ}
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight)
    {obstruction : POObstru}
    (hobstruction : obstruction ∈ polynomialOrbitObstructions program) :
    obstruction.weight leftWeight rightWeight < n := by
  rcases List.mem_map.mp hobstruction with
    ⟨crossing, hcrossing, rfl⟩
  rw [crossing_orbit_obstruction]
  exact program.weight_correction_crossings hcrossing

/--
The selected endpoint correction-shape trace is literally the list of erased
roots attached to its retained concrete crossings.
-/
lemma erasedObstructionsProgram
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    (polynomialOrbitObstructions
        (endpointConcreteProgram layer M N)).map
          (fun obstruction => obstruction.correction.erasedShape) =
      selectedErasedShape layer M N := by
  rw [
    RSPrograa.mapcor_erase_polyo,
    program_endpoint_schedule]

/-- Every selected endpoint polynomial-orbit obstruction root lies below cutoff. -/
lemma obstructions_endpoint_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    {obstruction : POObstru}
    (hobstruction :
      obstruction ∈
        polynomialOrbitObstructions
          (endpointConcreteProgram layer M N)) :
    obstruction.weight leftWeight rightWeight < n := by
  exact
    RSPrograa.weight_mempo_orbit
      (endpointConcreteProgram layer M N)
      hobstruction

end CRAlign
end TCTex
end Towers

/-!
# Concrete alignment for nested polynomial-orbit crossings

The recipe-free operational obstruction children have concrete
interpretations.  Starting from a retained parent crossing `(left, right)`,
the left child crosses `left` with the emitted correction and the right child
crosses `right` with that same correction.  This file records those equations
and their cutoff-weight forms.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace CNAlign

open HACoeff
open RRPkt
open
  RRPkt.POObstru
open CRAlign
open CFCollec
open OCPartit

/--
The left operational obstruction child is the concrete crossing of the left
parent with the emitted correction.
-/
@[simp]
lemma operational_nested_crossing
    {M N K : ℕ}
    (left right : DFTerm M N K) :
    (concreteCrossingObstruction
      (left, right)).operationalNestedLeft =
        concreteCrossingObstruction
          (left, left.correction right) := by
  simp [concreteCrossingObstruction,
    crossingRecipeObstruction, polynomialOrbitObstruction,
    POObstru.operationalNestedLeft,
    POObstru.correction, DFTerm.correction]

/--
The right operational obstruction child is the concrete crossing of the right
parent with the emitted correction.
-/
@[simp]
lemma operational_concrete_obstruction
    {M N K : ℕ}
    (left right : DFTerm M N K) :
    (concreteCrossingObstruction
      (left, right)).operationalNestedRight =
        concreteCrossingObstruction
          (right, left.correction right) := by
  simp [concreteCrossingObstruction,
    crossingRecipeObstruction, polynomialOrbitObstruction,
    POObstru.operationalNestedRight,
    POObstru.correction, DFTerm.correction]

/-- Concrete cutoff weight of the left operational child. -/
@[simp]
lemma operational_nested_obstruction
    {M N K leftWeight rightWeight : ℕ}
    (left right : DFTerm M N K) :
    (concreteCrossingObstruction
      (left, right)).operationalNestedLeft.weight leftWeight rightWeight =
        decoratedFamilyWeight leftWeight rightWeight
          (left.correction (left.correction right)) := by
  rw [operational_nested_crossing]
  exact
    crossing_orbit_obstruction
      (left, left.correction right)

/-- Concrete cutoff weight of the right operational child. -/
@[simp]
lemma nested_crossing_obstruction
    {M N K leftWeight rightWeight : ℕ}
    (left right : DFTerm M N K) :
    (concreteCrossingObstruction
      (left, right)).operationalNestedRight.weight leftWeight rightWeight =
        decoratedFamilyWeight leftWeight rightWeight
          (right.correction (left.correction right)) := by
  rw [operational_concrete_obstruction]
  exact
    crossing_orbit_obstruction
      (right, left.correction right)

/-- Erased Hall shape emitted at the left operational child. -/
@[simp]
lemma operational_crossing_obstruction
    {M N K : ℕ}
    (left right : DFTerm M N K) :
    (concreteCrossingObstruction
      (left, right)).operationalNestedLeft.correction.erasedShape =
        (left.correction (left.correction right)).erasedShape := by
  rw [operational_nested_crossing]
  exact
    concrete_crossing_obstruction
      (left, left.correction right)

/-- Erased Hall shape emitted at the right operational child. -/
@[simp]
lemma erased_crossing_obstruction
    {M N K : ℕ}
    (left right : DFTerm M N K) :
    (concreteCrossingObstruction
      (left, right)).operationalNestedRight.correction.erasedShape =
        (right.correction (left.correction right)).erasedShape := by
  rw [operational_concrete_obstruction]
  exact
    concrete_crossing_obstruction
      (right, left.correction right)

end CNAlign
end TCTex
end Towers

/-!
# Source provenance for concrete retained-correction schedule programs

The concrete retained-correction schedule remembers every crossed parent, but
its basic compiler only records the emitted correction trace.  This file
strengthens that compiler with causal provenance: both parents of every stored
crossing lie in the finite pairwise-correction closure of the original source.

The endpoint specialization selects a provenance-certified concrete schedule
whose source is the inverse raw packet.  Its recipe-free polynomial-orbit
roots still recover the literal selected correction-shape trace.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace CPProven

open
  HACoeff
open
  RRPkt
open
  CRAlign
open
  CRProgra
open
  CRProgra.RSPrograa
open
  CFCollec
open
  CFCollec.DFTerm
open
  FVSuppor
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
  RTProgra
open
  SEAlg

/--
Both parents of every concrete crossing stored by a schedule program are
generated from the designated source by finitely many pairwise corrections.
-/
def CGFroma
    {M N K n leftWeight rightWeight : ℕ}
    (source : List (DFTerm M N K))
    (program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight) :
    Prop :=
  ∀ crossing ∈ program.crossings,
    CGFrom source crossing.1 ∧
      CGFrom source crossing.2

namespace CGFroma

/-- The empty schedule has no crossing provenance obligations. -/
lemma empty
    {M N K n leftWeight rightWeight : ℕ}
    (source : List (DFTerm M N K)) :
    CGFroma source
      (RSPrograa.empty :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight) := by
  simp [CGFroma,
    RSPrograa.crossings]

/-- Concatenating schedules concatenates their crossing provenance proofs. -/
lemma append
    {M N K n leftWeight rightWeight : ℕ}
    {source : List (DFTerm M N K)}
    {left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hleft : CGFroma source left)
    (hright : CGFroma source right) :
    CGFroma source
      (RSPrograa.append left right) := by
  intro crossing hcrossing
  rcases List.mem_append.mp hcrossing with hcrossing | hcrossing
  · exact hleft crossing hcrossing
  · exact hright crossing hcrossing

/-- Add one retained crossing whose two concrete parents are generated. -/
lemma retained
    {M N K n leftWeight rightWeight : ℕ}
    {source : List (DFTerm M N K)}
    {left right :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    {crossedLeft crossedRight : DFTerm M N K}
    {hweight :
      decoratedFamilyWeight leftWeight rightWeight
        (crossedLeft.correction crossedRight) < n}
    (hleft : CGFroma source left)
    (hcrossedLeft : CGFrom source crossedLeft)
    (hcrossedRight : CGFrom source crossedRight)
    (hright : CGFroma source right) :
    CGFroma source
      (RSPrograa.retained
        left crossedLeft crossedRight hweight right) := by
  intro crossing hcrossing
  simp only [RSPrograa.crossings,
    List.mem_append, List.mem_singleton] at hcrossing
  rcases hcrossing with (hcrossing | hcrossing) | hcrossing
  · exact hleft crossing hcrossing
  · subst crossing
    exact ⟨hcrossedLeft, hcrossedRight⟩
  · exact hright crossing hcrossing

/-- Enlarge the source available to every parent crossing in a schedule. -/
lemma mono
    {M N K n leftWeight rightWeight : ℕ}
    {source source' : List (DFTerm M N K)}
    {program :
      RSPrograa
        (M := M) (N := N) (K := K) n leftWeight rightWeight}
    (hprogram : CGFroma source program)
    (hsource : ∀ term ∈ source, term ∈ source') :
    CGFroma source' program := by
  intro crossing hcrossing
  exact
    ⟨(hprogram crossing hcrossing).1.mono hsource,
      (hprogram crossing hcrossing).2.mono hsource⟩

end CGFroma

/--
Every traced cutoff insertion compiles to a concrete schedule whose stored
parents remain generated from any common source containing the input.
-/
lemma schedule_inserts_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {source L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections)
    (hL : ∀ term ∈ L, CGFrom source term)
    (hA : CGFrom source A) :
    ∃ program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight,
      program.correctionTrace = corrections ∧
        CGFroma source program := by
  induction hinsert with
  | nil A =>
      exact ⟨.empty, rfl, CGFroma.empty source⟩
  | append P B A hBA =>
      exact ⟨.empty, rfl, CGFroma.empty source⟩
  | retained P B A hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
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
      rcases ihcorrection hP hBA with
        ⟨left, hleftTrace, hleftGenerated⟩
      have hQ :=
        DFTerm.correction_cutoff_inserts
          hcorrection.cutoffInserts hP hBA
      rcases ihinsert hQ hA with
        ⟨right, hrightTrace, hrightGenerated⟩
      refine
        ⟨.retained left B A hweight right, ?_,
          CGFroma.retained
            hleftGenerated hB hA hrightGenerated⟩
      simp [hleftTrace, hrightTrace]
  | residual P B A hAB hweight hinsert ihinsert =>
      have hP :
          ∀ term ∈ P, CGFrom source term := by
        intro term hterm
        exact hL term (List.mem_append_left [B] hterm)
      exact ihinsert hP hA

/--
Every traced cutoff collection compiles to a concrete schedule whose stored
parents remain generated from its original source list.
-/
lemma schedule_collects_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    ∃ program :
        RSPrograa
          (M := M) (N := N) (K := K) n leftWeight rightWeight,
      program.correctionTrace = corrections ∧
        CGFroma L program := by
  induction hcollect with
  | nil =>
      exact ⟨.empty, rfl, CGFroma.empty []⟩
  | retained P A hweight hcollect hinsert ihcollect =>
      rcases ihcollect with
        ⟨collectProgram, hcollectTrace, hcollectGenerated⟩
      have hcollectGenerated' :
          CGFroma (P ++ [A]) collectProgram :=
        hcollectGenerated.mono fun term hterm =>
          List.mem_append_left [A] hterm
      have hC := fun term hterm => by
        exact
          (DFTerm.correction_cutoff_collects
            hcollect.cutoffCollects term hterm).mono fun next hnext =>
              List.mem_append_left [A] hnext
      have hA :
          CGFrom (P ++ [A]) A :=
        CGFrom.source (by simp)
      rcases
          schedule_inserts_corrections
            hinsert hC hA with
        ⟨insertProgram, hinsertTrace, hinsertGenerated⟩
      refine
        ⟨.append collectProgram insertProgram, ?_,
          CGFroma.append
            hcollectGenerated' hinsertGenerated⟩
      simp [hcollectTrace, hinsertTrace]
  | residual P A hweight hcollect ihcollect =>
      rcases ihcollect with
        ⟨program, htrace, hgenerated⟩
      exact
        ⟨program, htrace,
          hgenerated.mono fun term hterm =>
            List.mem_append_left [A] hterm⟩

/--
One selected endpoint schedule together with inverse-raw provenance for every
stored concrete parent crossing.
-/
structure EndpointGeneratedProgram
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) where
  program :
    RSPrograa
      (M := M) (N := N)
      (K := (inverseLabelledCollection M N).factors.length)
      n leftWeight rightWeight
  correctionTrace_eq :
    program.correctionTrace =
      (endpointCorrectionInventory layer M N).corrections
  crossings_generated :
    CGFroma (inverseDecoratedTerms M N) program

/-- Select an inverse-raw provenance-certified concrete endpoint schedule. -/
noncomputable def endpointScheduleProgram
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    EndpointGeneratedProgram layer M N :=
  let hexists :=
    schedule_collects_corrections
      (endpointCorrectionInventory layer M
        N).family_collects_corrections
  {
    program := Classical.choose hexists
    correctionTrace_eq := (Classical.choose_spec hexists).1
    crossings_generated := (Classical.choose_spec hexists).2
  }

/--
The erased roots of the provenance-certified endpoint obstructions recover
the literal selected retained-correction shape trace.
-/
lemma erasedEndpointProgram
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    (polynomialOrbitObstructions
        (endpointScheduleProgram
          layer M N).program).map
          (fun obstruction => obstruction.correction.erasedShape) =
      selectedErasedShape layer M N := by
  rw [
    RSPrograa.mapcor_erase_polyo,
    RSPrograa.trace_erased_shape,
    (endpointScheduleProgram
      layer M N).correctionTrace_eq]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/-- Every selected provenance-certified endpoint crossing has inverse-raw parents. -/
lemma inverse_schedule_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
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
    CGFrom
        (inverseDecoratedTerms M N) crossing.1 ∧
      CGFrom
        (inverseDecoratedTerms M N) crossing.2 :=
  (endpointScheduleProgram
    layer M N).crossings_generated crossing hcrossing

/-- Every provenance-certified endpoint obstruction root lies below cutoff. -/
lemma weight_schedule_program
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    {obstruction : POObstru}
    (hobstruction :
      obstruction ∈
        polynomialOrbitObstructions
          (endpointScheduleProgram
            layer M N).program) :
    obstruction.weight leftWeight rightWeight < n := by
  exact
    RSPrograa.weight_mempo_orbit
      (endpointScheduleProgram
        layer M N).program
      hobstruction

end CPProven
end TCTex
end Towers

/-!
# Finite-index orbit traces for concrete retained corrections

Inverse-raw normalization preserves the literal polynomial-orbit key, not
merely the erased Hall shape.  That exact source statement propagates through
finite correction trees.  Applied to the provenance-certified concrete
endpoint schedule, it places every retained concrete correction root in the
finite retained polynomial-orbit vocabulary.

The actual scheduler root trace therefore admits a finite-index encoding whose
decoded erased shapes recover the selected retained-correction shape trace.
This does not claim that the larger recipe-free recursive packets rooted at
those crossings are already supported.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace CRIndexa

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
  BRSpec
open
  CRAlign
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
  RHRecipe
open
  HHTrunc
open
  RONorm
open
  RRVocabu
open
  UCVocabu
open
  RITrace
open
  URVocabu
open
  SEAlg

/--
Every below-cutoff inverse-raw concrete source term has an exactly matching
polynomial-orbit key in the universal source recipe vocabulary.
-/
lemma key_decorated_terms
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ inverseDecoratedTerms M N)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight term < n) :
    ∃ recipe ∈ sourceRecipes n leftWeight rightWeight,
      polynomialOrbitKey recipe =
        polynomialOrbitKey term.family.recipe := by
  have htermShapeWeight :
      term.erasedShape.weight
          (HPAtom.weight leftWeight rightWeight) < n := by
    simpa [decoratedFamilyWeight, weightedWordWeight,
      term.erased_shape_family] using hweight
  rcases history_decorated_terms hterm with
    ⟨history, hhistory, hword⟩
  have hhistoryWeight :
      RHistor.weight leftWeight rightWeight history < n := by
    simpa [RHistor.weight, hword, DFTerm.erasedShape,
      DTerm.erasedShape] using htermShapeWeight
  have hretained :
      history ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N) :=
    mem_retainedHistories.mpr ⟨hhistory, hhistoryWeight⟩
  rcases
      orbit_key_histories
        hleftWeight hrightWeight hretained with
    ⟨recipe, hrecipe, hkey⟩
  refine ⟨recipe, hrecipe, hkey.trans ?_⟩
  apply congrArg polynomialOrbitKey
  unfold inverseDecoratedTerms at hterm
  rcases List.mem_ofFn.mp hterm with ⟨index, rfl⟩
  simp [RRVocabu.RHistor.initialRecipe,
    IRecipe.blockRecipe, DFTerm.ofLabelLinear,
    BFam.ofLinear, hword]

/--
Exact polynomial-orbit source representatives propagate through any finite
concrete correction tree, with closure depth bounded by the output weight.
-/
lemma recipe_key_generated
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {source : List (DFTerm M N K)}
    {sourceRecipes : List BRecipe}
    (hsource :
      ∀ sourceTerm ∈ source,
        decoratedFamilyWeight leftWeight rightWeight sourceTerm < n →
          ∃ recipe ∈ sourceRecipes,
            polynomialOrbitKey recipe =
              polynomialOrbitKey sourceTerm.family.recipe)
    {term : DFTerm M N K}
    (hterm : CGFrom source term) :
    decoratedFamilyWeight leftWeight rightWeight term < n →
      ∃ recipe ∈
          correctionClosure sourceRecipes
            (decoratedFamilyWeight leftWeight rightWeight term),
        polynomialOrbitKey recipe =
          polynomialOrbitKey term.family.recipe := by
  induction hterm with
  | source hterm =>
      intro hweight
      rcases hsource _ hterm hweight with
        ⟨recipe, hrecipe, hkey⟩
      exact
        ⟨recipe,
          correction_closure
            (show recipe ∈ correctionClosure sourceRecipes 0 by
              exact hrecipe)
            (Nat.zero_le _),
          hkey⟩
  | @correction left right _ _ ihleft ihright =>
      intro hweight
      have hleftCutoff :
          decoratedFamilyWeight leftWeight rightWeight left < n := by
        rw [decorated_family_correction] at hweight
        omega
      have hrightCutoff :
          decoratedFamilyWeight leftWeight rightWeight right < n := by
        rw [decorated_family_correction] at hweight
        omega
      rcases ihleft hleftCutoff with
        ⟨leftRecipe, hleftRecipe, hleftKey⟩
      rcases ihright hrightCutoff with
        ⟨rightRecipe, hrightRecipe, hrightKey⟩
      refine ⟨leftRecipe.correction rightRecipe, ?_, ?_⟩
      · apply correction_closure
          (correction_mem_closure hleftRecipe hrightRecipe)
        rw [decorated_family_correction]
        have hleftPos :
            0 <
              decoratedFamilyWeight leftWeight rightWeight left :=
          weighted_weight_pos hleftWeight hrightWeight left.family.recipe
        have hrightPos :
            0 <
              decoratedFamilyWeight leftWeight rightWeight right :=
          weighted_weight_pos hleftWeight hrightWeight right.family.recipe
        omega
      · simp [DFTerm.correction, hleftKey, hrightKey]

/--
Every below-cutoff generated concrete term has an exact polynomial-orbit
representative in the retained finite correction-closure vocabulary.
-/
lemma recipe_correction_inverse
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      CGFrom (inverseDecoratedTerms M N) term)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight term < n) :
    ∃ recipe ∈
        correctionClosureRecipes n leftWeight rightWeight,
      polynomialOrbitKey recipe =
        polynomialOrbitKey term.family.recipe := by
  rcases
      recipe_key_generated
        hleftWeight hrightWeight
        (sourceRecipes := sourceRecipes n leftWeight rightWeight)
        (fun sourceTerm hsourceTerm hsourceWeight =>
          key_decorated_terms
            hleftWeight hrightWeight hsourceTerm hsourceWeight)
        hterm hweight with
    ⟨recipe, hrecipe, hkey⟩
  refine
    ⟨recipe, retained_correction_closure.mpr ⟨?_, ?_⟩, hkey⟩
  · exact correction_closure hrecipe
      (Nat.le_of_lt hweight)
  · have hrecipeWeight :
        weightedWordWeight leftWeight rightWeight recipe =
          weightedWordWeight leftWeight rightWeight term.family.recipe := by
      rw [← weight_orbit_key, ← weight_orbit_key, hkey]
    rw [hrecipeWeight]
    exact hweight

/--
Every actual retained endpoint obstruction root belongs to the finite
polynomial-orbit vocabulary.
-/
lemma poly_schedule_program
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
    obstruction.correction ∈
      retainedOrbitVocabulary n leftWeight rightWeight := by
  rcases List.mem_map.mp hobstruction with
    ⟨crossing, hcrossing, rfl⟩
  have hparents :=
    inverse_schedule_program
      layer M N hcrossing
  have hgenerated :
      CGFrom (inverseDecoratedTerms M N)
        (crossing.1.correction crossing.2) :=
    CGFrom.correction hparents.1 hparents.2
  have hweight :=
    (endpointScheduleProgram
      layer M N).program.weight_correction_crossings hcrossing
  rcases
      recipe_correction_inverse
        hleftWeight hrightWeight hgenerated hweight with
    ⟨recipe, hrecipe, hkey⟩
  rw [correction_crossing_obstruction, ← hkey]
  exact
    key_vocabulary_recipes
      hrecipe

/-- Ordered finite-alphabet keys emitted by the actual retained endpoint roots. -/
def endpointGeneratedKeys
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ) :
    List POKey :=
  (polynomialOrbitObstructions
      (endpointScheduleProgram
        layer M N).program).map
    (fun obstruction => obstruction.correction)

/-- Every actual retained endpoint root key is supported by the finite alphabet. -/
lemma retained_poly_keys
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    {key : POKey}
    (hkey :
      key ∈
        endpointGeneratedKeys
          layer M N) :
    key ∈ retainedOrbitVocabulary n leftWeight rightWeight := by
  rcases List.mem_map.mp hkey with
    ⟨obstruction, hobstruction, rfl⟩
  exact
    poly_schedule_program
      layer hleftWeight hrightWeight M N hobstruction

/-- Finite-index encoding of the actual retained endpoint orbit-root trace. -/
noncomputable def endpointGeneratedConcrete
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  orbitIndexTrace
    (endpointGeneratedKeys
      layer M N)
    (fun _key hkey =>
      retained_poly_keys
        layer hleftWeight hrightWeight M N hkey)

/-- Decoding the finite endpoint root trace recovers its ordered key list. -/
lemma key_generated_concrete
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (endpointGeneratedConcrete
      layer hleftWeight hrightWeight M N).map
        retainedOrbitKey =
      endpointGeneratedKeys
        layer M N := by
  exact
    retained_key_trace
      (endpointGeneratedKeys
        layer M N)
      _

/--
Decoding finite indices and erasing orbit data recovers the selected literal
retained-correction shape trace.
-/
lemma key_endpoint_generated
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    (endpointGeneratedConcrete
      layer hleftWeight hrightWeight M N).map
        (fun index => (retainedOrbitKey index).erasedShape) =
      selectedErasedShape layer M N := by
  calc
    _ =
        ((endpointGeneratedConcrete
          layer hleftWeight hrightWeight M N).map
            retainedOrbitKey).map
          POKey.erasedShape := by
      simp [List.map_map, Function.comp_def]
    _ =
        (endpointGeneratedKeys
          layer M N).map POKey.erasedShape := by
      rw [
        key_generated_concrete]
    _ = selectedErasedShape layer M N := by
      simpa [
        endpointGeneratedKeys,
        List.map_map] using
        erasedEndpointProgram
          layer M N

end CRIndexa
end TCTex
end Towers

/-!
# Synchronizing concrete correction programs with occurrence runs

The traced cutoff-full collector already exposes two operational projections.
Its retained corrections compile to a provenance-certified concrete schedule
program, while its underlying collection derivation compiles to a literal
occurrence rewrite run.  This file packages those projections together.

The selected endpoint certificate therefore remembers, from one actual
cutoff-full derivation:

* every retained concrete parent crossing and its inverse-raw provenance;
* the emitted retained-correction trace;
* the cutoff-aware occurrence run from the inverse-raw source to the endpoint.

This is a constructor-facing boundary for the remaining symbolic scheduler
argument.  It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  TOSync

universe u

open scoped commutatorElement

open
  HACoeff
open
  CRAlign
open
  CRProgra
open
  CPProven
open
  CFCollec
open
  CFCollec.DFTerm
open
  FCEnd
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
open
  RTProgra
open
  SEAlg

/--
A traced cutoff insertion, its provenance-certified retained-correction
program, and its pure adjacent-swap occurrence run.
-/
structure IOCert
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (source L : List (DFTerm M N K))
    (A : DFTerm M N K)
    (R corrections : List (DFTerm M N K))
    (x y : G) where
  program :
    RSPrograa
      (M := M) (N := N) (K := K) n leftWeight rightWeight
  correctionTrace_eq :
    program.correctionTrace = corrections
  crossings_generated :
    CGFroma source program
  rewrites :
    CORw
      (collapsedEvaluatedFactors x y L ++ [collapsedEvalAt x y A])
      (collapsedEvaluatedFactors x y R)

namespace IOCert

/--
The traced insertion recursion constructs its synchronized operational
certificate.  The correction program and rewrite run are both projections of
the same recursive insertion derivation.
-/
noncomputable def cutoffInsertsCorrections
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    {source L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {x y : G}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (hinsert :
      CICorrec
        n leftWeight rightWeight L A R corrections)
    (hL : ∀ term ∈ L, CGFrom source term)
    (hA : CGFrom source A) :
    IOCert
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        source L A R corrections x y :=
  let hexists :=
    schedule_inserts_corrections
      hinsert hL hA
  {
    program := Classical.choose hexists
    correctionTrace_eq := (Classical.choose_spec hexists).1
    crossings_generated := (Classical.choose_spec hexists).2
    rewrites :=
      DFTerm.CInsert.occurrenceRewrites
        hleftWeight hrightWeight hx hy hbot hinsert.cutoffInserts
  }

end IOCert

/--
A traced cutoff collection, its provenance-certified retained-correction
program, and its cutoff-aware occurrence run.
-/
structure COCert
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (L R corrections : List (DFTerm M N K))
    (x y : G) where
  program :
    RSPrograa
      (M := M) (N := N) (K := K) n leftWeight rightWeight
  correctionTrace_eq :
    program.correctionTrace = corrections
  crossings_generated :
    CGFroma L program
  rewrites :
    TORwa
      (collapsedEvaluatedFactors x y L)
      (collapsedEvaluatedFactors x y R)

namespace COCert

/--
The traced collection recursion constructs its synchronized operational
certificate.  Terminal source erasures remain visible in the cutoff-aware
rewrite relation.
-/
noncomputable def cutoff_retained_corrections
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    {L R corrections : List (DFTerm M N K)}
    {x y : G}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (hcollect :
      CCCorrec
        n leftWeight rightWeight L R corrections) :
    COCert
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        L R corrections x y :=
  let hexists :=
    schedule_collects_corrections
      hcollect
  {
    program := Classical.choose hexists
    correctionTrace_eq := (Classical.choose_spec hexists).1
    crossings_generated := (Classical.choose_spec hexists).2
    rewrites :=
      DFTerm.CCollec.truncatedOccurrenceRewrites
        hleftWeight hrightWeight hx hy hbot hcollect.cutoffCollects
  }

end COCert

/--
One selected natural endpoint with synchronized inverse-raw provenance,
retained-correction trace, and cutoff-aware endpoint occurrence run.
-/
structure EOCert
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
  correctionTrace_eq :
    program.correctionTrace =
      (endpointCorrectionInventory layer M N).corrections
  crossings_generated :
    CGFroma (inverseDecoratedTerms M N) program
  rewrites :
    TORwa
      (collapsedEvaluatedFactors x y (inverseDecoratedTerms M N))
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors)

namespace EOCert

/-- Select the synchronized endpoint certificate from the actual traced
cutoff-full collector derivation. -/
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
    EOCert
      layer M N x y :=
  let certificate :=
    COCert.cutoff_retained_corrections
      hleftWeight hrightWeight hx hy hbot
        (endpointCorrectionInventory layer M
          N).family_collects_corrections
  {
    program := certificate.program
    correctionTrace_eq := certificate.correctionTrace_eq
    crossings_generated := certificate.crossings_generated
    rewrites := certificate.rewrites
  }

/--
The synchronized endpoint program emits the selected concrete retained
correction root trace.
-/
lemma
    correction_erased_shape
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {x y : G}
    (certificate :
      EOCert
        layer M N x y) :
    (polynomialOrbitObstructions certificate.program).map
          (fun obstruction => obstruction.correction.erasedShape) =
      selectedErasedShape layer M N := by
  rw [
    RSPrograa.mapcor_erase_polyo,
    RSPrograa.trace_erased_shape,
    certificate.correctionTrace_eq]
  simp [erasedShapeTrace,
    selectedErasedShape,
    DFTerm.erased_shape_family]

/--
Adjoining the powered parents turns the synchronized endpoint occurrence run
into the concrete natural parent-pair collection run.
-/
lemma parent_endpoint_rewrites
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
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
        [y ^ N, x ^ M]) := by
  have hrawProd :
      (collapsedEvaluatedFactors x y
        (inverseDecoratedTerms M N)).prod =
          ⁅x ^ M, y ^ N⁆ := by
    calc
      (collapsedEvaluatedFactors x y
            (inverseDecoratedTerms M N)).prod =
          (collapsedEvaluatedFactors x y
            (layer.endpoint M N).factors).prod :=
        certificate.rewrites.list_prod_eq.symm
      _ = ⁅x ^ M, y ^ N⁆ := by
        simpa [collapsedEvaluatedFactors, collapsedList] using
          (layer.endpoint M N).collapsed_list_pow
            x y hleftWeight hrightWeight hx hy hbot
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

/-- At root weights in the free lower-central truncation, the synchronized
endpoint certificate is unconditional. -/
noncomputable def rootNaturalRecollection
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    EOCert
      layer M N x y :=
  natural_recollect_layer layer M N x y
    (by omega) (by omega) (by simp) (by simp)
      SCFactor.trunc_last_bot

/-- The synchronized root endpoint certificate supplies the concrete natural
parent-pair occurrence run without additional hypotheses. -/
lemma parentEndpointTrunc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {M N : ℕ}
    {x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n}
    (certificate :
      EOCert
        layer M N x y) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
        [y ^ N, x ^ M]) :=
  certificate.parent_endpoint_rewrites
    (by omega) (by omega) (by simp) (by simp)
      SCFactor.trunc_last_bot

end EOCert

end
  TOSync
end TCTex
end Towers

/-!
# Multiplicity profiles for concrete retained-correction orbit roots

The provenance-certified concrete endpoint schedule has an exact finite-index
trace of its retained polynomial-orbit obstruction roots.  Its orbit indices
need not agree with the earlier representatives chosen only up to erased Hall
shape.  Nevertheless, erasing the exact root indices recovers the literal
selected correction-shape trace.

This file packages that bridge for polynomial multiplicity profiles.  Exact
orbit-index profiles for the concrete root trace aggregate to erased-shape
profiles and then compile to the existing cutoff-full endpoint interface.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  CIMultip

open
  CRIndexa
open
  CRLayer
open
  ISFiber
open
  FIProf
open
  RITrace
open
  FIBridge
open
  MPAlg
open
  SEAlg

/--
The selected concrete correction-shape multiplicity is the filtered fiber of
the exact finite-index polynomial-orbit root trace.
-/
lemma count_erased_idx
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (selectedErasedShape layer M N).count word =
      ((endpointGeneratedConcrete
        layer hleftWeight hrightWeight M N).filter fun index =>
          decide
            ((retainedOrbitKey index).erasedShape =
              word)).length := by
  rw [←
    key_endpoint_generated
      layer hleftWeight hrightWeight M N]
  exact
    count_length_filter
      (fun index => (retainedOrbitKey index).erasedShape)
      word
      (endpointGeneratedConcrete
        layer hleftWeight hrightWeight M N)

/--
Homogeneous multiplicity profiles for the exact finite-index roots emitted by
the provenance-certified concrete endpoint schedule.
-/
abbrev EIMult
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :=
  IMProfa
    (fun M N =>
      endpointGeneratedConcrete
        layer hleftWeight hrightWeight M N)

namespace EIMult

/-- Bundle exact concrete-root profiles as a generic profiled finite-index trace. -/
noncomputable def profiledIndexFamily
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIMult
        layer hleftWeight hrightWeight) :
    PIFam n leftWeight rightWeight where
  trace :=
    fun M N =>
      endpointGeneratedConcrete
        layer hleftWeight hrightWeight M N
  kernel :=
    kernel

/--
Exact concrete-root orbit profiles aggregate to multiplicity profiles for the
literal selected correction-shape trace.
-/
noncomputable def erasedMultiplicityProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIMult
        layer hleftWeight hrightWeight) :
    EMProf
      (selectedErasedShape layer) :=
  (SEAlg.profiledErasedFamily
      kernel.profiledIndexFamily).kernel.of_trace_eq
    (fun M N =>
      key_endpoint_generated
        layer hleftWeight hrightWeight M N)

/--
Exact concrete-root orbit profiles compile to the existing correction
shape-fiber interface.
-/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIMult
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  kernel.erasedMultiplicityProfile
    |>.shapeFiberProfile
      hleftWeight hrightWeight

/--
Together with raw-source profiles, exact concrete-root orbit profiles compile
to the aggregate cutoff-full endpoint profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIMult
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  EIFiber.idx_fiber_profile
    raw kernel.shapeFiberProfile

end EIMult

/--
A recursively profiled finite-index family identified with the exact concrete
retained-correction orbit-root trace.
-/
structure EPDecomp
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  family :
    PIFam n leftWeight rightWeight
  trace_eq :
    ∀ M N,
      family.trace M N =
        endpointGeneratedConcrete
          layer hleftWeight hrightWeight M N

namespace EPDecomp

/-- Forget recursive packaging and retain exact concrete-root orbit profiles. -/
noncomputable def indexMultiplicityKernel
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      EPDecomp
        layer hleftWeight hrightWeight) :
    EIMult
      layer hleftWeight hrightWeight :=
  decomposition.family.kernel.of_trace_eq decomposition.trace_eq

/-- Compile a recursively profiled exact concrete-root trace to shape fibers. -/
noncomputable def shapeFiberProfile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      EPDecomp
        layer hleftWeight hrightWeight) :
    SFProf
      layer hleftWeight hrightWeight :=
  decomposition.indexMultiplicityKernel
    |>.shapeFiberProfile

/--
Together with raw-source profiles, compile a recursively profiled exact
concrete-root trace to the aggregate cutoff-full endpoint profile kernel.
-/
noncomputable def
    selectedFullFiber
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (decomposition :
      EPDecomp
        layer hleftWeight hrightWeight)
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight :=
  decomposition.indexMultiplicityKernel
    |>.selectedFullFiber raw

end EPDecomp

end CIMultip
end TCTex
end Towers

/-!
# Recursive polynomial-orbit packet support for concrete retained corrections

Every retained concrete endpoint crossing has parents causally generated from
the inverse-raw source.  Exact polynomial-orbit representatives for those
parents occur in correction-closure layers indexed by their weighted degrees.
The operational Hall recursion preserves that closure-layer bound for every
surviving descendant correction.

Consequently, the complete recipe-free recursive packet rooted at every
actual retained endpoint crossing is supported by the finite retained
polynomial-orbit vocabulary, not merely its leading correction root.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace CRSuppor

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
  OCPartit
open
  UCVocabu
open
  RIRecurs
open
  URVocabu

/--
Operational orbit packets rooted at arbitrary correction-closure recipes are
supported by the retained finite orbit vocabulary when both parents occur by
their weighted-degree closure layers.
-/
lemma poly_orbit_keys
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    (hleft :
      O.left ∈
        correctionClosure (sourceRecipes n leftWeight rightWeight)
          (weightedWordWeight leftWeight rightWeight O.left))
    (hright :
      O.right ∈
        correctionClosure (sourceRecipes n leftWeight rightWeight)
          (weightedWordWeight leftWeight rightWeight O.right))
    (hroot : O.weight leftWeight rightWeight < n) :
    retainedOrbitKeys (n := n) hleftWeight hrightWeight O ⊆
      retainedOrbitVocabulary n leftWeight rightWeight := by
  intro key hkey
  unfold retainedOrbitKeys at hkey
  rcases List.mem_map.mp hkey with ⟨recipe, hrecipe, rfl⟩
  apply
    key_vocabulary_recipes
  apply retained_correction_closure.mpr
  have hrecipeWeight :=
    retained_recipe_cutoff hroot hrecipe
  exact
    ⟨correction_closure
        (RObstru.correction_closure_recipes
          hleftWeight hrightWeight O hleft hright hrecipe)
        (Nat.le_of_lt hrecipeWeight),
      hrecipeWeight⟩

/--
The complete recursive recipe-free packet rooted at one retained concrete
endpoint crossing is supported by the finite orbit vocabulary.
-/
lemma supported_crossing_program
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
    IsSupported (n := n) hleftWeight hrightWeight
      (concreteCrossingObstruction crossing) := by
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
Every actual retained endpoint obstruction carries a fully supported
recipe-free recursive packet.
-/
lemma supported_schedule_program
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
    IsSupported (n := n) hleftWeight hrightWeight obstruction := by
  rcases List.mem_map.mp hobstruction with
    ⟨crossing, hcrossing, rfl⟩
  exact
    supported_crossing_program
      layer hleftWeight hrightWeight M N hcrossing

end CRSuppor
end TCTex
end Towers

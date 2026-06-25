import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary
import Towers.Group.Zassenhaus.CanonicalPacketAlignment

/-!
# Finite-index profiles for the operational cutoff-full occurrence schedule

The cutoff-full collector now has a literal occurrence-level rewrite run.
Separately, the initially retained inverse-raw occurrences and the retained
scheduler corrections have occurrence-preserving encodings in the same finite
polynomial-orbit alphabet.

This file appends those two index traces and proves that its erased-shape
fibers are exactly the concrete endpoint coordinates.  Thus the remaining
arbitrary-cutoff interpolation theorem can be stated as polynomial counting
for one explicit finite-alphabet trace attached to the operational collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  FIBridge

universe u

open HACoeff
open
  FFCard
open CRLayer
open
  NRCoordi
open
  NRSubinv
open
  ISFiber
open
  CRInv
open
  RHFiber
open
  FIProf
open
  CFAlg
open
  CFAlg.FPkt
open
  CFSubsti
open RFIndex
open OREnvelo
open
  FCAssign
open
  UCSuppor
open
  RITrace
open
  IEDecomp
open
  PCBridge

/--
The occurrence-preserving finite-index trace attached to one selected
cutoff-full endpoint: initially retained inverse-raw occurrences followed by
the actual scheduler corrections that survive the cutoff.
-/
noncomputable def selectedFullEndpoint
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  universalIndexTrace
      M N n leftWeight rightWeight hleftWeight hrightWeight ++
    selectedIndexTrace
      layer M N hleftWeight hrightWeight

/--
Decoding the selected endpoint trace preserves every source and correction
occurrence in the inherited packet order.
-/
lemma key_selected_full
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (selectedFullEndpoint
      layer M N hleftWeight hrightWeight).map retainedOrbitKey =
        universalOrbitPacket
            M N n leftWeight rightWeight hleftWeight hrightWeight ++
          (selectedClosurePacket
            layer M N hleftWeight hrightWeight).map
              ROAggreg.polynomialOrbitKey := by
  rw [selectedFullEndpoint, List.map_append,
    key_universal_trace,
    key_selected_trace]

/--
Filtering the selected endpoint trace by erased Hall shape counts exactly the
corresponding concrete cutoff-full endpoint fiber.
-/
lemma
    filter_key_mult
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom) :
    ((selectedFullEndpoint
      layer M N hleftWeight hrightWeight).filter fun index =>
        decide ((retainedOrbitKey index).erasedShape = word)).length =
      endpointRecipeMultiplicity layer M N word := by
  rw [selectedFullEndpoint, List.filter_append,
    List.length_append,
    filter_key_histories,
    key_selected_corrections,
    endpoint_filter_corrections]
  congr 1
  simpa only [DFTerm.erased_shape_family] using
    (length_collapse_histories
      M N n leftWeight rightWeight word).symm

/--
The complete fixed-slot natural coordinate vector is the ordered vocabulary
mapped through filtered fibers of the selected endpoint index trace.
-/
lemma natural_slot_mult
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ) :
    naturalSlotVector layer hleftWeight hrightWeight M N =
      (orderedErasedVocabulary n leftWeight rightWeight).map fun word =>
        ((selectedFullEndpoint
          layer M N hleftWeight hrightWeight).filter fun index =>
            decide
              ((retainedOrbitKey index).erasedShape =
                word)).length := by
  rw [natural_slot_shape]
  apply List.map_congr_left
  intro word _hword
  exact
    (filter_key_mult
      layer M N hleftWeight hrightWeight word).symm

/--
The aggregate finite-alphabet polynomial-counting obligation for one
cutoff-full natural recollection layer.
-/
structure EIFiber
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  profiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  profiles_nat_trace :
    ∀ (M N : ℕ) word hword,
      (profiles word hword).value (M : ℤ) (N : ℤ) =
        (((selectedFullEndpoint
          layer M N hleftWeight hrightWeight).filter fun index =>
            decide
              ((retainedOrbitKey index).erasedShape =
                word)).length : ℤ)

namespace EIFiber

/--
Finite-index source and scheduler-correction profile kernels add to the
aggregate profile kernel for the appended endpoint trace.
-/
def idx_fiber_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (corrections :
      SFProf
        layer hleftWeight hrightWeight) :
    EIFiber
      layer hleftWeight hrightWeight where
  profiles word hword :=
    FPkt.add
      (raw.profiles word hword)
      (corrections.profiles word hword)
  profiles_nat_trace M N word hword := by
    rw [FPkt.value_add,
      raw.profiles_cast_trace M N word hword,
      corrections.profiles_nat_trace M N word hword,
      selectedFullEndpoint, List.filter_append,
      List.length_append, Int.natCast_add]

/-- Forget the aggregate trace presentation and retain its homogeneous
word-local assignment. -/
def signedProfileAssignment
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight) :
    SPAssign n leftWeight rightWeight where
  profiles :=
    kernel.profiles

/--
Aggregate finite-index trace counting proves the scalar endpoint-fiber
obligation consumed by fixed-slot interpolation.
-/
lemma counts_fibers_assignment
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight) :
    kernel.signedProfileAssignment
      |>.CountsFibersCast layer := by
  intro M N word hword
  change
    (kernel.profiles word
      (ordered_erased_vocabulary.mp hword)).value (M : ℤ) (N : ℤ) =
        (endpointRecipeMultiplicity layer M N word : ℤ)
  rw [kernel.profiles_nat_trace M N word
    (ordered_erased_vocabulary.mp hword)]
  exact congrArg (fun multiplicity : ℕ => (multiplicity : ℤ))
    (filter_key_mult
      layer M N hleftWeight hrightWeight word)

/--
Aggregate finite-index trace counting supplies the endpoint shape-fiber
interpolation package directly.
-/
noncomputable def fiberProfileInterpolation
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      EIFiber
        layer hleftWeight hrightWeight) :=
  kernel.signedProfileAssignment
    |>.fiberProfileInterpolation
      kernel.counts_fibers_assignment

end EIFiber

namespace NRLayer

/--
At root weights in the free lower-central truncation, one selected natural
endpoint simultaneously carries its literal cutoff-aware occurrence run and
its exact finite-index fixed-slot coordinate vector.
-/
lemma endpoint_occ_rewrites
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    TORwa
        (collapsedEvaluatedFactors x y
          (inverseDecoratedTerms M N))
        (collapsedEvaluatedFactors x y (layer.endpoint M N).factors) ∧
      naturalSlotVector layer (by simp) (by simp) M N =
        (orderedErasedVocabulary n 1 1).map fun word =>
          ((selectedFullEndpoint
            layer M N (by simp) (by simp)).filter fun index =>
              decide
                ((retainedOrbitKey index).erasedShape =
                  word)).length := by
  exact
    ⟨PCBridge.NRLayer.endpointOccRewrites
        layer M N x y,
      natural_slot_mult
        layer (by simp) (by simp) M N⟩

end NRLayer

end
  FIBridge
end TCTex
end Towers

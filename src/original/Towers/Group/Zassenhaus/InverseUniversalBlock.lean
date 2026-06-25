import Towers.Group.Zassenhaus.SignedProfilePackets
import Towers.Group.Zassenhaus.TruncatedRecipeInventories

/-!
# Ordered cutoff boundary for universal signed-block packets

The finite universal erased-word skeleton is a support universe, not by
itself a noncommutative collection schedule.  A cutoff packet must therefore
retain an explicit ordered list of signed-profile occurrences.  Repeated
words are allowed, while every occurrence is certified to belong to the
finite universal skeleton.

This file packages the exact cutoff-specific stabilization boundary consumed
by the natural Hall-Petresco packet interface.
-/

namespace Towers
namespace TCTex
namespace USOrdere

universe u

open scoped commutatorElement

open CSAggreg
open CFSubsti
open CCTrunc
open UNPkt
open UWSkelet

/--
One multiplicity-independent ordered signed-profile packet supported on the
finite universal erased-word skeleton.
-/
structure OBPkt
    (n leftWeight rightWeight : ℕ) where
  leftWeight_pos :
    0 < leftWeight
  rightWeight_pos :
    0 < rightWeight
  packets :
    List RFPkt
  word_erased_vocabulary :
    ∀ packet ∈ packets,
      packet.word ∈
        erasedShapeVocabulary n leftWeight rightWeight
          leftWeight_pos rightWeight_pos

namespace OBPkt

/-- Every packet occurrence in an ordered supported packet lies below cutoff. -/
lemma packet_weight_cutoff
    {n leftWeight rightWeight : ℕ}
    (packet : OBPkt n leftWeight rightWeight)
    {nextPacket : RFPkt}
    (hnextPacket : nextPacket ∈ packet.packets) :
    packetWeight leftWeight rightWeight nextPacket < n := by
  simpa [packetWeight] using
    erased_shape_vocabulary
      (packet.word_erased_vocabulary nextPacket hnextPacket)

/-- Supported ordered cutoff packets are fixed points of semantic truncation. -/
@[simp]
lemma truncate_packets
    {n leftWeight rightWeight : ℕ}
    (packet : OBPkt n leftWeight rightWeight) :
    truncate n leftWeight rightWeight packet.packets =
      packet.packets := by
  apply List.filter_eq_self.2
  intro nextPacket hnextPacket
  simpa only [decide_eq_true_eq] using
    packet.packet_weight_cutoff hnextPacket

end OBPkt

/--
An ordered cutoff packet together with the remaining finite stabilization
law against every multiplicity-dependent concrete operational packet.
-/
structure SBPkt
    (kernel : OCShape)
    (d n leftWeight rightWeight : ℕ)
    extends OBPkt n leftWeight rightWeight where
  packet_prod_concrete :
    ∀ (M N : ℕ)
      (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
      left ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (leftWeight - 1) →
        right ∈ Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (rightWeight - 1) →
          (packets.map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value (M : ℤ) (N : ℤ)).prod =
            ((truncatedConcretePackets kernel n leftWeight rightWeight M N).map
              fun packet =>
                packet.word.eval (HPAtom.eval left right) ^
                  packet.profiles.value (M : ℤ) (N : ℤ)).prod

namespace SBPkt

/-- Forget finite support while retaining the cutoff-specific stabilization
law consumed by the semantic truncation bridge. -/
def truncatedNaturalStabilization
    {kernel : OCShape}
    {d n leftWeight rightWeight : ℕ}
    (packet :
      SBPkt.{u}
        kernel d n leftWeight rightWeight) :
    TNStab.{u}
      kernel d n leftWeight rightWeight packet.packets where
  leftWeight_pos := packet.leftWeight_pos
  rightWeight_pos := packet.rightWeight_pos
  packet_prod_concrete := packet.packet_prod_concrete

/-- At root weights, an ordered stabilized cutoff packet is exactly the
natural Hall-Petresco packet needed by subsequent signed lifting. -/
def truncNaturalPacket
    {kernel : OCShape}
    {d n : ℕ}
    (packet :
      SBPkt.{u}
        kernel d n 1 1) :
    TBPkt.{u} d n :=
  packet.truncatedNaturalStabilization
    |>.truncNaturalPacket

@[simp]
lemma packetsTruncNatural
    {kernel : OCShape}
    {d n : ℕ}
    (packet :
      SBPkt.{u}
        kernel d n 1 1) :
    packet.truncNaturalPacket.packets =
      packet.packets :=
  rfl

end SBPkt

end USOrdere
end TCTex
end Towers

/-!
# Universal support for truncated concrete signed-block packets

To construct one finite cutoff schedule, it is enough to prove vocabulary
coverage term by term for the surviving factors of every operational
endpoint.  Maximal same-shape compression then transfers that support to
signed recollection packets automa, without changing their order.
-/

namespace Towers
namespace TCTex
namespace UCSuppora

open HACoeff
open FMEnd
open CSAdmiss
open CSAggreg
open CCPkt
open CSSpec
open CCTrunc
open CFSubsti
open URVocabu
open UWSkelet
open USOrdere
open OCAdmiss

/--
The remaining finite-support coverage law at the concrete operational layer:
every endpoint term below cutoff has an erased-shape representative in the
finite universal recipe vocabulary.
-/
structure OUCovera
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  exists_recipe :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (term : DFTerm M N
        (inverseLabelledCollection M N).factors.length),
      term ∈ endpoint.collected.factors →
        term.erasedShape.weight
            (HPAtom.weight leftWeight rightWeight) < n →
          ∃ recipe ∈
              recipes n leftWeight rightWeight hleftWeight hrightWeight,
            recipe.erasedShape = term.erasedShape

namespace OUCovera

/-- Coverage of endpoint terms transfers to the common word of one maximal
same-shape block. -/
lemma shape_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (coverage :
      OUCovera
        n leftWeight rightWeight hleftWeight hrightWeight)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors)
    (hweight :
      (shapeOfMem endpoint block hblock).weight
          (HPAtom.weight leftWeight rightWeight) < n) :
    shapeOfMem endpoint block hblock ∈
      erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight := by
  let term :=
    block.head (nil_same_blocks endpoint block hblock)
  have hterm_block :
      term ∈ block :=
    List.head_mem (nil_same_blocks endpoint block hblock)
  have hterm_factors :
      term ∈ endpoint.collected.factors := by
    rw [← flatten_same_blocks endpoint.collected.factors]
    exact List.mem_flatten.mpr ⟨block, hblock, hterm_block⟩
  rcases coverage.exists_recipe endpoint term hterm_factors
      (by
        rwa [erased_shape endpoint block hblock term hterm_block]) with
    ⟨recipe, hrecipe, hshape⟩
  rw [← erased_shape endpoint block hblock term hterm_block,
    ← hshape]
  exact shape_vocabulary_recipes hrecipe

end OUCovera

@[simp]
lemma word_packet
    (certificateKernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    (packetOfMem certificateKernel endpoint block hblock).word =
      shapeOfMem endpoint block hblock :=
  rfl

/-- Every below-cutoff packet produced from an ordered maximal-block list is
supported on the finite universal erased-word skeleton. -/
lemma vocabulary_packets_blocks
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (coverage :
      OUCovera
        n leftWeight rightWeight hleftWeight hrightWeight)
    (certificateKernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ∀ (blocks : List (List (DFTerm M N
          (inverseLabelledCollection M N).factors.length)))
      (hblocks : ∀ block ∈ blocks,
        block ∈ sameErasedBlocks endpoint.collected.factors)
      {packet : RFPkt},
      packet ∈ packetsOfBlocks certificateKernel endpoint blocks hblocks →
        packetWeight leftWeight rightWeight packet < n →
          packet.word ∈
            erasedShapeVocabulary n leftWeight rightWeight
              hleftWeight hrightWeight
  | [], _hblocks, packet, hpacket, _hweight => by
      simp [packetsOfBlocks.eq_def] at hpacket
  | block :: blocks, hblocks, packet, hpacket, hweight => by
      rw [packetsOfBlocks.eq_def] at hpacket
      rcases List.mem_cons.mp hpacket with hpacket | hpacket
      · subst packet
        apply coverage.shape_erased_vocabulary endpoint block
          (hblocks block (by simp))
        rw [← word_packet certificateKernel endpoint block
          (hblocks block (by simp))]
        exact hweight
      · exact
          vocabulary_packets_blocks
            coverage certificateKernel endpoint blocks
              (fun next hnext => hblocks next (by simp [hnext]))
              hpacket hweight

/-- Every below-cutoff packet in the canonically chosen concrete endpoint is
supported on the finite universal erased-word skeleton. -/
lemma vocabulary_concrete_packets
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (coverage :
      OUCovera
        n leftWeight rightWeight hleftWeight hrightWeight)
    (certificateKernel : OCShape)
    {M N : ℕ}
    {packet : RFPkt}
    (hpacket : packet ∈ concretePackets certificateKernel M N)
    (hweight : packetWeight leftWeight rightWeight packet < n) :
    packet.word ∈
      erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight := by
  exact
    vocabulary_packets_blocks
      coverage certificateKernel (endpoint M N)
        (sameErasedBlocks (endpoint M N).collected.factors)
        (fun _block hblock => hblock) hpacket hweight

/-- Each local truncated concrete packet is already an ordered finite
vocabulary-supported cutoff packet. -/
noncomputable def orderedBlockConcrete
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (coverage :
      OUCovera
        n leftWeight rightWeight hleftWeight hrightWeight)
    (certificateKernel : OCShape)
    (M N : ℕ) :
    OBPkt n leftWeight rightWeight where
  leftWeight_pos := hleftWeight
  rightWeight_pos := hrightWeight
  packets :=
    truncatedConcretePackets
      certificateKernel n leftWeight rightWeight M N
  word_erased_vocabulary packet hpacket := by
    have hpacket' :
        packet ∈
          truncate n leftWeight rightWeight
            (concretePackets certificateKernel M N) := by
      simpa [truncatedConcretePackets] using hpacket
    apply vocabulary_concrete_packets
      coverage certificateKernel
    · exact (List.mem_filter.mp hpacket').1
    · exact packet_weight_truncate hpacket'

end UCSuppora
end TCTex
end Towers

/-!
# Source and emitted-correction support for concrete signed-block packets

Raw endpoint factors are covered outright by the cutoff-sized dummy source
vocabulary.  Consequently, universal support for every endpoint factor
reduces to the narrower problem of covering emitted operational corrections.
-/

namespace Towers
namespace TCTex
namespace USSuppor

open HACoeff
open FMEnd
open CSAggreg
open RHRecipe
open HHTrunc
open RRVocabu
open URVocabu
open UCSuppora
open USOrdere

/-- Every below-cutoff indexed raw source term has a representative in the
finite universal source vocabulary. -/
lemma raw_decorated_terms
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ inverseDecoratedTerms M N)
    (hweight :
      term.erasedShape.weight
          (HPAtom.weight leftWeight rightWeight) < n) :
    ∃ recipe ∈ sourceRecipes n leftWeight rightWeight,
      recipe.erasedShape = term.erasedShape := by
  rcases history_decorated_terms hterm with
    ⟨history, hhistory, hword⟩
  have hhistoryWeight :
      RHistor.weight leftWeight rightWeight history < n := by
    simpa [RHistor.weight, hword, DFTerm.erasedShape,
      DTerm.erasedShape] using hweight
  rcases equivalent_initial_recipes
      hleftWeight hrightWeight history hhistory hhistoryWeight with
    ⟨recipe, hrecipe, hequivalent⟩
  refine ⟨recipe.blockRecipe, List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩, ?_⟩
  simpa [IRecipe.blockRecipe, BRecipe.erased_shape_linear,
    LRecipe.erasedShape, LRecipe.ofLabelLinear,
    RRVocabu.RHistor.initialRecipe,
    DFTerm.erasedShape, DTerm.erasedShape, hword] using
      hequivalent.2.2

/--
The remaining support law after raw terms have been discharged: every
below-cutoff correction emitted by an operational endpoint has a
representative in the finite universal correction vocabulary.
-/
structure OECovera
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  exists_recipe :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (term : DFTerm M N
        (inverseLabelledCollection M N).factors.length),
      term ∈ endpoint.corrections →
        term.erasedShape.weight
            (HPAtom.weight leftWeight rightWeight) < n →
          ∃ recipe ∈
              operationalCorrectionRecipes
                n leftWeight rightWeight hleftWeight hrightWeight,
            recipe.erasedShape = term.erasedShape

namespace OECovera

/-- Raw coverage plus emitted-correction coverage covers every factor of the
operational endpoint. -/
def operationalUniversalCoverage
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (coverage :
      OECovera
        n leftWeight rightWeight hleftWeight hrightWeight) :
    OUCovera
      n leftWeight rightWeight hleftWeight hrightWeight where
  exists_recipe endpoint term hterm hweight := by
    have hterm' :
        term ∈
          inverseDecoratedTerms _ _ ++ endpoint.corrections :=
      endpoint.perm_append_corrections.subset hterm
    rcases List.mem_append.mp hterm' with hraw | hcorrection
    · rcases raw_decorated_terms
          hleftWeight hrightWeight hraw hweight with
        ⟨recipe, hrecipe, hshape⟩
      exact ⟨recipe, List.mem_append_left _ hrecipe, hshape⟩
    · rcases coverage.exists_recipe endpoint term hcorrection hweight with
        ⟨recipe, hrecipe, hshape⟩
      exact ⟨recipe, List.mem_append_right _ hrecipe, hshape⟩

/-- Emitted-correction coverage is sufficient to package every local
truncated concrete packet as an ordered vocabulary-supported cutoff packet. -/
noncomputable def orderedPacketConcrete
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (coverage :
      OECovera
        n leftWeight rightWeight hleftWeight hrightWeight)
    (certificateKernel : OCShape)
    (M N : ℕ) :
    OBPkt n leftWeight rightWeight :=
  orderedBlockConcrete hleftWeight hrightWeight
    coverage.operationalUniversalCoverage
      certificateKernel M N

end OECovera

end USSuppor
end TCTex
end Towers

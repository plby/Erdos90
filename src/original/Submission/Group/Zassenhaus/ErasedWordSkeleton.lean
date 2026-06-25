import Submission.Group.Zassenhaus.CompatiblePacketRouting
import Submission.Group.Zassenhaus.Inverse

/-!
# Universal erased-word skeleton for signed Hall-Petresco packets

The cutoff recipe vocabulary is a finite universe of positive block recipes,
not an ordered collection schedule.  Its deduplicated erased shapes form a
canonical finite word skeleton.  A global support-pattern argument only needs
to attach one homogeneous signed-profile coefficient packet to each word in
that skeleton and prove the resulting ordered product identity.

This file packages that reduction independently of the existing collection
proof.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UWSkelet

universe v

open scoped commutatorElement

open HACoeff
open BRSpec
open URVocabu
open CFSubsti
open CFExp

/--
Canonical finite ordered skeleton of erased Hall words supplied by the
universal cutoff recipe vocabulary.
-/
noncomputable def erasedShapeVocabulary
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (CWord HPAtom) :=
  ((recipes n leftWeight rightWeight hleftWeight hrightWeight).map
    BRecipe.erasedShape).dedup

/-- Every recipe in the universal vocabulary contributes its erased shape. -/
lemma shape_vocabulary_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ recipes n leftWeight rightWeight hleftWeight hrightWeight) :
    recipe.erasedShape ∈
      erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight := by
  classical
  rw [erasedShapeVocabulary, List.mem_dedup]
  exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩

/-- Every word in the skeleton has a positive recipe representative. -/
lemma recipe_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {word : CWord HPAtom}
    (hword :
      word ∈ erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight) :
    ∃ recipe ∈ recipes n leftWeight rightWeight hleftWeight hrightWeight,
      recipe.erasedShape = word := by
  classical
  rw [erasedShapeVocabulary, List.mem_dedup] at hword
  exact List.mem_map.mp hword

/-- Every erased word in the canonical skeleton has positive Hall-pair bidegree. -/
lemma bidegree_positive_vocabulary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {word : CWord HPAtom}
    (hword :
      word ∈ erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight) :
    word.PBPos := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, _hrecipe, rfl⟩
  exact recipe.positive

/-- Every erased word in the canonical skeleton remains below the cutoff. -/
lemma weighted_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {word : CWord HPAtom}
    (hword :
      word ∈ erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight) :
    word.pairLeftDegree * leftWeight +
        word.pairRightDegree * rightWeight < n := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, rfl⟩
  simpa only [weighted_word_weight, recipe.erased_left_degree,
    recipe.erased_shape_degree] using
      weighted_word_recipes hrecipe

/-- Ordinary weighted Hall degree of every skeleton word remains below cutoff. -/
lemma erased_shape_vocabulary
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {word : CWord HPAtom}
    (hword :
      word ∈ erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight) :
    word.weight (HPAtom.weight leftWeight rightWeight) < n := by
  rw [CWord.pair_atom_degree]
  exact weighted_erased_vocabulary hword

/--
Multiplicity-independent signed-profile coefficients attached to every word
in the canonical cutoff skeleton.
-/
structure SPAssign
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  profiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree

namespace SPAssign

/-- Attach each assigned profile coefficient to its canonical skeleton word. -/
noncomputable def toPackets
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight
        hleftWeight hrightWeight) :
    List RFPkt :=
  (erasedShapeVocabulary n leftWeight rightWeight
      hleftWeight hrightWeight).attach.map fun word =>
    {
      word := word.1
      positive :=
        bidegree_positive_vocabulary word.2
      profiles := assignment.profiles word.1 word.2
    }

/-- Forgetting assigned profiles recovers the canonical erased-word skeleton. -/
@[simp]
lemma word_packets
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight
        hleftWeight hrightWeight) :
    assignment.toPackets.map RFPkt.word =
      erasedShapeVocabulary n leftWeight rightWeight
        hleftWeight hrightWeight := by
  classical
  simp [toPackets]

/-- Every attached packet word lies below the cutoff. -/
lemma weight_cutoff_packets
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      SPAssign n leftWeight rightWeight
        hleftWeight hrightWeight)
    {packet : RFPkt}
    (hpacket : packet ∈ assignment.toPackets) :
    packet.word.weight (HPAtom.weight leftWeight rightWeight) < n := by
  have hword :
      packet.word ∈
        erasedShapeVocabulary n leftWeight rightWeight
          hleftWeight hrightWeight := by
    rw [← assignment.word_packets]
    exact List.mem_map.mpr ⟨packet, hpacket, rfl⟩
  exact erased_shape_vocabulary hword

end SPAssign

/--
A semantic identity for one canonical signed-profile assignment is exactly
the universal all-integral packet needed by symbolic recollection.
-/
structure UPAssign
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    extends SPAssign n leftWeight rightWeight
      hleftWeight hrightWeight where
  listEval_eq :
    ∀ {G : Type v} [Group G]
      (left right : G)
      (leftExponent rightExponent : ℤ),
        (toSPAssign.toPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace UPAssign

/--
Canonical profile assignments with the universal product law compile to the
global signed packet consumed by the correction factory.
-/
noncomputable def universalAllPacket
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{v}
        n leftWeight rightWeight hleftWeight hrightWeight) :
    UAPkt.{v} where
  packets := assignment.toSPAssign.toPackets
  listEval_eq := assignment.listEval_eq

end UPAssign

end UWSkelet
end TCTex
end Submission

/-!
# Operational boundary for universal signed-block profile assignments

A universal signed-block profile assignment is already the semantic heart of
the Hall-Petresco collector: it attaches one homogeneous integral coefficient
packet to every word in the finite cutoff skeleton and proves their ordered
product law in every group.

This file exposes the direct constructor path from that assignment to the
operational normalization packet, its cutoff integral lift, and the symbolic
correction factory.  It also transports the skeleton cutoff bound through the
constructed packets.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UWSkelet

universe u v

open HACoeff
open CSNorm
open CFSubsti
open CFExp
open UNPkt

namespace UPAssign

/--
The universal product law automa agrees with every operational
compatible collection kernel at natural source multiplicities.
-/
noncomputable def uniformPacketNormalization
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{v}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern) :
    UPNorm.{v} kernel
      assignment.toSPAssign.toPackets :=
  uniformNormalizationUniversal
    assignment.universalAllPacket kernel

/--
Operational normalization specializes a universal profile assignment to one
natural packet in a free lower-central truncation.
-/
noncomputable def truncNaturalPacket
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (d truncation : ℕ) :
    TBPkt.{u} d truncation :=
  (assignment.uniformPacketNormalization kernel)
    |>.truncNaturalPacket d truncation

/--
The same universal product law supplies the integral extension of the
operationally constructed natural packet.
-/
noncomputable def allIntegralLift
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (d truncation : ℕ) :
    (assignment.truncNaturalPacket
      kernel d truncation).AILift where
  listEval_eq := assignment.listEval_eq

/--
Forget the intermediate natural specialization and expose the cutoff packet
consumed by signed-profile substitution.
-/
noncomputable def truncatedAllIntegral
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (d truncation : ℕ) :
    TAInt.{u} d truncation :=
  (assignment.allIntegralLift kernel d truncation)
    |>.truncatedAllIntegral

/--
Compile a universal profile assignment directly into one arbitrary-parent
symbolic Hall polynomial correction expansion.
-/
noncomputable def toCorrectionExpansion
    {n leftWeight rightWeight d truncation : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (normalizer :
      WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    SCExp (n := truncation) left right :=
  (assignment.truncatedAllIntegral
      kernel d truncation)
    |>.toCorrectionExpansion normalizer left right

/--
Compile a universal profile assignment into the correction factory used for
every supported symbolic word at one cutoff.
-/
noncomputable def supportedWordFactory
    {n leftWeight rightWeight d truncation : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (lowerWeight : ℕ) :
    SSFtrya
      (n := truncation) H lowerWeight :=
  (assignment.truncatedAllIntegral
      kernel d truncation)
    |>.supportedWordFactory normalizers lowerWeight

@[simp]
lemma packetsTruncNatural
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (d truncation : ℕ) :
    (assignment.truncNaturalPacket
      kernel d truncation).packets =
        assignment.toSPAssign.toPackets :=
  rfl

/-- Every operationally constructed packet word remains below the skeleton cutoff. -/
lemma truncated_natural_packet
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (d truncation : ℕ)
    {packet : RFPkt}
    (hpacket :
      packet ∈
        (assignment.truncNaturalPacket
          kernel d truncation).packets) :
    packet.word.weight (HPAtom.weight leftWeight rightWeight) < n := by
  exact
    assignment.toSPAssign.weight_cutoff_packets
      hpacket

@[simp]
lemma packets_truncated_all
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (d truncation : ℕ) :
    (assignment.truncatedAllIntegral
      kernel d truncation).packets =
        assignment.toSPAssign.toPackets :=
  rfl

/-- The integral substitution packet preserves the same finite cutoff support. -/
lemma all_integral_packet
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (kernel : OCKern)
    (d truncation : ℕ)
    {packet : RFPkt}
    (hpacket :
      packet ∈
        (assignment.truncatedAllIntegral
          kernel d truncation).packets) :
    packet.word.weight (HPAtom.weight leftWeight rightWeight) < n := by
  exact
    assignment.toSPAssign.weight_cutoff_packets
      hpacket

end UPAssign
end UWSkelet
end TCTex
end Submission

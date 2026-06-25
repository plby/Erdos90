import Submission.Group.Zassenhaus.InverseUniversalBlock
import Submission.Group.Zassenhaus.CompatiblePacketRouting
import Submission.Group.Zassenhaus.CompletePetrescoRecipe
import Submission.Group.Zassenhaus.SignedProfilePackets
import Submission.Group.Zassenhaus.Polynomial

/-!
# Finite correction-closure vocabulary for inverse collection

The pair-packet vocabulary is tailored to one operational recollection rooted
at a pair of raw histories.  A later More3 trace may interchange recursively
generated parents, so causal correction closure alone does not justify direct
membership in that narrower vocabulary.

This file constructs a conservative finite replacement.  Starting from the
cutoff-sized universal source vocabulary, it closes under pairwise recipe
correction for finitely many rounds and then discards recipes at or above the
nilpotent cutoff.  Every below-cutoff correction causally generated from the
inverse raw endpoint has an erased-shape representative in this finite list.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCVocabu

open HACoeff
open BRSpec
open CCAggreg
open OCClos
open OCPartit
open FMEnd
open URVocabu
open USSuppor

/-- All pairwise recipe corrections drawn from one finite recipe list. -/
def pairwiseCorrections
    (recipes : List BRecipe) :
    List BRecipe :=
  recipes.flatMap fun left =>
    recipes.map fun right =>
      left.correction right

/--
Finite iterated pairwise correction closure.  The depth-zero layer is the
source list; each successor layer retains older recipes and adds every
pairwise correction of recipes already constructed.
-/
def correctionClosure
    (source : List BRecipe) :
    ℕ → List BRecipe
  | 0 =>
      source
  | depth + 1 =>
      correctionClosure source depth ++
        pairwiseCorrections (correctionClosure source depth)

/-- Every recipe remains present after one additional closure round. -/
lemma correction_closure_succ
    {source : List BRecipe}
    {depth : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosure source depth) :
    recipe ∈ correctionClosure source (depth + 1) := by
  exact List.mem_append_left _ hrecipe

/-- Closure layers are monotone in their finite depth bound. -/
lemma correction_closure
    {source : List BRecipe}
    {lower upper : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosure source lower)
    (hdepth : lower ≤ upper) :
    recipe ∈ correctionClosure source upper := by
  induction hdepth with
  | refl =>
      exact hrecipe
  | @step upper _ ih =>
      exact correction_closure_succ ih

/-- Correcting two recipes from one layer produces a recipe in the next. -/
lemma closure_succ
    {source : List BRecipe}
    {depth : ℕ}
    {left right : BRecipe}
    (hleft : left ∈ correctionClosure source depth)
    (hright : right ∈ correctionClosure source depth) :
    left.correction right ∈ correctionClosure source (depth + 1) := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr
    ⟨left, hleft, List.mem_map.mpr ⟨right, hright, rfl⟩⟩

/--
Recipes constructed at different depths can be corrected after lifting both
parents to their common maximum layer.
-/
lemma correction_mem_closure
    {source : List BRecipe}
    {leftDepth rightDepth : ℕ}
    {left right : BRecipe}
    (hleft : left ∈ correctionClosure source leftDepth)
    (hright : right ∈ correctionClosure source rightDepth) :
    left.correction right ∈
      correctionClosure source (max leftDepth rightDepth + 1) := by
  apply closure_succ
  · exact correction_closure hleft
      (Nat.le_max_left _ _)
  · exact correction_closure hright
      (Nat.le_max_right _ _)

/--
Any below-cutoff concrete correction tree has a recipe representative in the
finite layer indexed by its weighted Hall degree, provided its source leaves
have representatives in the chosen source vocabulary.
-/
lemma recipe_generated_weight
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {source : List (DFTerm M N K)}
    {sourceRecipes : List BRecipe}
    (hsource :
      ∀ sourceTerm ∈ source,
        decoratedFamilyWeight leftWeight rightWeight sourceTerm < n →
          ∃ recipe ∈ sourceRecipes,
            recipe.erasedShape = sourceTerm.erasedShape)
    {term : DFTerm M N K}
    (hterm : DFTerm.CGFrom source term) :
    decoratedFamilyWeight leftWeight rightWeight term < n →
      ∃ recipe ∈
          correctionClosure sourceRecipes
            (decoratedFamilyWeight leftWeight rightWeight term),
        recipe.erasedShape = term.erasedShape := by
  induction hterm with
  | source hterm =>
      intro hweight
      rcases hsource _ hterm hweight with ⟨recipe, hrecipe, hshape⟩
      exact
        ⟨recipe,
          correction_closure
            (show recipe ∈ correctionClosure sourceRecipes 0 by
              exact hrecipe)
            (Nat.zero_le _),
          hshape⟩
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
        ⟨leftRecipe, hleftRecipe, hleftShape⟩
      rcases ihright hrightCutoff with
        ⟨rightRecipe, hrightRecipe, hrightShape⟩
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
      · rw [BRecipe.erasedShape_corr, hleftShape, hrightShape,
          DFTerm.erasedShape_corr]

/--
Finite universal correction-closure vocabulary retained strictly below the
nilpotent cutoff.
-/
noncomputable def correctionClosureRecipes
    (n leftWeight rightWeight : ℕ) :
    List BRecipe :=
  (correctionClosure (sourceRecipes n leftWeight rightWeight) n).filter
    fun recipe =>
      decide (weightedWordWeight leftWeight rightWeight recipe < n)

@[simp]
lemma retained_correction_closure
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe} :
    recipe ∈ correctionClosureRecipes n leftWeight rightWeight ↔
      recipe ∈ correctionClosure (sourceRecipes n leftWeight rightWeight) n ∧
        weightedWordWeight leftWeight rightWeight recipe < n := by
  simp [correctionClosureRecipes]

/-- Every recipe retained in the finite closure remains below the cutoff. -/
lemma weighted_closure_recipes
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight) :
    weightedWordWeight leftWeight rightWeight recipe < n :=
  (retained_correction_closure.mp hrecipe).2

/--
Every below-cutoff correction emitted by the genuine operational endpoint has
an erased-shape representative in the finite correction closure.
-/
lemma endpoint_corrections
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm : term ∈ endpoint.corrections)
    (hweight :
      term.erasedShape.weight
          (HPAtom.weight leftWeight rightWeight) < n) :
    ∃ recipe ∈
        correctionClosureRecipes n leftWeight rightWeight,
      recipe.erasedShape = term.erasedShape := by
  have htermWeight :
      decoratedFamilyWeight leftWeight rightWeight term < n := by
    simpa [decoratedFamilyWeight, weightedWordWeight,
      term.erased_shape_family] using hweight
  have hgenerated :
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) term :=
    FCollec.ECorrec.correctionGeneratedFrom
      endpoint.emits term hterm
  rcases
      recipe_generated_weight
        hleftWeight hrightWeight
        (sourceRecipes := sourceRecipes n leftWeight rightWeight)
        (fun sourceTerm hsourceTerm hsourceWeight => by
          apply raw_decorated_terms
            hleftWeight hrightWeight hsourceTerm
          simpa [decoratedFamilyWeight, weightedWordWeight,
            sourceTerm.erased_shape_family] using hsourceWeight)
        hgenerated htermWeight with
    ⟨recipe, hrecipe, hshape⟩
  refine ⟨recipe, retained_correction_closure.mpr ⟨?_, ?_⟩, hshape⟩
  · exact correction_closure hrecipe
      (Nat.le_of_lt htermWeight)
  · rw [weightedWordWeight, hshape]
    exact hweight

/--
Raw terms and emitted corrections are both covered by the same finite
correction-closure vocabulary.
-/
lemma recipe_endpoint_factors
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm : term ∈ endpoint.collected.factors)
    (hweight :
      term.erasedShape.weight
          (HPAtom.weight leftWeight rightWeight) < n) :
    ∃ recipe ∈
        correctionClosureRecipes n leftWeight rightWeight,
      recipe.erasedShape = term.erasedShape := by
  have hterm' :
      term ∈
        inverseDecoratedTerms M N ++ endpoint.corrections :=
    endpoint.perm_append_corrections.subset hterm
  rcases List.mem_append.mp hterm' with hraw | hcorrection
  · rcases raw_decorated_terms
        hleftWeight hrightWeight hraw hweight with
      ⟨recipe, hrecipe, hshape⟩
    refine ⟨recipe, retained_correction_closure.mpr ⟨?_, ?_⟩, hshape⟩
    · exact correction_closure
        (show recipe ∈
            correctionClosure (sourceRecipes n leftWeight rightWeight) 0 by
          exact hrecipe)
        (Nat.zero_le _)
    · rw [weightedWordWeight, hshape]
      exact hweight
  · exact endpoint_corrections
      hleftWeight hrightWeight endpoint term hcorrection hweight

end UCVocabu
end TCTex
end Submission

/-!
# Signed-block support from the finite correction-closure vocabulary

The conservative finite correction closure covers every below-cutoff factor of
the genuine operational endpoint.  This file deduplicates its erased words and
transfers that support theorem through maximal same-shape compression to the
ordered concrete signed-block packet.

The skeleton remains a finite support universe, not a noncommutative schedule:
ordered packets retain repetitions and operational order explicitly.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCSuppor

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open CSAdmiss
open CSAggreg
open CCPkt
open CSSpec
open CCTrunc
open CFSubsti
open UNPkt
open FMEnd
open UCVocabu
open UCSuppora
open OCAdmiss

/-- Canonical finite skeleton of erased Hall words in the retained correction closure. -/
noncomputable def erasedShapeVocabulary
    (n leftWeight rightWeight : ℕ) :
    List (CWord HPAtom) :=
  ((correctionClosureRecipes n leftWeight rightWeight).map
    BRecipe.erasedShape).dedup

/-- Every retained closure recipe contributes its erased Hall word. -/
lemma shape_vocabulary_recipes
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight) :
    recipe.erasedShape ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  classical
  rw [erasedShapeVocabulary, List.mem_dedup]
  exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩

/-- Every word in the finite skeleton has a retained closure-recipe representative. -/
lemma recipe_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃ recipe ∈ correctionClosureRecipes n leftWeight rightWeight,
      recipe.erasedShape = word := by
  classical
  rw [erasedShapeVocabulary, List.mem_dedup] at hword
  exact List.mem_map.mp hword

/-- Every word in the closure skeleton has positive Hall-pair bidegree. -/
lemma bidegree_positive_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    word.PBPos := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, _hrecipe, rfl⟩
  exact recipe.positive

/-- Every word in the closure skeleton remains strictly below cutoff. -/
lemma erased_shape_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    word.weight (HPAtom.weight leftWeight rightWeight) < n := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, rfl⟩
  exact weighted_closure_recipes
    hrecipe

/-- Every below-cutoff maximal same-shape endpoint block is supported in the
finite correction-closure skeleton. -/
lemma shape_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors)
    (hweight :
      (shapeOfMem endpoint block hblock).weight
          (HPAtom.weight leftWeight rightWeight) < n) :
    shapeOfMem endpoint block hblock ∈
      erasedShapeVocabulary n leftWeight rightWeight := by
  let term :=
    block.head (nil_same_blocks endpoint block hblock)
  have hterm_block :
      term ∈ block :=
    List.head_mem (nil_same_blocks endpoint block hblock)
  have hterm_factors :
      term ∈ endpoint.collected.factors := by
    rw [← flatten_same_blocks endpoint.collected.factors]
    exact List.mem_flatten.mpr ⟨block, hblock, hterm_block⟩
  rcases recipe_endpoint_factors
      hleftWeight hrightWeight endpoint term hterm_factors
      (by
        rwa [erased_shape endpoint block hblock term hterm_block]) with
    ⟨recipe, hrecipe, hshape⟩
  rw [← erased_shape endpoint block hblock term hterm_block,
    ← hshape]
  exact shape_vocabulary_recipes hrecipe

/-- Every below-cutoff compressed packet in an ordered maximal-block list is
supported in the finite correction-closure skeleton. -/
lemma vocabulary_packets_blocks
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
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
          packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight
  | [], _hblocks, packet, hpacket, _hweight => by
      simp [packetsOfBlocks.eq_def] at hpacket
  | block :: blocks, hblocks, packet, hpacket, hweight => by
      rw [packetsOfBlocks.eq_def] at hpacket
      rcases List.mem_cons.mp hpacket with hpacket | hpacket
      · subst packet
        apply shape_erased_vocabulary
          hleftWeight hrightWeight endpoint block (hblocks block (by simp))
        rw [← word_packet certificateKernel endpoint block
          (hblocks block (by simp))]
        exact hweight
      · exact
          vocabulary_packets_blocks
            hleftWeight hrightWeight certificateKernel endpoint blocks
              (fun next hnext => hblocks next (by simp [hnext]))
              hpacket hweight

/-- Every below-cutoff packet in a concrete operational expansion is supported
in the finite correction-closure skeleton. -/
lemma vocabulary_concrete_packets
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (certificateKernel : OCShape)
    {M N : ℕ}
    {packet : RFPkt}
    (hpacket : packet ∈ concretePackets certificateKernel M N)
    (hweight : packetWeight leftWeight rightWeight packet < n) :
    packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  exact
    vocabulary_packets_blocks
      hleftWeight hrightWeight certificateKernel (endpoint M N)
        (sameErasedBlocks (endpoint M N).collected.factors)
        (fun _block hblock => hblock) hpacket hweight

/--
One explicit ordered signed-block packet supported in the finite
correction-closure skeleton.
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
      packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight

namespace OBPkt

/-- Every occurrence in an ordered closure-supported packet lies below cutoff. -/
lemma packet_weight_cutoff
    {n leftWeight rightWeight : ℕ}
    (packet : OBPkt n leftWeight rightWeight)
    {nextPacket : RFPkt}
    (hnextPacket : nextPacket ∈ packet.packets) :
    packetWeight leftWeight rightWeight nextPacket < n := by
  simpa [packetWeight] using
    erased_shape_vocabulary
      (packet.word_erased_vocabulary nextPacket hnextPacket)

/-- Ordered closure-supported packets are fixed points of cutoff truncation. -/
@[simp]
lemma truncate_packets
    {n leftWeight rightWeight : ℕ}
    (packet : OBPkt n leftWeight rightWeight) :
    truncate n leftWeight rightWeight packet.packets = packet.packets := by
  apply List.filter_eq_self.2
  intro nextPacket hnextPacket
  simpa only [decide_eq_true_eq] using
    packet.packet_weight_cutoff hnextPacket

end OBPkt

/-- Every local truncated concrete packet is an ordered packet supported in
the finite correction-closure skeleton. -/
noncomputable def orderedBlockConcrete
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
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
      hleftWeight hrightWeight certificateKernel
    · exact (List.mem_filter.mp hpacket').1
    · exact packet_weight_truncate hpacket'

/--
A multiplicity-independent closure-supported packet together with the
remaining semantic stabilization law against every local concrete packet.
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

/-- Forget finite support while retaining the cutoff-specific stabilization law. -/
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

/-- At root weights, stabilization supplies the natural signed-block packet
required by the subsequent signed lift. -/
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
    packet.truncNaturalPacket.packets = packet.packets :=
  rfl

end SBPkt

end UCSuppor
end TCTex
end Submission

/-!
# Erased-word skeleton from the finite correction closure

The conservative finite correction closure covers mixed nested corrections
emitted by the concrete More3 collector.  Its deduplicated erased shapes form
an unconditional finite support skeleton for cutoff signed-block packets.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CWSkelet

open HACoeff
open BRSpec
open UCVocabu

/-- Canonical finite erased-word skeleton of the retained correction closure. -/
noncomputable def erasedShapeVocabulary
    (n leftWeight rightWeight : ℕ) :
    List (CWord HPAtom) :=
  ((correctionClosureRecipes n leftWeight rightWeight).map
    BRecipe.erasedShape).dedup

/-- Every recipe in the retained closure contributes its erased shape. -/
lemma erased_vocabulary_recipes
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight) :
    recipe.erasedShape ∈
      erasedShapeVocabulary n leftWeight rightWeight := by
  classical
  rw [erasedShapeVocabulary, List.mem_dedup]
  exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩

/-- Every skeleton word has a positive recipe representative. -/
lemma recipe_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃ recipe ∈ correctionClosureRecipes n leftWeight rightWeight,
      recipe.erasedShape = word := by
  classical
  rw [erasedShapeVocabulary, List.mem_dedup] at hword
  exact List.mem_map.mp hword

/-- Every word in the closure skeleton has positive Hall-pair bidegree. -/
lemma bidegree_positive_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    word.PBPos := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, _hrecipe, rfl⟩
  exact recipe.positive

/-- Every closure-skeleton word remains strictly below the cutoff. -/
lemma erased_shape_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    word.weight (HPAtom.weight leftWeight rightWeight) < n := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, rfl⟩
  exact
    weighted_closure_recipes
      hrecipe

end CWSkelet
end TCTex
end Submission

/-!
# All-integral cutoff packets supported in the finite correction closure

The primary symbolic normalization target is an ordered signed-profile packet
whose words lie in the finite correction-closure skeleton and whose product
law holds at arbitrary integral source exponents in one lower-central
truncation.

This is stronger and cleaner than separately postulating natural
stabilization.  At natural exponents, the all-integral law and the concrete
truncated-packet law both evaluate to the same powered commutator.  Their
comparison constructs the stabilization witness automa, while the
same packet supplies its own signed lift.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCAll

universe u

open scoped commutatorElement

open CSAggreg
open CCTrunc
open CFExp
open CFSubsti
open UNPkt
open
  UCSuppor

/--
One ordered finite-support packet with its all-integral product law in a
fixed free lower-central truncation.
-/
structure TAPkta
    (d n leftWeight rightWeight : ℕ)
    extends OBPkt n leftWeight rightWeight where
  listEval_eq :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
        (packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace TAPkta

/-- Forget finite support and expose the substitution packet consumed by the
signed polynomial collector. -/
def truncatedAllIntegral
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight) :
    TAInt.{u} d n where
  packets := packet.packets
  listEval_eq := packet.listEval_eq

/--
The all-integral cutoff law automa stabilizes the ordered packet
against every multiplicity-dependent concrete operational packet.
-/
def stabilizedBlockPacket
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (kernel : OCShape) :
    SBPkt.{u}
      kernel d n leftWeight rightWeight where
  toOBPkt :=
    packet.toOBPkt
  packet_prod_concrete M N left right hleft hright := by
    apply Eq.trans _ <|
      (concrete_packets_pow
        packet.leftWeight_pos packet.rightWeight_pos kernel M N
          left right hleft hright).symm
    simpa only [zpow_natCast] using
      packet.listEval_eq left right (M : ℤ) (N : ℤ)

/-- At root weights, the all-integral cutoff packet supplies the natural
packet interface used by the stabilization route. -/
def truncNaturalPacket
    {d n : ℕ}
    (packet :
      TAPkta.{u} d n 1 1)
    (kernel : OCShape) :
    TBPkt.{u} d n :=
  (packet.stabilizedBlockPacket kernel)
    |>.truncNaturalPacket

/-- The same all-integral law is the signed lift of its natural specialization. -/
def allIntegralLift
    {d n : ℕ}
    (packet :
      TAPkta.{u} d n 1 1)
    (kernel : OCShape) :
    (packet.truncNaturalPacket kernel).AILift where
  listEval_eq := packet.listEval_eq

@[simp]
lemma packets_truncated_all
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight) :
    packet.truncatedAllIntegral.packets =
      packet.packets :=
  rfl

@[simp]
lemma packets_stabilized_packet
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (kernel : OCShape) :
    (packet.stabilizedBlockPacket kernel).packets =
      packet.packets :=
  rfl

@[simp]
lemma packetsTruncNatural
    {d n : ℕ}
    (packet :
      TAPkta.{u} d n 1 1)
    (kernel : OCShape) :
    (packet.truncNaturalPacket kernel).packets =
      packet.packets :=
  rfl

end TAPkta

end UCAll
end TCTex
end Submission

/-!
# Principal separation for the finite correction closure

The finite correction closure is a support universe, not an ordered packet:
older recipes are intentionally retained at every round.  For structural
restart it is nevertheless important that closure does not create a new
principal `(1, 1)` shape.

Every block recipe already has positive left and right degree.  A pairwise
correction therefore has both degrees strictly larger than one.  Induction on
the finite closure rounds reduces every `(1, 1)` occurrence back to the source
vocabulary.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CPSep

open HACoeff
open BRSpec
open UCVocabu
open UCSuppor
open URVocabu

/-- A pairwise recipe correction cannot have principal bidegree `(1, 1)`. -/
lemma bidegree_pairwise_corrections
    {recipes : List BRecipe}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ pairwiseCorrections recipes) :
    recipe.leftDegree ≠ 1 ∨ recipe.rightDegree ≠ 1 := by
  rcases List.mem_flatMap.mp hrecipe with
    ⟨left, _hleft, hrecipe⟩
  rcases List.mem_map.mp hrecipe with
    ⟨right, _hright, rfl⟩
  left
  rw [leftDegree_correction]
  have hleftDegree := leftDegree_pos left
  have hrightDegree := leftDegree_pos right
  omega

/--
Every principal-bidegree recipe in a finite correction closure was already
present in the depth-zero source vocabulary.
-/
lemma source_closure_bidegree
    {source : List BRecipe}
    {depth : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosure source depth)
    (hleftDegree : recipe.leftDegree = 1)
    (hrightDegree : recipe.rightDegree = 1) :
    recipe ∈ source := by
  induction depth with
  | zero =>
      exact hrecipe
  | succ depth ih =>
      rcases List.mem_append.mp hrecipe with hrecipe | hrecipe
      · exact ih hrecipe
      · have hdegree :=
          bidegree_pairwise_corrections hrecipe
        exact False.elim
          (hdegree.elim
            (fun hleft => hleft hleftDegree)
            (fun hright => hright hrightDegree))

/-- The closure introduces no new occurrences of the distinguished basic recipe. -/
lemma source_closure_pair
    {source : List BRecipe}
    {depth : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosure source depth)
    (hbasic : recipe = hallPair) :
    recipe ∈ source := by
  apply source_closure_bidegree hrecipe
  · rw [hbasic]
    exact left_hall_pair
  · rw [hbasic]
    exact right_degree_pair

/--
Every retained principal-bidegree recipe in the finite cutoff closure came
from the cutoff-sized universal source list.
-/
lemma recipes_closure_bidegree
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight)
    (hleftDegree : recipe.leftDegree = 1)
    (hrightDegree : recipe.rightDegree = 1) :
    recipe ∈ sourceRecipes n leftWeight rightWeight := by
  exact
    source_closure_bidegree
      (retained_correction_closure.mp hrecipe).1
      hleftDegree hrightDegree

/-- Every retained occurrence of `basic` was already a source occurrence. -/
lemma source_recipes_pair
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight)
    (hbasic : recipe = hallPair) :
    recipe ∈ sourceRecipes n leftWeight rightWeight := by
  exact
    source_closure_pair
      (retained_correction_closure.mp hrecipe).1 hbasic

/--
At the erased-word level, every principal-bidegree member of the finite
closure skeleton already has a representative in the source vocabulary.
-/
lemma shape_vocabulary_bidegree
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight)
    (hleftDegree : word.pairLeftDegree = 1)
    (hrightDegree : word.pairRightDegree = 1) :
    ∃ recipe ∈ sourceRecipes n leftWeight rightWeight,
      recipe.erasedShape = word := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, hshape⟩
  refine
    ⟨recipe,
      recipes_closure_bidegree
        hrecipe ?_ ?_,
      hshape⟩
  · rw [← recipe.erased_left_degree, hshape]
    exact hleftDegree
  · rw [← recipe.erased_shape_degree, hshape]
    exact hrightDegree

end CPSep
end TCTex
end Submission

/-!
# Recursive decomposition of the finite correction closure

The retained finite correction closure is a conservative support universe.  To
construct formulas on that universe recursively, it is useful to run the
closure definition backwards: every retained recipe is either an original
source recipe or a correction of two retained parents of strictly smaller
weighted Hall degree.

This file records that backward decomposition, transfers it to erased words,
and packages the resulting well-founded induction principle.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CRDecomp

open HACoeff
open BRSpec
open CWSkelet
open UCVocabu
open URVocabu

/--
Every recipe in a finite correction-closure layer is either a source recipe or
a correction of two recipes already available in the same layer.
-/
lemma or_parent_recipes
    {source : List BRecipe} :
    ∀ {depth : ℕ}
      {recipe : BRecipe},
      recipe ∈ correctionClosure source depth →
        recipe ∈ source ∨
          ∃ left right : BRecipe,
            left ∈ correctionClosure source depth ∧
              right ∈ correctionClosure source depth ∧
                recipe = left.correction right
  | 0, recipe, hrecipe =>
      Or.inl hrecipe
  | depth + 1, recipe, hrecipe => by
      rcases List.mem_append.mp hrecipe with hrecipe | hrecipe
      · rcases
          or_parent_recipes
            hrecipe with
          hsource | ⟨left, right, hleft, hright, heq⟩
        · exact Or.inl hsource
        · exact
            Or.inr
              ⟨left, right,
                correction_closure_succ hleft,
                correction_closure_succ hright,
                heq⟩
      · rcases List.mem_flatMap.mp hrecipe with
          ⟨left, hleft, hrecipe⟩
        rcases List.mem_map.mp hrecipe with
          ⟨right, hright, rfl⟩
        exact
          Or.inr
            ⟨left, right,
              correction_closure_succ hleft,
              correction_closure_succ hright,
              rfl⟩

/--
Every retained closure recipe is either a source recipe or a correction of two
retained parents.  Both parents have strictly smaller weighted Hall degree.
-/
lemma
    recipes_or_parent
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight) :
    recipe ∈ sourceRecipes n leftWeight rightWeight ∨
      ∃ left ∈ correctionClosureRecipes n leftWeight rightWeight,
        ∃ right ∈ correctionClosureRecipes n leftWeight rightWeight,
          recipe = left.correction right ∧
            weightedWordWeight leftWeight rightWeight left <
                weightedWordWeight leftWeight rightWeight recipe ∧
              weightedWordWeight leftWeight rightWeight right <
                weightedWordWeight leftWeight rightWeight recipe := by
  have hrecipeClosure :=
    (retained_correction_closure.mp hrecipe).1
  have hrecipeCutoff :=
    (retained_correction_closure.mp hrecipe).2
  rcases
      or_parent_recipes
        hrecipeClosure with
    hsource | ⟨left, right, hleftClosure, hrightClosure, heq⟩
  · exact Or.inl hsource
  · have hleftWeightLt :
        weightedWordWeight leftWeight rightWeight left <
          weightedWordWeight leftWeight rightWeight recipe := by
      rw [heq]
      exact weighted_correction_left
        hleftWeight hrightWeight left right
    have hrightWeightLt :
        weightedWordWeight leftWeight rightWeight right <
          weightedWordWeight leftWeight rightWeight recipe := by
      rw [heq]
      exact weighted_correction_right
        hleftWeight hrightWeight left right
    exact
      Or.inr
        ⟨left,
          retained_correction_closure.mpr
            ⟨hleftClosure, hleftWeightLt.trans hrecipeCutoff⟩,
          right,
          retained_correction_closure.mpr
            ⟨hrightClosure, hrightWeightLt.trans hrecipeCutoff⟩,
          heq, hleftWeightLt, hrightWeightLt⟩

/--
Erased words in the finite skeleton have the same recursive decomposition.
The correction branch exposes two supported parent words of strictly smaller
weighted Hall degree.
-/
lemma
    parent_words_vocabulary
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    (∃ recipe ∈ sourceRecipes n leftWeight rightWeight,
      recipe.erasedShape = word) ∨
      ∃ leftWord ∈ erasedShapeVocabulary n leftWeight rightWeight,
        ∃ rightWord ∈ erasedShapeVocabulary n leftWeight rightWeight,
          word = .commutator leftWord rightWord ∧
            leftWord.weight (HPAtom.weight leftWeight rightWeight) <
                word.weight (HPAtom.weight leftWeight rightWeight) ∧
              rightWord.weight (HPAtom.weight leftWeight rightWeight) <
                word.weight (HPAtom.weight leftWeight rightWeight) := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, hshape⟩
  rcases
      recipes_or_parent
        hleftWeight hrightWeight hrecipe with
    hsource | ⟨left, hleft, right, hright, heq, hleftLt, hrightLt⟩
  · exact Or.inl ⟨recipe, hsource, hshape⟩
  · refine
      Or.inr
        ⟨left.erasedShape,
          erased_vocabulary_recipes
            hleft,
          right.erasedShape,
          erased_vocabulary_recipes
            hright,
          ?_, ?_, ?_⟩
    · rw [← hshape, heq, BRecipe.erasedShape_corr]
    · simpa only [weightedWordWeight, hshape] using hleftLt
    · simpa only [weightedWordWeight, hshape] using hrightLt

/--
Well-founded induction over retained closure recipes.  Source recipes are base
cases; every correction case may use the results already constructed for its
strictly lighter retained parents.
-/
theorem closure_recipes_induction
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {motive : BRecipe → Prop}
    (source :
      ∀ recipe ∈ sourceRecipes n leftWeight rightWeight,
        motive recipe)
    (correction :
      ∀ left right,
        left ∈ correctionClosureRecipes n leftWeight rightWeight →
          right ∈ correctionClosureRecipes n leftWeight rightWeight →
            motive left →
              motive right →
                motive (left.correction right)) :
    ∀ recipe ∈ correctionClosureRecipes n leftWeight rightWeight,
      motive recipe := by
  intro recipe hrecipe
  refine
    (InvImage.wf
      (fun nextRecipe : BRecipe =>
        weightedWordWeight leftWeight rightWeight nextRecipe)
      Nat.lt_wfRel.wf).induction
        (C := fun nextRecipe =>
          nextRecipe ∈
              correctionClosureRecipes n leftWeight rightWeight →
            motive nextRecipe)
        recipe ?_ hrecipe
  intro nextRecipe ih hnextRecipe
  rcases
      recipes_or_parent
        hleftWeight hrightWeight hnextRecipe with
    hsource | ⟨left, hleft, right, hright, heq, hleftLt, hrightLt⟩
  · exact source nextRecipe hsource
  · rw [heq]
    exact correction left right hleft hright
      (ih left hleftLt hleft)
      (ih right hrightLt hright)

/--
Word-level induction over the finite correction-closure skeleton.  This is the
recursion interface used when a symbolic collector attaches data to erased
Hall words rather than to recipe representatives.
-/
theorem erased_vocabulary_induction
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {motive : CWord HPAtom → Prop}
    (source :
      ∀ recipe ∈ sourceRecipes n leftWeight rightWeight,
        motive recipe.erasedShape)
    (correction :
      ∀ left right,
        left ∈ correctionClosureRecipes n leftWeight rightWeight →
          right ∈ correctionClosureRecipes n leftWeight rightWeight →
            motive left.erasedShape →
              motive right.erasedShape →
                motive (.commutator left.erasedShape right.erasedShape)) :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      motive word := by
  intro word hword
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, hshape⟩
  rw [← hshape]
  refine closure_recipes_induction
    hleftWeight hrightWeight source ?_ recipe hrecipe
  intro left right hleft hright ihleft ihright
  rw [BRecipe.erasedShape_corr]
  exact correction left right hleft hright ihleft ihright

end CRDecomp
end TCTex
end Submission

/-!
# Ordered signed-block packets supported on the finite correction closure

The correction-closure skeleton is finite but is not itself a noncommutative
collection schedule.  This file packages explicit ordered signed-profile
occurrences supported on that skeleton and the remaining stabilization law
against multiplicity-dependent concrete operational packets.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCOrdere

universe u

open scoped commutatorElement

open CSAggreg
open CCTrunc
open CFSubsti
open UNPkt
open CWSkelet

/--
One multiplicity-independent ordered signed-profile packet supported on the
finite correction-closure skeleton.
-/
structure CBPkt
    (n leftWeight rightWeight : ℕ) where
  leftWeight_pos :
    0 < leftWeight
  rightWeight_pos :
    0 < rightWeight
  packets :
    List RFPkt
  word_erased_vocabulary :
    ∀ packet ∈ packets,
      packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight

namespace CBPkt

/-- Every supported packet occurrence lies below the quotient cutoff. -/
lemma packet_weight_cutoff
    {n leftWeight rightWeight : ℕ}
    (packet :
      CBPkt
        n leftWeight rightWeight)
    {nextPacket : RFPkt}
    (hnextPacket : nextPacket ∈ packet.packets) :
    packetWeight leftWeight rightWeight nextPacket < n := by
  simpa [packetWeight] using
    erased_shape_vocabulary
      (packet.word_erased_vocabulary nextPacket hnextPacket)

/-- Supported closure packets are fixed points of semantic truncation. -/
@[simp]
lemma truncate_packets
    {n leftWeight rightWeight : ℕ}
    (packet :
      CBPkt
        n leftWeight rightWeight) :
    truncate n leftWeight rightWeight packet.packets =
      packet.packets := by
  apply List.filter_eq_self.2
  intro nextPacket hnextPacket
  simpa only [decide_eq_true_eq] using
    packet.packet_weight_cutoff hnextPacket

end CBPkt

/--
An ordered closure-supported packet together with its remaining stabilization
law against all concrete operational signed-block packets.
-/
structure SCPkt
    (kernel : OCShape)
    (d n leftWeight rightWeight : ℕ)
    extends
      CBPkt
        n leftWeight rightWeight where
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

namespace SCPkt

/-- Forget finite support while retaining the cutoff-specific stabilization
law consumed by the natural signed-block packet bridge. -/
def truncatedNaturalStabilization
    {kernel : OCShape}
    {d n leftWeight rightWeight : ℕ}
    (packet :
      SCPkt.{u}
        kernel d n leftWeight rightWeight) :
    TNStab.{u}
      kernel d n leftWeight rightWeight packet.packets where
  leftWeight_pos := packet.leftWeight_pos
  rightWeight_pos := packet.rightWeight_pos
  packet_prod_concrete := packet.packet_prod_concrete

/-- At root weights, closure-supported stabilization supplies the natural
Hall-Petresco packet used by signed lifting. -/
def truncNaturalPacket
    {kernel : OCShape}
    {d n : ℕ}
    (packet :
      SCPkt.{u}
        kernel d n 1 1) :
    TBPkt.{u} d n :=
  packet.truncatedNaturalStabilization
    |>.truncNaturalPacket

@[simp]
lemma packetsTruncNatural
    {kernel : OCShape}
    {d n : ℕ}
    (packet :
      SCPkt.{u}
        kernel d n 1 1) :
    packet.truncNaturalPacket.packets =
      packet.packets :=
  rfl

end SCPkt

end UCOrdere
end TCTex
end Submission

/-!
# Recipe packets as closure-supported signed-block packets

Positive Hall-Petresco block recipes are a special case of signed-profile
packets: retain the same erased word and attach the singleton positive block
profile of the recipe.  This file records that adapter at arbitrary integral
source exponents and lifts any closure-supported recipe packet to the ordered
signed-block boundary.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCAdapt

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open CSAggreg
open CSChunks
open CEComp
open CFSubsti
open UCAll
open UCSuppor
open UCVocabu

/-- Positive block lists evaluate to the ordinary generalized-binomial recipe
factor at arbitrary integral source exponents. -/
@[simp]
lemma signed_block_blocks
    (z : ℤ)
    (degrees : List ℕ) :
    signedBlockProduct z (positiveBlocks degrees) =
      (degrees.map fun degree => Ring.choose z degree).prod := by
  simp [signedBlockProduct, positiveBlocks, Sign.intValue,
    Function.comp_def]

/-- Regard one ordinary block recipe as one positively weighted signed profile. -/
def positiveWeightedProfile
    (recipe : BRecipe) :
    WBProf where
  multiplicity := 1
  profile := positiveBlockProfile recipe

@[simp]
lemma positive_weighted_profile
    (recipe : BRecipe) :
    (positiveWeightedProfile recipe).profile.leftDegree =
      recipe.erasedShape.pairLeftDegree := by
  simp [positiveWeightedProfile]

@[simp]
lemma positive_weighted_degree
    (recipe : BRecipe) :
    (positiveWeightedProfile recipe).profile.rightDegree =
      recipe.erasedShape.pairRightDegree := by
  simp [positiveWeightedProfile]

/-- The singleton positive signed profile has the recipe's coefficient at
arbitrary integral source exponents. -/
@[simp]
lemma weighted_profile_positive
    (recipe : BRecipe)
    (leftExponent rightExponent : ℤ) :
    weightedProfileValue
        (positiveWeightedProfile recipe)
        leftExponent rightExponent =
      coefficientValue recipe leftExponent rightExponent := by
  simp [weightedProfileValue, positiveWeightedProfile,
    positiveBlockProfile, coefficientValue]

/-- Singleton homogeneous signed-profile packet attached to one recipe. -/
def homogeneousFormulaRecipe
    (recipe : BRecipe) :
    HFPkt
      recipe.erasedShape.pairLeftDegree
      recipe.erasedShape.pairRightDegree where
  profiles := [positiveWeightedProfile recipe]
  profiles_leftDegree := by
    simp
  profiles_rightDegree := by
    simp

@[simp]
lemma value_homogeneous_recipe
    (recipe : BRecipe)
    (leftExponent rightExponent : ℤ) :
    (homogeneousFormulaRecipe recipe).value
        leftExponent rightExponent =
      coefficientValue recipe leftExponent rightExponent := by
  simp [homogeneousFormulaRecipe,
    HFPkt.value]

/-- Signed recollection packet attached to one positive block recipe. -/
def recollectionFormulaRecipe
    (recipe : BRecipe) :
    RFPkt where
  word := recipe.erasedShape
  positive := recipe.positive
  profiles := homogeneousFormulaRecipe recipe

@[simp]
lemma recollection_formula_recipe
    (recipe : BRecipe) :
    (recollectionFormulaRecipe recipe).word =
      recipe.erasedShape :=
  rfl

@[simp]
lemma value_profiles_recipe
    (recipe : BRecipe)
    (leftExponent rightExponent : ℤ) :
    (recollectionFormulaRecipe recipe).profiles.value
        leftExponent rightExponent =
      coefficientValue recipe leftExponent rightExponent :=
  value_homogeneous_recipe
    recipe leftExponent rightExponent

/-- Attach singleton positive signed profiles to an ordered recipe packet. -/
def formulaPacketsRecipes
    (recipes : List BRecipe) :
    List RFPkt :=
  recipes.map recollectionFormulaRecipe

/-- The signed-profile adapter preserves every ordered recipe evaluation. -/
lemma formula_packets_recipes
    {G : Type*}
    [Group G]
    (recipes : List BRecipe)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((formulaPacketsRecipes recipes).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent).prod =
      (recipes.map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod := by
  induction recipes with
  | nil =>
      rfl
  | cons recipe recipes ih =>
      change
        recipe.erasedShape.eval (HPAtom.eval left right) ^
              (recollectionFormulaRecipe recipe).profiles.value
                leftExponent rightExponent *
            ((formulaPacketsRecipes recipes).map
              fun packet =>
                packet.word.eval (HPAtom.eval left right) ^
                  packet.profiles.value leftExponent rightExponent).prod =
          recipe.erasedShape.eval (HPAtom.eval left right) ^
              coefficientValue recipe leftExponent rightExponent *
            (recipes.map fun nextRecipe =>
              nextRecipe.erasedShape.eval (HPAtom.eval left right) ^
                coefficientValue nextRecipe leftExponent rightExponent).prod
      rw [value_profiles_recipe, ih]

/--
Every closure-supported all-integral recipe packet is an ordered
closure-supported signed-profile packet with the same product law.
-/
def truncAllPacket
    {d n leftWeight rightWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hsupport :
      ∀ recipe ∈ packet.recipes,
        recipe.erasedShape ∈
          erasedShapeVocabulary n leftWeight rightWeight) :
    TAPkta.{u}
      d n leftWeight rightWeight where
  leftWeight_pos := hleftWeight
  rightWeight_pos := hrightWeight
  packets :=
    formulaPacketsRecipes packet.recipes
  word_erased_vocabulary := by
    intro nextPacket hnextPacket
    rcases List.mem_map.mp hnextPacket with
      ⟨recipe, hrecipe, rfl⟩
    exact hsupport recipe hrecipe
  listEval_eq left right leftExponent rightExponent := by
    rw [formula_packets_recipes]
    exact packet.listEval_eq left right leftExponent rightExponent

end UCAdapt
end TCTex
end Submission

/-!
# Profile assignments on the finite correction closure

The finite correction closure is a conservative support universe for the
genuine operational endpoint.  A symbolic Hall collector must still attach
one homogeneous signed-profile formula to each retained erased word and prove
their ordered product identity.

This file packages that remaining finite assignment problem.  A universal
profile assignment compiles directly to the all-integral closure-supported
packet, so its natural stabilization and signed lift are automatic.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  FCAssign

universe v

open scoped commutatorElement

open CSAggreg
open
  CFSubsti
open
  CFExp
open
  UCSuppor
open
  UCAll

/--
Multiplicity-independent signed-profile coefficients attached to every word
in the conservative finite correction-closure skeleton.
-/
structure SPAssign
    (n leftWeight rightWeight : ℕ) where
  profiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree

namespace SPAssign

/-- Attach each assigned profile formula to its retained erased word. -/
noncomputable def toPackets
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight) :
    List RFPkt :=
  (erasedShapeVocabulary n leftWeight rightWeight).attach.map fun word =>
    {
      word := word.1
      positive :=
        bidegree_positive_vocabulary word.2
      profiles := assignment.profiles word.1 word.2
    }

/-- Forgetting the assigned profiles recovers the finite closure skeleton. -/
@[simp]
lemma word_packets
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight) :
    assignment.toPackets.map RFPkt.word =
      erasedShapeVocabulary n leftWeight rightWeight := by
  classical
  simp [toPackets]

/-- Every attached packet word belongs to the conservative finite skeleton. -/
lemma word_vocabulary_packets
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    {packet : RFPkt}
    (hpacket : packet ∈ assignment.toPackets) :
    packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  rw [← assignment.word_packets]
  exact List.mem_map.mpr ⟨packet, hpacket, rfl⟩

/-- A profile assignment is an ordered cutoff packet supported on the closure. -/
noncomputable def orderedBlockPacket
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    OBPkt n leftWeight rightWeight where
  leftWeight_pos := hleftWeight
  rightWeight_pos := hrightWeight
  packets := assignment.toPackets
  word_erased_vocabulary packet hpacket :=
    assignment.word_vocabulary_packets
      (packet := packet) hpacket

end SPAssign

/--
One finite closure assignment whose ordered signed-profile product is the
Hall-Petresco commutator identity in every group.
-/
structure UPAssign
    (n leftWeight rightWeight : ℕ)
    extends SPAssign n leftWeight rightWeight where
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
A universal finite closure assignment is the primary all-integral ordered
cutoff packet boundary in every free lower-central truncation.
-/
noncomputable def truncAllPacket
    {n leftWeight rightWeight : ℕ}
    (assignment :
      UPAssign.{v}
        n leftWeight rightWeight)
    (d : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    TAPkta.{v}
      d n leftWeight rightWeight where
  toOBPkt :=
    assignment.toSPAssign
      |>.orderedBlockPacket hleftWeight hrightWeight
  listEval_eq := assignment.listEval_eq

/--
At root weights, a universal closure assignment automa supplies the
fixed stabilized packet compared with every local concrete packet.
-/
noncomputable def stabilizedBlockPacket
    {n : ℕ}
    (assignment :
      UPAssign.{v} n 1 1)
    (d : ℕ)
    (kernel : OCShape) :
    SBPkt.{v} kernel d n 1 1 :=
  (assignment.truncAllPacket d
    (by simp) (by simp)).stabilizedBlockPacket kernel

/--
The same universal closure assignment automa supplies the signed lift
consumed by symbolic Hall-polynomial substitution.
-/
noncomputable def allIntegralLift
    {n : ℕ}
    (assignment :
      UPAssign.{v} n 1 1)
    (d : ℕ)
    (kernel : OCShape) :
    ((assignment.stabilizedBlockPacket d kernel)
      |>.truncNaturalPacket).AILift :=
  (assignment.truncAllPacket d
    (by simp) (by simp)).allIntegralLift kernel

@[simp]
lemma packetsTruncAll
    {n leftWeight rightWeight : ℕ}
    (assignment :
      UPAssign.{v}
        n leftWeight rightWeight)
    (d : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (assignment.truncAllPacket
      d hleftWeight hrightWeight).packets =
        assignment.toSPAssign.toPackets :=
  rfl

end UPAssign

end
  FCAssign
end TCTex
end Submission

/-!
# Concrete signed-block packets supported by the finite correction closure

Every below-cutoff term of a concrete operational endpoint has a representative
in the finite correction closure.  Maximal same-shape compression transfers
that support to the ordered signed-block packet without changing packet order.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CCSuppor

open HACoeff
open CSAdmiss
open CSAggreg
open CCPkt
open CSSpec
open CCTrunc
open CFSubsti
open FMEnd
open UCOrdere
open CWSkelet
open UCVocabu
open OCAdmiss

/-- Coverage of endpoint terms transfers to the common erased shape of one
maximal same-shape block. -/
lemma shape_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors)
    (hweight :
      (shapeOfMem endpoint block hblock).weight
          (HPAtom.weight leftWeight rightWeight) < n) :
    shapeOfMem endpoint block hblock ∈
      erasedShapeVocabulary n leftWeight rightWeight := by
  let term :=
    block.head (nil_same_blocks endpoint block hblock)
  have htermBlock :
      term ∈ block :=
    List.head_mem (nil_same_blocks endpoint block hblock)
  have htermFactors :
      term ∈ endpoint.collected.factors := by
    rw [← flatten_same_blocks endpoint.collected.factors]
    exact List.mem_flatten.mpr ⟨block, hblock, htermBlock⟩
  rcases recipe_endpoint_factors
      hleftWeight hrightWeight endpoint term htermFactors
      (by
        rwa [erased_shape endpoint block hblock term htermBlock]) with
    ⟨recipe, hrecipe, hshape⟩
  rw [← erased_shape endpoint block hblock term htermBlock,
    ← hshape]
  exact
    erased_vocabulary_recipes hrecipe

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
supported on the finite correction-closure skeleton. -/
lemma vocabulary_packets_blocks
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
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
          packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight
  | [], _hblocks, packet, hpacket, _hweight => by
      simp [packetsOfBlocks.eq_def] at hpacket
  | block :: blocks, hblocks, packet, hpacket, hweight => by
      rw [packetsOfBlocks.eq_def] at hpacket
      rcases List.mem_cons.mp hpacket with hpacket | hpacket
      · subst packet
        apply shape_erased_vocabulary
          hleftWeight hrightWeight endpoint block (hblocks block (by simp))
        rw [← word_packet certificateKernel endpoint block
          (hblocks block (by simp))]
        exact hweight
      · exact
          vocabulary_packets_blocks
            hleftWeight hrightWeight certificateKernel endpoint blocks
              (fun next hnext => hblocks next (by simp [hnext]))
              hpacket hweight

/-- Every below-cutoff packet in the chosen concrete endpoint is supported on
the finite correction-closure skeleton. -/
lemma vocabulary_concrete_packets
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (certificateKernel : OCShape)
    {M N : ℕ}
    {packet : RFPkt}
    (hpacket : packet ∈ concretePackets certificateKernel M N)
    (hweight : packetWeight leftWeight rightWeight packet < n) :
    packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  exact
    vocabulary_packets_blocks
      hleftWeight hrightWeight certificateKernel (endpoint M N)
        (sameErasedBlocks (endpoint M N).collected.factors)
        (fun _block hblock => hblock) hpacket hweight

/-- Every local truncated concrete packet is already an ordered packet
supported on the finite correction closure. -/
noncomputable def
    closurePacketConcrete
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (certificateKernel : OCShape)
    (M N : ℕ) :
    CBPkt
      n leftWeight rightWeight where
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
      hleftWeight hrightWeight certificateKernel
    · exact (List.mem_filter.mp hpacket').1
    · exact packet_weight_truncate hpacket'

end CCSuppor
end TCTex
end Submission

/-!
# Low-cutoff closure-supported signed-block packets

The first closure-supported all-integral packets are completely explicit.
At cutoff at most two every powered commutator vanishes.  At cutoff three the
only surviving Hall-Petresco word is the basic bracket, whose raw dummy-trace
occurrence places it in the finite correction-closure skeleton.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CLPacket

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open RHRecurs
open RHRecipe
open HHTrunc
open RRVocabu
open UCAll
open UCAdapt
open UCSuppor
open UCVocabu
open URVocabu

/-- Every below-cutoff raw inverse history has its erased word in the retained
finite correction-closure skeleton. -/
lemma collapse_vocabulary_histories
    {M N n : ℕ}
    (history : RHistor M N)
    (hhistory : history ∈ inverseRawHistories M N)
    (hweight : RHistor.weight 1 1 history < n) :
    collapseWord history.word ∈ erasedShapeVocabulary n 1 1 := by
  rcases equivalent_initial_recipes
      (n := n) (leftWeight := 1) (rightWeight := 1)
      (by omega) (by omega) history hhistory hweight with
    ⟨recipe, hrecipe, hequivalent⟩
  have hsource :
      recipe.blockRecipe ∈ sourceRecipes n 1 1 :=
    List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩
  have hretained :
      recipe.blockRecipe ∈ correctionClosureRecipes n 1 1 := by
    apply retained_correction_closure.mpr
    constructor
    · exact correction_closure
        (show recipe.blockRecipe ∈ correctionClosure (sourceRecipes n 1 1) 0 by
          exact hsource)
        (Nat.zero_le _)
    · exact weighted_cutoff_recipes hsource
  have hpositive :=
    RHRecipe.RHistor.positive_raw_histories
      hhistory
  have hlinear :=
    RHRecipe.RHistor.inverse_raw_histories
      hhistory
  have hshape :
      recipe.blockRecipe.erasedShape = collapseWord history.word := by
    calc
      recipe.blockRecipe.erasedShape =
          (RRVocabu.RHistor.initialRecipe
            history hhistory).blockRecipe.erasedShape :=
        hequivalent.2.2
      _ = collapseWord history.word := by
        rw [IRecipe.blockRecipe, BRecipe.erased_shape_linear]
        change
          (LRecipe.ofLabelLinear history.word hpositive hlinear).erasedShape =
            collapseWord history.word
        exact erased_label_linear history.word _ _
  rw [← hshape]
  exact shape_vocabulary_recipes hretained

/-- The distinguished basic Hall-pair word occurs in the retained finite
correction-closure skeleton whenever its weight two lies below cutoff. -/
lemma base_erased_vocabulary
    {n : ℕ}
    (hn : 2 < n) :
    CWord.hallPairBase ∈ erasedShapeVocabulary n 1 1 := by
  let history : RHistor 1 1 :=
    .hallPair (Sum.inl 0) (Sum.inr 0)
  have hhistory :
      history ∈ inverseRawHistories 1 1 := by
    simp [history, inverseRawHistories, labelledLeftAtoms, labelledRightAtoms,
      inverseLeftHistories, inverseRightHistories, inverseConjHistory,
      inverseConjHistories]
  have hweight :
      RHistor.weight 1 1 history < n := by
    simp [history, RHistor.weight, collapseWord, collapseLabel,
      HPAtom.weight]
    omega
  simpa [history, collapseWord, CWord.hallPairBase] using
    collapse_vocabulary_histories
      history hhistory hweight

/-- At cutoff at most two, the closure-supported all-integral packet is empty. -/
def empty_n_two
    {d n : ℕ}
    (hn : n ≤ 2) :
    TAPkta.{u} d n 1 1 where
  leftWeight_pos := by omega
  rightWeight_pos := by omega
  packets := []
  word_erased_vocabulary := by
    simp
  listEval_eq left right leftExponent rightExponent := by
    simp only [List.map_nil, List.prod_nil]
    symm
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega)
      (element_lower_series
        (show left ^ leftExponent ∈
            Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 by
          simp)
        (show right ^ rightExponent ∈
            Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 by
          simp))

/-- At cutoff three, transport the singleton basic recipe formula into the
closure-supported signed-profile boundary. -/
def singleton_n_three
    {d n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    TAPkta.{u} d n 1 1 :=
  truncAllPacket
    (PFSubsti.TAPkt.n_three
      (d := d) hhigh)
    (by omega) (by omega) (by
      intro recipe hrecipe
      rcases List.mem_singleton.mp hrecipe with rfl
      simpa using base_erased_vocabulary hlow)

/-- Uniform explicit closure-supported signed-profile packet for every cutoff
at most three. -/
def n_three
    {d n : ℕ}
    (hn : n ≤ 3) :
    TAPkta.{u} d n 1 1 :=
  if hlow : n ≤ 2 then
    empty_n_two hlow
  else
    singleton_n_three (by omega) hn

end CLPacket
end TCTex
end Submission

/-!
# Recipe-chunk alignment for finite-closure profile assignments

A fixed signed-profile packet can aggregate several same-word recipe factors.
This file records the local chunk condition and proves that an ordered chunking
of an all-integral recipe packet transfers its product law to the finite-closure
profile assignment.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  ACAlign

universe u v

open scoped commutatorElement

open HACoeff
open BRSpec
open CFSubsti
open
  UCAll
open
  FCAssign

namespace RFPkt

/--
One signed-profile packet aggregates an ordered chunk of recipe factors when
all recipes have its erased word and its profile value is their coefficient
sum.
-/
structure RCAlign
    (packet : RFPkt)
    (recipes : List BRecipe) : Prop where
  erased_shape_word :
    ∀ recipe ∈ recipes, recipe.erasedShape = packet.word
  profiles_value_sum :
    ∀ leftExponent rightExponent : ℤ,
      packet.profiles.value leftExponent rightExponent =
        (recipes.map fun recipe =>
          coefficientValue recipe leftExponent rightExponent).sum

namespace RCAlign

private lemma zpow_value_prod
    {G : Type*}
    [Group G]
    (word : CWord HPAtom)
    (recipes : List BRecipe)
    (hrecipes :
      ∀ recipe ∈ recipes, recipe.erasedShape = word)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    word.eval (HPAtom.eval left right) ^
          (recipes.map fun recipe =>
            coefficientValue recipe leftExponent rightExponent).sum =
      (recipes.map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod := by
  induction recipes with
  | nil =>
      simp
  | cons recipe recipes ih =>
      have hrecipe :
          recipe.erasedShape = word :=
        hrecipes recipe (by simp)
      have htail :
          ∀ nextRecipe ∈ recipes, nextRecipe.erasedShape = word := by
        intro nextRecipe hnextRecipe
        exact hrecipes nextRecipe (by simp [hnextRecipe])
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [zpow_add, hrecipe, ih htail]

/-- A same-word recipe chunk evaluates as its aggregate signed-profile factor. -/
lemma eval_recipe_factors
    {G : Type*}
    [Group G]
    {packet : RFPkt}
    {recipes : List BRecipe}
    (alignment : RCAlign packet recipes)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent =
      (recipes.map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod := by
  rw [alignment.profiles_value_sum]
  exact
    zpow_value_prod packet.word recipes
      alignment.erased_shape_word left right leftExponent rightExponent

end RCAlign
end RFPkt

namespace SPAssign

/--
An assignment is recipe-chunk aligned when its ordered packets correspond to
chunks whose flattening recovers the ordered recipe packet.
-/
structure RCAlign
    {n leftWeight rightWeight : ℕ}
    (assignment : SPAssign n leftWeight rightWeight)
    (recipes : List BRecipe) where
  chunks :
    List (List BRecipe)
  packets_chunks :
    List.Forall₂
      RFPkt.RCAlign
      assignment.toPackets chunks
  flatten_chunks :
    chunks.flatten = recipes

namespace RCAlign

private lemma flatten_recipe_factors
    {G : Type*}
    [Group G]
    {packets : List RFPkt}
    {chunks : List (List BRecipe)}
    (alignment :
      List.Forall₂
        RFPkt.RCAlign
        packets chunks)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    (packets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent).prod =
      (chunks.flatten.map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod := by
  induction alignment with
  | nil =>
      simp
  | cons head_alignment _tail_alignment ih =>
      simp only [List.map_cons, List.prod_cons, List.flatten_cons,
        List.map_append, List.prod_append]
      rw [head_alignment.eval_recipe_factors, ih]

/-- Chunk alignment transfers the complete ordered recipe-factor evaluation. -/
lemma list_recipe_factors
    {G : Type*}
    [Group G]
    {n leftWeight rightWeight : ℕ}
    {assignment :
      SPAssign n leftWeight rightWeight}
    {recipes : List BRecipe}
    (alignment : RCAlign assignment recipes)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    (assignment.toPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent).prod =
      (recipes.map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod := by
  rw [← alignment.flatten_chunks]
  exact
    flatten_recipe_factors alignment.packets_chunks
      left right leftExponent rightExponent

end RCAlign

/--
A cutoff-specific all-integral recipe packet and a chunk alignment construct
the fixed closure-supported signed packet required for stabilization.
-/
noncomputable def
    allChunkAlignment
    {d n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (alignment : RCAlign assignment packet.recipes) :
    TAPkta.{u}
      d n leftWeight rightWeight where
  toOBPkt :=
    assignment.orderedBlockPacket hleftWeight hrightWeight
  listEval_eq left right leftExponent rightExponent :=
    (alignment.list_recipe_factors
      left right leftExponent rightExponent).trans
        (packet.listEval_eq left right leftExponent rightExponent)

/--
A universal all-integral recipe packet and a chunk alignment construct the
global finite-closure profile assignment.
-/
noncomputable def assignmentChunkAlignment
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (packet :
      PFSubsti.UAInt.{v})
    (alignment : RCAlign assignment packet.recipes) :
    UPAssign.{v}
      n leftWeight rightWeight where
  toSPAssign :=
    assignment
  listEval_eq left right leftExponent rightExponent :=
    (alignment.list_recipe_factors
      left right leftExponent rightExponent).trans
        (packet.listEval_eq left right leftExponent rightExponent)

end SPAssign

end
  ACAlign
end TCTex
end Submission

/-!
# Recursive decomposition of finite-closure profile assignments

A finite-closure profile assignment attaches one signed-profile formula to
each word in the deduplicated erased-shape skeleton.  The skeleton recursion
therefore lifts to the actual assigned packet list without changing any
profiles.

This packet-level induction interface lets a symbolic collector recurse on
the signed-profile factors that occur in its ordered product.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace PADecomp

open
  CCTrunc
open CFSubsti
open
  CRDecomp
open
  FCAssign
open
  UCSuppor
open URVocabu

namespace SPAssign

/--
Every skeleton word has an assigned packet occurrence with exactly that word.
-/
lemma packet_packets_word
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃ packet ∈ assignment.toPackets,
      packet.word = word := by
  rw [← assignment.word_packets] at hword
  exact List.mem_map.mp hword

/--
Every assigned packet is either source-shaped or has assigned parent packets
of strictly smaller weighted Hall degree.
-/
lemma or_parent_packets
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {packet : RFPkt}
    (hpacket : packet ∈ assignment.toPackets) :
    (∃ sourceRecipe ∈ sourceRecipes n leftWeight rightWeight,
      sourceRecipe.erasedShape = packet.word) ∨
      ∃ leftPacket ∈ assignment.toPackets,
        ∃ rightPacket ∈ assignment.toPackets,
          packet.word =
              .commutator leftPacket.word rightPacket.word ∧
            packetWeight leftWeight rightWeight leftPacket <
                packetWeight leftWeight rightWeight packet ∧
              packetWeight leftWeight rightWeight rightPacket <
                packetWeight leftWeight rightWeight packet := by
  have hword :
      packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight :=
    assignment.word_vocabulary_packets hpacket
  rcases
      parent_words_vocabulary
        hleftWeight hrightWeight hword with
    hsource |
      ⟨leftWord, hleftWord, rightWord, hrightWord, hshape, hleftLt,
        hrightLt⟩
  · exact Or.inl hsource
  · rcases packet_packets_word assignment hleftWord with
      ⟨leftPacket, hleftPacket, hleftShape⟩
    rcases packet_packets_word assignment hrightWord with
      ⟨rightPacket, hrightPacket, hrightShape⟩
    refine
      Or.inr
        ⟨leftPacket, hleftPacket, rightPacket, hrightPacket, ?_, ?_, ?_⟩
    · simpa only [hleftShape, hrightShape] using hshape
    · simpa only [packetWeight, hleftShape] using hleftLt
    · simpa only [packetWeight, hrightShape] using hrightLt

/--
Well-founded induction over the packets of one finite-closure profile
assignment.  The correction case receives assigned parent packets already
known to satisfy the motive.
-/
theorem toPackets_induction
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {motive : RFPkt → Prop}
    (source :
      ∀ packet ∈ assignment.toPackets,
        (∃ sourceRecipe ∈ sourceRecipes n leftWeight rightWeight,
          sourceRecipe.erasedShape = packet.word) →
          motive packet)
    (correction :
      ∀ packet leftPacket rightPacket,
        packet ∈ assignment.toPackets →
          leftPacket ∈ assignment.toPackets →
            rightPacket ∈ assignment.toPackets →
              packet.word =
                  .commutator leftPacket.word rightPacket.word →
                motive leftPacket →
                  motive rightPacket →
                    motive packet) :
    ∀ packet ∈ assignment.toPackets,
      motive packet := by
  intro packet hpacket
  refine
    (InvImage.wf
      (fun nextPacket : RFPkt =>
        packetWeight leftWeight rightWeight nextPacket)
      Nat.lt_wfRel.wf).induction
        (C := fun nextPacket =>
          nextPacket ∈ assignment.toPackets →
            motive nextPacket)
        packet ?_ hpacket
  intro nextPacket ih hnextPacket
  rcases
      or_parent_packets assignment
        hleftWeight hrightWeight hnextPacket with
    hsource |
      ⟨leftPacket, hleftPacket, rightPacket, hrightPacket, hshape, hleftLt,
        hrightLt⟩
  · exact source nextPacket hnextPacket hsource
  · exact correction nextPacket leftPacket rightPacket
      hnextPacket hleftPacket hrightPacket hshape
      (ih leftPacket hleftLt hleftPacket)
      (ih rightPacket hrightLt hrightPacket)

end SPAssign

end PADecomp
end TCTex
end Submission

/-!
# Recursive profile assignments on the finite correction closure

The finite correction closure is generated from source recipes by binary
correction.  Its backward decomposition therefore turns local profile builders
into a profile assignment on the complete retained erased-word skeleton.

This file packages that constructor.  It does not prove the final ordered
product identity: that remains the semantic collection theorem.  It removes
the separate global obligation to assign a homogeneous signed-profile formula
to every retained word by hand.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CRAssign

universe v

open scoped commutatorElement

open HACoeff
open CFSubsti
open
  CRDecomp
open
  FCAssign
open
  CWSkelet
open UCVocabu
open URVocabu

/--
Local homogeneous signed-profile builders for the finite correction closure.
Source recipes are base cases.  A correction builder combines formulas already
constructed for two retained parents.
-/
structure RPKern
    (n leftWeight rightWeight : ℕ) where
  sourceProfiles :
    ∀ recipe ∈ sourceRecipes n leftWeight rightWeight,
      HFPkt
        recipe.erasedShape.pairLeftDegree
        recipe.erasedShape.pairRightDegree
  correctionProfiles :
    ∀ left right,
      left ∈ correctionClosureRecipes n leftWeight rightWeight →
        right ∈ correctionClosureRecipes n leftWeight rightWeight →
          HFPkt
              left.erasedShape.pairLeftDegree
              left.erasedShape.pairRightDegree →
            HFPkt
                right.erasedShape.pairLeftDegree
                right.erasedShape.pairRightDegree →
              HFPkt
                (left.correction right).erasedShape.pairLeftDegree
                (left.correction right).erasedShape.pairRightDegree

namespace RPKern

/--
Local source and correction builders recursively construct a profile formula
for every retained closure recipe.
-/
theorem profiles_closure_recipes
    {n leftWeight rightWeight : ℕ}
    (kernel :
      RPKern n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight) :
    Nonempty
      (HFPkt
        recipe.erasedShape.pairLeftDegree
        recipe.erasedShape.pairRightDegree) := by
  refine closure_recipes_induction
    (motive := fun nextRecipe =>
      Nonempty
        (HFPkt
          nextRecipe.erasedShape.pairLeftDegree
          nextRecipe.erasedShape.pairRightDegree))
    hleftWeight hrightWeight ?_ ?_ recipe hrecipe
  · intro sourceRecipe hsourceRecipe
    exact ⟨kernel.sourceProfiles sourceRecipe hsourceRecipe⟩
  · intro left right hleft hright hleftProfiles hrightProfiles
    rcases hleftProfiles with ⟨leftProfiles⟩
    rcases hrightProfiles with ⟨rightProfiles⟩
    exact
      ⟨kernel.correctionProfiles left right hleft hright
        leftProfiles rightProfiles⟩

/--
Choosing a retained recipe representative transfers the recursive profile
construction to every erased word in the deduplicated closure skeleton.
-/
theorem profiles_erased_vocabulary
    {n leftWeight rightWeight : ℕ}
    (kernel :
      RPKern n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    Nonempty
      (HFPkt
        word.pairLeftDegree word.pairRightDegree) := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, rfl⟩
  exact
    kernel.profiles_closure_recipes
      hleftWeight hrightWeight hrecipe

/--
A recursive profile kernel compiles to one global profile assignment on the
finite correction-closure skeleton.
-/
noncomputable def signedProfileAssignment
    {n leftWeight rightWeight : ℕ}
    (kernel :
      RPKern n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SPAssign n leftWeight rightWeight where
  profiles _word hword :=
    Classical.choice
      (kernel.profiles_erased_vocabulary
        hleftWeight hrightWeight hword)

/--
Once the remaining ordered product identity is known, a recursive profile
kernel compiles to the universal assignment consumed by the all-integral
packet and Claim 5 adapters.
-/
noncomputable def universalProfileAssignment
    {n leftWeight rightWeight : ℕ}
    (kernel :
      RPKern n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (listEval_eq :
      ∀ {G : Type v} [Group G]
        (left right : G)
        (leftExponent rightExponent : ℤ),
          (((kernel.signedProfileAssignment
              hleftWeight hrightWeight).toPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod =
            ⁅left ^ leftExponent, right ^ rightExponent⁆) :
    UPAssign.{v}
      n leftWeight rightWeight where
  toSPAssign :=
    kernel.signedProfileAssignment hleftWeight hrightWeight
  listEval_eq := listEval_eq

end RPKern

end
  CRAssign
end TCTex
end Submission

/-!
# Truncated semantic boundary for finite-closure profile assignments

The arbitrary-cutoff collector must attach a finite sum of signed binomial
profiles to each retained erased Hall word.  For Claim 5, its semantic product
law is needed only in one free lower-central truncation, not universally in
every group.

This file packages that weaker and more expressive boundary.  It is the
cutoff-specific target for a symbolic Hall collector that recollects repeated
blocks while retaining the full signed-profile sums.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  UTAssign

universe u

open scoped commutatorElement

open
  UCAll
open
  FCAssign
open SPAssign

/--
The cutoff-specific collection law for one summed signed-profile assignment.
Unlike a singleton recipe transversal, each packet may contain an arbitrary
finite list of weighted signed profiles.
-/
def SatisfiesTruncEval
    {d n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      (assignment.toPackets.map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace SPAssign

/--
A summed profile assignment and its cutoff-specific semantic law construct
the all-integral ordered packet consumed by symbolic recollection.
-/
noncomputable def
    truncAllPacket
    {d n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hlistEval :
      SatisfiesTruncEval (d := d) assignment) :
    TAPkta.{u}
      d n leftWeight rightWeight where
  toOBPkt :=
    assignment.orderedBlockPacket
      hleftWeight hrightWeight
  listEval_eq :=
    hlistEval

@[simp]
lemma packetsTruncAll
    {d n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hlistEval :
      SatisfiesTruncEval (d := d) assignment) :
    (truncAllPacket
      assignment hleftWeight hrightWeight hlistEval).packets =
        assignment.toPackets :=
  rfl

end SPAssign

end
  UTAssign
end TCTex
end Submission

/-!
# Class-three closure-supported signed-block packets

The inverse-oriented raw trace stores its triple corrections as
`[[y,x],x]` and `[[y,x],y]`.  These are the finite-closure-supported words.
At cutoff at most four, triple commutators are central, so they evaluate to
the usual Hall-Petresco terms `[x,[x,y]]` and `[y,[x,y]]`.

This file attaches the standard class-three coefficient profiles to the raw
inverse-oriented words and constructs the explicit closure-supported packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CTPacket

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open CFSubsti
open RHRecurs
open RHRecipe
open HHTrunc
open UCAll
open CLPacket
open UCAdapt
open UCSuppor

/-- Raw inverse-trace representative of the left triple correction. -/
def inverseLeftTriple :
    CWord HPAtom :=
  .commutator (rootSwapWord CWord.hallPairBase) (.atom .left)

/-- Raw inverse-trace representative of the right triple correction. -/
def inverseTripleWord :
    CWord HPAtom :=
  .commutator (rootSwapWord CWord.hallPairBase) (.atom .right)

/-- The left raw triple word occurs in the finite closure skeleton whenever
its weight three lies below cutoff. -/
lemma triple_erased_vocabulary
    {n : ℕ}
    (hn : 3 < n) :
    inverseLeftTriple ∈ erasedShapeVocabulary n 1 1 := by
  let emitted : RHistor 2 1 :=
    .hallPair (Sum.inl 1) (Sum.inr 0)
  let history : RHistor 2 1 :=
    .conjugate (Sum.inl 0) emitted
  have hhistory :
      history ∈ inverseRawHistories 2 1 := by
    simp [history, emitted, inverseRawHistories, labelledLeftAtoms,
      labelledRightAtoms, inverseLeftHistories, inverseRightHistories,
      inverseConjHistory, inverseConjHistories,
      conjugateAtomHistories]
  have hshape :
      collapseWord history.word = inverseLeftTriple := by
    rfl
  have hweight :
      RHistor.weight 1 1 history < n := by
    rw [RHistor.weight, hshape]
    simpa [inverseLeftTriple, rootSwapWord, CWord.hallPairBase,
      HPAtom.weight] using hn
  rw [← hshape]
  exact
    collapse_vocabulary_histories
      history hhistory hweight

/-- The right raw triple word occurs in the finite closure skeleton whenever
its weight three lies below cutoff. -/
lemma inverse_triple_vocabulary
    {n : ℕ}
    (hn : 3 < n) :
    inverseTripleWord ∈ erasedShapeVocabulary n 1 1 := by
  let emitted : RHistor 1 2 :=
    .hallPair (Sum.inl 0) (Sum.inr 1)
  let history : RHistor 1 2 :=
    .conjugate (Sum.inr 0) emitted
  have hhistory :
      history ∈ inverseRawHistories 1 2 := by
    simp [history, emitted, inverseRawHistories, labelledLeftAtoms,
      labelledRightAtoms, inverseLeftHistories, inverseRightHistories,
      inverseConjHistory, inverseConjHistories,
      conjugateAtomHistories]
  have hshape :
      collapseWord history.word = inverseTripleWord := by
    rfl
  have hweight :
      RHistor.weight 1 1 history < n := by
    rw [RHistor.weight, hshape]
    simpa [inverseTripleWord, rootSwapWord, CWord.hallPairBase,
      HPAtom.weight] using hn
  rw [← hshape]
  exact
    collapse_vocabulary_histories
      history hhistory hweight

/-- In class three, commuting an inverse pair bracket past any element gives
the swapped triple bracket. -/
lemma swap_n_four
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right outer :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ⁅⁅left, right⁆⁻¹, outer⁆ =
      ⁅outer, ⁅left, right⁆⁆ := by
  let inner := ⁅left, right⁆
  have hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have houter :
      outer ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hinner :
      inner ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa [inner] using
      element_lower_series hleft hright
  have hnested :
      ⁅inner, outer⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using
      element_lower_series hinner houter
  have hcommute :
      Commute inner ⁅inner, outer⁆ :=
    HCThree.commute_series_four
      hn inner hnested
  change ⁅inner⁻¹, outer⁆ = ⁅outer, inner⁆
  calc
    ⁅inner⁻¹, outer⁆ =
        ⁅inner, outer⁆⁻¹ := by
      simpa only [zpow_neg_one] using
        commutator_zpow_commute hcommute (-1)
    _ = ⁅outer, inner⁆ :=
      commutatorElement_inv inner outer

/-- The raw left triple word evaluates to the conventional left Hall-Petresco
triple correction in every class-three truncation. -/
lemma left_triple_word
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    inverseLeftTriple.eval (HPAtom.eval left right) =
      ⁅left, ⁅left, right⁆⁆ := by
  change ⁅⁅right, left⁆, left⁆ = ⁅left, ⁅left, right⁆⁆
  rw [← commutatorElement_inv left right]
  exact swap_n_four
    hn left right left

/-- The raw right triple word evaluates to the conventional right
Hall-Petresco triple correction in every class-three truncation. -/
lemma eval_triple_word
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    inverseTripleWord.eval (HPAtom.eval left right) =
      ⁅right, ⁅left, right⁆⁆ := by
  change ⁅⁅right, left⁆, right⁆ = ⁅right, ⁅left, right⁆⁆
  rw [← commutatorElement_inv left right]
  exact swap_n_four
    hn left right right

/-- Attach the standard left-triple coefficient profile to its raw
inverse-oriented support word. -/
def leftTriplePacket :
    RFPkt where
  word := inverseLeftTriple
  positive := by
    simp [inverseLeftTriple, rootSwapWord, CWord.hallPairBase,
      CWord.PBPos]
  profiles :=
    { profiles :=
        (homogeneousFormulaRecipe leftTriple).profiles
      profiles_leftDegree := by
        intro profile hprofile
        simpa [inverseLeftTriple, rootSwapWord,
          CWord.hallPairBase] using
            (homogeneousFormulaRecipe leftTriple)
              |>.profiles_leftDegree profile hprofile
      profiles_rightDegree := by
        intro profile hprofile
        simpa [inverseLeftTriple, rootSwapWord,
          CWord.hallPairBase] using
            (homogeneousFormulaRecipe leftTriple)
              |>.profiles_rightDegree profile hprofile }

/-- Attach the standard right-triple coefficient profile to its raw
inverse-oriented support word. -/
def inverseTriplePacket :
    RFPkt where
  word := inverseTripleWord
  positive := by
    simp [inverseTripleWord, rootSwapWord, CWord.hallPairBase,
      CWord.PBPos]
  profiles :=
    { profiles :=
        (homogeneousFormulaRecipe rightTriple).profiles
      profiles_leftDegree := by
        intro profile hprofile
        simpa [inverseTripleWord, rootSwapWord,
          CWord.hallPairBase] using
            (homogeneousFormulaRecipe rightTriple)
              |>.profiles_leftDegree profile hprofile
      profiles_rightDegree := by
        intro profile hprofile
        simpa [inverseTripleWord, rootSwapWord,
          CWord.hallPairBase] using
            (homogeneousFormulaRecipe rightTriple)
              |>.profiles_rightDegree profile hprofile }

@[simp]
lemma left_triple_packet :
    leftTriplePacket.word = inverseLeftTriple :=
  rfl

@[simp]
lemma inverse_triple_packet :
    inverseTriplePacket.word = inverseTripleWord :=
  rfl

@[simp]
lemma value_profiles_packet
    (leftExponent rightExponent : ℤ) :
    leftTriplePacket.profiles.value leftExponent rightExponent =
      coefficientValue leftTriple leftExponent rightExponent := by
  change
    (homogeneousFormulaRecipe leftTriple).value
        leftExponent rightExponent =
      coefficientValue leftTriple leftExponent rightExponent
  exact value_homogeneous_recipe
    leftTriple leftExponent rightExponent

@[simp]
lemma profiles_triple_packet
    (leftExponent rightExponent : ℤ) :
    inverseTriplePacket.profiles.value leftExponent rightExponent =
      coefficientValue rightTriple leftExponent rightExponent := by
  change
    (homogeneousFormulaRecipe rightTriple).value
        leftExponent rightExponent =
      coefficientValue rightTriple leftExponent rightExponent
  exact value_homogeneous_recipe
    rightTriple leftExponent rightExponent

/-- At cutoff four, the two raw-oriented triple words surround the basic
bracket with the standard class-three coefficients. -/
def three_n_four
    {d n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    TAPkta.{u} d n 1 1 where
  leftWeight_pos := by omega
  rightWeight_pos := by omega
  packets :=
    [leftTriplePacket,
      recollectionFormulaRecipe hallPair,
      inverseTriplePacket]
  word_erased_vocabulary := by
    intro packet hpacket
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpacket
    rcases hpacket with rfl | rfl | rfl
    · exact triple_erased_vocabulary hlow
    · simpa using base_erased_vocabulary (by omega)
    · exact inverse_triple_vocabulary hlow
  listEval_eq left right leftExponent rightExponent := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one,
      left_triple_packet, inverse_triple_packet,
      recollection_formula_recipe, erased_shape_pair,
      CWord.eval_pair_base]
    change
      inverseLeftTriple.eval (HPAtom.eval left right) ^
            (homogeneousFormulaRecipe leftTriple).value
              leftExponent rightExponent *
          (⁅left, right⁆ ^
                (homogeneousFormulaRecipe hallPair).value
                  leftExponent rightExponent *
            inverseTripleWord.eval (HPAtom.eval left right) ^
              (homogeneousFormulaRecipe rightTriple).value
                leftExponent rightExponent) =
        ⁅left ^ leftExponent, right ^ rightExponent⁆
    rw [value_homogeneous_recipe,
      value_homogeneous_recipe,
      value_homogeneous_recipe,
      left_triple_word hhigh, eval_triple_word hhigh]
    simpa only [coefficient_left_triple, coefficient_value_pair,
      coefficient_value_triple, mul_assoc] using
      (HCThree.element_zpow_class
        hhigh left right leftExponent rightExponent).symm

/-- Uniform explicit closure-supported signed-profile packet for every cutoff
at most four. -/
def n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    TAPkta.{u} d n 1 1 :=
  if hlow : n ≤ 3 then
    CLPacket.n_three
      hlow
  else
    three_n_four (by omega) hn

end CTPacket
end TCTex
end Submission

/-!
# Principal-word separation for the finite correction closure

The finite correction closure is intentionally a conservative erased-word
support universe.  Its principal bidegree is nevertheless rigid: the only
retained word of bidegree `(1, 1)` is the basic Hall-pair bracket.

At the source level this follows from standardization.  A source recipe of
bidegree `(1, 1)` belongs to the minimal inverse trace with one left and one
right label, and that trace contains exactly the basic bracket.  Closure-level
principal separation then reduces every retained principal word to that
source case.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace PWSep

open HACoeff
open BRSpec
open RRVocabu
open ITEvalua
open CLPacket
open CPSep
open UCSuppor
open URVocabu

/--
A standardized raw source recipe of principal bidegree is the basic Hall-pair
word.
-/
lemma IRecipe.erased_hallp_bideg
    (recipe : IRecipe)
    (hleftDegree : recipe.blockRecipe.leftDegree = 1)
    (hrightDegree : recipe.blockRecipe.rightDegree = 1) :
    recipe.blockRecipe.erasedShape = CWord.hallPairBase := by
  have hleftLinear : recipe.linear.leftDegree = 1 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hleftDegree
  have hrightLinear : recipe.linear.rightDegree = 1 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hrightDegree
  let left : Fin recipe.linear.leftDegree ↪o Fin 1 :=
    Fin.castLEOrderEmb hleftLinear.le
  let right : Fin recipe.linear.rightDegree ↪o Fin 1 :=
    Fin.castLEOrderEmb hrightLinear.le
  have hword :
      recipe.linear.instantiate left right =
        .commutator (.atom (Sum.inl 0)) (.atom (Sum.inr 0)) := by
    have htrace :=
      LRecipe.instme_leftr_labea
        recipe.linear recipe.mem_trace left right
    simpa [inverseLeftTrace, inverseRightTrace, inverseTraceList,
      inverseConjTrace, inverseConjugateAtom, labelledLeftAtoms,
      labelledRightAtoms] using htrace
  rw [IRecipe.blockRecipe, BRecipe.erased_shape_linear]
  rw [← recipe.linear.collapseWord_instantiate left right, hword]
  rfl

/-- Every principal-bidegree source recipe erases to the basic Hall word. -/
lemma base_recipes_bidegree
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ sourceRecipes n leftWeight rightWeight)
    (hleftDegree : recipe.leftDegree = 1)
    (hrightDegree : recipe.rightDegree = 1) :
    recipe.erasedShape = CWord.hallPairBase := by
  rcases initial_recipe_recipes hrecipe with
    ⟨source, _hsource, hsource⟩
  rw [← hsource] at hleftDegree hrightDegree ⊢
  exact
    IRecipe.erased_hallp_bideg
      source hleftDegree hrightDegree

/--
The conservative finite correction-closure skeleton contains no new
principal word.
-/
lemma erased_vocabulary_bidegree
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight)
    (hleftDegree : word.pairLeftDegree = 1)
    (hrightDegree : word.pairRightDegree = 1) :
    word = CWord.hallPairBase := by
  rcases
      shape_vocabulary_bidegree
        hword hleftDegree hrightDegree with
    ⟨recipe, hrecipe, hshape⟩
  rw [← hshape]
  exact
    base_recipes_bidegree
      hrecipe
      (by
        rw [← recipe.erased_left_degree, hshape]
        exact hleftDegree)
      (by
        rw [← recipe.erased_shape_degree, hshape]
        exact hrightDegree)

/--
Above the first surviving bracket cutoff, the finite skeleton contains the
basic Hall-pair word exactly once.
-/
lemma unique_split_vocabulary
    {n : ℕ}
    (hn : 2 < n) :
    ∃ beforeBasic afterBasic : List (CWord HPAtom),
      erasedShapeVocabulary n 1 1 =
          beforeBasic ++ CWord.hallPairBase :: afterBasic ∧
        CWord.hallPairBase ∉ beforeBasic ∧
          CWord.hallPairBase ∉ afterBasic := by
  have hbasic :
      CWord.hallPairBase ∈ erasedShapeVocabulary n 1 1 :=
    base_erased_vocabulary hn
  rcases List.mem_iff_append.mp hbasic with
    ⟨beforeBasic, afterBasic, hsplit⟩
  have hnodup :
      (erasedShapeVocabulary n 1 1).Nodup := by
    exact List.nodup_dedup _
  have hnodup' :
      (beforeBasic ++ CWord.hallPairBase :: afterBasic).Nodup := by
    simpa only [hsplit] using hnodup
  refine ⟨beforeBasic, afterBasic, hsplit, ?_, ?_⟩
  · intro hmem
    exact
      (List.nodup_append.mp hnodup').2.2
        CWord.hallPairBase hmem CWord.hallPairBase
          (by simp) rfl
  · exact (List.nodup_cons.mp (List.nodup_append.mp hnodup').2.1).1

end PWSep
end TCTex
end Submission

/-!
# Signed-profile formulas for same-word recipe chunks

An ordered chunk of recipes with one erased word canonically defines a
homogeneous signed-profile formula by summing the recipes' positive weighted
profiles.  This is the local coefficient aggregation required by recipe-chunk
alignment.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  ACAlign

open HACoeff
open CFSubsti
open
  UCAdapt
open HFPkt

namespace HFPkt

/--
Aggregate the singleton positive signed profiles of a same-word recipe chunk.
-/
def ofRecipeChunk
    (word : CWord HPAtom)
    (recipes : List BRecipe)
    (herasedShape :
      ∀ recipe ∈ recipes, recipe.erasedShape = word) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree where
  profiles :=
    recipes.map positiveWeightedProfile
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_map.mp hprofile with
      ⟨recipe, hrecipe, rfl⟩
    rw [positive_weighted_profile,
      herasedShape recipe hrecipe]
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_map.mp hprofile with
      ⟨recipe, hrecipe, rfl⟩
    rw [positive_weighted_degree,
      herasedShape recipe hrecipe]

@[simp]
lemma value_recipe_chunk
    (word : CWord HPAtom)
    (recipes : List BRecipe)
    (herasedShape :
      ∀ recipe ∈ recipes, recipe.erasedShape = word)
    (leftExponent rightExponent : ℤ) :
    (ofRecipeChunk word recipes herasedShape).value
        leftExponent rightExponent =
      (recipes.map fun recipe =>
        BRSpec.coefficientValue
          recipe leftExponent rightExponent).sum := by
  simp only [ofRecipeChunk, value, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro recipe _hrecipe
  exact
    weighted_profile_positive
      recipe leftExponent rightExponent

end HFPkt

namespace RFPkt

/-- Attach an aggregate same-word recipe chunk to its erased Hall word. -/
def ofRecipeChunk
    (word : CWord HPAtom)
    (positive : word.PBPos)
    (recipes : List BRecipe)
    (herasedShape :
      ∀ recipe ∈ recipes, recipe.erasedShape = word) :
    RFPkt where
  word :=
    word
  positive :=
    positive
  profiles :=
    HFPkt.ofRecipeChunk
      word recipes herasedShape

/-- The canonical same-word chunk packet satisfies the local alignment law. -/
def recipe_chunk_alignment
    (word : CWord HPAtom)
    (positive : word.PBPos)
    (recipes : List BRecipe)
    (herasedShape :
      ∀ recipe ∈ recipes, recipe.erasedShape = word) :
    RCAlign
      (ofRecipeChunk word positive recipes herasedShape)
      recipes where
  erased_shape_word :=
    herasedShape
  profiles_value_sum := by
    intro leftExponent rightExponent
    exact
      HFPkt.value_recipe_chunk
        word recipes herasedShape leftExponent rightExponent

end RFPkt

end
  ACAlign
end TCTex
end Submission

/-!
# Semantic recursive profile assignments on the finite correction closure

Recursive profile builders are useful only when their local source and
correction choices preserve the invariant required by a later collector.  This
file packages that invariant, proves it for every retained closure recipe by
well-founded induction, and transfers it to the deduplicated erased-word
skeleton.

The final section instantiates the interface with the concrete invariant that
one signed profile packet evaluates as the coefficient of a shape-equivalent
Hall-Petresco recipe.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  RASem

open HACoeff
open CFSubsti
open
  CFExp
open
  UCAdapt
open
  CRDecomp
open
  CRAssign
open
  FCAssign
open
  CWSkelet
open UCVocabu

/--
A profile assignment together with a word-local invariant for each chosen
signed-profile formula.
-/
structure PAMotive
    (n leftWeight rightWeight : ℕ)
    (profileMotive :
      ∀ word : CWord HPAtom,
        HFPkt
            word.pairLeftDegree word.pairRightDegree →
          Prop)
    extends SPAssign n leftWeight rightWeight where
  profiles_motive :
    ∀ word hword,
      profileMotive word
        (toSPAssign.profiles word hword)

namespace PAMotive

/--
Every packet emitted by a motive-preserving profile assignment retains the
word-local invariant of its chosen profile.
-/
lemma profile_motive_packets
    {n leftWeight rightWeight : ℕ}
    {profileMotive :
      ∀ word : CWord HPAtom,
        HFPkt
            word.pairLeftDegree word.pairRightDegree →
          Prop}
    (assignment :
      PAMotive
        n leftWeight rightWeight profileMotive)
    {packet : RFPkt}
    (hpacket :
      packet ∈ assignment.toSPAssign.toPackets) :
    profileMotive packet.word packet.profiles := by
  rcases List.mem_map.mp hpacket with ⟨word, hword, rfl⟩
  exact assignment.profiles_motive word.1 word.2

end PAMotive

/--
Local recursive profile builders together with an invariant preserved by
source and correction cases.
-/
structure RPSem
    (n leftWeight rightWeight : ℕ)
    extends RPKern n leftWeight rightWeight where
  profileMotive :
    ∀ word : CWord HPAtom,
      HFPkt
          word.pairLeftDegree word.pairRightDegree →
        Prop
  sourceProfiles_motive :
    ∀ recipe hrecipe,
      profileMotive recipe.erasedShape
        (toRPKern.sourceProfiles recipe hrecipe)
  correctionProfiles_motive :
    ∀ left right hleft hright leftProfiles rightProfiles,
      profileMotive left.erasedShape leftProfiles →
        profileMotive right.erasedShape rightProfiles →
          profileMotive (left.correction right).erasedShape
            (toRPKern.correctionProfiles
              left right hleft hright leftProfiles rightProfiles)

namespace RPSem

/--
The semantic invariant propagates from source recipes through the complete
retained correction closure.
-/
theorem profiles_motive_recipes
    {n leftWeight rightWeight : ℕ}
    (kernel :
      RPSem n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight) :
    ∃ profiles :
        HFPkt
          recipe.erasedShape.pairLeftDegree
          recipe.erasedShape.pairRightDegree,
      kernel.profileMotive recipe.erasedShape profiles := by
  refine closure_recipes_induction
    (motive := fun nextRecipe =>
      ∃ profiles :
          HFPkt
            nextRecipe.erasedShape.pairLeftDegree
            nextRecipe.erasedShape.pairRightDegree,
        kernel.profileMotive nextRecipe.erasedShape profiles)
    hleftWeight hrightWeight ?_ ?_ recipe hrecipe
  · intro sourceRecipe hsourceRecipe
    exact
      ⟨kernel.sourceProfiles sourceRecipe hsourceRecipe,
        kernel.sourceProfiles_motive sourceRecipe hsourceRecipe⟩
  · intro left right hleft hright hleftProfiles hrightProfiles
    rcases hleftProfiles with ⟨leftProfiles, hleftProfiles⟩
    rcases hrightProfiles with ⟨rightProfiles, hrightProfiles⟩
    exact
      ⟨kernel.correctionProfiles
          left right hleft hright leftProfiles rightProfiles,
        kernel.correctionProfiles_motive
          left right hleft hright leftProfiles rightProfiles
            hleftProfiles hrightProfiles⟩

/--
Choosing a retained representative transfers the semantic invariant to every
word in the deduplicated finite closure skeleton.
-/
theorem profiles_motive_vocabulary
    {n leftWeight rightWeight : ℕ}
    (kernel :
      RPSem n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃ profiles :
        HFPkt
          word.pairLeftDegree word.pairRightDegree,
      kernel.profileMotive word profiles := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, rfl⟩
  exact
    kernel.profiles_motive_recipes
      hleftWeight hrightWeight hrecipe

/--
Compile a semantic recursive kernel to one global finite-closure assignment
while retaining its word-local invariant.
-/
noncomputable def profileAssignmentMotive
    {n leftWeight rightWeight : ℕ}
    (kernel :
      RPSem n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    PAMotive
      n leftWeight rightWeight kernel.profileMotive where
  toSPAssign :=
    { profiles := fun _word hword =>
        Exists.choose
          (kernel.profiles_motive_vocabulary
            hleftWeight hrightWeight hword) }
  profiles_motive := by
    intro _word hword
    exact
      Exists.choose_spec
        (kernel.profiles_motive_vocabulary
          hleftWeight hrightWeight hword)

end RPSem

/--
Concrete word-local invariant: the selected signed profile evaluates as the
coefficient of one shape-equivalent Hall-Petresco recipe.
-/
def RecipeProfile
    (word : CWord HPAtom)
    (profiles :
      HFPkt
        word.pairLeftDegree word.pairRightDegree) :
    Prop :=
  ∃ recipe : BRecipe,
    recipe.erasedShape = word ∧
      ∀ leftExponent rightExponent : ℤ,
        profiles.value leftExponent rightExponent =
          BRSpec.coefficientValue
            recipe leftExponent rightExponent

/--
Singleton positive recipe profiles form a semantic recursive kernel on every
finite correction closure.
-/
def positiveCoefficientSemantic
    (n leftWeight rightWeight : ℕ) :
    RPSem n leftWeight rightWeight where
  sourceProfiles recipe _ :=
    homogeneousFormulaRecipe recipe
  correctionProfiles left right _ _ _ _ :=
    homogeneousFormulaRecipe (left.correction right)
  profileMotive :=
    RecipeProfile
  sourceProfiles_motive recipe _ :=
    ⟨recipe, rfl, fun leftExponent rightExponent =>
      value_homogeneous_recipe
        recipe leftExponent rightExponent⟩
  correctionProfiles_motive left right _ _ _ _ _ _ :=
    ⟨left.correction right, rfl, fun leftExponent rightExponent =>
      value_homogeneous_recipe
        (left.correction right) leftExponent rightExponent⟩

/--
The concrete semantic kernel chooses one recipe-coefficient profile for every
word in the finite correction-closure skeleton.
-/
noncomputable def positiveProfileAssignment
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    PAMotive
      n leftWeight rightWeight RecipeProfile :=
  (positiveCoefficientSemantic n leftWeight rightWeight)
    |>.profileAssignmentMotive hleftWeight hrightWeight

/--
Every profile chosen by the concrete semantic assignment has a
shape-equivalent recipe whose generalized-binomial coefficient it evaluates.
-/
lemma recipe_profiles_assignment
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃ recipe : BRecipe,
      recipe.erasedShape = word ∧
        ∀ leftExponent rightExponent : ℤ,
          ((positiveProfileAssignment
              n leftWeight rightWeight hleftWeight hrightWeight)
            |>.toSPAssign.profiles word hword).value
              leftExponent rightExponent =
            BRSpec.coefficientValue
              recipe leftExponent rightExponent := by
  exact
    (positiveProfileAssignment
      n leftWeight rightWeight hleftWeight hrightWeight)
      |>.profiles_motive word hword

/--
Attach the concretely selected recipe-coefficient profile to one vocabulary
word as a recollection packet.
-/
noncomputable def positiveFormulaPacket
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    RFPkt where
  word :=
    word
  positive :=
    bidegree_positive_vocabulary hword
  profiles :=
    (positiveProfileAssignment
      n leftWeight rightWeight hleftWeight hrightWeight)
      |>.toSPAssign.profiles word hword

/--
The selected recollection packet still evaluates as one shape-equivalent
recipe coefficient.
-/
lemma
    profiles_formula_packet
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃ recipe : BRecipe,
      recipe.erasedShape = word ∧
        ∀ leftExponent rightExponent : ℤ,
          (positiveFormulaPacket
            hleftWeight hrightWeight word hword).profiles.value
              leftExponent rightExponent =
            BRSpec.coefficientValue
              recipe leftExponent rightExponent := by
  exact
    recipe_profiles_assignment
      hleftWeight hrightWeight word hword

/--
Every packet in the complete concrete semantic assignment evaluates as one
shape-equivalent Hall-Petresco recipe coefficient.
-/
lemma
    profiles_assignment_packets
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {packet : RFPkt}
    (hpacket :
      packet ∈
        ((positiveProfileAssignment
          n leftWeight rightWeight hleftWeight hrightWeight)
          |>.toSPAssign.toPackets)) :
    ∃ recipe : BRecipe,
      recipe.erasedShape = packet.word ∧
        ∀ leftExponent rightExponent : ℤ,
          packet.profiles.value leftExponent rightExponent =
            BRSpec.coefficientValue
              recipe leftExponent rightExponent := by
  exact
    (positiveProfileAssignment
      n leftWeight rightWeight hleftWeight hrightWeight)
      |>.profile_motive_packets hpacket

/--
After substituting arbitrary symbolic parents, the selected recollection
factor evaluates as a shape-equivalent recipe factor.
-/
lemma
    recollection_formula_packet
    {d cutoff n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta d r}
    {ι : Type}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight)
    (normalizer :
      WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (e : ι → HEFam H) :
    ∃ recipe : BRecipe,
      recipe.erasedShape = word ∧
        ((positiveFormulaPacket
          hleftWeight hrightWeight word hword).symbolicFactor
            normalizer left right).eval (n := cutoff) e =
          recipe.erasedShape.eval
              (HPAtom.eval
                (left.wordValue (n := cutoff))
                (right.wordValue (n := cutoff))) ^
            BRSpec.coefficientValue recipe
              (left.coefficient.eval e) (right.coefficient.eval e) := by
  rcases
      profiles_formula_packet
        hleftWeight hrightWeight word hword with
    ⟨recipe, hrecipe, hvalue⟩
  refine ⟨recipe, hrecipe, ?_⟩
  rw [eval_symbolicFactor, hvalue, hrecipe]
  rfl

/--
Every symbolic factor compiled from the complete concrete semantic assignment
has an explicit Hall-Petresco recipe witness for its substituted word and
evaluation.
-/
lemma
    recipe_positive_assignment
    {d cutoff n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta d r}
    {ι : Type}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (normalizer :
      WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (e : ι → HEFam H)
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈
        symbolicFactors normalizer
          ((positiveProfileAssignment
            n leftWeight rightWeight hleftWeight hrightWeight)
            |>.toSPAssign.toPackets)
          left right) :
    ∃ recipe : BRecipe,
      factor.word =
          CWord.hallPairBind
            left.word right.word recipe.erasedShape ∧
        factor.eval (n := cutoff) e =
          recipe.erasedShape.eval
              (HPAtom.eval
                (left.wordValue (n := cutoff))
                (right.wordValue (n := cutoff))) ^
            BRSpec.coefficientValue recipe
              (left.coefficient.eval e) (right.coefficient.eval e) := by
  rcases packet_symbolic_factors hfactor with
    ⟨packet, hpacket, rfl⟩
  rcases
      profiles_assignment_packets
        hleftWeight hrightWeight hpacket with
    ⟨recipe, hrecipe, hvalue⟩
  refine ⟨recipe, ?_, ?_⟩
  · rw [RFPkt.word_symbolicFactor,
      RFPkt.boundWord, hrecipe]
  · rw [eval_symbolicFactor, hvalue, hrecipe]

end
  RASem
end TCTex
end Submission

/-!
# Class-three source-word separation for the finite correction closure

Below weight four, a retained finite-closure recipe cannot be a correction:
both of its positive parents already have weight at least two.  The remaining
source recipes can be read in the minimal labelled inverse trace.  At
bidegrees `(2, 1)` and `(1, 2)`, that trace has exactly the two raw-oriented
triple words.

Consequently, at cutoff at most four the finite skeleton contains only the
basic bracket and those two triple words.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace SWSep

open HACoeff
open BRSpec
open RRVocabu
open ITEvalua
open CTPacket
open CLPacket
open PWSep
open CRDecomp
open UCSuppor
open UCVocabu
open URVocabu

/--
A standardized raw source recipe of bidegree `(2, 1)` is the raw-oriented
left triple word.
-/
lemma IRecipe.erased_invle_worbi
    (recipe : IRecipe)
    (hleftDegree : recipe.blockRecipe.leftDegree = 2)
    (hrightDegree : recipe.blockRecipe.rightDegree = 1) :
    recipe.blockRecipe.erasedShape = inverseLeftTriple := by
  have hleftLinear : recipe.linear.leftDegree = 2 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hleftDegree
  have hrightLinear : recipe.linear.rightDegree = 1 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hrightDegree
  let left : Fin recipe.linear.leftDegree ↪o Fin 2 :=
    Fin.castLEOrderEmb hleftLinear.le
  let right : Fin recipe.linear.rightDegree ↪o Fin 1 :=
    Fin.castLEOrderEmb hrightLinear.le
  have htrace :=
    LRecipe.instme_leftr_labea
      recipe.linear recipe.mem_trace left right
  have hword :
      recipe.linear.instantiate left right =
        .commutator
          (rootSwapWord
            (.commutator (.atom (Sum.inl 1)) (.atom (Sum.inr 0))))
          (.atom (Sum.inl 0)) := by
    have htrace' :
        recipe.linear.instantiate left right =
            .commutator (.atom (Sum.inl 1)) (.atom (Sum.inr 0)) ∨
          recipe.linear.instantiate left right =
              .commutator
                (rootSwapWord
                  (.commutator (.atom (Sum.inl 1)) (.atom (Sum.inr 0))))
                (.atom (Sum.inl 0)) ∨
            recipe.linear.instantiate left right =
              .commutator (.atom (Sum.inl 0)) (.atom (Sum.inr 0)) := by
      simpa [left, right, inverseLeftTrace, inverseRightTrace,
        inverseTraceList, inverseConjTrace, inverseConjugateAtom,
        labelledLeftAtoms, labelledRightAtoms] using htrace
    rcases htrace' with hword | hword | hword
    · have hcollapse := congrArg collapseWord hword
      rw [recipe.linear.collapseWord_instantiate left right] at hcollapse
      have hdegree :=
        congrArg (fun word => word.pairLeftDegree) hcollapse
      simp [LRecipe.erased_left_degree, collapseWord, collapseLabel,
        hleftLinear] at hdegree
    · exact hword
    · have hcollapse := congrArg collapseWord hword
      rw [recipe.linear.collapseWord_instantiate left right] at hcollapse
      have hdegree :=
        congrArg (fun word => word.pairLeftDegree) hcollapse
      simp [LRecipe.erased_left_degree, collapseWord, collapseLabel,
        hleftLinear] at hdegree
  rw [IRecipe.blockRecipe, BRecipe.erased_shape_linear]
  rw [← recipe.linear.collapseWord_instantiate left right, hword]
  rfl

/--
A standardized raw source recipe of bidegree `(1, 2)` is the raw-oriented
right triple word.
-/
lemma IRecipe.erased_invri_worbi
    (recipe : IRecipe)
    (hleftDegree : recipe.blockRecipe.leftDegree = 1)
    (hrightDegree : recipe.blockRecipe.rightDegree = 2) :
    recipe.blockRecipe.erasedShape = inverseTripleWord := by
  have hleftLinear : recipe.linear.leftDegree = 1 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hleftDegree
  have hrightLinear : recipe.linear.rightDegree = 2 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hrightDegree
  let left : Fin recipe.linear.leftDegree ↪o Fin 1 :=
    Fin.castLEOrderEmb hleftLinear.le
  let right : Fin recipe.linear.rightDegree ↪o Fin 2 :=
    Fin.castLEOrderEmb hrightLinear.le
  have htrace :=
    LRecipe.instme_leftr_labea
      recipe.linear recipe.mem_trace left right
  have hword :
      recipe.linear.instantiate left right =
        .commutator
          (rootSwapWord
            (.commutator (.atom (Sum.inl 0)) (.atom (Sum.inr 1))))
          (.atom (Sum.inr 0)) := by
    have htrace' :
        recipe.linear.instantiate left right =
            .commutator (.atom (Sum.inl 0)) (.atom (Sum.inr 0)) ∨
          recipe.linear.instantiate left right =
              .commutator (.atom (Sum.inl 0)) (.atom (Sum.inr 1)) ∨
            recipe.linear.instantiate left right =
              .commutator
                (rootSwapWord
                  (.commutator (.atom (Sum.inl 0)) (.atom (Sum.inr 1))))
                (.atom (Sum.inr 0)) := by
      simpa [left, right, inverseLeftTrace, inverseRightTrace,
        inverseTraceList, inverseConjTrace, inverseConjugateAtom,
        labelledLeftAtoms, labelledRightAtoms] using htrace
    rcases htrace' with hword | hword | hword
    · have hcollapse := congrArg collapseWord hword
      rw [recipe.linear.collapseWord_instantiate left right] at hcollapse
      have hdegree :=
        congrArg (fun word => word.pairRightDegree) hcollapse
      simp [LRecipe.erased_shape_degree, collapseWord, collapseLabel,
        hrightLinear] at hdegree
    · have hcollapse := congrArg collapseWord hword
      rw [recipe.linear.collapseWord_instantiate left right] at hcollapse
      have hdegree :=
        congrArg (fun word => word.pairRightDegree) hcollapse
      simp [LRecipe.erased_shape_degree, collapseWord, collapseLabel,
        hrightLinear] at hdegree
    · exact hword
  rw [IRecipe.blockRecipe, BRecipe.erased_shape_linear]
  rw [← recipe.linear.collapseWord_instantiate left right, hword]
  rfl

/-- Every `(2, 1)` source recipe erases to the raw-oriented left triple word. -/
lemma triple_recipes_bidegree
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ sourceRecipes n leftWeight rightWeight)
    (hleftDegree : recipe.leftDegree = 2)
    (hrightDegree : recipe.rightDegree = 1) :
    recipe.erasedShape = inverseLeftTriple := by
  rcases initial_recipe_recipes hrecipe with
    ⟨source, _hsource, hsource⟩
  rw [← hsource] at hleftDegree hrightDegree ⊢
  exact
    IRecipe.erased_invle_worbi
      source hleftDegree hrightDegree

/-- Every `(1, 2)` source recipe erases to the raw-oriented right triple word. -/
lemma erased_recipes_bidegree
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ sourceRecipes n leftWeight rightWeight)
    (hleftDegree : recipe.leftDegree = 1)
    (hrightDegree : recipe.rightDegree = 2) :
    recipe.erasedShape = inverseTripleWord := by
  rcases initial_recipe_recipes hrecipe with
    ⟨source, _hsource, hsource⟩
  rw [← hsource] at hleftDegree hrightDegree ⊢
  exact
    IRecipe.erased_invri_worbi
      source hleftDegree hrightDegree

/--
Every `(2, 1)` source recipe has the standard left-triple binomial
coefficient.
-/
lemma choose_recipes_bidegree
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ sourceRecipes n leftWeight rightWeight)
    (hleftDegree : recipe.leftDegree = 2)
    (hrightDegree : recipe.rightDegree = 1)
    (leftExponent rightExponent : ℤ) :
    coefficientValue recipe leftExponent rightExponent =
      Ring.choose leftExponent 2 * rightExponent := by
  rcases initial_recipe_recipes hrecipe with
    ⟨source, _hsource, hsource⟩
  rw [← hsource] at hleftDegree hrightDegree ⊢
  have hleftLinear : source.linear.leftDegree = 2 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hleftDegree
  have hrightLinear : source.linear.rightDegree = 1 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hrightDegree
  simp [coefficientValue, IRecipe.blockRecipe, BRecipe.ofLinear,
    hleftLinear, hrightLinear]

/--
Every `(1, 2)` source recipe has the standard right-triple binomial
coefficient.
-/
lemma coefficient_recipes_bidegree
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ sourceRecipes n leftWeight rightWeight)
    (hleftDegree : recipe.leftDegree = 1)
    (hrightDegree : recipe.rightDegree = 2)
    (leftExponent rightExponent : ℤ) :
    coefficientValue recipe leftExponent rightExponent =
      leftExponent * Ring.choose rightExponent 2 := by
  rcases initial_recipe_recipes hrecipe with
    ⟨source, _hsource, hsource⟩
  rw [← hsource] at hleftDegree hrightDegree ⊢
  have hleftLinear : source.linear.leftDegree = 1 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hleftDegree
  have hrightLinear : source.linear.rightDegree = 2 := by
    simpa [IRecipe.blockRecipe, BRecipe.ofLinear] using hrightDegree
  simp [coefficientValue, IRecipe.blockRecipe, BRecipe.ofLinear,
    hleftLinear, hrightLinear]

/--
Every retained root-weight recipe below weight four was already present in
the source vocabulary.
-/
lemma source_recipes_four
    {n : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosureRecipes n 1 1)
    (hweight : weightedWordWeight 1 1 recipe < 4) :
    recipe ∈ sourceRecipes n 1 1 := by
  rcases
      recipes_or_parent
        (by omega) (by omega) hrecipe with
    hsource | ⟨left, _hleft, right, _hright, heq, _hleftLt, _hrightLt⟩
  · exact hsource
  · have hleftLeftPositive := leftDegree_pos left
    have hleftRightPositive := rightDegree_pos left
    have hrightLeftPositive := leftDegree_pos right
    have hrightRightPositive := rightDegree_pos right
    rw [heq, weighted_weight_correction] at hweight
    simp only [weighted_word_weight, Nat.mul_one] at hweight
    omega

/--
Every retained root-weight `(2, 1)` recipe has the standard left-triple
binomial coefficient.
-/
lemma coefficient_choose_bidegree
    {n : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosureRecipes n 1 1)
    (hleftDegree : recipe.leftDegree = 2)
    (hrightDegree : recipe.rightDegree = 1)
    (leftExponent rightExponent : ℤ) :
    coefficientValue recipe leftExponent rightExponent =
      Ring.choose leftExponent 2 * rightExponent := by
  apply
    choose_recipes_bidegree
      (source_recipes_four
        hrecipe (by simp [weighted_word_weight, hleftDegree, hrightDegree]))
      hleftDegree hrightDegree

/--
Every retained root-weight `(1, 2)` recipe has the standard right-triple
binomial coefficient.
-/
lemma value_choose_bidegree
    {n : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosureRecipes n 1 1)
    (hleftDegree : recipe.leftDegree = 1)
    (hrightDegree : recipe.rightDegree = 2)
    (leftExponent rightExponent : ℤ) :
    coefficientValue recipe leftExponent rightExponent =
      leftExponent * Ring.choose rightExponent 2 := by
  apply
    coefficient_recipes_bidegree
      (source_recipes_four
        hrecipe (by simp [weighted_word_weight, hleftDegree, hrightDegree]))
      hleftDegree hrightDegree

/--
At root weights and cutoff at most four, every finite-skeleton word is one of
the two raw-oriented triple words or the basic Hall-pair bracket.
-/
theorem or_vocabulary_four
    {n : ℕ}
    (hn : n ≤ 4)
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n 1 1) :
    word = inverseLeftTriple ∨
      word = CWord.hallPairBase ∨
        word = inverseTripleWord := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, hshape⟩
  have hweight :
      weightedWordWeight 1 1 recipe < 4 :=
    (weighted_closure_recipes
      hrecipe).trans_le hn
  have hsource :
      recipe ∈ sourceRecipes n 1 1 :=
    source_recipes_four
      hrecipe hweight
  have hdegrees :
      recipe.leftDegree + recipe.rightDegree < 4 := by
    simpa [weighted_word_weight] using hweight
  have hleftPositive := leftDegree_pos recipe
  have hrightPositive := rightDegree_pos recipe
  have hdegreeCases :
      (recipe.leftDegree = 1 ∧ recipe.rightDegree = 1) ∨
        (recipe.leftDegree = 1 ∧ recipe.rightDegree = 2) ∨
          (recipe.leftDegree = 2 ∧ recipe.rightDegree = 1) := by
    omega
  rcases hdegreeCases with
    ⟨hleftOne, hrightOne⟩ |
      ⟨hleftOne, hrightTwo⟩ |
        ⟨hleftTwo, hrightOne⟩
  · exact
      Or.inr
        (Or.inl
          (by
            rw [← hshape]
            exact
              base_recipes_bidegree
                hsource hleftOne hrightOne))
  · exact
      Or.inr
        (Or.inr
          (by
            rw [← hshape]
            exact
              erased_recipes_bidegree
                hsource hleftOne hrightTwo))
  · exact
      Or.inl
        (by
          rw [← hshape]
          exact
            triple_recipes_bidegree
              hsource hleftTwo hrightOne)

/--
Above weight three and through cutoff four, membership in the finite skeleton
is exactly membership in the three raw-oriented class-three words.
-/
lemma erased_vocabulary_four
    {n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    {word : CWord HPAtom} :
    word ∈ erasedShapeVocabulary n 1 1 ↔
      word = inverseLeftTriple ∨
        word = CWord.hallPairBase ∨
          word = inverseTripleWord := by
  constructor
  · exact
      or_vocabulary_four
        hhigh
  · intro hword
    rcases hword with hword | hword | hword
    · rw [hword]
      exact triple_erased_vocabulary hlow
    · rw [hword]
      exact base_erased_vocabulary (by omega)
    · rw [hword]
      exact inverse_triple_vocabulary hlow

/--
At cutoff four, the deduplicated finite skeleton has exactly the three
raw-oriented class-three words as a finite set.
-/
lemma finset_vocabulary_four
    {n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    (erasedShapeVocabulary n 1 1).toFinset =
      {inverseLeftTriple, CWord.hallPairBase,
        inverseTripleWord} := by
  ext word
  simp only [List.mem_toFinset]
  rw [erased_vocabulary_four hlow hhigh]
  simp

end SWSep
end TCTex
end Submission

/-!
# Principal words in ordered finite-closure packets

The correction-closure skeleton is a support universe rather than a schedule.
Nevertheless, every ordered packet supported in that universe inherits its
principal-word rigidity: a packet occurrence of bidegree `(1, 1)` must carry
the literal basic Hall-pair bracket.

For the explicit packets through cutoff four, the basic word also occurs
exactly once in the ordered list.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CPWord

universe u

open HACoeff
open BRSpec
open CFSubsti
open
  UCAll
open CTPacket
open CLPacket
open
  PWSep
open
  UCAdapt
open
  UCSuppor

namespace OBPkt

/--
The mapped packet-word list contains exactly one occurrence of the literal
basic Hall-pair bracket.
-/
def UniqueBaseOccurrence
    {n leftWeight rightWeight : ℕ}
    (packet : OBPkt n leftWeight rightWeight) :
    Prop :=
  ∃ beforeBasic afterBasic : List (CWord HPAtom),
    packet.packets.map RFPkt.word =
        beforeBasic ++ CWord.hallPairBase :: afterBasic ∧
      CWord.hallPairBase ∉ beforeBasic ∧
        CWord.hallPairBase ∉ afterBasic

/-- Every principal-bidegree occurrence in an ordered closure-supported
packet is the literal basic Hall-pair bracket. -/
lemma pair_packets_bidegree
    {n leftWeight rightWeight : ℕ}
    (packet : OBPkt n leftWeight rightWeight)
    {nextPacket : RFPkt}
    (hnextPacket : nextPacket ∈ packet.packets)
    (hleftDegree : nextPacket.word.pairLeftDegree = 1)
    (hrightDegree : nextPacket.word.pairRightDegree = 1) :
    nextPacket.word = CWord.hallPairBase := by
  exact
    erased_vocabulary_bidegree
      (packet.word_erased_vocabulary nextPacket hnextPacket)
      hleftDegree hrightDegree

end OBPkt

namespace TAPkta

/-- The all-integral packet boundary inherits principal-word rigidity from
its ordered finite-support packet. -/
lemma pair_packets_bidegree
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    {nextPacket : RFPkt}
    (hnextPacket : nextPacket ∈ packet.packets)
    (hleftDegree : nextPacket.word.pairLeftDegree = 1)
    (hrightDegree : nextPacket.word.pairRightDegree = 1) :
    nextPacket.word = CWord.hallPairBase := by
  exact
    OBPkt.pair_packets_bidegree
      packet.toOBPkt hnextPacket hleftDegree
        hrightDegree

end TAPkta

/-- The singleton class-two packet has one literal basic-word occurrence. -/
lemma singleton_unique_occurrence
    {d n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    OBPkt.UniqueBaseOccurrence
      ((singleton_n_three (d := d) hlow hhigh)
        |>.toOBPkt) := by
  refine ⟨[], [], ?_⟩
  simp [singleton_n_three,
    PFSubsti.TAPkt.n_three,
    truncAllPacket,
    formulaPacketsRecipes,
    recollection_formula_recipe, erased_shape_pair]

/-- Every explicit low-cutoff packet above the first surviving bracket has
one literal basic-word occurrence. -/
lemma n_base_occurrence
    {d n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    OBPkt.UniqueBaseOccurrence
      (CLPacket.n_three
        (d := d) hhigh).toOBPkt := by
  simpa [CLPacket.n_three,
    show ¬n ≤ 2 by omega] using
      singleton_unique_occurrence (d := d) hlow hhigh

/-- The raw-oriented class-three packet has one literal basic-word
occurrence between its two triple corrections. -/
lemma four_unique_occurrence
    {d n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    OBPkt.UniqueBaseOccurrence
      ((three_n_four (d := d) hlow hhigh)
        |>.toOBPkt) := by
  refine ⟨[inverseLeftTriple], [inverseTripleWord], ?_⟩
  simp [three_n_four, inverseLeftTriple,
    inverseTripleWord, rootSwapWord, CWord.hallPairBase,
    recollection_formula_recipe, erased_shape_pair]

/-- Every explicit packet through cutoff four above the first surviving
bracket has one literal basic-word occurrence. -/
lemma n_four_occurrence
    {d n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 4) :
    OBPkt.UniqueBaseOccurrence
      (n_four (d := d) hhigh).toOBPkt := by
  by_cases hn3 : n ≤ 3
  · simpa [n_four, hn3] using
      n_base_occurrence (d := d) hlow hn3
  · simpa [n_four, hn3] using
      four_unique_occurrence
        (d := d) (by omega) hhigh

end
  CPWord
end TCTex
end Submission

/-!
# Principal words in finite-closure profile assignments

A finite-closure signed-profile assignment enumerates the deduplicated erased
support skeleton and attaches one homogeneous profile formula to every word.
The skeleton's principal-word separation therefore transports directly to the
assigned packet list.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  APWord

open CFSubsti
open
  PWSep
open
  FCAssign

namespace SPAssign

/-- Assigned packet words remain duplicate-free because the finite closure
skeleton was deduplicated before profiles were attached. -/
lemma nodup_word_packets
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight) :
    (assignment.toPackets.map RFPkt.word).Nodup := by
  rw [assignment.word_packets]
  exact List.nodup_dedup _

/-- Every assigned packet of principal bidegree carries the literal basic
Hall-pair word. -/
lemma base_packets_bidegree
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    {packet : RFPkt}
    (hpacket : packet ∈ assignment.toPackets)
    (hleftDegree : packet.word.pairLeftDegree = 1)
    (hrightDegree : packet.word.pairRightDegree = 1) :
    packet.word = CWord.hallPairBase := by
  exact
    erased_vocabulary_bidegree
      (assignment.word_vocabulary_packets hpacket)
      hleftDegree hrightDegree

/--
Above the first surviving bracket cutoff, mapped assigned packet words split
uniquely around `hallPairBase`.
-/
lemma unique_split_packets
    {n : ℕ}
    (assignment : SPAssign n 1 1)
    (hn : 2 < n) :
    ∃ beforeBasic afterBasic : List (CWord HPAtom),
      assignment.toPackets.map RFPkt.word =
          beforeBasic ++ CWord.hallPairBase :: afterBasic ∧
        CWord.hallPairBase ∉ beforeBasic ∧
          CWord.hallPairBase ∉ afterBasic := by
  rw [assignment.word_packets]
  exact unique_split_vocabulary hn

end SPAssign

end
  APWord
end TCTex
end Submission

/-!
# Canonical recipe chunks on the finite correction closure

Group retained correction-closure recipes by their erased Hall word, following
the canonical deduplicated vocabulary order.  Each same-word chunk has the
aggregate signed-profile formula constructed by the recipe-chunk boundary.

The resulting fixed profile assignment and its recipe-chunk alignment witness
are unconditional.  The remaining semantic theorem is the ordered
all-integral recollection law for the flattened canonical recipe list.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  ACAlign

open HACoeff
open CFSubsti
open
  FCAssign
open
  UCSuppor
open UCVocabu

/-- Retained closure recipes with one fixed erased Hall word. -/
noncomputable def recipesForWord
    (n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    List BRecipe := by
  classical
  exact
    (correctionClosureRecipes n leftWeight rightWeight).filter
      fun recipe => recipe.erasedShape = word

/-- Every recipe in the canonical per-word chunk has the requested shape. -/
lemma erased_shape_recipes
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ recipesForWord n leftWeight rightWeight word) :
    recipe.erasedShape = word := by
  classical
  exact of_decide_eq_true (List.mem_filter.mp hrecipe).2

/-- Canonical same-word chunks, ordered by the deduplicated closure vocabulary. -/
noncomputable def canonicalRecipeChunks
    (n leftWeight rightWeight : ℕ) :
    List (List BRecipe) :=
  (erasedShapeVocabulary n leftWeight rightWeight).attach.map fun word =>
    recipesForWord n leftWeight rightWeight word.1

/-- Flatten the canonical same-word chunks into one fixed ordered recipe list. -/
noncomputable def canonicalRecipes
    (n leftWeight rightWeight : ℕ) :
    List BRecipe :=
  (canonicalRecipeChunks n leftWeight rightWeight).flatten

/-- The recollection packet attached to one canonical vocabulary word. -/
noncomputable def canonicalPacketWord
    {n leftWeight rightWeight : ℕ}
    (word :
      { word // word ∈ erasedShapeVocabulary n leftWeight rightWeight }) :
    RFPkt :=
  RFPkt.ofRecipeChunk
    word.1
    (bidegree_positive_vocabulary word.2)
    (recipesForWord n leftWeight rightWeight word.1)
    (fun _recipe hrecipe =>
      erased_shape_recipes hrecipe)

/-- Canonical coefficient-sum profiles attached to every retained erased word. -/
noncomputable def canonicalProfileAssignment
    (n leftWeight rightWeight : ℕ) :
    SPAssign n leftWeight rightWeight where
  profiles word _hword :=
    HFPkt.ofRecipeChunk
      word
      (recipesForWord n leftWeight rightWeight word)
      (fun _recipe hrecipe =>
        erased_shape_recipes hrecipe)

/-- Attaching canonical profiles maps exactly to the canonical per-word packets. -/
lemma packets_profile_assignment
    (n leftWeight rightWeight : ℕ) :
    (canonicalProfileAssignment
      n leftWeight rightWeight).toPackets =
      (erasedShapeVocabulary n leftWeight rightWeight).attach.map
        canonicalPacketWord := by
  rfl

/--
The canonical fixed assignment is aligned with the flattened canonical recipe
list by construction.
-/
noncomputable def canonicalChunkAlignment
    (n leftWeight rightWeight : ℕ) :
    SPAssign.RCAlign
      (canonicalProfileAssignment n leftWeight rightWeight)
      (canonicalRecipes n leftWeight rightWeight) where
  chunks :=
    canonicalRecipeChunks n leftWeight rightWeight
  packets_chunks := by
    rw [packets_profile_assignment]
    unfold canonicalRecipeChunks
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro word _hword
    exact
      RFPkt.recipe_chunk_alignment
        word.1
        (bidegree_positive_vocabulary word.2)
        (recipesForWord n leftWeight rightWeight word.1)
        (fun _recipe hrecipe =>
          erased_shape_recipes hrecipe)
  flatten_chunks :=
    rfl

end
  ACAlign
end TCTex
end Submission

/-!
# Principal weights in ordered finite-closure packets

A unique literal Hall-pair occurrence can survive in an ordered cutoff packet
only when the combined parent weight remains strictly below cutoff.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CPWord

universe u

open
  CCTrunc
open
  CFSubsti
open
  UCAll
open
  UCSuppor

namespace OBPkt

/--
If an ordered closure-supported packet contains its unique literal basic
Hall-pair bracket, the combined parent weight lies below cutoff.
-/
lemma unique_base_occurrence
    {n leftWeight rightWeight : ℕ}
    (packet : OBPkt n leftWeight rightWeight)
    (hunique :
      OBPkt.UniqueBaseOccurrence packet) :
    leftWeight + rightWeight < n := by
  rcases hunique with ⟨beforeBasic, afterBasic, hmap, _hbefore, _hafter⟩
  have hbase :
      CWord.hallPairBase ∈
        packet.packets.map RFPkt.word := by
    rw [hmap]
    simp
  rcases List.mem_map.mp hbase with
    ⟨nextPacket, hnextPacket, hword⟩
  have hweight :=
    packet.packet_weight_cutoff hnextPacket
  simpa [packetWeight, hword, HPAtom.weight,
    CWord.hallPairBase] using hweight

end OBPkt

namespace TAPkta

/--
The all-integral finite-closure packet inherits the principal combined-weight
cutoff bound from its ordered support packet.
-/
lemma unique_base_occurrence
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (hunique :
      OBPkt.UniqueBaseOccurrence
        packet.toOBPkt) :
    leftWeight + rightWeight < n :=
  OBPkt.unique_base_occurrence
    packet.toOBPkt hunique

end TAPkta

end
  CPWord
end TCTex
end Submission

/-!
# Polynomial correction factories from finite correction-closure packets

An all-integral ordered packet supported in the finite correction closure
already supplies the arbitrary-parent signed-polynomial correction expansion.
This file records that direct adapter and the support fact retained by the
closure vocabulary: when the two symbolic parents have the declared weights,
every attached polynomial factor is already physically below the quotient
cutoff.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCFtry

universe u

open CCTrunc
open CFExp
open CFSubsti
open UCSuppor
open UCAll
open CPWord
open PWSep
open SSFtrya

private lemma split_append_cons
    {α β : Type*}
    (f : α → β)
    (L : List α)
    (before : List β)
    (middle : β)
    (after : List β)
    (hmap : L.map f = before ++ middle :: after) :
    ∃ before' middle' after',
      L = before' ++ middle' :: after' ∧
        before'.map f = before ∧
          f middle' = middle ∧
            after'.map f = after := by
  induction before generalizing L with
  | nil =>
      cases L with
      | nil => simp at hmap
      | cons head tail =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at hmap
          exact ⟨[], head, tail, rfl, rfl, hmap.1, hmap.2⟩
  | cons beforeHead beforeTail ih =>
      cases L with
      | nil => simp at hmap
      | cons head tail =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at hmap
          rcases ih tail hmap.2 with
            ⟨before', middle', after', htail, hbefore', hmiddle', hafter'⟩
          exact
            ⟨head :: before', middle', after', by simp [htail],
              by simp [hmap.1, hbefore'], hmiddle', hafter'⟩

private lemma packets_forget_support
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight) :
    packet.truncatedAllIntegral.packets =
      packet.packets :=
  rfl

namespace TAPkta

/--
An ordered closure-supported packet split around its unique principal
Hall-pair bracket.  Both surrounding lists contain only nonprincipal packet
occurrences.
-/
structure SBSplita
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) where
  beforePackets : List RFPkt
  principalPacket : RFPkt
  afterPackets : List RFPkt
  packets_eq :
    packet.packets =
      beforePackets ++ principalPacket :: afterPackets
  principal_word_eq :
    principalPacket.word = CWord.hallPairBase
  before_word_ne :
    ∀ nextPacket ∈ beforePackets,
      nextPacket.word ≠ CWord.hallPairBase
  after_word_ne :
    ∀ nextPacket ∈ afterPackets,
      nextPacket.word ≠ CWord.hallPairBase

/--
Lift the unique principal occurrence from the mapped word list back to the
ordered packet list.
-/
noncomputable def symbolic_split_unique
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (hunique :
      OBPkt.UniqueBaseOccurrence
        packet.toOBPkt) :
    SBSplita packet normalizer left right := by
  let beforeBasic := Classical.choose hunique
  let afterBasic := Classical.choose (Classical.choose_spec hunique)
  have huniqueSpec :=
    Classical.choose_spec (Classical.choose_spec hunique)
  have hsplit :=
    split_append_cons
      RFPkt.word packet.packets
        beforeBasic CWord.hallPairBase afterBasic huniqueSpec.1
  let beforePackets := Classical.choose hsplit
  let principalPacket := Classical.choose (Classical.choose_spec hsplit)
  let afterPackets :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec hsplit))
  have hsplitSpec :=
    Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec hsplit))
  refine
    { beforePackets := beforePackets
      principalPacket := principalPacket
      afterPackets := afterPackets
      packets_eq := hsplitSpec.1
      principal_word_eq := hsplitSpec.2.2.1
      before_word_ne := ?_
      after_word_ne := ?_ }
  · intro nextPacket hnextPacket hword
    apply huniqueSpec.2.1
    change CWord.hallPairBase ∈ beforeBasic
    rw [← hsplitSpec.2.1]
    exact List.mem_map.mpr ⟨nextPacket, hnextPacket, hword⟩
  · intro nextPacket hnextPacket hword
    apply huniqueSpec.2.2
    change CWord.hallPairBase ∈ afterBasic
    rw [← hsplitSpec.2.2.2]
    exact List.mem_map.mpr ⟨nextPacket, hnextPacket, hword⟩

/--
Forget closure support and compile the ordered packet to the arbitrary-parent
signed-polynomial correction expansion.
-/
noncomputable def polynomialCorrectionExpansion
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    SCExp (n := n) left right :=
  packet.truncatedAllIntegral
    |>.toCorrectionExpansion normalizer left right

/--
Compile the closure-supported packet to the uniform expansion factory used by
signed semantic collection at one support stratum.
-/
noncomputable def supportedExpansionFactory
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (lowerWeight : ℕ) :
    SSFtrya
      (n := n) H lowerWeight :=
  packet.truncatedAllIntegral
    |>.supportedWordFactory normalizers lowerWeight

/--
Compile the closure-supported packet all the way to the physically truncated
correction factory consumed by signed semantic routing.
-/
noncomputable def supportedPacketFactory
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (lowerWeight : ℕ) :
    TSFtry
      (n := n) H lowerWeight :=
  (supportedExpansionFactory
    packet normalizers lowerWeight).correctionPacketFactory

/--
At parents of the declared weights, every polynomial factor attached to the
finite closure packet remains strictly below cutoff.
-/
lemma weight_symbolic_factors
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right factor : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight)
    (hfactor :
      factor ∈ symbolicFactors normalizer packet.packets left right) :
    factor.word.weight HEAddres.weight < n := by
  rcases packet_symbolic_factors hfactor with
    ⟨nextPacket, hnextPacket, rfl⟩
  rw [nextPacket.word_symbolicFactor, nextPacket.weight_boundWord,
    hleft, hright]
  simpa [packetWeight, HPAtom.weight] using
    OBPkt.packet_weight_cutoff
      packet.toOBPkt hnextPacket

/--
At parents of the declared weights, physical truncation removes no attached
polynomial factor.
-/
@[simp]
lemma truncate_symbolic_factors
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.truncate n
        (symbolicFactors normalizer packet.packets left right) =
      symbolicFactors normalizer packet.packets left right := by
  apply List.filter_eq_self.2
  intro factor hfactor
  simpa only [decide_eq_true_eq] using
    weight_symbolic_factors packet
      normalizer left right factor hleft hright hfactor

/--
At parents of the declared weights, every attached correction factor has at
least the combined parent weight.
-/
lemma add_symbolic_factors
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right factor : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight)
    (hfactor :
      factor ∈ symbolicFactors normalizer packet.packets left right) :
    leftWeight + rightWeight ≤
      factor.word.weight HEAddres.weight := by
  rcases packet_symbolic_factors hfactor with
    ⟨nextPacket, _hnextPacket, rfl⟩
  rw [nextPacket.word_symbolicFactor, nextPacket.weight_boundWord,
    hleft, hright]
  exact
    Nat.add_le_add
      (Nat.le_mul_of_pos_left leftWeight nextPacket.positive.1)
      (Nat.le_mul_of_pos_left rightWeight nextPacket.positive.2)

/--
A closure-supported packet occurrence has minimum declared weighted degree
only when its erased word is the principal Hall-pair bracket.
-/
lemma pair_base_packets
    {d n leftWeight rightWeight : ℕ}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (nextPacket : RFPkt)
    (hnextPacket : nextPacket ∈ packet.packets)
    (hweight :
      nextPacket.word.pairLeftDegree * leftWeight +
          nextPacket.word.pairRightDegree * rightWeight =
        leftWeight + rightWeight) :
    nextPacket.word = CWord.hallPairBase := by
  have hleftLe :=
    Nat.le_mul_of_pos_left leftWeight nextPacket.positive.1
  have hrightLe :=
    Nat.le_mul_of_pos_left rightWeight nextPacket.positive.2
  have hleftProduct :
      nextPacket.word.pairLeftDegree * leftWeight =
        leftWeight := by
    omega
  have hrightProduct :
      nextPacket.word.pairRightDegree * rightWeight =
        rightWeight := by
    omega
  have hleftDegree :
      nextPacket.word.pairLeftDegree = 1 := by
    apply Nat.mul_right_cancel packet.leftWeight_pos
    simpa using hleftProduct
  have hrightDegree :
      nextPacket.word.pairRightDegree = 1 := by
    apply Nat.mul_right_cancel packet.rightWeight_pos
    simpa using hrightProduct
  exact
    erased_vocabulary_bidegree
      (packet.word_erased_vocabulary nextPacket hnextPacket)
      hleftDegree hrightDegree

/--
A generated correction factor has minimum possible combined weight only when
its erased closure word is the literal principal Hall-pair bracket.
-/
lemma pair_base_add
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right factor : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight)
    (hfactor :
      factor ∈ symbolicFactors normalizer packet.packets left right)
    (hweight :
      factor.word.weight HEAddres.weight =
        leftWeight + rightWeight) :
    factor.word =
      CWord.hallPairBind
        left.word right.word CWord.hallPairBase := by
  rcases packet_symbolic_factors hfactor with
    ⟨nextPacket, hnextPacket, rfl⟩
  have hpacketWeight :
      nextPacket.word.pairLeftDegree * leftWeight +
          nextPacket.word.pairRightDegree * rightWeight =
        leftWeight + rightWeight := by
    simpa [nextPacket.word_symbolicFactor, nextPacket.weight_boundWord,
      hleft, hright] using hweight
  have hword :
      nextPacket.word = CWord.hallPairBase :=
    pair_base_packets
      packet nextPacket hnextPacket hpacketWeight
  rw [nextPacket.word_symbolicFactor]
  change
    CWord.hallPairBind left.word right.word nextPacket.word =
      CWord.hallPairBind
        left.word right.word CWord.hallPairBase
  rw [hword]

/--
Every nonprincipal attached correction factor lies strictly above the
combined parent weight.
-/
lemma ne_pair_base
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right factor : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight)
    (hfactor :
      factor ∈ symbolicFactors normalizer packet.packets left right)
    (hne :
      factor.word ≠
        CWord.hallPairBind
          left.word right.word CWord.hallPairBase) :
    leftWeight + rightWeight <
      factor.word.weight HEAddres.weight := by
  have hle :=
    add_symbolic_factors
      packet normalizer left right factor hleft hright hfactor
  by_contra hnot
  have heq :
      factor.word.weight HEAddres.weight =
        leftWeight + rightWeight := by
    omega
  exact hne
    (pair_base_add
      packet normalizer left right factor hleft hright hfactor heq)

/--
An occurrence whose erased closure word is not principal compiles to a factor
strictly above the combined parent weight.
-/
lemma packets_ne_base
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (nextPacket : RFPkt)
    (hnextPacket : nextPacket ∈ packet.packets)
    (hne : nextPacket.word ≠ CWord.hallPairBase)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    leftWeight + rightWeight <
      (nextPacket.symbolicFactor normalizer left right).word.weight
        HEAddres.weight := by
  rw [nextPacket.word_symbolicFactor, nextPacket.weight_boundWord,
    hleft, hright]
  have hle :
      leftWeight + rightWeight ≤
        nextPacket.word.pairLeftDegree * leftWeight +
          nextPacket.word.pairRightDegree * rightWeight :=
    Nat.add_le_add
      (Nat.le_mul_of_pos_left leftWeight nextPacket.positive.1)
      (Nat.le_mul_of_pos_left rightWeight nextPacket.positive.2)
  by_contra hnot
  have heq :
      nextPacket.word.pairLeftDegree * leftWeight +
          nextPacket.word.pairRightDegree * rightWeight =
        leftWeight + rightWeight := by
    omega
  exact hne
    (pair_base_packets
      packet nextPacket hnextPacket heq)

/--
Every order-preserving sublist of nonprincipal packet occurrences compiles to
a strict higher tail.
-/
lemma
    least_subset_base
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (subPackets : List RFPkt)
    (hsub : ∀ nextPacket ∈ subPackets, nextPacket ∈ packet.packets)
    (hne :
      ∀ nextPacket ∈ subPackets,
        nextPacket.word ≠ CWord.hallPairBase)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.WordWeightLeast
      (leftWeight + rightWeight + 1)
        (symbolicFactors normalizer subPackets left right) := by
  intro factor hfactor
  rcases List.mem_map.mp hfactor with
    ⟨nextPacket, hnextPacket, rfl⟩
  have hlt :=
    packets_ne_base
      packet normalizer left right nextPacket
        (hsub nextPacket hnextPacket) (hne nextPacket hnextPacket)
          hleft hright
  omega

namespace SBSplita

/-- Every packet occurrence before the principal bracket belongs to the
original ordered packet. -/
lemma before_packets_subset
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right)
    {nextPacket : RFPkt}
    (hnextPacket : nextPacket ∈ split.beforePackets) :
    nextPacket ∈ packet.packets := by
  rw [split.packets_eq]
  exact List.mem_append_left _ hnextPacket

/-- The principal packet occurrence belongs to the original ordered packet. -/
lemma princi_packe_packe
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right) :
    split.principalPacket ∈ packet.packets := by
  rw [split.packets_eq]
  simp

/-- Every packet occurrence after the principal bracket belongs to the
original ordered packet. -/
lemma after_packets_subset
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right)
    {nextPacket : RFPkt}
    (hnextPacket : nextPacket ∈ split.afterPackets) :
    nextPacket ∈ packet.packets := by
  rw [split.packets_eq]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ hnextPacket)

/--
Compiling the ordered packet preserves its decomposition around the unique
principal bracket.
-/
lemma symbolicFactors_eq
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right) :
    symbolicFactors normalizer packet.packets left right =
      symbolicFactors normalizer split.beforePackets left right ++
        split.principalPacket.symbolicFactor normalizer left right ::
          symbolicFactors normalizer split.afterPackets left right := by
  rw [split.packets_eq]
  simp only [symbolicFactors, List.map_append, List.map_cons]

/-- The selected polynomial factor has the bound principal Hall-pair word. -/
@[simp]
lemma word_principal_factor
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right) :
    (split.principalPacket.symbolicFactor normalizer left right).word =
      CWord.hallPairBind
        left.word right.word CWord.hallPairBase := by
  rw [split.principalPacket.word_symbolicFactor,
    RFPkt.boundWord, split.principal_word_eq]

/-- At parents of the declared weights, the principal compiled factor has
exactly their combined weight. -/
lemma princi_symbo_facto
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    (split.principalPacket.symbolicFactor normalizer left right).word.weight
        HEAddres.weight =
      leftWeight + rightWeight := by
  rw [split.principalPacket.word_symbolicFactor,
    split.principalPacket.weight_boundWord, split.principal_word_eq,
    CWord.pair_left_base,
    CWord.pair_degree_base, hleft, hright]
  omega

/-- The compiled factors before the selected principal bracket form a strict
higher tail. -/
lemma least_before_factors
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.WordWeightLeast
      (leftWeight + rightWeight + 1)
        (symbolicFactors normalizer split.beforePackets left right) := by
  exact
    least_subset_base
      packet normalizer left right split.beforePackets
        (fun _ hnextPacket => split.before_packets_subset hnextPacket)
        split.before_word_ne hleft hright

/-- The compiled factors after the selected principal bracket form a strict
higher tail. -/
lemma least_after_factors
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer : WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split : SBSplita packet normalizer left right)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.WordWeightLeast
      (leftWeight + rightWeight + 1)
        (symbolicFactors normalizer split.afterPackets left right) := by
  exact
    least_subset_base
      packet normalizer left right split.afterPackets
        (fun _ hnextPacket => split.after_packets_subset hnextPacket)
        split.after_word_ne hleft hright

end SBSplita

/--
For parents of the declared weights, the routed correction packet is the raw
attached closure packet: no quotient-trivial term needs to be erased.
-/
lemma supported_factory_symbolic
    {d n leftWeight rightWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    ((supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported).factors =
      symbolicFactors (normalizers.normalizer ι) packet.packets left right := by
  simp only [supportedPacketFactory,
    correctionPacketFactory,
    SCExp.truncate,
    supportedExpansionFactory,
    TAInt.supportedWordFactory,
    TAInt.toCorrectionExpansion,
    packets_forget_support]
  exact truncate_symbolic_factors packet
    (normalizers.normalizer ι) left right hleft hright

end TAPkta

end UCFtry
end TCTex
end Submission

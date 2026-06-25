import Towers.Group.Zassenhaus.ErasedWordSkeleton
import Towers.Group.Zassenhaus.CompatiblePacketRouting
import Towers.Group.Zassenhaus.OperationalInventory
import Towers.Group.Zassenhaus.FamilyOperationalSupport


/-!
# Concrete signed-profile packets from operational shape blocks

At fixed natural source multiplicities, every certified maximal same-shape
operational block already carries an explicit finite signed-profile packet.
Keeping the existing maximal-block order gives a concrete recollection packet
whose specialization is the powered commutator.

The remaining global theorem is therefore a stabilization theorem: replace
these multiplicity-dependent packets by one fixed ordered signed-profile
packet without changing any natural specialization.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CCPkt

open scoped commutatorElement

open HACoeff
open FMEnd
open CSAdmiss
open CSAggreg
open CFSubsti
open PPColl
open PPColl.RCColl.RPAggreg
open OCAdmiss

/-- Forget the concrete multiplicities while retaining one block's profiles. -/
def formulaPacketCertificate
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SBCert block word) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree where
  profiles := certificate.profiles
  profiles_leftDegree := certificate.profiles_leftDegree
  profiles_rightDegree := certificate.profiles_rightDegree

/-- Specializing the forgotten packet recovers the concrete shape-block length. -/
@[simp]
lemma formula_certificate_cast
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SBCert block word) :
    (formulaPacketCertificate certificate).value (M : ℤ) (N : ℤ) =
      block.length := by
  rw [formulaPacketCertificate,
    HFPkt.value_natCast]
  exact certificate.length_eq.symm

/-- Attach a concrete block certificate to its erased Hall word. -/
def recollectionPacketCertificate
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SBCert block word)
    (hpositive : word.PBPos) :
    RFPkt where
  word := word
  positive := hpositive
  profiles := formulaPacketCertificate certificate

@[simp]
lemma recollection_packet_certificate
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SBCert block word)
    (hpositive : word.PBPos) :
    (recollectionPacketCertificate certificate hpositive).word = word :=
  rfl

@[simp]
lemma recollection_certificate_cast
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SBCert block word)
    (hpositive : word.PBPos) :
    (recollectionPacketCertificate certificate hpositive).profiles.value
        (M : ℤ) (N : ℤ) =
      block.length :=
  formula_certificate_cast certificate

/-- Chosen signed-block certificate for one canonical maximal shape block. -/
noncomputable def certificateOfMem
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    SBCert block
      (shapeOfMem endpoint block hblock) :=
  Classical.choice
    (kernel.certificate endpoint block hblock
      (shapeOfMem endpoint block hblock)
      (erased_shape endpoint block hblock))

/-- The chosen shape of every canonical maximal block has positive bidegree. -/
lemma bidegree_positive_shape
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    (shapeOfMem endpoint block hblock).PBPos := by
  let term :=
    block.head (nil_same_blocks endpoint block hblock)
  rw [← erased_shape endpoint block hblock term
    (List.head_mem
      (nil_same_blocks endpoint block hblock))]
  exact term.positive

/-- Concrete recollection packet carried by one canonical maximal block. -/
noncomputable def packetOfMem
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    RFPkt :=
  recollectionPacketCertificate
    (certificateOfMem kernel endpoint block hblock)
    (bidegree_positive_shape endpoint block hblock)

/-- One concrete packet evaluates to its original maximal same-shape block. -/
lemma eval_packet
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    (packetOfMem kernel endpoint block hblock).word.eval
          (HPAtom.eval universalLeft universalRight) ^
        (packetOfMem kernel endpoint block hblock).profiles.value
          (M : ℤ) (N : ℤ) =
      decoratedCollapsedEval
        (block.map DFTerm.decorated) := by
  change
    (shapeOfMem endpoint block hblock).eval
          (HPAtom.eval universalLeft universalRight) ^
        (formulaPacketCertificate
          (certificateOfMem kernel endpoint block hblock)).value
            (M : ℤ) (N : ℤ) =
      decoratedCollapsedEval
        (block.map DFTerm.decorated)
  rw [formula_certificate_cast]
  exact
    (decorated_collapsed_same
      block (shapeOfMem endpoint block hblock)
      (erased_shape endpoint block hblock)).symm

/-- Preserve maximal-block order while attaching concrete signed-profile packets. -/
noncomputable def packetsOfBlocks
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ∀ blocks : List (List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      (∀ block ∈ blocks,
        block ∈ sameErasedBlocks endpoint.collected.factors) →
          List RFPkt
  | [], _ => []
  | block :: blocks, hblocks =>
      packetOfMem kernel endpoint block (hblocks block (by simp)) ::
        packetsOfBlocks kernel endpoint blocks
          (fun next hnext => hblocks next (by simp [hnext]))

/-- Ordered packet evaluation agrees with ordered collapsed block evaluation. -/
lemma list_packets_blocks
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ∀ (blocks : List (List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)))
      (hblocks : ∀ block ∈ blocks,
        block ∈ sameErasedBlocks endpoint.collected.factors),
      ((packetsOfBlocks kernel endpoint blocks hblocks).map fun packet =>
        packet.word.eval (HPAtom.eval universalLeft universalRight) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod =
        decoratedCollapsedEval
          (blocks.flatten.map DFTerm.decorated)
  | [], _ => rfl
  | block :: blocks, hblocks => by
      rw [packetsOfBlocks, List.map_cons, List.prod_cons,
        eval_packet,
        List.flatten_cons, List.map_append,
        decorated_collapsed_append,
        list_packets_blocks kernel endpoint blocks]

/-- Concrete ordered packet attached to all maximal blocks of one endpoint. -/
noncomputable def packets
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List RFPkt :=
  packetsOfBlocks kernel endpoint
    (sameErasedBlocks endpoint.collected.factors)
    (fun _block hblock => hblock)

/-- The concrete signed-profile packet recovers the powered commutator. -/
lemma packets_commutator_pow
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ((packets kernel endpoint).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  rw [packets,
    list_packets_blocks kernel endpoint
      (sameErasedBlocks endpoint.collected.factors),
    flatten_same_blocks]
  calc
    decoratedCollapsedEval
          (endpoint.collected.factors.map DFTerm.decorated) =
        collapseHom M N
          (decoratedListEval
            (endpoint.collected.factors.map DFTerm.decorated)) :=
      (collapse_decorated_eval _).symm
    _ = collapseHom M N
          (DFTerm.listEval endpoint.collected.factors) := by
      rw [DFTerm.list_eval_decorated]
    _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
      rw [endpoint.collected.eval_eq]
    _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [map_commutatorElement, collapse_labelled_left,
        collapse_labelled_right]

/-- The exact local precursor to multiplicity-independent stabilization. -/
structure SpecializedNaturalPacket
    (M N : ℕ) where
  packets :
    List RFPkt
  listEval_eq :
    (packets.map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆

/-- Every explicit shape-block kernel supplies a packet at each natural specialization. -/
noncomputable def specializedNaturalPacket
    (kernel : OCShape)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    SpecializedNaturalPacket M N where
  packets := packets kernel endpoint
  listEval_eq := packets_commutator_pow kernel endpoint

end CCPkt
end TCTex
end Towers

/-!
# Signed-block certificates for complete compatible routing worklists

The complete-packet reuse-first scheduler remembers enough information to
apply retained-grid homogeneous cancellation to every opened schedule batch.
This file packages that consequence without replacing genuine filtered grids
by a conservative closure inventory.

Different worklist batches may carry different erased Hall shapes.  This layer
therefore certifies each batch separately; same-shape aggregation is a later
step.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CCTrace

open HACoeff
open CCGrida
open CCWork
open FMEnd
open
  CTRoute
open
  CRRoutec
open
  CSAggreg
open
  SHPres
open HSPacket

namespace BWItem

/--
One opened compatible schedule batch has complete parent packets and an
explicit homogeneous signed-block certificate for its genuine filtered grid.
-/
def SignedBlockCertificate
    {M N K : ℕ}
    (item : BWItem M N K) :
    Prop :=
  ∃ (leftFamily rightFamily : BFam M N),
    RPFor leftFamily item.leftTerms ∧
      RPFor rightFamily item.rightTerms ∧
        Nonempty
          (SBCert
            (compatibleCorrectionGrid item.leftTerms item.rightTerms)
            (leftFamily.correction rightFamily).recipe.erasedShape)

/--
Retained-grid homogeneous cancellation certifies one opened schedule batch
whose complete represented parents have been recorded.
-/
lemma complete_parent_packets
    (kernel : CHCancel)
    {M N K : ℕ}
    {item : BWItem M N K}
    (hitem :
      BWItem.HPPacket item) :
    SignedBlockCertificate item := by
  rcases hitem with
    ⟨leftFamily, rightFamily, hleft, hright,
      leftTerm, hleftTerm, rightTerm, hrightTerm, hcompatible⟩
  exact
    ⟨leftFamily, rightFamily, hleft, hright,
      ⟨kernel.certificate hleft hright
        hleftTerm hrightTerm hcompatible⟩⟩

end BWItem

namespace CBWork

/-- Every opened schedule batch has its own signed-block certificate. -/
def SignedBlockCertificates
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    Prop :=
  ∀ item ∈ worklist,
    BWItem.SignedBlockCertificate item

/--
The complete-parent invariant compiles pointwise to signed-block certificates
for every genuine compatible grid opened by the scheduler.
-/
lemma HPPacket.signed_block_certi
    (kernel : CHCancel)
    {M N K : ℕ}
    {worklist : CBWork M N K}
    (hworklist :
      CBWork.HPPacket worklist) :
    SignedBlockCertificates worklist := by
  intro item hitem
  exact
    BWItem.complete_parent_packets
      kernel
        (hworklist item hitem)

end CBWork

/--
Every compatible grid opened while routing one genuine More3 endpoint has an
explicit signed-block certificate, assuming retained-grid homogeneous
cancellation for complete family packets.
-/
lemma reuse_routing_certificates
    (kernel : CHCancel)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    CBWork.SignedBlockCertificates
      (reuseRoutingPrefix endpoint).state.state.worklist :=
  CBWork.HPPacket.signed_block_certi
    kernel
      (reuseRoutingPrefix endpoint).state.complete

end CCTrace
end TCTex
end Towers

/-!
# Specializing concrete signed-profile packets

Concrete operational signed-profile packets are constructed in the universal
free group.  This file specializes their ordered evaluations to arbitrary
groups, chooses the terminating endpoint canonically for each pair of natural
multiplicities, and isolates the remaining stabilization theorem.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSSpec

open scoped commutatorElement

open HACoeff
open FMEnd
open CSAggreg
open CFSubsti
open CCPkt
open UNPkt
open PPColl
open PPColl.RCColl.RPAggreg

/-- Erased Hall-word evaluation commutes with Hall-pair specialization. -/
lemma specialize_word_eval
    {G : Type*}
    [Group G]
    (left right : G)
    (word : CWord HPAtom) :
    specialize left right
        (word.eval (HPAtom.eval universalLeft universalRight)) =
      word.eval (HPAtom.eval left right) := by
  rw [CWord.map_eval]
  congr 1
  funext atom
  cases atom <;> simp [HPAtom.eval]

/-- One signed-profile packet evaluation commutes with specialization. -/
lemma specialize_packet_eval
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ)
    (packet : RFPkt) :
    specialize left right
        (packet.word.eval (HPAtom.eval universalLeft universalRight) ^
          packet.profiles.value leftExponent rightExponent) =
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent := by
  rw [map_zpow, specialize_word_eval]

/-- Ordered signed-profile packet evaluation commutes with specialization. -/
lemma specialize_listEval
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ∀ packets : List RFPkt,
      specialize left right
          ((packets.map fun packet =>
            packet.word.eval (HPAtom.eval universalLeft universalRight) ^
              packet.profiles.value leftExponent rightExponent).prod) =
        (packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod
  | [] => by simp
  | packet :: packets => by
      simp [specialize_packet_eval,
        specialize_listEval left right leftExponent rightExponent packets]

/-- Canonically choose one terminating operational endpoint at each specialization. -/
noncomputable def endpoint
    (M N : ℕ) :
    ODEmissi M N :=
  Classical.choice
    (nonempty_decorated_emissions M N)

/-- Concrete signed-profile packet chosen at one natural specialization. -/
noncomputable def concretePackets
    (kernel : OCShape)
    (M N : ℕ) :
    List RFPkt :=
  packets kernel (endpoint M N)

/-- The chosen concrete packet has the powered-commutator law in the universal group. -/
lemma list_packets_commutator
    (kernel : OCShape)
    (M N : ℕ) :
    ((concretePackets kernel M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  packets_commutator_pow kernel (endpoint M N)

/--
The remaining natural stabilization theorem: one fixed ordered signed-profile
packet has the same universal specialization as every concrete operational
packet.
-/
structure UNStab
    (kernel : OCShape)
    (fixedPackets : List RFPkt) :
    Prop where
  packet_prod_concrete :
    ∀ (M N : ℕ),
      (fixedPackets.map fun packet =>
        packet.word.eval (HPAtom.eval universalLeft universalRight) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod =
        ((concretePackets kernel M N).map fun packet =>
          packet.word.eval (HPAtom.eval universalLeft universalRight) ^
            packet.profiles.value (M : ℤ) (N : ℤ)).prod

namespace UNStab

/-- Universal-group stabilization specializes to every ambient group. -/
lemma nat_cast_pow
    {kernel : OCShape}
    {fixedPackets : List RFPkt}
    (stabilization :
      UNStab
        kernel fixedPackets)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [← specialize_listEval left right (M : ℤ) (N : ℤ) fixedPackets,
    stabilization.packet_prod_concrete M N,
    list_packets_commutator]
  simp [map_commutatorElement, map_pow]

/-- A fixed stabilized packet supplies the cutoff natural packet interface. -/
def truncNaturalPacket
    {kernel : OCShape}
    {fixedPackets : List RFPkt}
    (stabilization :
      UNStab
        kernel fixedPackets)
    (d n : ℕ) :
    TBPkt d n where
  packets := fixedPackets
  list_nat_cast left right M N :=
    stabilization.nat_cast_pow M N left right

end UNStab

end CSSpec
end TCTex
end Towers

/-!
# Fixed formula packets for filtered compatible-grid subtraction

Operational compatibility removes the overlapping-support complement from a
full Cartesian correction grid.  Concrete certificates implement this by
appending negated overlap profiles.  This file records the corresponding
multiplicity-independent packet subtraction and proves that forgetting the
concrete partition certificate commutes with it.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CGComp

open HACoeff
open CSAggreg
open CCPkt
open CSFilter
open CFAlg
open CFSubsti

namespace FPkt

/-- Negate every multiplicity in one fixed homogeneous formula packet. -/
def negate
    {leftDegree rightDegree : ℕ}
    (packet :
      HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree where
  profiles := negateWeightedProfiles packet.profiles
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_map.mp hprofile with ⟨original, horiginal, rfl⟩
    exact packet.profiles_leftDegree original horiginal
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_map.mp hprofile with ⟨original, horiginal, rfl⟩
    exact packet.profiles_rightDegree original horiginal

/-- Subtract one fixed homogeneous formula packet from another. -/
def subtract
    {leftDegree rightDegree : ℕ}
    (whole rejected :
      HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree :=
  FPkt.add whole (negate rejected)

@[simp]
lemma weighted_value_negate
    (profile : WBProf)
    (left right : ℤ) :
    weightedProfileValue
        (negateWeightedProfile profile) left right =
      -weightedProfileValue profile left right := by
  simp [weightedProfileValue, negateWeightedProfile]

@[simp]
lemma weighted_profile_negate
    (left right : ℤ)
    (profiles : List WBProf) :
    ((negateWeightedProfiles profiles).map fun profile =>
        weightedProfileValue profile left right).sum =
      -(profiles.map fun profile =>
        weightedProfileValue profile left right).sum := by
  induction profiles with
  | nil =>
      rfl
  | cons profile profiles ih =>
      change
        weightedProfileValue
              (negateWeightedProfile profile) left right +
            ((negateWeightedProfiles profiles).map fun next =>
              weightedProfileValue next left right).sum =
          -(weightedProfileValue profile left right +
            (profiles.map fun next =>
              weightedProfileValue next left right).sum)
      rw [weighted_value_negate, ih]
      ring

@[simp]
lemma value_negate
    {leftDegree rightDegree : ℕ}
    (packet :
      HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (negate packet).value left right =
      -packet.value left right := by
  exact weighted_profile_negate
    left right packet.profiles

@[simp]
lemma value_subtract
    {leftDegree rightDegree : ℕ}
    (whole rejected :
      HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (subtract whole rejected).value left right =
      whole.value left right - rejected.value left right := by
  simp [subtract, sub_eq_add_neg]

end FPkt

/--
Forgetting a concrete partition certificate is fixed-packet subtraction.
-/
@[simp]
lemma formula_certificate_partition
    {M N K : ℕ}
    {whole retained rejected : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (wholeCertificate : SBCert whole word)
    (rejectedCertificate : SBCert rejected word)
    (hpartition : List.Perm whole (retained ++ rejected)) :
    formulaPacketCertificate
        (shapeCertificatePartition
          wholeCertificate rejectedCertificate hpartition) =
      FPkt.subtract
        (formulaPacketCertificate wholeCertificate)
        (formulaPacketCertificate rejectedCertificate) := by
  rfl

end CGComp
end TCTex
end Towers

/-!
# Shape-filtered signed-block certificates for compatible routing worklists

Each compatible grid opened by the complete-packet reuse-first scheduler has
one correction-family erased shape.  Filtering the flattened worklist by a
target shape therefore keeps or discards each certified grid as a whole.

This file appends those pointwise certificates and includes the exact inverse
raw source packet, producing one signed-block certificate for every
shape-filtered routed source.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CCFilter

open HACoeff
open FIFilter.MIBlock
open IMPropag
open CCAggreg
open CCGrida
open CCWork
open
  CTRoute
open
  CSAggreg
open
  CSChunks
open
  SHPres
open HSPacket

/--
Every term retained by one compatible grid has the correction-family shape of
its two complete parent packets.
-/
lemma family_compatible_grid
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RPFor leftFamily leftTerms)
    (hright : RPFor rightFamily rightTerms)
    {term : DFTerm M N K}
    (hterm : term ∈ compatibleCorrectionGrid leftTerms rightTerms) :
    term.family.recipe.erasedShape =
      (leftFamily.correction rightFamily).recipe.erasedShape := by
  rcases compatible_grid.mp hterm with
    ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, _hcompatible, rfl⟩
  change
    (leftTerm.family.correction rightTerm.family).recipe.erasedShape =
      (leftFamily.correction rightFamily).recipe.erasedShape
  rw [hleft.family_eq_mem hleftTerm, hright.family_eq_mem hrightTerm]

/--
Filtering a complete compatible worklist by one erased Hall shape appends
exactly the signed-block certificates of the retained genuine grids.
-/
lemma nonempty_certificate_grids
    (kernel : CHCancel)
    {M N K : ℕ}
    {worklist : CBWork M N K}
    (hworklist :
      CBWork.HPPacket worklist)
    (shape : CWord HPAtom) :
    Nonempty
      (SBCert
        (worklist.compatibleGrids.filter fun term =>
          term.family.recipe.erasedShape = shape)
        shape) := by
  induction worklist with
  | nil =>
      exact ⟨SBCert.nil shape⟩
  | cons item worklist ih =>
      have hitem := hworklist item (by simp)
      have htail :
          CBWork.HPPacket worklist := by
        intro next hnext
        exact hworklist next (by simp [hnext])
      rcases hitem with
        ⟨leftFamily, rightFamily, hleft, hright,
          leftTerm, hleftTerm, rightTerm, hrightTerm, hcompatible⟩
      let itemCertificate :=
        kernel.certificate hleft hright
          hleftTerm hrightTerm hcompatible
      rcases ih htail with ⟨tailCertificate⟩
      by_cases hshape :
          (leftFamily.correction rightFamily).recipe.erasedShape = shape
      · subst shape
        rw [CBWork.compatibleGrids,
          List.flatMap_cons, List.filter_append, List.filter_eq_self.2]
        · exact ⟨itemCertificate.append tailCertificate⟩
        · intro term hterm
          simpa only [decide_eq_true_eq] using
            family_compatible_grid
              hleft hright hterm
      · rw [CBWork.compatibleGrids,
          List.flatMap_cons, List.filter_append]
        have hfilter :
            (compatibleCorrectionGrid item.leftTerms item.rightTerms).filter
                (fun term => term.family.recipe.erasedShape = shape) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro term hterm htermShape
          apply hshape
          exact
            (family_compatible_grid
              hleft hright hterm).symm.trans
                (of_decide_eq_true htermShape)
        rw [hfilter, List.nil_append]
        exact ⟨tailCertificate⟩

/--
The inverse raw source filtered by one shape has its canonical positive
signed-block certificate.
-/
noncomputable def inverseFilterCertificate
    (M N : ℕ)
    (shape : CWord HPAtom) :
    SBCert
      ((inverseDecoratedTerms M N).filter fun term =>
        term.family.recipe.erasedShape = shape)
      shape :=
  realizationInventoryCertificate
    (filterShape (MIBlock.inverseRaw M N) shape).inventory
    (filter_shape_families
      (MIBlock.inverseRaw M N) shape)

/--
The inverse raw source followed by every opened compatible grid has an
explicit certificate after filtering by any one erased Hall shape.
-/
noncomputable def gridsFilterCertificate
    (kernel : CHCancel)
    {M N : ℕ}
    {worklist : CBWork M N
      (inverseLabelledCollection M N).factors.length}
    (hworklist :
      CBWork.HPPacket worklist)
    (shape : CWord HPAtom) :
    SBCert
      ((inverseDecoratedTerms M N ++ worklist.compatibleGrids).filter
        fun term => term.family.recipe.erasedShape = shape)
      shape := by
  rw [List.filter_append]
  exact
    (inverseFilterCertificate M N shape).append
      (Classical.choice
        (nonempty_certificate_grids
          kernel hworklist shape))

end CCFilter
end TCTex
end Towers

/-!
# Cutoff truncation for concrete signed-block packets

Each compressed signed-block packet has a single erased Hall word.  Its weighted
degree therefore gives a canonical cutoff filter.  In a lower-central
truncation, discarded packet factors evaluate to one.
-/

namespace Towers
namespace TCTex
namespace CCTrunc

universe u

open scoped commutatorElement

open CSAggreg
open CFSubsti
open CSSpec
open UNPkt

/-- The lower-central weight of a signed-block packet when its two inputs have
weights `leftWeight` and `rightWeight`. -/
def packetWeight
    (leftWeight rightWeight : ℕ)
    (packet : RFPkt) :
    ℕ :=
  packet.word.weight (HPAtom.weight leftWeight rightWeight)

/-- Keep exactly the signed-block packets whose erased Hall words lie below the
lower-central cutoff. -/
def truncate
    (n leftWeight rightWeight : ℕ)
    (packets : List RFPkt) :
    List RFPkt :=
  packets.filter fun packet =>
    packetWeight leftWeight rightWeight packet < n

@[simp]
lemma truncate_nil
    (n leftWeight rightWeight : ℕ) :
    truncate n leftWeight rightWeight [] = [] := by
  rfl

@[simp]
lemma truncate_append
    (n leftWeight rightWeight : ℕ)
    (left right : List RFPkt) :
    truncate n leftWeight rightWeight (left ++ right) =
      truncate n leftWeight rightWeight left ++
        truncate n leftWeight rightWeight right := by
  simp [truncate]

lemma packet_weight_truncate
    {n leftWeight rightWeight : ℕ}
    {packets : List RFPkt}
    {packet : RFPkt}
    (hpacket : packet ∈ truncate n leftWeight rightWeight packets) :
    packetWeight leftWeight rightWeight packet < n := by
  simpa [truncate] using (List.mem_filter.mp hpacket).2

@[simp]
lemma truncate_truncate
    (n leftWeight rightWeight : ℕ)
    (packets : List RFPkt) :
    truncate n leftWeight rightWeight
        (truncate n leftWeight rightWeight packets) =
      truncate n leftWeight rightWeight packets := by
  simp [truncate]

lemma length_truncate_le
    (n leftWeight rightWeight : ℕ)
    (packets : List RFPkt) :
    (truncate n leftWeight rightWeight packets).length ≤ packets.length := by
  simpa [truncate] using
    (List.length_filter_le
      (fun packet : RFPkt =>
        packetWeight leftWeight rightWeight packet < n)
      packets)

lemma n_packet_weight
    {d n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (leftWeight - 1))
    (hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (rightWeight - 1))
    (packet : RFPkt)
    (leftExponent rightExponent : ℤ)
    (hweight : n ≤ packetWeight leftWeight rightWeight packet) :
    packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent =
      1 := by
  have hleftSucc : leftWeight - 1 + 1 = leftWeight :=
    Nat.sub_add_cancel hleftWeight
  have hrightSucc : rightWeight - 1 + 1 = rightWeight :=
    Nat.sub_add_cancel hrightWeight
  have hword :
      packet.word.eval (HPAtom.eval left right) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (packetWeight leftWeight rightWeight packet - 1) := by
    simpa [packetWeight, hleftSucc, hrightSucc] using
      packet.word.pair_lower_series hleft hright
  have hlast :
      packet.word.eval (HPAtom.eval left right) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (n - 1) := by
    exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hweight 1) hword
  have hword_eq_one :
      packet.word.eval (HPAtom.eval left right) = 1 := by
    rw [
      SCFactor.trunc_last_bot
    ] at hlast
    simpa using hlast
  rw [hword_eq_one]
  exact one_zpow _

lemma listEval_truncate
    {d n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (leftWeight - 1))
    (hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (rightWeight - 1))
    (leftExponent rightExponent : ℤ)
    (packets : List RFPkt) :
    ((truncate n leftWeight rightWeight packets).map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent).prod =
      (packets.map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent).prod := by
  induction packets with
  | nil =>
      rfl
  | cons packet packets ih =>
      by_cases hpacket :
          packetWeight leftWeight rightWeight packet < n
      · simpa [truncate, hpacket] using congrArg
          (fun tail =>
            packet.word.eval (HPAtom.eval left right) ^
                packet.profiles.value leftExponent rightExponent *
              tail)
          ih
      · have hweight :
            n ≤ packetWeight leftWeight rightWeight packet :=
          Nat.le_of_not_gt hpacket
        have hpacket_eval :
            packet.word.eval (HPAtom.eval left right) ^
                packet.profiles.value leftExponent rightExponent =
              1 :=
          n_packet_weight hleftWeight hrightWeight left right
            hleft hright packet leftExponent rightExponent hweight
        simpa [truncate, hpacket, hpacket_eval] using ih

/-- The concrete packet chosen at `(M, N)` specializes from the universal free
group to every ambient group. -/
lemma specialized_concrete_packets
    (kernel : OCShape)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((concretePackets kernel M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [← specialize_listEval left right (M : ℤ) (N : ℤ)
    (concretePackets kernel M N),
    list_packets_commutator]
  simp [map_commutatorElement, map_pow]

/-- The below-cutoff part of the concrete packet selected at `(M, N)`. -/
noncomputable def truncatedConcretePackets
    (kernel : OCShape)
    (n leftWeight rightWeight M N : ℕ) :
    List RFPkt :=
  truncate n leftWeight rightWeight (concretePackets kernel M N)

/-- Removing high-weight concrete packets preserves the powered-commutator law
in the lower-central truncation. -/
lemma concrete_packets_pow
    {d n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (kernel : OCShape)
    (M N : ℕ)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (leftWeight - 1))
    (hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (rightWeight - 1)) :
    ((truncatedConcretePackets kernel n leftWeight rightWeight M N).map
      fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [truncatedConcretePackets,
    listEval_truncate hleftWeight hrightWeight left right hleft hright
      (M : ℤ) (N : ℤ),
    specialized_concrete_packets]

/--
The cutoff-specific stabilization theorem: one fixed ordered packet agrees
with every concrete operational packet after high-weight factors are removed.
-/
structure TNStab
    (kernel : OCShape)
    (d n leftWeight rightWeight : ℕ)
    (fixedPackets : List RFPkt) :
    Prop where
  leftWeight_pos :
    0 < leftWeight
  rightWeight_pos :
    0 < rightWeight
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
          (fixedPackets.map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value (M : ℤ) (N : ℤ)).prod =
            ((truncatedConcretePackets kernel n leftWeight rightWeight M N).map
              fun packet =>
                packet.word.eval (HPAtom.eval left right) ^
                  packet.profiles.value (M : ℤ) (N : ℤ)).prod

namespace TNStab

/-- Cutoff stabilization gives the natural powered-commutator law on the
prescribed lower-central layers. -/
lemma nat_cast_pow
    {kernel : OCShape}
    {d n leftWeight rightWeight : ℕ}
    {fixedPackets : List RFPkt}
    (stabilization :
      TNStab.{u}
        kernel d n leftWeight rightWeight fixedPackets)
    (M N : ℕ)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (leftWeight - 1))
    (hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (rightWeight - 1)) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [stabilization.packet_prod_concrete M N left right hleft hright]
  exact concrete_packets_pow
    stabilization.leftWeight_pos stabilization.rightWeight_pos
      kernel M N left right hleft hright

/-- Root-layer cutoff stabilization supplies the existing natural packet
interface. -/
def truncNaturalPacket
    {kernel : OCShape}
    {d n : ℕ}
    {fixedPackets : List RFPkt}
    (stabilization :
      TNStab.{u}
        kernel d n 1 1 fixedPackets) :
    TBPkt.{u} d n where
  packets := fixedPackets
  list_nat_cast left right M N :=
    stabilization.nat_cast_pow M N left right
      (by simp) (by simp)

end TNStab

end CCTrunc
end TCTex
end Towers

/-!
# Specializing fixed formula packets for compatible correction grids

The support compiler constructs the rejected overlap packet from recursively
supplied avoidance packets.  The filtered-grid compiler subtracts that rejected
packet from the full Cartesian packet.  This file composes the two facts:
whenever parent avoidance families specialize fixed formulas, the concrete
compatible-grid certificate forgets to one fixed subtraction packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CGSpec

open HACoeff
open CCGrida
open CSAggreg
open CGCompa
open CCPkt
open CEAlg
open CGComp
open CSFilter
open CFSubsti
open CSOverla
open SEComp
open SFComp
open SFSpec
open HSPacket

/-- Forgetting a certificate built from one concrete expression returns its global packet. -/
@[simp]
lemma formula_certificate_signed
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (expression :
      HBExpr
        M N word.pairLeftDegree word.pairRightDegree)
    (hlength : (block.length : ℤ) = expression.value) :
    formulaPacketCertificate
        (expression.shapeBlockCertificate hlength) =
      HFPkt.ofExpression expression := by
  rfl

/-- Forgetting a certificate is invariant under transport of its concrete block list. -/
@[simp]
lemma formula_certificate_transport
    {M N K : ℕ}
    {leftBlock rightBlock : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (hblock : rightBlock = leftBlock)
    (certificate : SBCert rightBlock word) :
    formulaPacketCertificate (hblock ▸ certificate) =
      formulaPacketCertificate certificate := by
  subst leftBlock
  rfl

/-- The overlap certificate forgets to the global packet of its overlap expression. -/
@[simp]
lemma certificate_overlap_avoidance
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (leftShape rightShape : CWord HPAtom)
    (left :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftShape.pairLeftDegree
            leftShape.pairRightDegree)
    (right :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots rightShape.pairLeftDegree
            rightShape.pairRightDegree) :
    formulaPacketCertificate
        (overlapCertificateAvoidance
          leftShape rightShape left right) =
      HFPkt.ofExpression
        (overlapExpressionAvoidance left right).expression := by
  rfl

/-- Forgetting compatible-grid subtraction is fixed formula-packet subtraction. -/
@[simp]
lemma formula_certificate_incompatible
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (fullCertificate :
      SBCert
        (DFTerm.correctionGrid leftTerms rightTerms) word)
    (incompatibleCertificate :
      SBCert
        (incompatibleCorrectionGrid leftTerms rightTerms) word) :
    formulaPacketCertificate
        (compatibleCertificateIncompatible
          fullCertificate incompatibleCertificate) =
      FPkt.subtract
        (formulaPacketCertificate fullCertificate)
        (formulaPacketCertificate incompatibleCertificate) := by
  unfold compatibleCertificateIncompatible
  rw [formula_certificate_partition]

end CGSpec
end TCTex
end Towers

/-!
# Global signed-block compiler from complete compatible routing

The complete-packet scheduler opens genuine support-compatible grids.  If that
scheduler exhausts every opened grid, retained-grid homogeneous cancellation
certifies each grid, and maximal endpoint shape blocks are complete shape
fibers, then every endpoint shape block receives an explicit signed-block
certificate.

This is the schedule-derived global symbolic compiler.  It uses permutations
only for coefficient-length transport; it does not reorder noncommutative
products.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  RGComp

open HACoeff
open RGClosa
open CTRoutea
open CCWork
open
  CRRoutec
open
  CCFilter
open
  CSAdmiss
open
  CSAggreg
open
  SHPres
open FMEnd
open MSCompre

/--
Global complete-packet compatible reuse-first closure law: after traversing
every actual operational correction, every opened compatible grid is
exhausted.
-/
structure OCReusea : Prop where
  closed :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      (reuseRoutingPrefix endpoint).state.state.worklist.Closed

namespace OCReusea

/--
Under complete compatible closure, the flattened emitted history of every
opened batch is exactly the operational correction list up to permutation.
-/
lemma emitted_perm_corrections
    (_kernel : OCReusea)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm
      (batchWorklistEmitted
        (reuseRoutingPrefix endpoint).state.state.worklist)
      endpoint.corrections := by
  let routingPrefix := reuseRoutingPrefix endpoint
  rw [← routingPrefix.routed_eq]
  exact routingPrefix.state.state.emitted_perm

/--
Under complete compatible closure, the flattened compatible grids opened by
the genuine trace are exactly the operational correction list up to
permutation.
-/
lemma compatible_perm_corrections
    (kernel : OCReusea)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm
      (reuseRoutingPrefix
        endpoint).state.state.worklist.compatibleGrids
      endpoint.corrections := by
  apply List.Perm.trans
    (OCReuse.emitted_grids_closed
        (reuseRoutingPrefix endpoint).state.state.worklist
        (kernel.closed endpoint)).symm
  exact kernel.emitted_perm_corrections endpoint

/--
The inverse raw source followed by the flattened genuine compatible grids is
the operational endpoint factor list up to permutation.
-/
lemma grids_perm_factors
    (kernel : OCReusea)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm
      (inverseDecoratedTerms M N ++
        (reuseRoutingPrefix
          endpoint).state.state.worklist.compatibleGrids)
      endpoint.collected.factors := by
  apply List.Perm.trans
  · exact (kernel.compatible_perm_corrections endpoint).append_left _
  · exact endpoint.perm_append_corrections.symm

end OCReusea

/--
Compile the three remaining truthful schedule boundaries into explicit
signed-block certificates for every maximal endpoint shape block.
-/
noncomputable def operationalCompatibleShape
    (closure : OCReusea)
    (cancellation :
      CHCancel)
    (shapeFiber : OperationalShapeFiber) :
    OCShape where
  certificate endpoint block hblock word hterms := by
    rcases shapeFiber.filter_eq endpoint.collected block hblock with
      ⟨shape, hshape⟩
    let term :=
      block.head
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have hterm : term ∈ block :=
      List.head_mem
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have htermFilter :
        term ∈ endpoint.collected.factors.filter
          (fun next => next.family.recipe.erasedShape = shape) := by
      rw [hshape]
      exact hterm
    have htermShape :
        term.family.recipe.erasedShape = shape :=
      of_decide_eq_true (List.mem_filter.mp htermFilter).2
    have htermWord :
        term.family.recipe.erasedShape = word := by
      rw [← term.erased_shape_family]
      exact hterms term hterm
    have hshapeWord : shape = word :=
      htermShape.symm.trans htermWord
    have hendpointFilter :
        endpoint.collected.factors.filter
            (fun next => next.family.recipe.erasedShape = word) =
          block := by
      rw [← hshapeWord]
      exact hshape
    let routingPrefix :=
      reuseRoutingPrefix endpoint
    let certificate :=
      gridsFilterCertificate cancellation
        routingPrefix.state.complete word
    have hperm :=
      (closure.grids_perm_factors endpoint).filter
        (fun next => next.family.recipe.erasedShape = word)
    rw [hendpointFilter] at hperm
    exact ⟨certificate.permTerms hperm⟩

end RGComp
end TCTex
end Towers

/-!
# Residual-aware signed-block compiler for complete compatible routing

Every genuine operational prefix has an unconditional finite closed compatible
extension.  Closing the schedule may append residual correction terms.  This
file first certifies each shape fiber of the endpoint factors together with
those residuals.  It then isolates the exact remaining normalization theorem:
certify the residual shape fibers themselves.  Signed-block subtraction removes
such a certified residual and recovers certificates for the genuine endpoint.

This replaces an empty-residual closure assumption with the weaker, explicit
residual normalization boundary.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CRComp

open HACoeff
open
  CRCompa
open
  CCFilter
open
  CSAdmiss
open
  CSAggreg
open
  CSFilter
open
  SHPres
open FMEnd
open MSCompre

/-- The concrete residual suffix added only to drain one operational schedule. -/
noncomputable def operationalCompleteCorrections
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length) :=
  (operationalCompleteRouting endpoint).residualCorrections

/--
Under retained-grid homogeneous cancellation, every shape fiber of endpoint
factors together with its drained residual suffix has an explicit signed-block
certificate.
-/
noncomputable def endpointFilterCertificate
    (cancellation :
      CHCancel)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    SBCert
      ((endpoint.collected.factors ++
        operationalCompleteCorrections endpoint).filter
          fun term => term.family.recipe.erasedShape = shape)
      shape := by
  let extension :=
    operationalCompleteRouting endpoint
  let certificate :=
    gridsFilterCertificate cancellation
      extension.state.complete shape
  exact certificate.permTerms <| by
    change List.Perm
      ((inverseDecoratedTerms M N ++
        extension.state.state.worklist.compatibleGrids).filter
          fun term => term.family.recipe.erasedShape = shape)
      ((endpoint.collected.factors ++ extension.residualCorrections).filter
        fun term => term.family.recipe.erasedShape = shape)
    exact
      (extension.grids_perm_corrections).filter
        (fun term => term.family.recipe.erasedShape = shape)

/--
The precise residual normalization boundary: each shape-filtered suffix added
by compatible schedule completion has its own signed-block certificate.
-/
structure OperationalCompleteResidual : Prop where
  certificate :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (shape : CWord HPAtom),
      Nonempty
        (SBCert
          ((operationalCompleteCorrections endpoint).filter
            fun term => term.family.recipe.erasedShape = shape)
          shape)

/--
Subtract a certified completion residual from the certified endpoint-plus-
residual shape fiber.
-/
noncomputable def endpointBlockCertificate
    (cancellation :
      CHCancel)
    (residual : OperationalCompleteResidual)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    SBCert
      (endpoint.collected.factors.filter fun term =>
        term.family.recipe.erasedShape = shape)
      shape := by
  let whole :=
    endpointFilterCertificate cancellation endpoint shape
  let rejected := Classical.choice (residual.certificate endpoint shape)
  exact shapeCertificatePartition whole rejected <| by
    rw [List.filter_append]

/--
Residual normalization and shape-fiber ordering compile retained-grid
cancellation to certificates for every maximal operational shape block.
-/
noncomputable def operationalCompatibleShape
    (cancellation :
      CHCancel)
    (residual : OperationalCompleteResidual)
    (shapeFiber : OperationalShapeFiber) :
    OCShape where
  certificate endpoint block hblock word hterms := by
    rcases shapeFiber.filter_eq endpoint.collected block hblock with
      ⟨shape, hshape⟩
    let term :=
      block.head
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have hterm : term ∈ block :=
      List.head_mem
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have htermFilter :
        term ∈ endpoint.collected.factors.filter
          (fun next => next.family.recipe.erasedShape = shape) := by
      rw [hshape]
      exact hterm
    have htermShape :
        term.family.recipe.erasedShape = shape :=
      of_decide_eq_true (List.mem_filter.mp htermFilter).2
    have htermWord :
        term.family.recipe.erasedShape = word := by
      rw [← term.erased_shape_family]
      exact hterms term hterm
    have hshapeWord : shape = word :=
      htermShape.symm.trans htermWord
    have hendpointFilter :
        endpoint.collected.factors.filter
            (fun next => next.family.recipe.erasedShape = word) =
          block := by
      rw [← hshapeWord]
      exact hshape
    rw [← hendpointFilter]
    exact ⟨endpointBlockCertificate
      cancellation residual endpoint word⟩

end CRComp
end TCTex
end Towers

/-!
# Schedule-derived global symbolic recollection polynomials

This file packages the genuine compatible-routing compiler as a global
symbolic recollection boundary.  Under complete scheduler closure, retained
grid homogeneous cancellation, and endpoint shape-fiber order, every natural
source multiplicity pair has an explicit ordered signed-profile recollection
packet computing the powered commutator.

The packet may still depend on the natural multiplicities.  Replacing these
packets by one fixed ordered signed-profile packet is the remaining
stabilization theorem.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CGPolyno

open scoped commutatorElement

open HACoeff
open
  RGComp
open
  CSAggreg
open
  CSSpec
open
  CFSubsti
open
  SHPres
open MSCompre
open PPColl
open PPColl.RCColl.RPAggreg

/--
The three remaining truthful schedule boundaries needed to construct concrete
global symbolic recollection packets.
-/
structure OCGlobal : Prop where
  closure :
    OCReusea
  cancellation :
    CHCancel
  shapeFiber :
    OperationalShapeFiber

namespace OCGlobal

/-- Compile the schedule boundaries to explicit maximal-shape certificates. -/
noncomputable def shapeBlockSigned
    (kernel : OCGlobal) :
    OCShape :=
  operationalCompatibleShape
    kernel.closure kernel.cancellation kernel.shapeFiber

/-- Ordered schedule-derived signed-profile packet at one natural specialization. -/
noncomputable def concretePackets
    (kernel : OCGlobal)
    (M N : ℕ) :
    List RFPkt :=
  CSSpec.concretePackets
    kernel.shapeBlockSigned M N

/--
The schedule-derived concrete packet computes the powered commutator in the
universal free group.
-/
lemma list_packets_commutator
    (kernel : OCGlobal)
    (M N : ℕ) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
      packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  CSSpec.list_packets_commutator
    kernel.shapeBlockSigned M N

/--
The schedule-derived concrete packet specializes to every ambient group.
-/
lemma list_packets_group
    (kernel : OCGlobal)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [← specialize_listEval left right (M : ℤ) (N : ℤ)
      (kernel.concretePackets M N),
    kernel.list_packets_commutator M N]
  simp [map_commutatorElement, map_pow]

end OCGlobal

end CGPolyno
end TCTex
end Towers

/-!
# Residual-aware signed-block compilation from certified closed worklists

The homogeneous retained-grid cancellation kernel quantifies over every pair of
complete family packets.  The residual-aware operational compiler only consumes
the finitely many compatible grids opened while closing one genuine endpoint.

This file records that smaller interface.  A closed operational extension whose
opened grids already carry signed-block certificates compiles to the same
endpoint certificates after residual normalization.  The earlier universal
homogeneous cancellation kernel remains a sufficient source of the local
certificates, but is no longer built into the operational boundary.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  CWComp

open HACoeff
open CCGrida
open CCWork
open
  CTRoute
open
  CRCompa
open
  CCTrace
open
  CCFilter
open
  CRComp
open
  CSAdmiss
open
  CSAggreg
open
  CSFilter
open
  SHPres
open FMEnd
open MSCompre

/--
Filtering a worklist whose opened compatible grids already carry signed-block
certificates appends exactly the certificates of the retained shape fiber.
-/
lemma nonempty_grids_certified
    {M N K : ℕ}
    {worklist : CBWork M N K}
    (hworklist :
      CBWork.SignedBlockCertificates worklist)
    (shape : CWord HPAtom) :
    Nonempty
      (SBCert
        (worklist.compatibleGrids.filter fun term =>
          term.family.recipe.erasedShape = shape)
        shape) := by
  induction worklist with
  | nil =>
      exact ⟨SBCert.nil shape⟩
  | cons item worklist ih =>
      have hitem := hworklist item (by simp)
      have htail :
          CBWork.SignedBlockCertificates
            worklist := by
        intro next hnext
        exact hworklist next (by simp [hnext])
      rcases hitem with
        ⟨leftFamily, rightFamily, hleft, hright, ⟨itemCertificate⟩⟩
      rcases ih htail with ⟨tailCertificate⟩
      by_cases hshape :
          (leftFamily.correction rightFamily).recipe.erasedShape = shape
      · subst shape
        rw [CBWork.compatibleGrids,
          List.flatMap_cons, List.filter_append, List.filter_eq_self.2]
        · exact ⟨itemCertificate.append tailCertificate⟩
        · intro term hterm
          simpa only [decide_eq_true_eq] using
            family_compatible_grid
              hleft hright hterm
      · rw [CBWork.compatibleGrids,
          List.flatMap_cons, List.filter_append]
        have hfilter :
            (compatibleCorrectionGrid item.leftTerms item.rightTerms).filter
                (fun term => term.family.recipe.erasedShape = shape) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro term hterm htermShape
          apply hshape
          exact
            (family_compatible_grid
              hleft hright hterm).symm.trans
                (of_decide_eq_true htermShape)
        rw [hfilter, List.nil_append]
        exact ⟨tailCertificate⟩

/--
The inverse raw source followed by any certified compatible worklist has a
signed-block certificate after filtering by one erased Hall shape.
-/
noncomputable def grids_certificate_certified
    {M N : ℕ}
    {worklist : CBWork M N
      (inverseLabelledCollection M N).factors.length}
    (hworklist :
      CBWork.SignedBlockCertificates worklist)
    (shape : CWord HPAtom) :
    SBCert
      ((inverseDecoratedTerms M N ++ worklist.compatibleGrids).filter
        fun term => term.family.recipe.erasedShape = shape)
      shape := by
  rw [List.filter_append]
  exact
    (inverseFilterCertificate M N shape).append
      (Classical.choice
        (nonempty_grids_certified
          hworklist shape))

/--
The local operational cancellation boundary: every grid opened while finitely
closing one genuine endpoint already carries its signed-block certificate.
-/
structure OperationalCompleteClosed :
    Prop where
  certificates :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      CBWork.SignedBlockCertificates
        (operationalCompleteRouting endpoint).state.state.worklist

/--
The universal retained-grid homogeneous cancellation kernel implies the smaller
closed-extension certificate kernel consumed below.
-/
noncomputable def closedHomogeneousCancellation
    (cancellation :
      CHCancel) :
    OperationalCompleteClosed where
  certificates endpoint :=
    CBWork.HPPacket.signed_block_certi
      cancellation
        (operationalCompleteRouting endpoint).state.complete

/--
Every shape fiber of endpoint factors together with its completion residual has
a certificate once the concrete closed worklist grids are certified.
-/
noncomputable def endpointFilterCertificate
    (closedExtension :
      OperationalCompleteClosed)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    SBCert
      ((endpoint.collected.factors ++
        operationalCompleteCorrections endpoint).filter
          fun term => term.family.recipe.erasedShape = shape)
      shape := by
  let extension :=
    operationalCompleteRouting endpoint
  let certificate :=
    grids_certificate_certified
      (closedExtension.certificates endpoint) shape
  exact certificate.permTerms <| by
    change List.Perm
      ((inverseDecoratedTerms M N ++
        extension.state.state.worklist.compatibleGrids).filter
          fun term => term.family.recipe.erasedShape = shape)
      ((endpoint.collected.factors ++ extension.residualCorrections).filter
        fun term => term.family.recipe.erasedShape = shape)
    exact
      (extension.grids_perm_corrections).filter
        (fun term => term.family.recipe.erasedShape = shape)

/-- Remove a certified completion residual from a certified whole shape fiber. -/
noncomputable def endpointBlockCertificate
    (closedExtension :
      OperationalCompleteClosed)
    (residual : OperationalCompleteResidual)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    SBCert
      (endpoint.collected.factors.filter fun term =>
        term.family.recipe.erasedShape = shape)
      shape := by
  let whole :=
    endpointFilterCertificate closedExtension endpoint shape
  let rejected := Classical.choice (residual.certificate endpoint shape)
  exact shapeCertificatePartition whole rejected <| by
    rw [List.filter_append]

/--
Closed-extension certificates, residual normalization, and shape-fiber ordering
compile to certificates for every maximal operational shape block.
-/
noncomputable def operationalCompatibleShape
    (closedExtension :
      OperationalCompleteClosed)
    (residual : OperationalCompleteResidual)
    (shapeFiber : OperationalShapeFiber) :
    OCShape where
  certificate endpoint block hblock word hterms := by
    rcases shapeFiber.filter_eq endpoint.collected block hblock with
      ⟨shape, hshape⟩
    let term :=
      block.head
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have hterm : term ∈ block :=
      List.head_mem
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have htermFilter :
        term ∈ endpoint.collected.factors.filter
          (fun next => next.family.recipe.erasedShape = shape) := by
      rw [hshape]
      exact hterm
    have htermShape :
        term.family.recipe.erasedShape = shape :=
      of_decide_eq_true (List.mem_filter.mp htermFilter).2
    have htermWord :
        term.family.recipe.erasedShape = word := by
      rw [← term.erased_shape_family]
      exact hterms term hterm
    have hshapeWord : shape = word :=
      htermShape.symm.trans htermWord
    have hendpointFilter :
        endpoint.collected.factors.filter
            (fun next => next.family.recipe.erasedShape = word) =
          block := by
      rw [← hshapeWord]
      exact hshape
    rw [← hendpointFilter]
    exact ⟨endpointBlockCertificate
      closedExtension residual endpoint word⟩

end CWComp
end TCTex
end Towers

/-!
# Residual-aware global symbolic recollection polynomials

This file packages the finite compatible-schedule drain as a global symbolic
recollection boundary.  Complete scheduler closure is no longer assumed.
Instead, the exact residual suffix introduced by schedule completion is exposed
and normalized separately.  Under retained-grid homogeneous cancellation,
residual signed-block normalization, and endpoint shape-fiber order, every
natural source multiplicity pair has an explicit ordered signed-profile packet
computing the powered commutator.

The packet may still depend on the natural multiplicities.  Replacing these
packets by one fixed ordered signed-profile packet remains a stabilization
theorem.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  GRPolyno

open scoped commutatorElement

open HACoeff
open
  CRComp
open
  CSAggreg
open
  CSSpec
open
  CFSubsti
open
  SHPres
open MSCompre
open PPColl
open PPColl.RCColl.RPAggreg

/--
The three residual-aware boundaries needed to construct concrete global
symbolic recollection packets.
-/
structure OCComple :
    Prop where
  cancellation :
    CHCancel
  residual :
    OperationalCompleteResidual
  shapeFiber :
    OperationalShapeFiber

namespace OCComple

/-- Compile residual-aware boundaries to explicit maximal-shape certificates. -/
noncomputable def shapeBlockSigned
    (kernel :
      OCComple) :
    OCShape :=
  operationalCompatibleShape
    kernel.cancellation kernel.residual kernel.shapeFiber

/-- Ordered residual-aware signed-profile packet at one natural specialization. -/
noncomputable def concretePackets
    (kernel :
      OCComple)
    (M N : ℕ) :
    List RFPkt :=
  CSSpec.concretePackets
    kernel.shapeBlockSigned M N

/--
The residual-aware concrete packet computes the powered commutator in the
universal free group.
-/
lemma list_packets_commutator
    (kernel :
      OCComple)
    (M N : ℕ) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
      packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  CSSpec.list_packets_commutator
    kernel.shapeBlockSigned M N

/-- The residual-aware concrete packet specializes to every ambient group. -/
lemma list_packets_group
    (kernel :
      OCComple)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [← specialize_listEval left right (M : ℤ) (N : ℤ)
      (kernel.concretePackets M N),
    kernel.list_packets_commutator M N]
  simp [map_commutatorElement, map_pow]

end OCComple

end GRPolyno
end TCTex
end Towers

/-!
# Completion residuals are genuine-prefix pending terms

Finite completion drains the pending slots left by the genuine compatible
reuse-routing prefix.  This file flattens those pending ledgers and proves that
the residual correction suffix introduced by completion is exactly that
flattened pending list up to permutation.

Residual signed-block normalization can therefore be stated directly on the
genuine operational prefix, independently of the implementation details of the
finite drain.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RPCorr

open HACoeff
open CTRoutea
open CCWork
open
  CRRoutec
open
  CRCompa
open
  CRComp
open
  CSAggreg
open FMEnd

/-- Concrete terms still pending across every opened compatible batch. -/
def batchWorklistPending
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    List (DFTerm M N K) :=
  worklist.flatMap fun item => item.ledger.pending

/--
For every compatible worklist, flattened emitted terms followed by flattened
pending terms account for all opened compatible grids up to permutation.
-/
lemma emitted_pending_grids
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    List.Perm
      (batchWorklistEmitted worklist ++
        batchWorklistPending worklist)
      worklist.compatibleGrids := by
  induction worklist with
  | nil =>
      rfl
  | cons item worklist ih =>
      apply List.Perm.trans
      · have hcomm :
            List.Perm
              (batchWorklistEmitted worklist ++
                item.ledger.pending)
              (item.ledger.pending ++
                batchWorklistEmitted worklist) :=
          List.perm_append_comm
        simpa [batchWorklistEmitted,
          batchWorklistPending,
          CBWork.compatibleGrids,
          List.append_assoc] using
            (hcomm.append_left item.ledger.emitted).append_right
              (batchWorklistPending worklist)
      · simpa [batchWorklistEmitted,
          batchWorklistPending,
          CBWork.compatibleGrids,
          List.append_assoc] using
            List.Perm.append item.ledger.accounting ih

/--
The suffix added by finite completion is exactly the pending-term flattening of
the genuine compatible reuse-routing prefix, up to permutation.
-/
lemma pending_perm_corrections
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint) :
    List.Perm
      (batchWorklistPending
        (reuseRoutingPrefix endpoint).state.state.worklist)
      extension.residualCorrections := by
  let routingPrefix :=
    reuseRoutingPrefix endpoint
  have hemitted :
      List.Perm
        (batchWorklistEmitted
          routingPrefix.state.state.worklist)
        endpoint.corrections := by
    apply routingPrefix.state.state.emitted_perm.trans
    rw [routingPrefix.routed_eq]
  have hgrids :
      List.Perm routingPrefix.state.state.worklist.compatibleGrids
        (endpoint.corrections ++ extension.residualCorrections) := by
    rw [← extension.compatible_grids_prefix]
    exact extension.compatible_grids_perm
  have hwhole :
      List.Perm
        (endpoint.corrections ++
          batchWorklistPending
            routingPrefix.state.state.worklist)
        (endpoint.corrections ++ extension.residualCorrections) := by
    apply (hemitted.append_right
      (batchWorklistPending
        routingPrefix.state.state.worklist)).symm.trans
    exact
      (emitted_pending_grids
        routingPrefix.state.state.worklist).trans hgrids
  exact (List.perm_append_left_iff endpoint.corrections).mp hwhole

/-- Shape filtering preserves the pending-term/residual permutation. -/
lemma filter_pending_corrections
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint)
    (shape : CWord HPAtom) :
    List.Perm
      ((batchWorklistPending
        (reuseRoutingPrefix endpoint).state.state.worklist).filter
          fun term => term.family.recipe.erasedShape = shape)
      (extension.residualCorrections.filter fun term =>
        term.family.recipe.erasedShape = shape) :=
  (pending_perm_corrections extension).filter
    (fun term => term.family.recipe.erasedShape = shape)

/--
The residual-normalization boundary stated directly on the pending slots of
the genuine operational routing prefix.
-/
structure OperationalCompletePending :
    Prop where
  certificate :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (shape : CWord HPAtom),
      Nonempty
        (SBCert
          ((batchWorklistPending
            (reuseRoutingPrefix endpoint).state.state.worklist).filter
              fun term => term.family.recipe.erasedShape = shape)
          shape)

/-- Pending-prefix normalization implies completion-residual normalization. -/
noncomputable def residualPrefixPending
    (pending : OperationalCompletePending) :
    OperationalCompleteResidual where
  certificate endpoint shape := by
    let extension :=
      operationalCompleteRouting endpoint
    let certificate := Classical.choice (pending.certificate endpoint shape)
    exact ⟨certificate.permTerms
      (filter_pending_corrections extension shape)⟩

/-- Completion-residual normalization also implies pending-prefix normalization. -/
noncomputable def prefixPendingResidual
    (residual : OperationalCompleteResidual) :
    OperationalCompletePending where
  certificate endpoint shape := by
    let extension :=
      operationalCompleteRouting endpoint
    let certificate := Classical.choice (residual.certificate endpoint shape)
    exact ⟨certificate.permTerms
      (filter_pending_corrections extension shape).symm⟩

end RPCorr
end TCTex
end Towers

/-!
# Residual-aware global recollection from aggregated closed-worklist certificates

Retained-grid support formulas may contain inhomogeneous intermediate terms.
Their cancellation need not occur grid by grid.  The global operational
recollection argument only needs one signed-block certificate for each
shape-filtered aggregate of the finitely many grids opened while closing a
genuine endpoint.

This file records that weaker boundary and compiles it all the way to ordered
concrete recollection packets.  Individually certified worklists remain a
sufficient source of aggregate certificates.

The packets may still depend on the natural multiplicities.  Fixed packet
stabilization, aggregate cancellation, residual normalization, and shape-fiber
ordering remain separate theorems.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace WRPolys

open scoped commutatorElement

open HACoeff
open CCWork
open
  CWComp
open
  CRCompa
open
  CCFilter
open
  CRComp
open
  CSAdmiss
open
  CSAggreg
open
  CSSpec
open
  CSFilter
open
  CFSubsti
open FMEnd
open MSCompre
open PPColl
open PPColl.RCColl.RPAggreg

/--
The finite closed-worklist cancellation boundary: after aggregation, every
shape-filtered collection of opened compatible grids has a signed-block
certificate.
-/
structure OperationalCompatibleAggregated :
    Prop where
  certificate :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (shape : CWord HPAtom),
      Nonempty
        (SBCert
          ((operationalCompleteRouting
            endpoint).state.state.worklist.compatibleGrids.filter
            fun term => term.family.recipe.erasedShape = shape)
          shape)

/--
Grid-by-grid certificates imply the weaker aggregate closed-worklist
certificate boundary.
-/
noncomputable def aggregatedClosedBlocks
    (closedExtension :
      OperationalCompleteClosed) :
    OperationalCompatibleAggregated where
  certificate endpoint shape :=
    nonempty_grids_certified
      (closedExtension.certificates endpoint) shape

/--
The inverse raw source followed by the aggregate closed-worklist grids has a
shape-filtered certificate.
-/
noncomputable def gridsFilterCertificate
    (aggregated :
      OperationalCompatibleAggregated)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    SBCert
      ((inverseDecoratedTerms M N ++
        (operationalCompleteRouting
          endpoint).state.state.worklist.compatibleGrids).filter
          fun term => term.family.recipe.erasedShape = shape)
      shape := by
  rw [List.filter_append]
  exact
    (inverseFilterCertificate M N shape).append
      (Classical.choice (aggregated.certificate endpoint shape))

/--
Aggregate closed-worklist cancellation certifies endpoint factors together with
the residual suffix introduced by finite schedule completion.
-/
noncomputable def endpointFilterCertificate
    (aggregated :
      OperationalCompatibleAggregated)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    SBCert
      ((endpoint.collected.factors ++
        operationalCompleteCorrections endpoint).filter
          fun term => term.family.recipe.erasedShape = shape)
      shape := by
  let extension :=
    operationalCompleteRouting endpoint
  let certificate :=
    gridsFilterCertificate
      aggregated endpoint shape
  exact certificate.permTerms <| by
    change List.Perm
      ((inverseDecoratedTerms M N ++
        extension.state.state.worklist.compatibleGrids).filter
          fun term => term.family.recipe.erasedShape = shape)
      ((endpoint.collected.factors ++ extension.residualCorrections).filter
        fun term => term.family.recipe.erasedShape = shape)
    exact
      (extension.grids_perm_corrections).filter
        (fun term => term.family.recipe.erasedShape = shape)

/-- Subtract the separately certified residual suffix. -/
noncomputable def endpointBlockCertificate
    (aggregated :
      OperationalCompatibleAggregated)
    (residual : OperationalCompleteResidual)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    SBCert
      (endpoint.collected.factors.filter fun term =>
        term.family.recipe.erasedShape = shape)
      shape := by
  let whole :=
    endpointFilterCertificate aggregated endpoint shape
  let rejected := Classical.choice (residual.certificate endpoint shape)
  exact shapeCertificatePartition whole rejected <| by
    rw [List.filter_append]

/--
Aggregate cancellation, residual normalization, and shape-fiber ordering
compile to certificates for every maximal operational shape block.
-/
noncomputable def operationalCompatibleShape
    (aggregated :
      OperationalCompatibleAggregated)
    (residual : OperationalCompleteResidual)
    (shapeFiber : OperationalShapeFiber) :
    OCShape where
  certificate endpoint block hblock word hterms := by
    rcases shapeFiber.filter_eq endpoint.collected block hblock with
      ⟨shape, hshape⟩
    let term :=
      block.head
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have hterm : term ∈ block :=
      List.head_mem
        (OCAdmiss.nil_same_blocks
          endpoint block hblock)
    have htermFilter :
        term ∈ endpoint.collected.factors.filter
          (fun next => next.family.recipe.erasedShape = shape) := by
      rw [hshape]
      exact hterm
    have htermShape :
        term.family.recipe.erasedShape = shape :=
      of_decide_eq_true (List.mem_filter.mp htermFilter).2
    have htermWord :
        term.family.recipe.erasedShape = word := by
      rw [← term.erased_shape_family]
      exact hterms term hterm
    have hshapeWord : shape = word :=
      htermShape.symm.trans htermWord
    have hendpointFilter :
        endpoint.collected.factors.filter
            (fun next => next.family.recipe.erasedShape = word) =
          block := by
      rw [← hshapeWord]
      exact hshape
    rw [← hendpointFilter]
    exact ⟨endpointBlockCertificate
      aggregated residual endpoint word⟩

/--
The three aggregate residual-aware boundaries needed to construct concrete
global symbolic recollection packets.
-/
structure OCAggreg :
    Prop where
  aggregated :
    OperationalCompatibleAggregated
  residual :
    OperationalCompleteResidual
  shapeFiber :
    OperationalShapeFiber

namespace OCAggreg

/-- Compile aggregate residual-aware boundaries to maximal-shape certificates. -/
noncomputable def shapeBlockSigned
    (kernel :
      OCAggreg) :
    OCShape :=
  operationalCompatibleShape
    kernel.aggregated kernel.residual kernel.shapeFiber

/-- Ordered aggregate residual-aware packet at one natural specialization. -/
noncomputable def concretePackets
    (kernel :
      OCAggreg)
    (M N : ℕ) :
    List RFPkt :=
  CSSpec.concretePackets
    kernel.shapeBlockSigned M N

/-- The aggregate residual-aware packet computes the powered commutator. -/
lemma list_packets_commutator
    (kernel :
      OCAggreg)
    (M N : ℕ) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
      packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  CSSpec.list_packets_commutator
    kernel.shapeBlockSigned M N

/-- The aggregate residual-aware packet specializes to every ambient group. -/
lemma list_packets_group
    (kernel :
      OCAggreg)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [← specialize_listEval left right (M : ℤ) (N : ℤ)
      (kernel.concretePackets M N),
    kernel.list_packets_commutator M N]
  simp [map_commutatorElement, map_pow]

end OCAggreg

end WRPolys
end TCTex
end Towers

/-!
# Empty-residual adapter for global symbolic recollection

The residual-aware compiler is a weakening of the earlier closed-prefix
compiler.  When the genuine compatible routing prefix is already closed, its
finite drain adds no residual corrections.  The empty signed-block certificate
therefore discharges residual normalization.

This file records the adapter explicitly.  It is intentionally not imported by
the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  RRAdapt

open
  RGComp
open
  CRRoutec
open
  CRCompa
open
  CGPolyno
open
  GRPolyno
open
  CRComp
open
  CSAggreg
open FMEnd

/-- A closed genuine compatible prefix has no completion residual. -/
lemma operational_nil_closed
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hclosed :
      (reuseRoutingPrefix
        endpoint).state.state.worklist.Closed) :
    operationalCompleteCorrections endpoint = [] := by
  simp [operationalCompleteCorrections,
    operationalCompleteRouting,
    hclosed,
    (reuseRoutingPrefix endpoint).routed_eq,
    OCRoute.residualCorrections]

/-- Earlier complete-prefix closure discharges residual normalization trivially. -/
noncomputable def residualBlockClosure
    (closure : OCReusea) :
    OperationalCompleteResidual where
  certificate endpoint shape := by
    rw [operational_nil_closed
      endpoint (closure.closed endpoint)]
    exact ⟨SBCert.nil shape⟩

/-- Forget empty-residual closure in favor of the weaker residual-aware API. -/
noncomputable def residualGlobalClosure
    (kernel : OCGlobal) :
    OCComple where
  cancellation := kernel.cancellation
  residual := residualBlockClosure kernel.closure
  shapeFiber := kernel.shapeFiber

end RRAdapt
end TCTex
end Towers

/-!
# Inhomogeneous formula packets for aggregated closed compatible worklists

Fixed physical-slot support deletion produces inhomogeneous intermediate
packets.  Cancellation may occur only after aggregating several compatible
grids opened by the operational scheduler.  This file constructs the exact
unrestricted packet for one shape-filtered closed worklist aggregate and proves
that its natural specialization is the corresponding concrete filtered-grid
length.

The remaining algebraic boundary is now precise: exhibit one homogeneous
presentation of this aggregate unrestricted packet in the target Hall
bidegree.  Such a presentation compiles directly to the aggregate signed-block
kernel consumed by residual-aware global recollection.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CIComp

open scoped commutatorElement

open HACoeff
open CCGrida
open CCWork
open
  WRPolys
open
  CTRoute
open
  CRCompa
open
  CCFilter
open
  CRComp
open
  CSAggreg
open
  CFSubsti
open
  SHPres
open
  CSComp
open FMEnd
open MSCompre
open HSPacket
open PPColl
open PPColl.RCColl.RPAggreg

/--
The complete represented parent packets and one genuine compatible witness
carried by an opened scheduler batch.
-/
structure CCBatch
    {M N K : ℕ}
    (item : BWItem M N K) where
  leftFamily :
    BFam M N
  rightFamily :
    BFam M N
  left :
    RPFor leftFamily item.leftTerms
  right :
    RPFor rightFamily item.rightTerms
  leftWitness :
    DFTerm M N K
  leftWitness_mem :
    leftWitness ∈ item.leftTerms
  rightWitness :
    DFTerm M N K
  rightWitness_mem :
    rightWitness ∈ item.rightTerms
  compatible :
    correctionPairCompatible leftWitness rightWitness

namespace CCBatch

open AISpec

/-- Choose the recorded complete parents and compatible witness of one batch. -/
noncomputable def completeParentPackets
    {M N K : ℕ}
    (item : BWItem M N K)
    (hitem : BWItem.HPPacket item) :
    CCBatch item :=
  Classical.choice <| by
    rcases hitem with
      ⟨leftFamily, rightFamily, left, right,
        leftWitness, leftWitness_mem, rightWitness, rightWitness_mem,
        compatible⟩
    exact ⟨{
      leftFamily := leftFamily
      rightFamily := rightFamily
      left := left
      right := right
      leftWitness := leftWitness
      leftWitness_mem := leftWitness_mem
      rightWitness := rightWitness
      rightWitness_mem := rightWitness_mem
      compatible := compatible }⟩

/-- The erased Hall shape shared by every term in one retained compatible grid. -/
def erasedShape
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item) :
    CWord HPAtom :=
  (packet.leftFamily.correction packet.rightFamily).recipe.erasedShape

/-- The unrestricted physical-slot formula packet of one retained grid. -/
noncomputable def inhomogeneousFormulaPacket
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item) :
    IFPkt :=
  AISpec.compatibleGridPackets
    packet.left packet.right

/-- Every term retained by one batch has the batch correction-family shape. -/
lemma shape_compatible_grid
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item)
    {term : DFTerm M N K}
    (hterm : term ∈ compatibleCorrectionGrid item.leftTerms item.rightTerms) :
    term.family.recipe.erasedShape = packet.erasedShape :=
  family_compatible_grid
    packet.left packet.right hterm

/-- One unrestricted retained-grid packet specializes to its concrete length. -/
lemma inhomogeneous_compatible_grid
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item) :
    packet.inhomogeneousFormulaPacket.value (M : ℤ) (N : ℤ) =
      ((compatibleCorrectionGrid item.leftTerms item.rightTerms).length : ℤ) := by
  apply
    compat_grid_length
      packet.left packet.right
  · intro leftTerm hleftTerm
    rw [leftTerm.erased_shape_family,
      packet.left.family_eq_mem hleftTerm]
  · intro rightTerm hrightTerm
    rw [rightTerm.erased_shape_family,
      packet.right.family_eq_mem hrightTerm]
  · exact packet.leftWitness_mem
  · exact packet.rightWitness_mem
  · exact packet.compatible

end CCBatch

open IFPkt

/--
Sum the unrestricted retained-grid packets of exactly those opened batches
whose correction-family erased shape is the target shape.
-/
noncomputable def compatibleGridsInhomogeneous
    {M N K : ℕ} :
    (worklist : CBWork M N K) →
      CBWork.HPPacket worklist →
        CWord HPAtom →
          IFPkt
  | [], _hworklist, _shape =>
      zero
  | item :: worklist, hworklist, shape =>
      let itemPacket :=
        CCBatch.completeParentPackets
          item (hworklist item (by simp))
      let tailPacket :=
        compatibleGridsInhomogeneous worklist
          (fun next hnext => hworklist next (by simp [hnext])) shape
      if itemPacket.erasedShape = shape then
        add itemPacket.inhomogeneousFormulaPacket tailPacket
      else
        tailPacket

/--
The aggregate unrestricted packet specializes to the concrete length of the
shape-filtered flattened compatible grids.
-/
lemma grids_inhomogeneous_length
    {M N K : ℕ} :
    ∀ (worklist : CBWork M N K)
      (hworklist :
        CBWork.HPPacket worklist)
      (shape : CWord HPAtom),
      (compatibleGridsInhomogeneous
          worklist hworklist shape).value (M : ℤ) (N : ℤ) =
        ((worklist.compatibleGrids.filter fun term =>
          term.family.recipe.erasedShape = shape).length : ℤ)
  | [], _hworklist, _shape => by
      rfl
  | item :: worklist, hworklist, shape => by
      let itemPacket :=
        CCBatch.completeParentPackets
          item (hworklist item (by simp))
      have htail :
          CBWork.HPPacket
            worklist :=
        fun next hnext => hworklist next (by simp [hnext])
      rw [compatibleGridsInhomogeneous]
      simp only [CBWork.compatibleGrids,
        List.flatMap_cons, List.filter_append, List.length_append,
        Int.natCast_add]
      by_cases hshape : itemPacket.erasedShape = shape
      · rw [if_pos hshape, value_add,
          itemPacket.inhomogeneous_compatible_grid,
          grids_inhomogeneous_length
            worklist htail shape]
        congr 1
        rw [List.filter_eq_self.2]
        intro term hterm
        simpa only [decide_eq_true_eq, hshape] using
          itemPacket.shape_compatible_grid hterm
      · rw [if_neg hshape,
          grids_inhomogeneous_length
            worklist htail shape]
        have hfilter :
            (compatibleCorrectionGrid item.leftTerms item.rightTerms).filter
                (fun term => term.family.recipe.erasedShape = shape) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro term hterm htermShape
          apply hshape
          exact
            (itemPacket.shape_compatible_grid
              hterm).symm.trans
                (of_decide_eq_true htermShape)
        rw [hfilter]
        simp [CBWork.compatibleGrids]

/-- The unrestricted aggregate packet attached to one closed endpoint extension. -/
noncomputable def closedInhomogeneousShape
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    IFPkt :=
  let extension :=
    operationalCompleteRouting endpoint
  compatibleGridsInhomogeneous
    extension.state.state.worklist extension.state.complete shape

/--
The closed-extension unrestricted packet specializes to the concrete aggregate
filtered-grid length.
-/
lemma inhomogeneous_cast_length
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    (closedInhomogeneousShape endpoint shape).value
        (M : ℤ) (N : ℤ) =
      (((operationalCompleteRouting
        endpoint).state.state.worklist.compatibleGrids.filter
        fun term => term.family.recipe.erasedShape = shape).length : ℤ) :=
  grids_inhomogeneous_length
    (operationalCompleteRouting endpoint).state.state.worklist
    (operationalCompleteRouting endpoint).state.complete
    shape

/--
The exact aggregate cancellation theorem still needed from physical-slot
support algebra: each closed-extension unrestricted packet has a homogeneous
presentation in its target Hall bidegree.
-/
structure OperationalAggregatedHomogeneous :
    Prop where
  presentation :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (shape : CWord HPAtom),
      Nonempty
        (HPres
          (closedInhomogeneousShape endpoint shape)
          shape.pairLeftDegree shape.pairRightDegree)

/--
Aggregate homogeneous presentations compile to the concrete aggregate
signed-block certificates consumed by residual-aware recollection.
-/
noncomputable def aggregatedHomogeneousPresentations
    (kernel :
      OperationalAggregatedHomogeneous) :
    OperationalCompatibleAggregated where
  certificate endpoint shape := by
    let presentation := Classical.choice (kernel.presentation endpoint shape)
    exact ⟨presentation.shapeBlockCertificate <|
      inhomogeneous_cast_length
        endpoint shape⟩

/--
Aggregate homogeneous presentations, residual normalization, and shape-fiber
ordering are the precise remaining boundaries for the residual-aware global
symbolic recollection packet.
-/
structure
  OAPres :
    Prop where
  presentations :
    OperationalAggregatedHomogeneous
  residual :
    OperationalCompleteResidual
  shapeFiber :
    OperationalShapeFiber

namespace
  OAPres

/-- Forget aggregate presentations to the concrete aggregate certificate facade. -/
noncomputable def aggregatedGlobalRecollection
    (kernel :
      OAPres) :
    OCAggreg where
  aggregated :=
    aggregatedHomogeneousPresentations kernel.presentations
  residual := kernel.residual
  shapeFiber := kernel.shapeFiber

/-- Ordered packet at one natural specialization. -/
noncomputable def concretePackets
    (kernel :
      OAPres)
    (M N : ℕ) :
    List RFPkt :=
  kernel.aggregatedGlobalRecollection.concretePackets M N

/-- The presentation-derived aggregate packet computes the powered commutator. -/
lemma list_packets_commutator
    (kernel :
      OAPres)
    (M N : ℕ) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
      packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  kernel.aggregatedGlobalRecollection.list_packets_commutator
    M N

/-- The presentation-derived aggregate packet specializes to every ambient group. -/
lemma list_packets_group
    (kernel :
      OAPres)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
      packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  let compiled := kernel.aggregatedGlobalRecollection
  exact compiled.list_packets_group M N left right

end OAPres

end CIComp
end TCTex
end Towers

/-!
# Equivalent forms of empty compatible-routing residuals

The genuine compatible reuse-first scheduler need not exhaust every opened
grid.  Finite completion drains the remaining slots and records them as a
residual suffix.  This file identifies that suffix exactly:

* a compatible worklist is closed iff its flattened pending list is empty;
* a routed state is closed iff its opened compatible grids permute to the
  routed correction list;
* a completion residual is empty iff the genuine operational prefix was
  already closed.

Thus empty-residual closure is not an extra presentation artifact.  It is
precisely the assertion that the genuine scheduler trace exhausts the
compatible grids it opens.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex


namespace
  CREquiv

open
  RGClosa
open
  CTRoutea
open
  CCWork
open
  RGComp
open
  CRRoutec
open
  CRCompa
open
  RPCorr
open
  CRComp
open FMEnd

namespace CBWork

/--
A compatible worklist is closed exactly when the flattening of its pending
ledgers is empty.
-/
lemma closed_pending_nil
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    worklist.Closed ↔
      batchWorklistPending worklist = [] := by
  constructor
  · intro hclosed
    apply List.flatMap_eq_nil_iff.2
    intro item hitem
    exact hclosed item hitem
  · intro hpending item hitem
    exact (List.flatMap_eq_nil_iff.mp hpending) item hitem

/-- Flattened pending-term length is the worklist pending-slot measure. -/
lemma length_pendingTerms
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    (batchWorklistPending worklist).length =
      worklist.pendingSlots := by
  rw [batchWorklistPending, List.length_flatMap,
    CBWork.pendingSlots]
  congr 1

/-- A compatible worklist is closed exactly when its pending-slot measure is zero. -/
lemma closed_pending_slots
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    worklist.Closed ↔ worklist.pendingSlots = 0 := by
  rw [closed_pending_nil, ← List.length_eq_zero_iff,
    length_pendingTerms]

end CBWork

namespace CRState

/--
A routed compatible state is closed exactly when its opened compatible grids
permute to the correction terms routed so far.
-/
lemma worklist_grids_routed
    {M N K : ℕ}
    (state : CRState M N K) :
    state.worklist.Closed ↔
      List.Perm state.worklist.compatibleGrids state.routedTerms := by
  constructor
  · intro hclosed
    apply List.Perm.trans
      (OCReuse.emitted_grids_closed
        state.worklist hclosed).symm
    exact state.emitted_perm
  · intro hgrids
    apply
      (CBWork.closed_pending_nil
        state.worklist).2
    apply List.eq_nil_of_length_eq_zero
    have haccounting :=
      (emitted_pending_grids
        state.worklist).length_eq
    have hemitted :=
      state.emitted_perm.length_eq
    have hgridsLength :=
      hgrids.length_eq
    simp only [List.length_append] at haccounting
    omega

end CRState

/--
The complete genuine routing prefix is closed exactly when its opened
compatible grids permute to the operational correction list.
-/
lemma reuse_routing_grids
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    (reuseRoutingPrefix
      endpoint).state.state.worklist.Closed ↔
      List.Perm
        (reuseRoutingPrefix
          endpoint).state.state.worklist.compatibleGrids
        endpoint.corrections := by
  let routingPrefix :=
    reuseRoutingPrefix endpoint
  have hclosed :=
    CRState.worklist_grids_routed
      routingPrefix.state.state
  rw [routingPrefix.routed_eq] at hclosed
  exact hclosed

/--
For any chosen finite closed extension, its residual suffix is empty exactly
when the genuine compatible routing prefix was already closed.
-/
lemma corrections_nil_closed
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint) :
    extension.residualCorrections = [] ↔
      (reuseRoutingPrefix
        endpoint).state.state.worklist.Closed := by
  have hperm :=
    pending_perm_corrections extension
  constructor
  · intro hresidual
    apply
      (CBWork.closed_pending_nil
        (reuseRoutingPrefix
          endpoint).state.state.worklist).2
    apply List.eq_nil_of_length_eq_zero
    rw [hperm.length_eq, hresidual]
    rfl
  · intro hclosed
    apply List.eq_nil_of_length_eq_zero
    rw [← hperm.length_eq,
      (CBWork.closed_pending_nil
        (reuseRoutingPrefix
          endpoint).state.state.worklist).1 hclosed]
    rfl

/--
The completion residual length is exactly the number of slots still pending
in the genuine compatible routing prefix.
-/
lemma corrections_pending_slots
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint) :
    extension.residualCorrections.length =
      (reuseRoutingPrefix
        endpoint).state.state.worklist.pendingSlots := by
  rw [← (pending_perm_corrections extension).length_eq,
    CBWork.length_pendingTerms]

/--
The canonical finite-completion residual vanishes exactly when the genuine
compatible routing prefix was already closed.
-/
lemma operational_corrections_closed
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    operationalCompleteCorrections endpoint = [] ↔
      (reuseRoutingPrefix
        endpoint).state.state.worklist.Closed :=
  corrections_nil_closed
    (operationalCompleteRouting endpoint)

/--
The canonical completion residual length is the genuine prefix pending-slot
measure.
-/
lemma length_pending_slots
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    (operationalCompleteCorrections endpoint).length =
      (reuseRoutingPrefix
        endpoint).state.state.worklist.pendingSlots :=
  corrections_pending_slots
    (operationalCompleteRouting endpoint)

/--
The canonical residual vanishes exactly when the opened compatible grids
permute to the genuine operational correction list.
-/
theorem operational_grids_perm
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    operationalCompleteCorrections endpoint = [] ↔
      List.Perm
        (reuseRoutingPrefix
          endpoint).state.state.worklist.compatibleGrids
        endpoint.corrections :=
  (operational_corrections_closed
      endpoint).trans
    (reuse_routing_grids
      endpoint)

/--
The global complete-prefix closure kernel is equivalent to saying that every
canonical completion residual is empty.
-/
theorem operational_reuse_nil :
    OCReusea ↔
      ∀ {M N : ℕ}
        (endpoint : ODEmissi M N),
        operationalCompleteCorrections endpoint = [] := by
  constructor
  · intro closure M N endpoint
    exact
      (operational_corrections_closed
        endpoint).2 (closure.closed endpoint)
  · intro hresidual
    exact {
      closed := fun endpoint =>
        (operational_corrections_closed
          endpoint).1 (hresidual endpoint) }

/--
The global complete-prefix closure kernel is equivalently the assertion that
every opened compatible-grid flattening permutes to the operational correction
trace.
-/
theorem
  reuse_grids_corrections :
    OCReusea ↔
      ∀ {M N : ℕ}
        (endpoint : ODEmissi M N),
        List.Perm
          (reuseRoutingPrefix
            endpoint).state.state.worklist.compatibleGrids
          endpoint.corrections := by
  constructor
  · intro closure M N endpoint
    exact
      (reuse_routing_grids
        endpoint).1 (closure.closed endpoint)
  · intro hgrids
    exact {
      closed := fun endpoint =>
        (reuse_routing_grids
          endpoint).2 (hgrids endpoint) }

end
  CREquiv
end TCTex
end Towers

/-!
# Fixed-packet stabilization after aggregate presentation and residual normalization

Closed compatible-grid aggregates carry homogeneous presentations, while the
residual suffix introduced by finite scheduler completion is normalized by a
separate concrete signed-block certificate.  Together with endpoint shape-fiber
ordering, these truthful boundaries produce one concrete ordered signed-profile
packet at each pair of natural source multiplicities.

This file isolates the remaining global theorem: replace those
multiplicity-dependent concrete packets by one fixed ordered packet list.  The
comparison is order-aware.  It does not require a homogeneous presentation of
the pending suffix by itself.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex


namespace
  AFStab

universe u

open scoped commutatorElement

open
  CIComp
open
  CSSpec
open
  CFExp
open
  CFSubsti
open
  UNPkt
open PPColl
open PPColl.RCColl.RPAggreg

/--
The order-aware fixed-packet stabilization theorem left after aggregate
homogeneous presentation, residual normalization, and shape-fiber ordering.
-/
structure
    CAStab
    (kernel :
      OAPres)
    (fixedPackets : List RFPkt) :
    Prop where
  packet_prod_concrete :
    ∀ (M N : ℕ),
      (fixedPackets.map fun packet =>
        packet.word.eval (HPAtom.eval universalLeft universalRight) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod =
        ((kernel.concretePackets M N).map fun packet =>
          packet.word.eval (HPAtom.eval universalLeft universalRight) ^
            packet.profiles.value (M : ℤ) (N : ℤ)).prod

namespace
  CAStab

/-- Fixed-packet stabilization proves the natural Hall-Petresco identity in
the universal group. -/
lemma nat_cast_pow
    {kernel :
      OAPres}
    {fixedPackets : List RFPkt}
    (stabilization :
      CAStab
        kernel fixedPackets)
    (M N : ℕ) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  (stabilization.packet_prod_concrete M N).trans
    (kernel.list_packets_commutator M N)

/-- Universal-group fixed-packet stabilization specializes to every ambient
group. -/
lemma nat_cast_group
    {kernel :
      OAPres}
    {fixedPackets : List RFPkt}
    (stabilization :
      CAStab
        kernel fixedPackets)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [← specialize_listEval left right (M : ℤ) (N : ℤ) fixedPackets,
    stabilization.nat_cast_pow M N]
  simp [map_commutatorElement, map_pow]

/-- A fixed stabilized packet supplies the natural packet interface consumed
by signed-profile collection. -/
def truncNaturalPacket
    {kernel :
      OAPres}
    {fixedPackets : List RFPkt}
    (stabilization :
      CAStab
        kernel fixedPackets)
    (d n : ℕ) :
    TBPkt.{u} d n where
  packets := fixedPackets
  list_nat_cast left right M N :=
    stabilization.nat_cast_group M N left right

end
  CAStab

/--
A universal all-integral signed packet automa stabilizes against every
concrete packet produced by the aggregate-presentation residual-aware route.
-/
noncomputable def
    naturalStabilizationIntegral
    (kernel :
      OAPres)
    (packet : UAPkt.{0}) :
      CAStab
      kernel packet.packets where
  packet_prod_concrete M N := by
    calc
      (packet.packets.map fun nextPacket =>
        nextPacket.word.eval
            (HPAtom.eval universalLeft universalRight) ^
          nextPacket.profiles.value (M : ℤ) (N : ℤ)).prod =
          ⁅universalLeft ^ M, universalRight ^ N⁆ := by
        simpa only [zpow_natCast] using
          packet.listEval_eq universalLeft universalRight (M : ℤ) (N : ℤ)
      _ = ((kernel.concretePackets M N).map fun nextPacket =>
          nextPacket.word.eval
              (HPAtom.eval universalLeft universalRight) ^
            nextPacket.profiles.value (M : ℤ) (N : ℤ)).prod :=
        (kernel.list_packets_commutator M N).symm

/--
An all-integral packet with the same fixed packet list is the signed lift of a
stabilized natural packet at every free lower-central cutoff.
-/
def allUniversalPacket
    {kernel :
      OAPres}
    {fixedPackets : List RFPkt}
    (stabilization :
      CAStab
        kernel fixedPackets)
    (packet : UAPkt.{u})
    (hpackets : packet.packets = fixedPackets)
    (d n : ℕ) :
    (CAStab.truncNaturalPacket.{u}
      stabilization d n).AILift where
  listEval_eq left right leftExponent rightExponent := by
    change
      (fixedPackets.map fun nextPacket =>
        nextPacket.word.eval (HPAtom.eval left right) ^
          nextPacket.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆
    simpa only [hpackets] using
      packet.listEval_eq left right leftExponent rightExponent

end
  AFStab
end TCTex
end Towers

/-!
# Sorted shape-fiber adapter for aggregate presentation and residual normalization

The residual-aware aggregate-presentation compiler consumes an abstract
`OperationalShapeFiber`.  The operational order reduction constructs
that kernel from the weaker structural statement that erased-shape fibers are
interval-convex.

This file packages that intermediate facade without requiring a homogeneous
presentation of the pending suffix.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  FSAdapt

open
  CIComp
open
  CRComp
open FORed
open FSComp

/--
The aggregate-presentation residual-aware boundary with interval-convex
erased-shape fibers in place of an abstract complete-fiber witness.
-/
structure
    CAInterv :
    Prop where
  presentations :
    OperationalAggregatedHomogeneous
  residual :
    OperationalCompleteResidual
  shapeFiberConvex :
    EIConvex

namespace
  CAInterv

/--
Interval convexity compiles to the complete shape-fiber witness expected by the
aggregate-presentation residual-aware route.
-/
noncomputable def aggregatedPresentationRecollect
    (kernel :
      CAInterv) :
    OAPres
      where
  presentations := kernel.presentations
  residual := kernel.residual
  shapeFiber :=
    FSComp.EIConvex.shapeFiberKernel
      kernel.shapeFiberConvex

end
  CAInterv

end
  FSAdapt
end TCTex
end Towers

/-!
# Adapter from per-grid cancellation to aggregated worklist presentations

The earlier retained-grid cancellation kernel presents every complete retained
grid homogeneously.  The sharper operational boundary only asks for one
homogeneous presentation of the shape-filtered sum of unrestricted packets in a
finite closed worklist.  This file proves the former implies the latter by
recursively adding exactly the presentations whose correction-family shapes
match the target shape.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CCAdapt

open HACoeff
open CCWork
open
  CIComp
open
  WRPolys
open
  CTRoute
open
  CRCompa
open
  GRPolyno
open
  SHPres

/--
Per-grid homogeneous cancellation recursively presents the shape-filtered
unrestricted packet sum of any complete compatible worklist.
-/
noncomputable def compatibleGridsCancellation
    (cancellation : CHCancel)
    {M N K : ℕ} :
    (worklist : CBWork M N K) →
      (hworklist :
        CBWork.HPPacket worklist) →
      (shape : CWord HPAtom) →
        HPres
          (compatibleGridsInhomogeneous
            worklist hworklist shape)
          shape.pairLeftDegree shape.pairRightDegree
  | [], _hworklist, shape =>
      HPres.zero
        shape.pairLeftDegree shape.pairRightDegree
  | item :: worklist, hworklist, shape => by
      let itemPacket :=
        CCBatch.completeParentPackets
          item (hworklist item (by simp))
      have htail :
          CBWork.HPPacket
            worklist :=
        fun next hnext => hworklist next (by simp [hnext])
      let tailPresentation :=
        compatibleGridsCancellation cancellation
          worklist htail shape
      rw [compatibleGridsInhomogeneous]
      by_cases hshape : itemPacket.erasedShape = shape
      · rw [if_pos hshape]
        subst shape
        let itemPresentation :=
          Classical.choice <|
            cancellation.presentation itemPacket.left itemPacket.right
              itemPacket.leftWitness_mem itemPacket.rightWitness_mem
                itemPacket.compatible
        exact itemPresentation.add tailPresentation
      · rw [if_neg hshape]
        exact tailPresentation

/--
The old universal per-grid cancellation kernel implies the sharper aggregate
closed-extension homogeneous-presentation kernel.
-/
noncomputable def aggregatedPresentationsCancellation
    (cancellation : CHCancel) :
    OperationalAggregatedHomogeneous where
  presentation endpoint shape :=
    ⟨compatibleGridsCancellation cancellation
      (operationalCompleteRouting endpoint).state.state.worklist
      (operationalCompleteRouting endpoint).state.complete
      shape⟩

/--
The earlier residual-aware global recollection kernel maps into the sharper
aggregate-presentation facade.
-/
noncomputable def aggregatedPresentationGlobal
    (kernel :
      OCComple) :
    OAPres
      where
  presentations :=
    aggregatedPresentationsCancellation kernel.cancellation
  residual := kernel.residual
  shapeFiber := kernel.shapeFiber

end CCAdapt
end TCTex
end Towers

/-!
# Inhomogeneous formula packets for genuine-prefix pending slots

The finite completion residual is the pending-term flattening left by the
genuine compatible reuse-routing prefix.  For one opened batch, its pending
length is the retained compatible-grid length minus the number of slots already
emitted.  This file packages that equality as an unrestricted signed-profile
packet and sums the packets of exactly the batches with one target Hall shape.

The remaining residual-normalization theorem is therefore explicit: present
this aggregate pending packet homogeneously in the target Hall bidegree.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace PIComp

open scoped commutatorElement

open HACoeff
open CCWork
open
  CIComp
open
  CRRoutec
open
  CTRoute
open
  RPCorr
open
  CRComp
open
  CSAggreg
open
  CFSubsti
open
  SHPres
open
  CSComp
open FMEnd
open MSCompre
open PPColl
open PPColl.RCColl.RPAggreg

open IFPkt

/--
The unrestricted pending packet of one opened batch: retained compatible-grid
packet minus its concretely emitted slots.
-/
noncomputable def pendingInhomogeneousFormula
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item) :
    IFPkt :=
  subtract packet.inhomogeneousFormulaPacket
    (constant (item.ledger.emitted.length : ℤ))

/-- Every pending term in one batch has its correction-family erased shape. -/
lemma family_erased_pending
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item)
    {term : DFTerm M N K}
    (hterm : term ∈ item.ledger.pending) :
    term.family.recipe.erasedShape = packet.erasedShape :=
  packet.shape_compatible_grid <|
    item.ledger.accounting.subset (List.mem_append_right item.ledger.emitted hterm)

/-- One unrestricted pending packet specializes to its concrete pending length. -/
lemma pending_inhomogeneous_cast
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item) :
    (pendingInhomogeneousFormula packet).value (M : ℤ) (N : ℤ) =
      (item.ledger.pending.length : ℤ) := by
  rw [pendingInhomogeneousFormula, value_subtract,
    packet.inhomogeneous_compatible_grid,
    value_constant]
  have hlength := item.ledger.accounting.length_eq
  simp only [List.length_append] at hlength
  omega

/--
Sum the unrestricted pending packets of exactly those opened batches whose
correction-family erased shape is the target shape.
-/
noncomputable def pendingInhomogeneousShape
    {M N K : ℕ} :
    (worklist : CBWork M N K) →
      CBWork.HPPacket worklist →
        CWord HPAtom →
          IFPkt
  | [], _hworklist, _shape =>
      zero
  | item :: worklist, hworklist, shape =>
      let itemPacket :=
        CCBatch.completeParentPackets
          item (hworklist item (by simp))
      let tailPacket :=
        pendingInhomogeneousShape worklist
          (fun next hnext => hworklist next (by simp [hnext])) shape
      if itemPacket.erasedShape = shape then
        add (pendingInhomogeneousFormula itemPacket) tailPacket
      else
        tailPacket

/--
The aggregate unrestricted pending packet specializes to the shape-filtered
pending-term flattening length.
-/
lemma inhomogeneous_formula_length
    {M N K : ℕ} :
    ∀ (worklist : CBWork M N K)
      (hworklist :
        CBWork.HPPacket worklist)
      (shape : CWord HPAtom),
      (pendingInhomogeneousShape
          worklist hworklist shape).value (M : ℤ) (N : ℤ) =
        ((batchWorklistPending worklist).filter
          (fun term => term.family.recipe.erasedShape = shape) |>.length : ℤ)
  | [], _hworklist, _shape => by
      rfl
  | item :: worklist, hworklist, shape => by
      let itemPacket :=
        CCBatch.completeParentPackets
          item (hworklist item (by simp))
      have htail :
          CBWork.HPPacket
            worklist :=
        fun next hnext => hworklist next (by simp [hnext])
      rw [pendingInhomogeneousShape]
      simp only [batchWorklistPending,
        List.flatMap_cons, List.filter_append, List.length_append,
        Int.natCast_add]
      by_cases hshape : itemPacket.erasedShape = shape
      · rw [if_pos hshape, value_add,
          pending_inhomogeneous_cast itemPacket,
          inhomogeneous_formula_length
            worklist htail shape]
        congr 1
        rw [List.filter_eq_self.2]
        intro term hterm
        simpa only [decide_eq_true_eq, hshape] using
          family_erased_pending itemPacket hterm
      · rw [if_neg hshape,
          inhomogeneous_formula_length
            worklist htail shape]
        have hfilter :
            item.ledger.pending.filter
                (fun term => term.family.recipe.erasedShape = shape) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro term hterm htermShape
          apply hshape
          exact
            (family_erased_pending itemPacket
              hterm).symm.trans
                (of_decide_eq_true htermShape)
        rw [hfilter]
        simp [batchWorklistPending]

/-- The unrestricted pending packet of one genuine compatible routing prefix. -/
noncomputable def prefixPendingInhomogeneous
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    IFPkt :=
  let routingPrefix :=
    reuseRoutingPrefix endpoint
  pendingInhomogeneousShape
    routingPrefix.state.state.worklist routingPrefix.state.complete shape

/--
The genuine-prefix unrestricted pending packet specializes to the concrete
shape-filtered pending-term length.
-/
lemma pending_inhomogeneous_length
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    (prefixPendingInhomogeneous endpoint shape).value
        (M : ℤ) (N : ℤ) =
      (((batchWorklistPending
        (reuseRoutingPrefix endpoint).state.state.worklist).filter
          fun term => term.family.recipe.erasedShape = shape).length : ℤ) :=
  inhomogeneous_formula_length
    (reuseRoutingPrefix endpoint).state.state.worklist
    (reuseRoutingPrefix endpoint).state.complete
    shape

/--
The exact residual-normalization algebraic boundary: each genuine-prefix
pending packet has a homogeneous presentation in its target Hall bidegree.
-/
structure PendingAggregatedHomogeneous :
    Prop where
  presentation :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (shape : CWord HPAtom),
      Nonempty
        (HPres
          (prefixPendingInhomogeneous endpoint shape)
          shape.pairLeftDegree shape.pairRightDegree)

/-- Pending homogeneous presentations compile to pending signed-block certificates. -/
noncomputable def pendingHomogeneousPresentations
    (kernel :
      PendingAggregatedHomogeneous) :
    OperationalCompletePending where
  certificate endpoint shape := by
    let presentation := Classical.choice (kernel.presentation endpoint shape)
    exact ⟨presentation.shapeBlockCertificate <|
      pending_inhomogeneous_length
        endpoint shape⟩

/-- Pending homogeneous presentations compile to completion-residual certificates. -/
noncomputable def residualHomogeneousPresentations
    (kernel :
      PendingAggregatedHomogeneous) :
    OperationalCompleteResidual :=
  residualPrefixPending
    (pendingHomogeneousPresentations kernel)

/--
The two explicit aggregate homogeneous-presentation theorems and shape-fiber
ordering are sufficient for global symbolic recollection at every natural
specialization.
-/
structure
  OAPendin :
    Prop where
  grids :
    OperationalAggregatedHomogeneous
  pending :
    PendingAggregatedHomogeneous
  shapeFiber :
    OperationalShapeFiber

namespace
  OAPendin

/-- Compile the two presentation boundaries into the residual-aware facade. -/
noncomputable def aggregatedPresentationRecollect
    (kernel :
      OAPendin)
        :
    OAPres
      where
  presentations := kernel.grids
  residual :=
    residualHomogeneousPresentations kernel.pending
  shapeFiber := kernel.shapeFiber

/-- Ordered packet at one natural specialization. -/
noncomputable def concretePackets
    (kernel :
      OAPendin)
    (M N : ℕ) :
    List RFPkt :=
  kernel.aggregatedPresentationRecollect.concretePackets
    M N

/-- The two-presentation aggregate packet computes the powered commutator. -/
lemma list_packets_commutator
    (kernel :
      OAPendin)
    (M N : ℕ) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
      packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  let compiled := kernel.aggregatedPresentationRecollect
  exact compiled.list_packets_commutator M N

/-- The two-presentation aggregate packet specializes to every ambient group. -/
lemma list_packets_group
    (kernel :
      OAPendin)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
      packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  let compiled := kernel.aggregatedPresentationRecollect
  exact compiled.list_packets_group M N left right

end OAPendin

end PIComp
end TCTex
end Towers

/-!
# Finite completion of productive compatible routing states

The productive complete-packet prefix records that every batch opened by the
genuine scheduler has already emitted a term.  This file drains its remaining
pending slots while retaining that fact and packages the resulting residual
suffix.

As for the earlier completion boundary, the residual is exactly the flattened
pending list of the genuine prefix up to permutation.
-/

namespace Towers
namespace TCTex
namespace
  PRComp

open HACoeff
open CCGrida
open RGClosa
open CTRoutea
open CCWork
open
  CRCompa
open
  CPRoute
open
  CREquiv
open
  RPCorr
open FMEnd

/-- Drain one pending slot while retaining complete parents and productivity. -/
noncomputable def routeProductivePending
    {M N K : ℕ}
    (state : PRState M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    PRState M N K where
  state :=
    routeCompletePending state.state pre post item hworklist emission
  productive := by
    change CBWork.Productive
      (pre ++ emission.emitItem :: post)
    exact state.productive.replace_emit
      pre post item hworklist emission.pendingPrefix
      (emission.leftTerm.correction emission.rightTerm)
      emission.pendingSuffix emission.pending_eq

@[simp]
lemma routed_productive_pending
    {M N K : ℕ}
    (state : PRState M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    (routeProductivePending
      state pre post item hworklist emission).state.state.routedTerms =
        state.state.state.routedTerms ++
          [emission.leftTerm.correction emission.rightTerm] :=
  rfl

/-- Routing one productive pending slot strictly lowers the pending count. -/
lemma pending_slots_productive
    {M N K : ℕ}
    (state : PRState M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    (routeProductivePending
      state pre post item hworklist emission).state.state.worklist.pendingSlots <
        state.state.state.worklist.pendingSlots :=
  pending_slots_route state.state pre post item hworklist emission

/-- Draining one productive pending slot does not change opened grids. -/
@[simp]
lemma grids_productive_pending
    {M N K : ℕ}
    (state : PRState M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    (routeProductivePending
      state pre post item hworklist emission).state.state.worklist.compatibleGrids =
        state.state.state.worklist.compatibleGrids :=
  compatible_grids_pending
    state.state pre post item hworklist emission

/--
Any productive complete-packet prefix extends through finitely many concrete
emissions to a closed productive state.
-/
lemma closed_productive_complete
    {M N K : ℕ}
    (state : PRState M N K) :
    ∃ final : PRState M N K,
      final.state.state.worklist.Closed ∧
        state.state.state.routedTerms <+: final.state.state.routedTerms ∧
          final.state.state.worklist.compatibleGrids =
            state.state.state.worklist.compatibleGrids := by
  by_cases hclosed : state.state.state.worklist.Closed
  · exact ⟨state, hclosed, List.prefix_rfl, rfl⟩
  · simp only [CBWork.Closed, not_forall] at hclosed
    rcases hclosed with ⟨item, hitem, hopen⟩
    rcases List.mem_iff_append.mp hitem with ⟨pre, post, hworklist⟩
    simp only [BWItem.Closed] at hopen
    cases hpending : item.ledger.pending with
    | nil =>
        exact False.elim (hopen hpending)
    | cons term after =>
        have hterm : term ∈ item.ledger.pending := by
          rw [hpending]
          simp
        rcases item.ledger.parent_terms_pending hterm with
          ⟨leftTerm, hleft, rightTerm, hright, hcompatible, htermEq⟩
        subst term
        let emission : CBEmissi item := {
          leftTerm := leftTerm
          rightTerm := rightTerm
          left_mem := hleft
          right_mem := hright
          compatible := hcompatible
          pendingPrefix := []
          pendingSuffix := after
          pending_eq := hpending }
        let next :=
          routeProductivePending state pre post item hworklist emission
        rcases closed_productive_complete next with
          ⟨final, hfinalClosed, hprefix, hgrids⟩
        refine ⟨final, hfinalClosed, ?_, ?_⟩
        · apply (List.prefix_append state.state.state.routedTerms
            [leftTerm.correction rightTerm]).trans
          simpa [next, emission] using hprefix
        · calc
            final.state.state.worklist.compatibleGrids =
                next.state.state.worklist.compatibleGrids :=
              hgrids
            _ = state.state.state.worklist.compatibleGrids :=
              grids_productive_pending
                state pre post item hworklist emission
termination_by state.state.state.worklist.pendingSlots
decreasing_by
  exact pending_slots_productive
    state pre post item hworklist emission

/--
A closed productive extension of one genuine productive operational prefix.
-/
structure OPRoute
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  state :
    PRState M N
      (inverseLabelledCollection M N).factors.length
  closed :
    state.state.state.worklist.Closed
  corrections_prefix :
    endpoint.corrections <+: state.state.state.routedTerms
  compatible_grids_prefix :
    state.state.state.worklist.compatibleGrids =
      (productiveReuseRouting
        endpoint).state.state.state.worklist.compatibleGrids

/-- Every productive operational prefix has a finite closed extension. -/
noncomputable def operationalProductiveRouting
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    OPRoute endpoint := by
  let routingPrefix :=
    productiveReuseRouting endpoint
  by_cases hclosed : routingPrefix.state.state.state.worklist.Closed
  · exact {
      state := routingPrefix.state
      closed := hclosed
      corrections_prefix := by
        rw [routingPrefix.routed_eq]
      compatible_grids_prefix := rfl }
  · let completion := closed_productive_complete routingPrefix.state
    let final := Classical.choose completion
    have hfinal := Classical.choose_spec completion
    exact {
      state := final
      closed := hfinal.1
      corrections_prefix := by
        rw [← routingPrefix.routed_eq]
        exact hfinal.2.1
      compatible_grids_prefix := hfinal.2.2 }

namespace OPRoute

/-- The residual corrections added only to drain the productive schedule. -/
def residualCorrections
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension :
      OPRoute endpoint) :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length) :=
  extension.state.state.state.routedTerms.drop endpoint.corrections.length

/-- A productive closed extension is the emitted trace followed by its residual. -/
lemma routed_corrections_append
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension :
      OPRoute endpoint) :
    extension.state.state.state.routedTerms =
      endpoint.corrections ++ extension.residualCorrections :=
  List.prefix_append_drop extension.corrections_prefix

/-- Productive closed grids are the emitted corrections followed by the residual. -/
lemma compatible_grids_perm
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension :
      OPRoute endpoint) :
    List.Perm extension.state.state.state.worklist.compatibleGrids
      (endpoint.corrections ++ extension.residualCorrections) := by
  apply List.Perm.trans
    (OCReuse.emitted_grids_closed
      extension.state.state.state.worklist extension.closed).symm
  rw [← extension.routed_corrections_append]
  exact extension.state.state.state.emitted_perm

end OPRoute

/--
The residual suffix of a productive completion is exactly the pending flattening
of its genuine productive prefix, up to permutation.
-/
lemma productive_pending_corrections
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension :
      OPRoute endpoint) :
    List.Perm
      (batchWorklistPending
        (productiveReuseRouting
          endpoint).state.state.state.worklist)
      extension.residualCorrections := by
  let routingPrefix :=
    productiveReuseRouting endpoint
  have hemitted :
      List.Perm
        (batchWorklistEmitted
          routingPrefix.state.state.state.worklist)
        endpoint.corrections := by
    apply routingPrefix.state.state.state.emitted_perm.trans
    rw [routingPrefix.routed_eq]
  have hgrids :
      List.Perm routingPrefix.state.state.state.worklist.compatibleGrids
        (endpoint.corrections ++ extension.residualCorrections) := by
    rw [← extension.compatible_grids_prefix]
    exact extension.compatible_grids_perm
  have hwhole :
      List.Perm
        (endpoint.corrections ++
          batchWorklistPending
            routingPrefix.state.state.state.worklist)
        (endpoint.corrections ++ extension.residualCorrections) := by
    apply (hemitted.append_right
      (batchWorklistPending
        routingPrefix.state.state.state.worklist)).symm.trans
    exact
      (emitted_pending_grids
        routingPrefix.state.state.state.worklist).trans hgrids
  exact (List.perm_append_left_iff endpoint.corrections).mp hwhole

/--
A productive completion residual vanishes exactly when its productive genuine
prefix was already closed.
-/
lemma productive_corrections_closed
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension :
      OPRoute endpoint) :
    extension.residualCorrections = [] ↔
      (productiveReuseRouting
        endpoint).state.state.state.worklist.Closed := by
  have hperm := productive_pending_corrections extension
  constructor
  · intro hresidual
    apply
      (CBWork.closed_pending_nil
        (productiveReuseRouting
          endpoint).state.state.state.worklist).2
    apply List.eq_nil_of_length_eq_zero
    rw [hperm.length_eq, hresidual]
    rfl
  · intro hclosed
    apply List.eq_nil_of_length_eq_zero
    rw [← hperm.length_eq,
      (CBWork.closed_pending_nil
        (productiveReuseRouting
          endpoint).state.state.state.worklist).1 hclosed]
    rfl

/--
The productive completion residual length is exactly the pending-slot measure
of its genuine productive prefix.
-/
lemma length_productive_slots
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension :
      OPRoute endpoint) :
    extension.residualCorrections.length =
      (productiveReuseRouting
        endpoint).state.state.state.worklist.pendingSlots := by
  rw [← (productive_pending_corrections extension).length_eq,
    CBWork.length_pendingTerms]

/-- The canonical residual suffix of the productive compatible completion. -/
noncomputable def operationalProductiveCorrections
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length) :=
  (operationalProductiveRouting
    endpoint).residualCorrections

/--
The canonical productive residual vanishes exactly when the genuine productive
prefix was already closed.
-/
lemma operational_productive_closed
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    operationalProductiveCorrections endpoint = [] ↔
      (productiveReuseRouting
        endpoint).state.state.state.worklist.Closed :=
  productive_corrections_closed
    (operationalProductiveRouting endpoint)

/--
The canonical productive residual length is the pending-slot measure of the
genuine productive prefix.
-/
lemma productive_pending_slots
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    (operationalProductiveCorrections endpoint).length =
      (productiveReuseRouting
        endpoint).state.state.state.worklist.pendingSlots :=
  length_productive_slots
    (operationalProductiveRouting endpoint)

/--
The canonical productive residual vanishes when the genuine operational trace
contains no corrections.
-/
theorem operational_productive_nil
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hcorrections : endpoint.corrections = []) :
    operationalProductiveCorrections endpoint = [] := by
  apply
    (operational_productive_closed
      endpoint).2
  exact
    productive_reuse_nil
      endpoint hcorrections

end
  PRComp
end TCTex
end Towers

/-!
# Shape-sorted aggregate-presentation residual-aware symbolic recollection

The residual-aware aggregate-presentation compiler consumes complete endpoint
shape fibers.  Primary erased-shape sorting is a sharper operational boundary:
interval convexity and maximal-run completion turn it into those exact fibers.

This file threads that sharper boundary through ordered symbolic recollection
and fixed-packet stabilization.  Unlike the pending-presentation route, it
normalizes the residual suffix separately and does not require that suffix to
have a homogeneous presentation by itself.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex


namespace
  PRPolysa

universe u

open scoped commutatorElement

open HACoeff
open
  AFStab
open
  FSAdapt
open
  CIComp
open
  CRComp
open
  CFExp
open
  CFSubsti
open
  UNPkt
open
  FORed
open PPColl
open PPColl.RCColl.RPAggreg

/--
Aggregate homogeneous presentation, residual normalization, and pairwise
primary endpoint shape sorting.
-/
structure
    CARecoll :
    Prop where
  presentations :
    OperationalAggregatedHomogeneous
  residual :
    OperationalCompleteResidual
  shapeSorted :
    OESorted

namespace
  CARecoll

/-- Compile pairwise endpoint shape sorting to interval-convex shape fibers. -/
noncomputable def intervalConvexGlobal
    (kernel :
      CARecoll) :
    CAInterv where
  presentations := kernel.presentations
  residual := kernel.residual
  shapeFiberConvex :=
    kernel.shapeSorted.operationalIntervalConvex

/-- Compile primary endpoint shape sorting to the exact shape-fiber interface. -/
noncomputable def presentationGlobalRecollection
    (kernel :
      CARecoll) :
    OAPres :=
  kernel.intervalConvexGlobal.aggregatedPresentationRecollect

/-- Ordered symbolic recollection packets at one natural specialization. -/
noncomputable def concretePackets
    (kernel :
      CARecoll)
    (M N : ℕ) :
    List RFPkt :=
  kernel.presentationGlobalRecollection.concretePackets M N

/-- Shape-sorted residual-aware packets compute the powered commutator. -/
lemma list_packets_commutator
    (kernel :
      CARecoll)
    (M N : ℕ) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  kernel.presentationGlobalRecollection.list_packets_commutator
    M N

/-- The shape-sorted residual-aware packet specializes to every ambient group. -/
lemma list_packets_group
    (kernel :
      CARecoll)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ :=
  kernel.presentationGlobalRecollection.list_packets_group
    M N left right

end
  CARecoll

/--
Order-aware stabilization of a fixed packet list against the shape-sorted
aggregate-presentation residual-aware route.
-/
abbrev
    CPStaba
    (kernel :
      CARecoll)
    (fixedPackets : List RFPkt) :
    Prop :=
  CAStab
    kernel.presentationGlobalRecollection fixedPackets

namespace
  CPStaba

/-- A stabilized fixed packet computes the natural powered commutator. -/
lemma nat_cast_pow
    {kernel :
      CARecoll}
    {fixedPackets : List RFPkt}
    (stabilization :
      CPStaba
        kernel fixedPackets)
    (M N : ℕ) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  AFStab.CAStab.nat_cast_pow
    stabilization M N

/-- Shape-sorted fixed-packet stabilization supplies the truncated natural packet. -/
def truncNaturalPacket
    {kernel :
      CARecoll}
    {fixedPackets : List RFPkt}
    (stabilization :
      CPStaba
        kernel fixedPackets)
    (d n : ℕ) :
    TBPkt.{u} d n :=
  AFStab.CAStab.truncNaturalPacket
    stabilization d n

end
  CPStaba

/--
A universal all-integral packet automa stabilizes the shape-sorted
aggregate-presentation residual-aware route.
-/
noncomputable def
    sortedStabilizationIntegral
    (kernel :
      CARecoll)
    (packet : UAPkt.{0}) :
    CPStaba
      kernel packet.packets :=
  naturalStabilizationIntegral
    kernel.presentationGlobalRecollection packet

/--
An all-integral packet with the same fixed list is the signed cutoff lift of
shape-sorted natural stabilization.
-/
def sortedAllUniversal
    {kernel :
      CARecoll}
    {fixedPackets : List RFPkt}
    (stabilization :
      CPStaba
        kernel fixedPackets)
    (packet : UAPkt.{u})
    (hpackets : packet.packets = fixedPackets)
    (d n : ℕ) :
    (CPStaba.truncNaturalPacket.{u}
      stabilization d n).AILift :=
  allUniversalPacket
    stabilization packet hpackets d n

end
  PRPolysa
end TCTex
end Towers

/-!
# Proper pending batches are not individually homogeneous

The genuine-prefix pending compiler subtracts the number of already-emitted
physical slots from the unrestricted retained-grid formula.  A homogeneous
positive-left-degree packet vanishes when the left source exponent is zero,
but this emitted-slot constant does not.

Consequently, once a retained compatible grid has emitted at least one slot,
its remaining pending formula cannot be presented homogeneously by itself.
Any valid residual normalization theorem must aggregate cancellation across a
larger scheduler scope.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  CPObstru


open BRSpec
open CCWork
open
  CTRoute
open
  CIComp
open
  PIComp
open
  SHPres
open
  CSComp
open
  CSComp.IFPkt


namespace HPres

/-- A positive-left-degree homogeneous presentation vanishes at left input
zero after forgetting to its unrestricted packet. -/
lemma packet_value_pos
    {packet : IFPkt}
    {leftDegree rightDegree : ℕ}
    (presentation :
      HPres packet leftDegree rightDegree)
    (hdegree : 0 < leftDegree)
    (right : ℤ) :
    packet.value 0 right = 0 := by
  rw [← presentation.value_eq]
  exact
    homogeneous_formula_pos
      presentation.homogeneous hdegree right

end HPres

/-- Every retained compatible grid has positive target left degree. -/
lemma erased_pair_pos
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item) :
    0 < packet.erasedShape.pairLeftDegree := by
  unfold CCBatch.erasedShape
  rw [
    (packet.leftFamily.correction
      packet.rightFamily).recipe.erased_left_degree]
  exact leftDegree_pos _

/--
If a positive-left-degree retained compatible grid has already emitted at
least one physical slot, its remaining pending packet cannot itself have a
homogeneous presentation in the grid's target bidegree.
-/
theorem pending_emitted_pos
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item)
    (hgrid :
      Nonempty
        (HPres
          packet.inhomogeneousFormulaPacket
          packet.erasedShape.pairLeftDegree
          packet.erasedShape.pairRightDegree))
    (hemitted : 0 < item.ledger.emitted.length) :
    ¬ Nonempty
      (HPres
        (pendingInhomogeneousFormula packet)
        packet.erasedShape.pairLeftDegree
        packet.erasedShape.pairRightDegree) := by
  rintro ⟨pendingPresentation⟩
  rcases hgrid with ⟨gridPresentation⟩
  have hleftDegree :=
    erased_pair_pos packet
  have hgridZero :=
    HPres.packet_value_pos
      gridPresentation
      hleftDegree 0
  have hpendingZero :=
    HPres.packet_value_pos
      pendingPresentation
      hleftDegree 0
  rw [pendingInhomogeneousFormula, value_subtract, hgridZero,
    value_constant] at hpendingZero
  omega

/--
The universal retained-grid cancellation kernel therefore cannot normalize a
proper positive-left-degree pending batch in isolation.
-/
theorem presentation_pending_cancellation
    (cancellation : CHCancel)
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item)
    (hemitted : 0 < item.ledger.emitted.length) :
    ¬ Nonempty
      (HPres
        (pendingInhomogeneousFormula packet)
        packet.erasedShape.pairLeftDegree
        packet.erasedShape.pairRightDegree) := by
  apply
    pending_emitted_pos
      packet _ hemitted
  exact
    cancellation.presentation packet.left packet.right
      packet.leftWitness_mem packet.rightWitness_mem packet.compatible

/--
The singleton scheduler aggregate exposes the same obstruction: after one
physical slot has been emitted, even the pending compiler's own one-item
worklist packet cannot be normalized homogeneously in isolation.
-/
theorem
    homogeneous_pending_cancellation
    (cancellation : CHCancel)
    {M N K : ℕ}
    {item : BWItem M N K}
    (hworklist :
      CBWork.HPPacket [item])
    (hemitted : 0 < item.ledger.emitted.length) :
    let packet :=
      CCBatch.completeParentPackets
        item (hworklist item (by simp))
    ¬ Nonempty
      (HPres
        (pendingInhomogeneousShape
          [item] hworklist packet.erasedShape)
        packet.erasedShape.pairLeftDegree
        packet.erasedShape.pairRightDegree) := by
  let packet :=
    CCBatch.completeParentPackets
      item (hworklist item (by simp))
  change
    ¬ Nonempty
      (HPres
        (pendingInhomogeneousShape
          [item] hworklist packet.erasedShape)
        packet.erasedShape.pairLeftDegree
        packet.erasedShape.pairRightDegree)
  intro hpresentation
  apply
    presentation_pending_cancellation
      cancellation packet hemitted
  simpa [pendingInhomogeneousShape, packet,
    IFPkt.add,
    IFPkt.zero] using hpresentation

end
  CPObstru
end TCTex
end Towers

/-!
# Fixed-packet stabilization after aggregate and pending presentations

The complete operational route now exposes two explicit inhomogeneous packets
for each erased Hall shape: the closed compatible-grid aggregate and the
genuine-prefix pending aggregate.  Homogeneous presentations of those packets,
together with endpoint shape-fiber ordering, produce one concrete ordered
signed-profile packet at each pair of natural source multiplicities.

This file isolates the remaining global theorem: replace those
multiplicity-dependent concrete packets by one fixed ordered packet list.
The comparison is order-aware.  No permutation or commutative regrouping is
used.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  PFStab

universe u

open scoped commutatorElement

open
  PIComp
open
  CSSpec
open
  CFExp
open
  CFSubsti
open
  UNPkt
open PPColl
open PPColl.RCColl.RPAggreg

/--
The order-aware fixed-packet stabilization theorem left after the two
aggregate homogeneous-presentation boundaries and shape-fiber ordering.
-/
structure
    CPStab
    (kernel :
      OAPendin)
    (fixedPackets : List RFPkt) :
    Prop where
  packet_prod_concrete :
    ∀ (M N : ℕ),
      (fixedPackets.map fun packet =>
        packet.word.eval (HPAtom.eval universalLeft universalRight) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod =
        ((kernel.concretePackets M N).map fun packet =>
          packet.word.eval (HPAtom.eval universalLeft universalRight) ^
            packet.profiles.value (M : ℤ) (N : ℤ)).prod

namespace
  CPStab

/-- Fixed-packet stabilization proves the natural Hall-Petresco identity in
the universal group. -/
lemma nat_cast_pow
    {kernel :
      OAPendin}
    {fixedPackets : List RFPkt}
    (stabilization :
      CPStab
        kernel fixedPackets)
    (M N : ℕ) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  (stabilization.packet_prod_concrete M N).trans
    (kernel.list_packets_commutator M N)

/-- Universal-group fixed-packet stabilization specializes to every ambient
group. -/
lemma nat_cast_group
    {kernel :
      OAPendin}
    {fixedPackets : List RFPkt}
    (stabilization :
      CPStab
        kernel fixedPackets)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  rw [← specialize_listEval left right (M : ℤ) (N : ℤ) fixedPackets,
    stabilization.nat_cast_pow M N]
  simp [map_commutatorElement, map_pow]

/-- A fixed stabilized packet supplies the natural packet interface consumed
by signed-profile collection. -/
def truncNaturalPacket
    {kernel :
      OAPendin}
    {fixedPackets : List RFPkt}
    (stabilization :
      CPStab
        kernel fixedPackets)
    (d n : ℕ) :
    TBPkt.{u} d n where
  packets := fixedPackets
  list_nat_cast left right M N :=
    stabilization.nat_cast_group M N left right

end
  CPStab

open CPStab

/--
A universal all-integral signed packet automa stabilizes against every
concrete packet produced by the aggregate-and-pending presentation route.
-/
noncomputable def
    naturalStabilizationIntegral
    (kernel :
      OAPendin)
    (packet : UAPkt.{0}) :
      CPStab
      kernel packet.packets where
  packet_prod_concrete M N := by
    calc
      (packet.packets.map fun nextPacket =>
        nextPacket.word.eval
            (HPAtom.eval universalLeft universalRight) ^
          nextPacket.profiles.value (M : ℤ) (N : ℤ)).prod =
          ⁅universalLeft ^ M, universalRight ^ N⁆ := by
        simpa only [zpow_natCast] using
          packet.listEval_eq universalLeft universalRight (M : ℤ) (N : ℤ)
      _ = ((kernel.concretePackets M N).map fun nextPacket =>
          nextPacket.word.eval
              (HPAtom.eval universalLeft universalRight) ^
            nextPacket.profiles.value (M : ℤ) (N : ℤ)).prod :=
        (kernel.list_packets_commutator M N).symm

/--
An all-integral packet with the same fixed packet list is the signed lift of a
stabilized natural packet at every free lower-central cutoff.
-/
def allUniversalPacket
    {kernel :
      OAPendin}
    {fixedPackets : List RFPkt}
    (stabilization :
      CPStab
        kernel fixedPackets)
    (packet : UAPkt.{u})
    (hpackets : packet.packets = fixedPackets)
    (d n : ℕ) :
    (truncNaturalPacket.{u} stabilization d n).AILift where
  listEval_eq left right leftExponent rightExponent := by
    change
      (fixedPackets.map fun nextPacket =>
        nextPacket.word.eval (HPAtom.eval left right) ^
          nextPacket.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆
    simpa only [hpackets] using
      packet.listEval_eq left right leftExponent rightExponent

end
  PFStab
end TCTex
end Towers

/-!
# Sorted shape-fiber adapter for complete pending presentations

The complete aggregate-and-pending presentation compiler consumes an abstract
`OperationalShapeFiber`.  The operational order reduction constructs
that kernel from the weaker structural statement that erased-shape fibers are
interval-convex.

This file packages that intermediate facade.  Pairwise primary erased-shape
sorting compiles to interval convexity in the ordering reduction and is
threaded through its richer symbolic facade separately.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  PSAdapt

open
  CIComp
open
  PIComp
open FORed
open FSComp

/--
The complete pending-presentation boundary with interval-convex erased-shape
fibers in place of an abstract complete-fiber witness.
-/
structure
    CIRecoll :
    Prop where
  grids :
    OperationalAggregatedHomogeneous
  pending :
    PendingAggregatedHomogeneous
  shapeFiberConvex :
    EIConvex

namespace
  CIRecoll

/--
Interval convexity compiles to the complete shape-fiber witness expected by the
aggregate-and-pending presentation route.
-/
noncomputable def aggregatedPendingPresentation
    (kernel :
      CIRecoll) :
    OAPendin
      where
  grids := kernel.grids
  pending := kernel.pending
  shapeFiber :=
    FSComp.EIConvex.shapeFiberKernel
      kernel.shapeFiberConvex

end
  CIRecoll

end
  PSAdapt
end TCTex
end Towers

/-!
# Base cases for productive compatible residuals

The full operational correction trace is empty when either inverse-raw side is
empty and for the first positive-positive input `1 x 1`.  The productive
completion therefore has no residual in those cases.

This isolates the remaining productive residual boundary to nontrivial
positive inputs.
-/

namespace Towers
namespace TCTex
namespace
  PBCases

open HACoeff
open CPRoute
open PRComp
open OCClos
open FMEnd
open MTRoute

/-- Any operational endpoint with at most one inverse-raw term emits no corrections. -/
lemma corrections_nil_decorated
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hsource : (inverseDecoratedTerms M N).length ≤ 1) :
    endpoint.corrections = [] :=
  FCollec.ECorrec.nil_source_length
    endpoint.emits hsource

/--
Any productive compatible prefix with at most one inverse-raw source term opens
no batches.
-/
theorem productive_reuse_worklist
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hsource : (inverseDecoratedTerms M N).length ≤ 1) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist = [] :=
  productive_reuse_corrections
    endpoint
    (corrections_nil_decorated
      endpoint hsource)

/--
Any productive compatible completion with at most one inverse-raw source term
has empty residual.
-/
theorem productive_corrections_decorated
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hsource : (inverseDecoratedTerms M N).length ≤ 1) :
    operationalProductiveCorrections endpoint = [] :=
  operational_productive_nil
    endpoint
    (corrections_nil_decorated
      endpoint hsource)

/-- No-left-label operational endpoints emit no corrections. -/
lemma corrections_nil_left
    (N : ℕ)
    (endpoint : ODEmissi 0 N) :
    endpoint.corrections = [] :=
  FCollec.ECorrec.nil_source endpoint.emits
    (inverse_decorated_terms N)

/-- No-right-label operational endpoints emit no corrections. -/
lemma corrections_nil_right
    (M : ℕ)
    (endpoint : ODEmissi M 0) :
    endpoint.corrections = [] :=
  FCollec.ECorrec.nil_source endpoint.emits
    (inverse_raw_decorated M)

/-- The first positive-positive operational endpoint emits no corrections. -/
lemma corrections_nil_one
    (endpoint : ODEmissi 1 1) :
    endpoint.corrections = [] :=
  FCollec.ECorrec.nil_source_length
    endpoint.emits (by
      rw [inverse_decorated_length])

/-- No-left-label productive compatible prefixes open no batches. -/
theorem productive_routing_worklist
    (N : ℕ)
    (endpoint : ODEmissi 0 N) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist = [] :=
  productive_reuse_corrections
    endpoint (corrections_nil_left N endpoint)

/-- No-right-label productive compatible prefixes open no batches. -/
theorem productive_reuse_routing
    (M : ℕ)
    (endpoint : ODEmissi M 0) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist = [] :=
  productive_reuse_corrections
    endpoint (corrections_nil_right M endpoint)

/-- The `1 x 1` productive compatible prefix opens no batches. -/
theorem reuse_routing_worklist
    (endpoint : ODEmissi 1 1) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist = [] :=
  productive_reuse_corrections
    endpoint (corrections_nil_one endpoint)

/-- No-left-label productive compatible completions have empty residual. -/
theorem productive_corrections_left
    (N : ℕ)
    (endpoint : ODEmissi 0 N) :
    operationalProductiveCorrections endpoint = [] :=
  operational_productive_nil
    endpoint (corrections_nil_left N endpoint)

/-- No-right-label productive compatible completions have empty residual. -/
theorem productive_corrections_nil
    (M : ℕ)
    (endpoint : ODEmissi M 0) :
    operationalProductiveCorrections endpoint = [] :=
  operational_productive_nil
    endpoint (corrections_nil_right M endpoint)

/-- The `1 x 1` productive compatible completion has empty residual. -/
theorem productive_residual_corrections
    (endpoint : ODEmissi 1 1) :
    operationalProductiveCorrections endpoint = [] :=
  operational_productive_nil
    endpoint (corrections_nil_one endpoint)

end
  PBCases
end TCTex
end Towers

/-!
# Residual shape-sorted adapter to aggregated presentations

Per-grid retained-slot cancellation is a sufficient source of homogeneous
presentations for closed compatible-worklist aggregates.  Combining that
conversion with residual signed-block normalization and pairwise endpoint shape
sorting yields the sound shape-sorted symbolic recollection route.

This file keeps the aggregate presentation compiler internal to a smaller
operational entry point.  No homogeneous presentation of a pending suffix is
required.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex


namespace
  SAPres

open
  PRPolysa
open
  CCAdapt
open
  GRPolyno
open
  CRComp
open
  SHPres
open FORed

/--
The sound operational hypotheses before compiling per-grid cancellation to
closed-worklist aggregate presentations.
-/
structure
    OCSorted :
    Prop where
  cancellation :
    CHCancel
  residual :
    OperationalCompleteResidual
  shapeSorted :
    OESorted

namespace
  OCSorted

/--
Compile per-grid cancellation to aggregate presentations while retaining
residual normalization and pairwise endpoint shape sorting.
-/
noncomputable def aggregatedSortedGlobal
    (kernel :
      OCSorted) :
    CARecoll where
  presentations :=
    aggregatedPresentationsCancellation kernel.cancellation
  residual := kernel.residual
  shapeSorted := kernel.shapeSorted

/-- The earlier residual-aware facade maps into the shape-sorted route once
pairwise endpoint sorting is supplied. -/
noncomputable def residualGlobalRecollection
    (kernel :
      OCComple)
    (shapeSorted : OESorted) :
    OCSorted where
  cancellation := kernel.cancellation
  residual := kernel.residual
  shapeSorted := shapeSorted

end
  OCSorted

end
  SAPres
end TCTex
end Towers

/-!
# Pending aggregates retain emitted-slot constants

The pending packet of one opened compatible batch subtracts the number of
physical slots already emitted from that batch.  Aggregating pending packets by
Hall shape does not cancel those constants: every selected batch contributes
with the same negative sign.

This file computes the zero-left specialization of an arbitrary shape-filtered
pending worklist packet.  Under retained-grid homogeneous cancellation, it is
the negative number of emitted slots of that shape.  Consequently a pending
aggregate can have a homogeneous presentation only when no selected slot has
yet been emitted.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  CAObstru


open HACoeff
open CTRoutea
open CCWork
open
  CIComp
open
  CTRoute
open
  CRRoutec
open
  PIComp
open
  CPObstru
open
  SHPres
open
  CSComp
open
  CSComp.IFPkt
open FMEnd


/-- Every slot already emitted from one opened batch has the batch's erased
Hall shape. -/
lemma family_erased_emitted
    {M N K : ℕ}
    {item : BWItem M N K}
    (packet : CCBatch item)
    {term : DFTerm M N K}
    (hterm : term ∈ item.ledger.emitted) :
    term.family.recipe.erasedShape = packet.erasedShape :=
  packet.shape_compatible_grid <|
    item.ledger.accounting.subset <|
      List.mem_append_left item.ledger.pending hterm

/--
At zero left input, the shape-filtered pending packet of a complete worklist is
the negative number of already-emitted slots of that shape.
-/
theorem pending_inhomogeneous_formula
    (cancellation : CHCancel)
    {M N K : ℕ} :
    ∀ (worklist : CBWork M N K)
      (hworklist :
        CBWork.HPPacket worklist)
      (shape : CWord HPAtom)
      (right : ℤ),
      (pendingInhomogeneousShape
          worklist hworklist shape).value 0 right =
        -(((batchWorklistEmitted worklist).filter
          fun term => term.family.recipe.erasedShape = shape).length : ℤ)
  | [], _hworklist, _shape, _right => by
      rfl
  | item :: worklist, hworklist, shape, right => by
      let itemPacket :=
        CCBatch.completeParentPackets
          item (hworklist item (by simp))
      have htail :
          CBWork.HPPacket
            worklist :=
        fun next hnext => hworklist next (by simp [hnext])
      have hgridZero :
          itemPacket.inhomogeneousFormulaPacket.value 0 right = 0 := by
        let presentation :=
          Classical.choice <|
            cancellation.presentation itemPacket.left itemPacket.right
              itemPacket.leftWitness_mem itemPacket.rightWitness_mem
                itemPacket.compatible
        exact
          HPres.packet_value_pos
            presentation (erased_pair_pos itemPacket) right
      rw [pendingInhomogeneousShape]
      simp only [batchWorklistEmitted,
        List.flatMap_cons, List.filter_append, List.length_append,
        Int.natCast_add]
      by_cases hshape : itemPacket.erasedShape = shape
      · have hfilter :
            item.ledger.emitted.filter
                (fun term => term.family.recipe.erasedShape = shape) =
              item.ledger.emitted := by
          apply List.filter_eq_self.2
          intro term hterm
          simpa only [decide_eq_true_eq, hshape] using
            family_erased_emitted itemPacket hterm
        rw [if_pos hshape, value_add, pendingInhomogeneousFormula,
          value_subtract, hgridZero, value_constant,
          pending_inhomogeneous_formula
            cancellation worklist htail shape right,
          hfilter]
        simp [batchWorklistEmitted, add_comm]
      · have hfilter :
            item.ledger.emitted.filter
                (fun term => term.family.recipe.erasedShape = shape) =
              [] := by
          apply List.filter_eq_nil_iff.mpr
          intro term hterm htermShape
          apply hshape
          exact
            (family_erased_emitted
              itemPacket hterm).symm.trans
                (of_decide_eq_true htermShape)
        rw [if_neg hshape,
          pending_inhomogeneous_formula
            cancellation worklist htail shape right,
          hfilter]
        simp [batchWorklistEmitted]

/-- If one shape has an emitted slot, its Hall left degree is positive. -/
lemma emitted_filter_length
    {M N K : ℕ}
    (worklist : CBWork M N K)
    (hworklist :
      CBWork.HPPacket worklist)
    (shape : CWord HPAtom)
    (hemitted :
      0 <
        ((batchWorklistEmitted worklist).filter
          fun term => term.family.recipe.erasedShape = shape).length) :
    0 < shape.pairLeftDegree := by
  have hne :
      (batchWorklistEmitted worklist).filter
          (fun term => term.family.recipe.erasedShape = shape) ≠ [] :=
    List.ne_nil_of_length_pos hemitted
  rcases List.exists_mem_of_ne_nil _ hne with ⟨term, hterm⟩
  rcases List.mem_filter.mp hterm with ⟨htermEmitted, htermShape⟩
  rcases List.mem_flatMap.mp htermEmitted with ⟨item, hitem, htermItem⟩
  let packet :=
    CCBatch.completeParentPackets
      item (hworklist item hitem)
  have hshape :
      packet.erasedShape = shape :=
    (family_erased_emitted
      packet htermItem).symm.trans
        (of_decide_eq_true htermShape)
  rw [← hshape]
  exact erased_pair_pos packet

/--
If a complete worklist has emitted any slot of one shape, its pending aggregate
for that shape cannot have a homogeneous presentation.
-/
theorem
    homogeneous_emitted_pos
    (cancellation : CHCancel)
    {M N K : ℕ}
    (worklist : CBWork M N K)
    (hworklist :
      CBWork.HPPacket worklist)
    (shape : CWord HPAtom)
    (hemitted :
      0 <
        ((batchWorklistEmitted worklist).filter
          fun term => term.family.recipe.erasedShape = shape).length) :
    ¬ Nonempty
      (HPres
        (pendingInhomogeneousShape
          worklist hworklist shape)
        shape.pairLeftDegree shape.pairRightDegree) := by
  rintro ⟨presentation⟩
  have hpendingZero :=
    HPres.packet_value_pos
      presentation
      (emitted_filter_length
        worklist hworklist shape hemitted) 0
  rw [
    pending_inhomogeneous_formula
      cancellation worklist hworklist shape 0] at hpendingZero
  omega

/--
The emitted terms of the genuine routing prefix and the endpoint correction
list have the same shape-filtered cardinalities.
-/
lemma length_emitted_corrections
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    ((batchWorklistEmitted
      (reuseRoutingPrefix
        endpoint).state.state.worklist).filter
        fun term => term.family.recipe.erasedShape = shape).length =
      (endpoint.corrections.filter
        fun term => term.family.recipe.erasedShape = shape).length := by
  let routingPrefix :=
    reuseRoutingPrefix endpoint
  have hperm :=
    routingPrefix.state.state.emitted_perm.filter
      (fun term => term.family.recipe.erasedShape = shape)
  rw [routingPrefix.routed_eq] at hperm
  exact hperm.length_eq

/--
If an operational endpoint emitted any correction of one shape, the
corresponding genuine-prefix pending packet cannot have a homogeneous
presentation.
-/
theorem
    homogeneous_pending_pos
    (cancellation : CHCancel)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom)
    (hcorrections :
      0 <
        (endpoint.corrections.filter
          fun term => term.family.recipe.erasedShape = shape).length) :
    ¬ Nonempty
      (HPres
        (prefixPendingInhomogeneous endpoint shape)
        shape.pairLeftDegree shape.pairRightDegree) := by
  let routingPrefix :=
    reuseRoutingPrefix endpoint
  apply
    homogeneous_emitted_pos
      cancellation routingPrefix.state.state.worklist routingPrefix.state.complete
        shape
  rw [length_emitted_corrections
    endpoint shape]
  exact hcorrections

/--
Retained-grid cancellation and the proposed pending-presentation kernel force
every shape-filtered operational correction list to be empty.
-/
theorem cancellation_pending_presentation
    (cancellation : CHCancel)
    (pending :
      PendingAggregatedHomogeneous)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (shape : CWord HPAtom) :
    endpoint.corrections.filter
        (fun term => term.family.recipe.erasedShape = shape) =
      [] := by
  by_contra hne
  exact
    homogeneous_pending_pos
      cancellation endpoint shape (List.length_pos_of_ne_nil hne)
        (pending.presentation endpoint shape)

/--
In particular, retained-grid cancellation and the proposed pending-presentation
kernel permit only operational endpoints with no emitted corrections at all.
-/
theorem corrections_cancellation_pending
    (cancellation : CHCancel)
    (pending :
      PendingAggregatedHomogeneous)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    endpoint.corrections = [] := by
  by_contra hne
  rcases List.exists_mem_of_ne_nil _ hne with ⟨term, hterm⟩
  have hfilter :=
    cancellation_pending_presentation
      cancellation pending endpoint term.family.recipe.erasedShape
  have htermFilter :
      term ∈ endpoint.corrections.filter
        (fun next =>
          next.family.recipe.erasedShape = term.family.recipe.erasedShape) := by
    exact List.mem_filter.mpr ⟨hterm, by simp⟩
  rw [hfilter] at htermFilter
  simp at htermFilter

end
  CAObstru
end TCTex
end Towers

/-!
# Shape-sorted aggregate-and-pending symbolic recollection

The aggregate-and-pending compiler consumes complete endpoint shape fibers.
Primary erased-shape sorting is a sharper operational boundary: interval
convexity and maximal-run completion turn it into those exact fibers.

This file threads that sharper boundary through ordered symbolic recollection
and fixed-packet stabilization.  It does not assert that the support-sensitive
independent collector already supplies primary shape sorting.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  PRPolys

universe u

open scoped commutatorElement

open HACoeff
open
  CIComp
open
  PIComp
open
  PFStab
open
  CPStab
open
  CFExp
open
  CFSubsti
open
  UNPkt
open
  FORed
open
  FSComp.OESorted
open PPColl
open PPColl.RCColl.RPAggreg

/--
The two explicit aggregate homogeneous-presentation theorems together with
pairwise primary endpoint shape sorting.
-/
structure
    CPRecoll :
    Prop where
  grids :
    OperationalAggregatedHomogeneous
  pending :
    PendingAggregatedHomogeneous
  shapeSorted :
    OESorted

namespace
  CPRecoll

/-- Compile primary endpoint shape sorting to the exact shape-fiber interface. -/
noncomputable def presentationGlobalSymbolic
    (kernel :
      CPRecoll) :
    OAPendin
      where
  grids := kernel.grids
  pending := kernel.pending
  shapeFiber := shapeFiberKernel kernel.shapeSorted

/-- Ordered symbolic recollection packets at one natural specialization. -/
noncomputable def concretePackets
    (kernel :
      CPRecoll)
    (M N : ℕ) :
    List RFPkt :=
  kernel.presentationGlobalSymbolic.concretePackets M N

/-- Shape-sorted aggregate-and-pending packets compute the powered commutator. -/
lemma list_packets_commutator
    (kernel :
      CPRecoll)
    (M N : ℕ) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  kernel.presentationGlobalSymbolic.list_packets_commutator
    M N

/-- The shape-sorted symbolic packet specializes to every ambient group. -/
lemma list_packets_group
    (kernel :
      CPRecoll)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    ((kernel.concretePackets M N).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ :=
  kernel.presentationGlobalSymbolic.list_packets_group
    M N left right

end
  CPRecoll

/--
Order-aware stabilization of a fixed packet list against the shape-sorted
aggregate-and-pending route.
-/
abbrev
    CAPendin
    (kernel :
      CPRecoll)
    (fixedPackets : List RFPkt) :
    Prop :=
  CPStab
    kernel.presentationGlobalSymbolic fixedPackets

namespace
  CAPendin

/-- A stabilized fixed packet computes the natural powered commutator. -/
lemma fixed_packet_power
    {kernel :
      CPRecoll}
    {fixedPackets : List RFPkt}
    (stabilization :
      CAPendin
        kernel fixedPackets)
    (M N : ℕ) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval universalLeft universalRight) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  stabilization.nat_cast_pow M N

/-- Shape-sorted fixed-packet stabilization supplies the truncated natural packet. -/
def sortedNaturalPacket
    {kernel :
      CPRecoll}
    {fixedPackets : List RFPkt}
    (stabilization :
      CAPendin
        kernel fixedPackets)
    (d n : ℕ) :
    TBPkt.{u} d n :=
  truncNaturalPacket stabilization d n

end
  CAPendin

open CAPendin

/--
A universal all-integral packet automa stabilizes the shape-sorted
aggregate-and-pending route.
-/
noncomputable def
    sortedStabilizationIntegral
    (kernel :
      CPRecoll)
    (packet : UAPkt.{0}) :
    CAPendin
      kernel packet.packets :=
  naturalStabilizationIntegral
    kernel.presentationGlobalSymbolic packet

/--
An all-integral packet with the same fixed list is the signed cutoff lift of
shape-sorted natural stabilization.
-/
def sortedAllUniversal
    {kernel :
      CPRecoll}
    {fixedPackets : List RFPkt}
    (stabilization :
      CAPendin
        kernel fixedPackets)
    (packet : UAPkt.{u})
    (hpackets : packet.packets = fixedPackets)
    (d n : ℕ) :
    (sortedNaturalPacket.{u} stabilization d n).AILift :=
  allUniversalPacket
    stabilization packet hpackets d n

end
  PRPolys
end TCTex
end Towers

/-!
# Reduction of productive compatible residual closure

The productive compatible scheduler opens only genuine support-compatible
grids and records that every opened batch has already emitted at least one
term.  Its finite completion introduces an explicit residual suffix.

This file packages three equivalent global formulations of the remaining
closure theorem:

* every canonical productive residual suffix is empty;
* every genuine productive prefix is already closed;
* every flattened productive compatible-grid history permutes to the genuine
  operational correction trace.

The verified empty and `1 x 1` base cases reduce each formulation to one
precise residual theorem for nontrivial positive inputs.
-/

namespace Towers
namespace TCTex
namespace
  PRRed

open RGClosa
open CTRoutea
open CCWork
open
  CPRoute
open
  PBCases
open
  PRComp
open
  CREquiv
open FMEnd

/--
Global productive compatible closure law: every genuine productive routing
prefix has exhausted all compatible batches it opened.
-/
structure OPReuse :
    Prop where
  closed :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      (productiveReuseRouting
        endpoint).state.state.state.worklist.Closed

/-- Global productive residual law: every canonical completion residual is empty. -/
structure OCProduc :
    Prop where
  residual_eq_nil :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      operationalProductiveCorrections endpoint = []

/--
Global productive compatible-grid law: every flattened opened-grid history
permutes to the genuine correction trace.
-/
structure OPPerm :
    Prop where
  compatible_perm_corrections :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      List.Perm
        (productiveReuseRouting
          endpoint).state.state.state.worklist.compatibleGrids
        endpoint.corrections

namespace OCProduc

/-- Empty productive residuals imply closure of every genuine productive prefix. -/
def reuseGridClosure
    (kernel : OCProduc) :
    OPReuse where
  closed := fun endpoint =>
    (operational_productive_closed
      endpoint).1 (kernel.residual_eq_nil endpoint)

end OCProduc

namespace OPReuse

/-- Closed genuine productive prefixes imply empty canonical productive residuals. -/
def residualClosureKernel
    (kernel : OPReuse) :
    OCProduc where
  residual_eq_nil := fun endpoint =>
    (operational_productive_closed
      endpoint).2 (kernel.closed endpoint)

/--
Closed genuine productive prefixes identify flattened opened grids with the
genuine correction trace up to permutation.
-/
def gridPermutationKernel
    (kernel : OPReuse) :
    OPPerm where
  compatible_perm_corrections := fun endpoint => by
    let routingPrefix :=
      productiveReuseRouting endpoint
    apply List.Perm.trans
      (OCReuse.emitted_grids_closed
        routingPrefix.state.state.state.worklist
        (kernel.closed endpoint)).symm
    apply routingPrefix.state.state.state.emitted_perm.trans
    rw [routingPrefix.routed_eq]

end OPReuse

namespace OPPerm

/--
Productive compatible-grid permutation forces closure of every genuine
productive prefix.
-/
def reuseGridClosure
    (kernel : OPPerm) :
    OPReuse where
  closed := fun endpoint => by
    let routingPrefix :=
      productiveReuseRouting endpoint
    apply
      (CRState.worklist_grids_routed
        routingPrefix.state.state.state).2
    rw [routingPrefix.routed_eq]
    exact kernel.compatible_perm_corrections endpoint

end OPPerm

/-- Empty productive residuals and productive-prefix closure are equivalent. -/
theorem compat_reuse_grid :
    OCProduc ↔
      OPReuse :=
  ⟨OCProduc.reuseGridClosure,
    OPReuse.residualClosureKernel⟩

/-- Productive-prefix closure and productive compatible-grid permutation are equivalent. -/
theorem productive_reuse_permutation :
    OPReuse ↔
      OPPerm :=
  ⟨OPReuse.gridPermutationKernel,
    OPPerm.reuseGridClosure⟩

/-- Empty productive residuals and productive compatible-grid permutation are equivalent. -/
theorem compat_grid_permutation :
    OCProduc ↔
      OPPerm :=
  compat_reuse_grid.trans
    productive_reuse_permutation

/--
Positive-input productive residual law.  The zero-left and zero-right cases are
already formalized independently.
-/
structure CCProduc :
    Prop where
  residual_eq_nil :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          ∀ endpoint :
              ODEmissi M N,
            operationalProductiveCorrections
              endpoint = []

/--
Nontrivial positive-input productive residual law.  The `1 x 1` case is
already formalized independently.
-/
structure NCProduc :
    Prop where
  residual_eq_nil :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          (M ≠ 1 ∨ N ≠ 1) →
            ∀ endpoint :
                ODEmissi M N,
              operationalProductiveCorrections
                endpoint = []

namespace OCProduc

/-- Global productive residual closure restricts to positive inputs. -/
def toPositiveKernel
    (kernel : OCProduc) :
    CCProduc where
  residual_eq_nil := fun _M _N _hM _hN endpoint =>
    kernel.residual_eq_nil endpoint

/-- Global productive residual closure restricts to nontrivial positive inputs. -/
def nontrivialPositiveKernel
    (kernel : OCProduc) :
    NCProduc where
  residual_eq_nil := fun _M _N _hM _hN _hnontrivial endpoint =>
    kernel.residual_eq_nil endpoint

end OCProduc

namespace CCProduc

/-- Zero-left and zero-right base cases upgrade positive closure to global closure. -/
def compatProductiveClosure
    (kernel :
      CCProduc) :
    OCProduc where
  residual_eq_nil := fun {M N} endpoint => by
    by_cases hM : M = 0
    · subst M
      exact productive_corrections_left N endpoint
    by_cases hN : N = 0
    · subst N
      exact productive_corrections_nil M endpoint
    exact kernel.residual_eq_nil M N
      (Nat.pos_of_ne_zero hM) (Nat.pos_of_ne_zero hN) endpoint

end CCProduc

namespace NCProduc

/-- The `1 x 1` base case upgrades nontrivial-positive closure to positive closure. -/
def toPositiveKernel
    (kernel :
      NCProduc) :
    CCProduc where
  residual_eq_nil := fun M N hM hN endpoint => by
    by_cases hMone : M = 1
    · by_cases hNone : N = 1
      · subst M
        subst N
        exact productive_residual_corrections endpoint
      · exact kernel.residual_eq_nil M N hM hN (Or.inr hNone) endpoint
    · exact kernel.residual_eq_nil M N hM hN (Or.inl hMone) endpoint

/--
The verified empty and `1 x 1` cases upgrade nontrivial-positive closure to
global productive residual closure.
-/
def compatProductiveClosure
    (kernel :
      NCProduc) :
    OCProduc :=
  kernel.toPositiveKernel
    |>.compatProductiveClosure

end NCProduc

/--
Global productive residual closure is equivalent to its nontrivial-positive
restriction.
-/
theorem operational_productive_nontrivial :
    OCProduc ↔
      NCProduc :=
  ⟨OCProduc.nontrivialPositiveKernel,
    NCProduc.compatProductiveClosure⟩

/--
Productive-prefix closure is equivalently the nontrivial-positive residual
law.
-/
theorem compat_productive_reuse :
    OPReuse ↔
      NCProduc :=
  compat_reuse_grid.symm.trans
    operational_productive_nontrivial

/--
Productive compatible-grid permutation is equivalently the
nontrivial-positive residual law.
-/
theorem compat_productive_permutation :
    OPPerm ↔
      NCProduc :=
  compat_grid_permutation.symm.trans
    operational_productive_nontrivial

end
  PRRed
end TCTex
end Towers

/-!
# Cardinality of the inverse-raw productive source

The inverse-oriented raw trace branches once for every possible inverse
conjugation correction.  A singleton inverse conjugation doubles a packet.
Consequently the right trace has cardinality `2 ^ N - 1`, and the full
left-right trace has cardinality

`(2 ^ M - 1) * (2 ^ N - 1)`.

The inverse-raw decorated-family source is indexed by that trace, so it has the
same cardinality.  This identifies the exact small-source region discharged by
the productive residual base cases.
-/

namespace Towers
namespace TCTex
namespace
  CPCard

open HACoeff
open
  PRComp
open
  PRRed
open FMEnd

/-- Applying one inverse conjugation atom doubles a trace packet. -/
lemma length_inverse_singleton
    {M N : ℕ}
    (a : LabelledAtom M N)
    (terms : List (CWord (LabelledAtom M N))) :
    (inverseTraceList [a] terms).length = 2 * terms.length := by
  simp [inverseTraceList, List.length_flatMap, inverseConjTrace,
    inverseConjugateAtom, Nat.mul_comm]

/-- The inverse-oriented trace against a right block has geometric cardinality. -/
lemma length_right_trace
    {M N : ℕ}
    (x : LabelledAtom M N) :
    ∀ rights : List (LabelledAtom M N),
      (inverseRightTrace x rights).length = 2 ^ rights.length - 1
  | [] => by
      simp [inverseRightTrace]
  | y :: rights => by
      rw [inverseRightTrace, List.length_cons,
        length_inverse_singleton,
        length_right_trace]
      simp only [List.length_cons]
      rw [pow_succ]
      have hpow : 0 < 2 ^ rights.length := by positivity
      omega

/-- The full inverse-oriented left-right trace is the product of two geometric factors. -/
lemma length_inverse_trace
    {M N : ℕ} :
    ∀ lefts rights : List (LabelledAtom M N),
      (inverseLeftTrace lefts rights).length =
        (2 ^ lefts.length - 1) * (2 ^ rights.length - 1)
  | [], rights => by
      simp [inverseLeftTrace]
  | x :: lefts, rights => by
      rw [inverseLeftTrace, List.length_append,
        length_inverse_singleton,
        length_inverse_trace,
        length_right_trace]
      simp only [List.length_cons]
      have hpow : 0 < 2 ^ lefts.length := by positivity
      have hstep :
          2 ^ (lefts.length + 1) - 1 =
            2 * (2 ^ lefts.length - 1) + 1 := by
        rw [pow_succ]
        omega
      rw [hstep]
      ring

/-- The labelled inverse-oriented raw trace has the closed geometric cardinality. -/
lemma length_labelled_atoms
    (M N : ℕ) :
    (inverseLeftTrace
      (labelledLeftAtoms M N)
      (labelledRightAtoms M N)).length =
        (2 ^ M - 1) * (2 ^ N - 1) := by
  rw [length_inverse_trace]
  simp [labelledLeftAtoms, labelledRightAtoms]

/-- The inverse-raw decorated-family source has the same geometric cardinality. -/
lemma length_inverse_decorated
    (M N : ℕ) :
    (inverseDecoratedTerms M N).length =
      (2 ^ M - 1) * (2 ^ N - 1) := by
  rw [inverseDecoratedTerms, List.length_ofFn]
  exact length_labelled_atoms M N

/-- A zero-left inverse-raw source has geometric cardinality zero. -/
lemma length_decorated_left
    (N : ℕ) :
    (inverseDecoratedTerms 0 N).length = 0 := by
  rw [length_inverse_decorated]
  simp

/-- A zero-right inverse-raw source has geometric cardinality zero. -/
lemma length_raw_decorated
    (M : ℕ) :
    (inverseDecoratedTerms M 0).length = 0 := by
  rw [length_inverse_decorated]
  simp

/-- The first positive-positive inverse-raw source has geometric cardinality one. -/
lemma length_decorated_family :
    (inverseDecoratedTerms 1 1).length = 1 := by
  rw [length_inverse_decorated]
  norm_num

/-- A positive exponent gives a positive geometric factor. -/
lemma pow_sub_pos
    {n : ℕ}
    (hn : 0 < n) :
    1 ≤ 2 ^ n - 1 := by
  have hpow : 1 < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  omega

/-- An exponent greater than one gives a geometric factor of at least two. -/
lemma two_pow_sub
    {n : ℕ}
    (hn : 1 < n) :
    2 ≤ 2 ^ n - 1 := by
  have hpow : 2 ^ 2 ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hn
  norm_num at hpow ⊢
  omega

/--
The inverse-raw source has at most one term exactly in the zero-left,
zero-right, and `1 x 1` cases.
-/
theorem length_decorated_terms
    (M N : ℕ) :
    (inverseDecoratedTerms M N).length ≤ 1 ↔
      M = 0 ∨ N = 0 ∨ (M = 1 ∧ N = 1) := by
  rw [length_inverse_decorated]
  constructor
  · intro hlength
    by_cases hM : M = 0
    · exact Or.inl hM
    by_cases hN : N = 0
    · exact Or.inr (Or.inl hN)
    have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hleftPos : 0 < 2 ^ M - 1 :=
      Nat.zero_lt_of_lt (pow_sub_pos hMpos)
    have hrightPos : 0 < 2 ^ N - 1 :=
      Nat.zero_lt_of_lt (pow_sub_pos hNpos)
    have hleftLe : 2 ^ M - 1 ≤ 1 :=
      (Nat.le_mul_of_pos_right _ hrightPos).trans hlength
    have hrightLe : 2 ^ N - 1 ≤ 1 := by
      apply (Nat.le_mul_of_pos_right _ hleftPos).trans
      simpa [Nat.mul_comm] using hlength
    have hMle : M ≤ 1 := by
      by_contra hMle
      have htwo := two_pow_sub (by omega : 1 < M)
      omega
    have hNle : N ≤ 1 := by
      by_contra hNle
      have htwo := two_pow_sub (by omega : 1 < N)
      omega
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · intro hsmall
    rcases hsmall with rfl | rfl | ⟨rfl, rfl⟩ <;> norm_num

/--
The genuinely recursive inverse-raw region is exactly the complement of the
three discharged source-size cases.
-/
theorem decorated_family_terms
    (M N : ℕ) :
    1 < (inverseDecoratedTerms M N).length ↔
      0 < M ∧ 0 < N ∧ (M ≠ 1 ∨ N ≠ 1) := by
  rw [← not_le, length_decorated_terms]
  omega

/--
Remaining productive residual theorem stated intrinsically: only inverse-raw
sources with more than one term require a proof.
-/
structure NCClos :
    Prop where
  residual_eq_nil :
    ∀ (M N : ℕ),
      1 < (inverseDecoratedTerms M N).length →
        ∀ endpoint :
            ODEmissi M N,
          operationalProductiveCorrections endpoint = []

namespace
  NCClos

/--
The intrinsic nontrivial-source law restricts to the nontrivial positive-input
law.
-/
def nontrivialPositiveKernel
    (kernel :
      NCClos) :
    NCProduc where
  residual_eq_nil := fun M N hM hN hnontrivial endpoint =>
    kernel.residual_eq_nil M N
      ((decorated_family_terms M N).2
        ⟨hM, hN, hnontrivial⟩)
      endpoint

/--
The intrinsic nontrivial-source law upgrades to the global productive residual
law through the verified small-source cases.
-/
def compatProductiveClosure
    (kernel :
      NCClos) :
    OCProduc :=
  kernel.nontrivialPositiveKernel
    |>.compatProductiveClosure

end
  NCClos

namespace
  NCProduc

/--
The nontrivial positive-input law is the intrinsic nontrivial-source law,
because the inverse-raw source cardinality detects exactly the same region.
-/
def nontrivialSourceKernel
    (kernel :
      NCProduc) :
    NCClos where
  residual_eq_nil := fun M N hsource endpoint => by
    obtain ⟨hM, hN, hnontrivial⟩ :=
      (decorated_family_terms M N).1 hsource
    exact kernel.residual_eq_nil M N hM hN hnontrivial endpoint

end
  NCProduc

/--
The intrinsic nontrivial-source law and the nontrivial positive-input law are
equivalent.
-/
theorem nontrivial_compat_productive :
    NCClos ↔
      NCProduc :=
  ⟨NCClos.nontrivialPositiveKernel,
    NCProduc.nontrivialSourceKernel⟩

/--
Global productive residual closure is equivalent to proving residual emptiness
only for inverse-raw sources with more than one term.
-/
theorem complete_productive_nontrivial :
    OCProduc ↔
      NCClos :=
  operational_productive_nontrivial.trans
    nontrivial_compat_productive.symm

/--
Productive-prefix closure is equivalently the intrinsic nontrivial-source
residual law.
-/
theorem compat_reuse_nontrivial :
    OPReuse ↔
      NCClos :=
  compat_reuse_grid.symm.trans
    complete_productive_nontrivial

/--
Productive compatible-grid permutation is equivalently the intrinsic
nontrivial-source residual law.
-/
theorem
  productive_permutation_nontrivial :
    OPPerm ↔
      NCClos :=
  compat_grid_permutation.symm.trans
    complete_productive_nontrivial

end
  CPCard
end TCTex
end Towers

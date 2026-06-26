import Towers.Group.Zassenhaus.BlockFamily
import Towers.Group.Zassenhaus.PermutedPacketWorklist

/-!
# Exact realization-slot packets for product and inverse collection

Collapsed packet counting remembers one erased Hall shape and the required
number of concrete words.  The operational collector needs a stronger local
invariant: every realization slot of a represented block family occurs
exactly once, although the concrete emission order may be arbitrary.

This file packages that invariant for lists of decorated family terms.  The
Cartesian grid of pairwise correction terms is proved to be a complete packet
for the canonical correction family.  Forgetting slot identities recovers the
collapsed-packet invariant consumed by the polynomial endpoint.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace HSPacket

open HACoeff
open PCCounti
open HPWork

namespace DFTerm

/-- Cartesian correction grid emitted by two complete concrete term packets. -/
noncomputable def correctionGrid
    {M N K : ℕ}
    (left right : List (DFTerm M N K)) :
    List (DFTerm M N K) :=
  left.flatMap fun B =>
    right.map fun A => B.correction A

@[simp]
lemma grid_nil_left
    {M N K : ℕ}
    (right : List (DFTerm M N K)) :
    correctionGrid [] right = [] :=
  rfl

@[simp]
lemma grid_nil_right
    {M N K : ℕ}
    (left : List (DFTerm M N K)) :
    correctionGrid left [] = [] := by
  simp [correctionGrid]

/--
The realization token of each emitted correction term is the pairwise
correction of its two parent tokens.
-/
lemma realization_token_grid
    {M N K : ℕ}
    (left right : List (DFTerm M N K)) :
    (correctionGrid left right).map
        DFTerm.realizationToken =
      (left.map DFTerm.realizationToken).flatMap fun b =>
        (right.map DFTerm.realizationToken).map
          (BFam.RToken.correction b) := by
  simp only [correctionGrid, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]
  rfl

/--
Forgetting decorated provenance turns the correction grid into the ordinary
Cartesian list of labelled commutator words.
-/
lemma decorated_family_grid
    {M N K : ℕ}
    (left right : List (DFTerm M N K)) :
    decoratedFamilyList (correctionGrid left right) =
      correctionWords
        (decoratedFamilyList left)
        (decoratedFamilyList right) := by
  simp [correctionGrid, decoratedFamilyList, correctionWords,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    DTerm.correction]

end DFTerm

/--
A concrete term packet realizes every slot of one counted block family
exactly once.  Concrete order is deliberately forgotten by permutation.
-/
def RPFor
    {M N K : ℕ}
    (F : BFam M N)
    (terms : List (DFTerm M N K)) :
    Prop :=
  List.Perm
    (BFam.realizationTokenList [F])
    (terms.map DFTerm.realizationToken)

namespace RPFor

/-- Every term of an exact packet carries the packet's represented family. -/
lemma family_eq_mem
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor F terms)
    {T : DFTerm M N K}
    (hT : T ∈ terms) :
    T.family = F := by
  have hfamilies :=
    hpacket.map Sigma.fst
  have hTfamily :
      T.family ∈
        (terms.map DFTerm.realizationToken).map Sigma.fst := by
    exact List.mem_map.mpr
      ⟨T.realizationToken, List.mem_map.mpr ⟨T, hT, rfl⟩, rfl⟩
  have hcanonical :=
    hfamilies.symm.subset hTfamily
  have hcanonical' : ¬ F.realizations = [] ∧ T.family = F := by
    simpa [RPFor,
    BFam.realization_tokenlist_fammap,
    BFam.realizationFamilyList] using hcanonical
  exact hcanonical'.2

/-- Exact slot coverage implies the required family realization count. -/
lemma terms_length_eq
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor F terms) :
    terms.length = F.realizations.length := by
  have hlength := hpacket.length_eq.symm
  simpa [RPFor, BFam.realizationTokenList] using hlength

/-- Forgetting exact slot identities yields the collapsed packet invariant. -/
lemma toCollapsedFor
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor F terms) :
    PCCounti.CPFor F
      (decoratedFamilyList terms) where
  same_shape := by
    intro word hword
    rcases List.mem_map.mp hword with ⟨T, hT, rfl⟩
    rw [← hpacket.family_eq_mem hT]
    exact T.family.collapse_word T.decorated.word T.word_mem
  length_eq := by
    simpa [decoratedFamilyList] using hpacket.terms_length_eq

/--
The Cartesian grid of two complete packets is a complete packet for the
canonical pairwise correction family.
-/
lemma correctionGrid
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    RPFor (B.correction A)
      (DFTerm.correctionGrid left right) := by
  rw [RPFor,
    DFTerm.realization_token_grid]
  exact
    (BFam.realizatoken_listsingleton_corrperm B A).trans
      (hleft.flatMap fun b _hb =>
        hright.map (BFam.RToken.correction b))

/--
The correction grid also closes after forgetting term provenance.  This is
the exact-slot strengthening of `CPFor.correctionWords`.
-/
lemma grid_collapsed_packet
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    PCCounti.CPFor (B.correction A)
      (decoratedFamilyList
      (DFTerm.correctionGrid left right)) :=
  (hleft.correctionGrid hright).toCollapsedFor

/--
A nonempty singleton-family packet has no represented family other than its
canonical packet family.
-/
lemma distinct_families_nonempty
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor F terms)
    (hnonempty : terms ≠ []) :
    distinctBlockFamilies terms = [F] := by
  classical
  have hfamilies :
      terms.map DFTerm.family =
        List.replicate terms.length F := by
    simpa using
      (List.eq_replicate_of_mem
        (l := terms.map DFTerm.family)
        (a := F)
        (by
          intro family hfamily
          rcases List.mem_map.mp hfamily with ⟨T, hT, rfl⟩
          exact hpacket.family_eq_mem hT))
  have hlength : 0 < terms.length :=
    List.length_pos_of_ne_nil hnonempty
  rw [distinctBlockFamilies, hfamilies]
  exact List.replicate_dedup hlength.ne'

/-- Every nonempty exact singleton-family packet is a realization-indexed block. -/
lemma realization_indexed_block
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor F terms)
    (hnonempty : terms ≠ []) :
    RealizationIndexedBlock terms := by
  rw [RealizationIndexedBlock,
    hpacket.distinct_families_nonempty hnonempty]
  exact hpacket

/-- Every nonempty Cartesian correction grid is an exact indexed block. -/
lemma realization_indexed_nonempty
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right)
    (hnonempty : DFTerm.correctionGrid left right ≠ []) :
    RealizationIndexedBlock
      (DFTerm.correctionGrid left right) :=
  (hleft.correctionGrid hright).realization_indexed_block hnonempty

/--
The concrete correction grid closes the permutation-aware arithmetic ledger.
This is the word-level image of the exact realization-token theorem above.
-/
noncomputable def gridClosedLedger
    {M N K : ℕ}
    (B A : BFam M N)
    (left right : List (DFTerm M N K)) :
    PSLedger B A
      (decoratedFamilyList left)
      (decoratedFamilyList right) where
  emitted :=
    decoratedFamilyList
      (DFTerm.correctionGrid left right)
  pending := []
  accounting := by
    simp only [List.append_nil]
    rw [DFTerm.decorated_family_grid]

@[simp]
lemma closed_ledger_pending
    {M N K : ℕ}
    (B A : BFam M N)
    (left right : List (DFTerm M N K)) :
    (gridClosedLedger B A left right).pending = [] :=
  rfl

/--
Two exact concrete packets therefore produce an already-closed work item for
the existing permutation-aware scheduler.
-/
noncomputable def closedWorkItem
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    PWItem M N where
  leftFamily := B
  rightFamily := A
  leftWords := decoratedFamilyList left
  rightWords := decoratedFamilyList right
  leftPacket := hleft.toCollapsedFor
  rightPacket := hright.toCollapsedFor
  ledger := gridClosedLedger B A left right

@[simp]
lemma grid_work_item
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    (closedWorkItem hleft hright).Closed :=
  rfl

/--
Closing the work item through the generic worklist API recovers the same
canonical correction packet.
-/
lemma closed_work_item
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    PCCounti.CPFor
      (B.correction A)
      (decoratedFamilyList
        (DFTerm.correctionGrid left right)) := by
  exact
    (closedWorkItem hleft hright).closedPacket
      (grid_work_item hleft hright)

end RPFor

/--
Ordered decomposition of concrete decorated terms into complete realization
packets.  The family order is the canonical recipe-endpoint order retained by
the polynomial collector.
-/
inductive RPBy
    {M N K : ℕ} :
    List (BFam M N) →
      List (DFTerm M N K) →
        Prop where
  | nil :
      RPBy [] []
  | cons
      (F : BFam M N)
      (families : List (BFam M N))
      (packet rest : List (DFTerm M N K))
      (hpacket : RPFor F packet)
      (hrest : RPBy families rest) :
      RPBy (F :: families) (packet ++ rest)

namespace RPBy

/-- Forget exact realization slots in every packet of an ordered endpoint. -/
lemma collapsedPacketed
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hpacketed : RPBy families terms) :
    PCCounti.CPBy
      families (decoratedFamilyList terms) := by
  induction hpacketed with
  | nil =>
      exact PCCounti.CPBy.nil
  | cons F families packet rest hpacket hrest ih =>
      rw [decoratedFamilyList, List.map_append]
      exact
        PCCounti.CPBy.cons
          F families
          (decoratedFamilyList packet)
          (decoratedFamilyList rest)
          hpacket.toCollapsedFor ih

/--
An exact-slot packet endpoint evaluates like the canonical realization lists
of its block families after collapse in every target group.
-/
lemma collapsed_list_realization
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hpacketed : RPBy families terms)
    (x y : G) :
    BFTrunc.collapsedList x y
        (decoratedFamilyList terms) =
      BFTrunc.collapsedList x y
        (BFam.realizationList families) :=
  hpacketed.collapsedPacketed.collapsed_list_realization x y

/-- One Cartesian correction grid is a singleton canonical packet endpoint. -/
lemma correctionGrid
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    RPBy [B.correction A]
      (DFTerm.correctionGrid left right) := by
  simpa using
    RPBy.cons
      (B.correction A) []
      (DFTerm.correctionGrid left right) []
      (hleft.correctionGrid hright)
      RPBy.nil

end RPBy

end HSPacket
end TCTex
end Towers

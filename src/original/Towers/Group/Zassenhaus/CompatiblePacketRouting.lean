import Towers.Group.Zassenhaus.FamilyOperationalSupport
import Towers.Group.Zassenhaus.OperationalInventory
import Towers.Group.Zassenhaus.Polynomial
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Towers.Group.HallPetrescoClaim


/-!
# Complete represented packets for compatible correction routing

Compatible routing stores a represented inventory around every concrete
correction occurrence.  The recursively constructed inventories satisfy a
stronger invariant than the routing state records: they are complete packets
for one block family, not arbitrary multi-family inventories.

This file exposes that singleton-family invariant.  It is the local input
needed by support-sensitive compatible-grid cancellation: each opened
schedule batch has two genuine complete parent packets.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CRRoutea

open HACoeff
open FIFilter
open OCClos
open RCRoutea
open HSPacket
open RSCovera

private lemma filter_singleton_nodup
    {α : Type*}
    [DecidableEq α]
    (value : α) :
    ∀ {values : List α},
      value ∈ values →
        values.Nodup →
          values.filter (· = value) = [value]
  | [], hmem, _ => by
      simp at hmem
  | head :: tail, hmem, hnodup => by
      rcases List.nodup_cons.mp hnodup with ⟨hhead, htail⟩
      by_cases hvalue : head = value
      · subst head
        rw [List.filter_cons_of_pos (by simp)]
        have htailFilter : tail.filter (· = value) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro next hnext hnextValue
          have hnextEq : next = value := of_decide_eq_true hnextValue
          subst next
          exact hhead hnext
        rw [htailFilter]
      · have hmemTail : value ∈ tail := by
          rcases List.mem_cons.mp hmem with hmemHead | hmemTail
          · exact False.elim (hvalue hmemHead.symm)
          · exact hmemTail
        simp [hvalue,
          filter_singleton_nodup value hmemTail htail]

/-- The inverse-raw terms carrying one represented family. -/
noncomputable def inverseRawTerms
    {M N : ℕ}
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length) :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length) := by
  classical
  exact
    (inverseDecoratedTerms M N).filter fun candidate =>
      candidate.family = term.family

/--
The inverse-raw terms carrying one represented family form the complete
singleton packet of that family.
-/
lemma realization_raw_terms
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ inverseDecoratedTerms M N) :
    RPFor term.family
      (inverseRawTerms term) := by
  classical
  let raw := inverseDecoratedTerms M N
  let full :=
    IMPropag.MIBlock.realization_indexed
      (realization_indexed_decorated M N)
  let filtered :=
    FIFilter.MIBlock.filterFamilies
      full fun family => family = term.family
  have hfamilies : filtered.families = [term.family] := by
    change
      (distinctBlockFamilies raw).filter (· = term.family) =
        [term.family]
    apply filter_singleton_nodup
    · exact distinct_block_families.mpr ⟨term, hterm, rfl⟩
    · exact distinct_families_nodup raw
  have hinventory := filtered.inventory
  rw [hfamilies] at hinventory
  simpa [inverseRawTerms] using hinventory

/--
One represented occurrence together with the complete singleton-family packet
that contains its realization slot.
-/
structure RTPkt
    {M N K : ℕ}
    (term : DFTerm M N K) where
  terms :
    List (DFTerm M N K)
  packet :
    RPFor term.family terms
  term_mem :
    term ∈ terms

namespace RTPkt

/-- Forget completeness and retain the represented inventory used by routing. -/
def representedTermInventory
    {M N K : ℕ}
    {term : DFTerm M N K}
    (packet : RTPkt term) :
    RTInv term where
  terms := packet.terms
  inventory :=
    IMPropag.MIBlock.ofPacket
      packet.packet
      (List.ne_nil_of_mem term.word_mem)
  term_mem := packet.term_mem

/-- Initialize a complete represented packet from one inverse-raw occurrence. -/
noncomputable def ofInverseRaw
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ inverseDecoratedTerms M N) :
    RTPkt term := by
  classical
  exact {
    terms := inverseRawTerms term
    packet := realization_raw_terms hterm
    term_mem := by
      simp [inverseRawTerms, hterm] }

/-- Recursive correction preserves complete singleton-family packets. -/
noncomputable def correction
    {M N K : ℕ}
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm) :
    RTPkt (leftTerm.correction rightTerm) where
  terms := DFTerm.correctionGrid left.terms right.terms
  packet := left.packet.correctionGrid right.packet
  term_mem := by
    apply List.mem_flatMap.mpr
    exact
      ⟨leftTerm, left.term_mem,
        List.mem_map.mpr ⟨rightTerm, right.term_mem, rfl⟩⟩

/--
Every finite correction tree whose leaves carry complete represented packets
has a complete represented packet at its root.
-/
lemma nonempty_correction_generated
    {M N K : ℕ}
    {source : List (DFTerm M N K)}
    (hsource :
      ∀ sourceTerm ∈ source,
        Nonempty (RTPkt sourceTerm))
    {term : DFTerm M N K}
    (hterm : DFTerm.CGFrom source term) :
    Nonempty (RTPkt term) := by
  induction hterm with
  | source hmem =>
      exact hsource _ hmem
  | correction _ _ ihleft ihright =>
      rcases ihleft with ⟨left⟩
      rcases ihright with ⟨right⟩
      exact ⟨left.correction right⟩

/--
Every term recursively generated from the inverse raw trace carries a
complete represented singleton-family packet.
-/
lemma nonempty_generated_raw
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) term) :
    Nonempty (RTPkt term) := by
  apply nonempty_correction_generated
    (source := inverseDecoratedTerms M N) _ hterm
  intro sourceTerm hsourceTerm
  exact ⟨ofInverseRaw hsourceTerm⟩

/--
Choose the complete represented packet carried by one term generated from the
inverse raw trace.
-/
noncomputable def correctionGeneratedRaw
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) term) :
    RTPkt term :=
  Classical.choice (nonempty_generated_raw hterm)

end RTPkt

end CRRoutea
end TCTex
end Towers

/-!
# Operationally compatible correction grids

The More3 collector does not emit every pairwise correction in a represented
Cartesian family grid.  It emits `B.correction A` only when
`A.decorated.independentBefore B.decorated`; in particular, the two support
histories must be disjoint.

This file defines the compatible filtered grid and records its elementary
properties.  It is the correct arithmetic source for future operational
worklists.  A full unfiltered represented grid is useful for symbolic family
inventory calculations, but it is too strong as an operational closure
target once recursively generated histories may overlap.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CCGrida

open HACoeff
open RCRoutea
open HSPacket

/-- The exact support-sensitive condition under which More3 emits one swap correction. -/
def correctionPairCompatible
    {M N K : ℕ}
    (left right : DFTerm M N K) :
    Prop :=
  right.decorated.independentBefore left.decorated

instance pairCompatibleDecidable
    {M N K : ℕ}
    (left right : DFTerm M N K) :
    Decidable (correctionPairCompatible left right) := by
  unfold correctionPairCompatible
  infer_instance

/--
Pairwise corrections whose parent histories satisfy the genuine operational
More3 obstruction condition.
-/
noncomputable def compatibleCorrectionGrid
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    List (DFTerm M N K) :=
  leftTerms.flatMap fun left =>
    (rightTerms.filter fun right =>
      decide (correctionPairCompatible left right)).map fun right =>
        left.correction right

@[simp]
lemma compatible_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {term : DFTerm M N K} :
    term ∈ compatibleCorrectionGrid leftTerms rightTerms ↔
      ∃ left ∈ leftTerms, ∃ right ∈ rightTerms,
        correctionPairCompatible left right ∧
          term = left.correction right := by
  simp [compatibleCorrectionGrid, correctionPairCompatible, eq_comm,
    and_assoc]

/-- Every compatible operational correction belongs to the full symbolic grid. -/
lemma compatible_grid_subset
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    ∀ ⦃term⦄,
      term ∈ compatibleCorrectionGrid leftTerms rightTerms →
        term ∈ DFTerm.correctionGrid leftTerms rightTerms := by
  intro term hterm
  rcases compatible_grid.mp hterm with
    ⟨left, hleft, right, hright, _hcompatible, rfl⟩
  apply List.mem_flatMap.mpr
  exact ⟨left, hleft, List.mem_map.mpr ⟨right, hright, rfl⟩⟩

/-- One genuine More3 obstruction belongs to its compatible parent grid. -/
lemma correction_compatible_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left right : DFTerm M N K}
    (hleft : left ∈ leftTerms)
    (hright : right ∈ rightTerms)
    (hcompatible : correctionPairCompatible left right) :
    left.correction right ∈
      compatibleCorrectionGrid leftTerms rightTerms :=
  compatible_grid.mpr
    ⟨left, hleft, right, hright, hcompatible, rfl⟩

/--
The selected genuine More3 obstruction belongs to the compatible grid of any
represented parent inventories containing its two occurrences.
-/
lemma represented_compatible_grid
    {M N K : ℕ}
    {left right : DFTerm M N K}
    (leftInventory : RTInv left)
    (rightInventory : RTInv right)
    (hcompatible : correctionPairCompatible left right) :
    left.correction right ∈
      compatibleCorrectionGrid leftInventory.terms rightInventory.terms :=
  correction_compatible_grid
    leftInventory.term_mem rightInventory.term_mem hcompatible

/-- Every compatible correction has a genuine operational parent pair. -/
lemma parents_compatible_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {term : DFTerm M N K}
    (hterm : term ∈ compatibleCorrectionGrid leftTerms rightTerms) :
    ∃ left ∈ leftTerms, ∃ right ∈ rightTerms,
      correctionPairCompatible left right ∧
        term = left.correction right :=
  compatible_grid.mp hterm

/-- Compatible corrections strictly increase support size over the left parent. -/
lemma support_correction_compatible
    {M N K : ℕ}
    {left right : DFTerm M N K}
    (hcompatible : correctionPairCompatible left right)
    (hright : right.decorated.support.Nonempty) :
    left.decorated.support.card <
      (left.correction right).decorated.support.card := by
  exact DTerm.support_correction_disjoint
    hcompatible.2.symm hright

/-- Compatible corrections strictly increase support size over the right parent. -/
lemma support_card_compatible
    {M N K : ℕ}
    {left right : DFTerm M N K}
    (hcompatible : correctionPairCompatible left right)
    (hleft : left.decorated.support.Nonempty) :
    right.decorated.support.card <
      (left.correction right).decorated.support.card := by
  exact DTerm.support_card_disjoint
    hcompatible.2.symm hleft

/-- Compatible corrections strictly lower support defect from the left parent. -/
lemma support_left_compatible
    {M N K : ℕ}
    {left right : DFTerm M N K}
    (hcompatible : correctionPairCompatible left right)
    (hright : right.decorated.support.Nonempty) :
    (left.correction right).decorated.supportDefect <
      left.decorated.supportDefect := by
  exact DTerm.support_left_disjoint
    hcompatible.2.symm hright

/-- Compatible corrections strictly lower support defect from the right parent. -/
lemma support_defect_compatible
    {M N K : ℕ}
    {left right : DFTerm M N K}
    (hcompatible : correctionPairCompatible left right)
    (hleft : left.decorated.support.Nonempty) :
    (left.correction right).decorated.supportDefect <
      right.decorated.supportDefect := by
  exact DTerm.support_defect_disjoint
    hcompatible.2.symm hleft

end CCGrida
end TCTex
end Towers

/-!
# Worklists for operationally compatible correction grids

More3 emits only support-compatible pairwise corrections.  This file provides
the finite pending-slot ledger and heterogeneous worklist for those filtered
grids.

Unlike the older full Cartesian multiplicity ledger, closing one compatible
ledger does not immediately claim a complete `BFam.correctionGrid`
inventory.  Support filtering is operationally necessary and may discard
overlapping-history pairs.  Polynomial aggregation of the resulting compatible
histories is a subsequent symbolic normalization theorem.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CCWork

open HACoeff
open IMPropag
open CCGrida

/-- Permutation-aware pending ledger for one compatible represented grid. -/
structure CTLedger
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) where
  emitted :
    List (DFTerm M N K)
  pending :
    List (DFTerm M N K)
  accounting :
    List.Perm (emitted ++ pending)
      (compatibleCorrectionGrid leftTerms rightTerms)

namespace CTLedger

/-- Open one compatible batch with every operationally admissible slot pending. -/
noncomputable def initial
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    CTLedger leftTerms rightTerms where
  emitted := []
  pending := compatibleCorrectionGrid leftTerms rightTerms
  accounting := by simp

/-- Consume one selected compatible correction slot. -/
def emit
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (ledger : CTLedger leftTerms rightTerms)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    CTLedger leftTerms rightTerms where
  emitted := ledger.emitted ++ [term]
  pending := before ++ after
  accounting := by
    apply List.Perm.trans _ ledger.accounting
    rw [hpending]
    simp only [List.append_assoc]
    apply List.Perm.append_left
    have hcomm :
        List.Perm
          (([term] : List (DFTerm M N K)) ++ before)
          (before ++ [term]) :=
      List.perm_append_comm
    simpa [List.append_assoc] using hcomm.append_right after

/-- Emitting one selected term removes exactly one pending slot. -/
lemma pending_length_emit
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (ledger : CTLedger leftTerms rightTerms)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    (ledger.emit before term after hpending).pending.length + 1 =
      ledger.pending.length := by
  simp [emit, hpending]
  omega

/-- Every pending compatible term has operationally admissible parents. -/
lemma parent_terms_pending
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (ledger : CTLedger leftTerms rightTerms)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ left ∈ leftTerms, ∃ right ∈ rightTerms,
      correctionPairCompatible left right ∧
        term = left.correction right := by
  have hcanonical :
      term ∈ compatibleCorrectionGrid leftTerms rightTerms :=
    ledger.accounting.subset (List.mem_append_right ledger.emitted hterm)
  exact parents_compatible_grid hcanonical

/--
Once one compatible ledger is exhausted, its emitted list is exactly its
compatible grid up to permutation.
-/
lemma emitted_perm_closed
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (ledger : CTLedger leftTerms rightTerms)
    (hclosed : ledger.pending = []) :
    List.Perm ledger.emitted
      (compatibleCorrectionGrid leftTerms rightTerms) := by
  simpa [hclosed] using ledger.accounting

end CTLedger

/-- One heterogeneous compatible correction batch with represented parents. -/
structure BWItem
    (M N K : ℕ) where
  leftTerms :
    List (DFTerm M N K)
  rightTerms :
    List (DFTerm M N K)
  left :
    MIBlock leftTerms
  right :
    MIBlock rightTerms
  ledger :
    CTLedger leftTerms rightTerms

namespace BWItem

/-- Open one represented compatible batch. -/
noncomputable def initial
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    BWItem M N K where
  leftTerms := leftTerms
  rightTerms := rightTerms
  left := left
  right := right
  ledger := CTLedger.initial leftTerms rightTerms

/-- Consume one selected compatible slot inside one heterogeneous batch. -/
def emit
    {M N K : ℕ}
    (item : BWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    BWItem M N K where
  leftTerms := item.leftTerms
  rightTerms := item.rightTerms
  left := item.left
  right := item.right
  ledger := item.ledger.emit before term after hpending

/-- A compatible batch is closed once every admissible slot has been consumed. -/
def Closed
    {M N K : ℕ}
    (item : BWItem M N K) :
    Prop :=
  item.ledger.pending = []

/-- Number of still-pending compatible slots in one batch. -/
def pendingSlots
    {M N K : ℕ}
    (item : BWItem M N K) :
    ℕ :=
  item.ledger.pending.length

/-- Consuming one compatible slot strictly lowers the batch pending count. -/
lemma pendingSlots_emit
    {M N K : ℕ}
    (item : BWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    (item.emit before term after hpending).pendingSlots + 1 =
      item.pendingSlots :=
  item.ledger.pending_length_emit before term after hpending

end BWItem

/-- One actual More3 obstruction routed to one compatible open batch. -/
structure CBEmissi
    {M N K : ℕ}
    (item : BWItem M N K) where
  leftTerm :
    DFTerm M N K
  rightTerm :
    DFTerm M N K
  left_mem :
    leftTerm ∈ item.leftTerms
  right_mem :
    rightTerm ∈ item.rightTerms
  compatible :
    correctionPairCompatible leftTerm rightTerm
  pendingPrefix :
    List (DFTerm M N K)
  pendingSuffix :
    List (DFTerm M N K)
  pending_eq :
    item.ledger.pending =
      pendingPrefix ++ leftTerm.correction rightTerm :: pendingSuffix

namespace CBEmissi

/-- Route one selected compatible parent pair to its pending slot. -/
noncomputable def ofMemPending
    {M N K : ℕ}
    (item : BWItem M N K)
    (leftTerm rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ item.leftTerms)
    (hright : rightTerm ∈ item.rightTerms)
    (hcompatible : correctionPairCompatible leftTerm rightTerm)
    (hpending :
      leftTerm.correction rightTerm ∈ item.ledger.pending) :
    CBEmissi item := by
  let hdecomposition := List.mem_iff_append.mp hpending
  exact {
    leftTerm := leftTerm
    rightTerm := rightTerm
    left_mem := hleft
    right_mem := hright
    compatible := hcompatible
    pendingPrefix := hdecomposition.choose
    pendingSuffix := hdecomposition.choose_spec.choose
    pending_eq := hdecomposition.choose_spec.choose_spec }

/-- One represented compatible pair routes in its freshly opened batch. -/
noncomputable def ofInitialCorrection
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms)
    (leftTerm rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ leftTerms)
    (hright : rightTerm ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    CBEmissi
      (BWItem.initial left right) :=
  ofMemPending _ leftTerm rightTerm hleft hright hcompatible <| by
    change leftTerm.correction rightTerm ∈
      compatibleCorrectionGrid leftTerms rightTerms
    exact correction_compatible_grid hleft hright hcompatible

/-- Consume the routed compatible correction slot. -/
noncomputable def emitItem
    {M N K : ℕ}
    {item : BWItem M N K}
    (emission : CBEmissi item) :
    BWItem M N K :=
  item.emit emission.pendingPrefix
    (emission.leftTerm.correction emission.rightTerm)
    emission.pendingSuffix emission.pending_eq

end CBEmissi

/-- Finite heterogeneous list of compatible open or closed batches. -/
abbrev CBWork
    (M N K : ℕ) :=
  List (BWItem M N K)

namespace CBWork

/-- Total number of pending compatible slots in a heterogeneous worklist. -/
def pendingSlots
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    ℕ :=
  (worklist.map BWItem.pendingSlots).sum

/-- Every compatible batch in the worklist has been exhausted. -/
def Closed
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    Prop :=
  ∀ item ∈ worklist, item.Closed

/-- Flattened support-compatible grids opened by one heterogeneous worklist. -/
noncomputable def compatibleGrids
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    List (DFTerm M N K) :=
  worklist.flatMap fun item =>
    compatibleCorrectionGrid item.leftTerms item.rightTerms

/-- Consume one selected compatible slot inside one worklist item. -/
inductive Step
    {M N K : ℕ} :
    CBWork M N K →
      CBWork M N K →
        Prop where
  | emit
      (pre post : CBWork M N K)
      (item : BWItem M N K)
      (before : List (DFTerm M N K))
      (term : DFTerm M N K)
      (after : List (DFTerm M N K))
      (hpending : item.ledger.pending = before ++ term :: after) :
      Step
        (pre ++ item :: post)
        (pre ++ item.emit before term after hpending :: post)

/-- Every compatible worklist emission strictly lowers pending-slot count. -/
lemma pending_slots_step
    {M N K : ℕ}
    {before after : CBWork M N K}
    (hstep : Step before after) :
    pendingSlots after < pendingSlots before := by
  cases hstep with
  | emit pre post item before term after hpending =>
      simp only [pendingSlots, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons]
      have hlength := item.pendingSlots_emit before term after hpending
      omega

/-- A routed genuine More3 obstruction consumes one compatible worklist slot. -/
def stepConcreteEmission
    {M N K : ℕ}
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (emission : CBEmissi item) :
    Step
      (pre ++ item :: post)
      (pre ++ emission.emitItem :: post) :=
  Step.emit pre post item emission.pendingPrefix
    (emission.leftTerm.correction emission.rightTerm)
    emission.pendingSuffix emission.pending_eq

/-- Every nonclosed compatible worklist admits one arithmetic emission. -/
lemma step_not_closed
    {M N K : ℕ}
    (worklist : CBWork M N K)
    (hclosed : ¬ worklist.Closed) :
    ∃ next, Step worklist next := by
  simp only [Closed, not_forall] at hclosed
  rcases hclosed with ⟨item, hitem, hopen⟩
  rcases List.mem_iff_append.mp hitem with ⟨pre, post, hworklist⟩
  simp only [BWItem.Closed] at hopen
  cases hpending : item.ledger.pending with
  | nil =>
      exact False.elim (hopen hpending)
  | cons term after =>
      refine ⟨pre ++ item.emit [] term after hpending :: post, ?_⟩
      rw [hworklist]
      exact Step.emit pre post item [] term after hpending

/-- Every finite compatible worklist can be drained arithmetically. -/
lemma exists_rewrites_closed
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    ∃ final, Relation.ReflTransGen Step worklist final ∧ final.Closed := by
  by_cases hclosed : worklist.Closed
  · exact ⟨worklist, Relation.ReflTransGen.refl, hclosed⟩
  · rcases step_not_closed worklist hclosed with ⟨next, hstep⟩
    rcases exists_rewrites_closed next with ⟨final, hrewrites, hclosed⟩
    exact ⟨final, hrewrites.head hstep, hclosed⟩
termination_by worklist.pendingSlots
decreasing_by
  exact pending_slots_step hstep

end CBWork

end CCWork
end TCTex
end Towers

/-!
# Reuse-first routing of compatible operational corrections

This file lifts support-compatible worklists to sequential routing states.
Each actual More3 obstruction consumes an already-open matching compatible
slot whenever possible.  A represented compatible grid is opened only when no
existing pending slot can route the occurrence.

The routed-prefix permutation invariant is purely operational.  Polynomial
normalization of closed compatible histories is a subsequent theorem.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CTRoutea

open HACoeff
open IMPropag
open CCGrida
open CCWork
open RCRoutea

/-- Concrete terms emitted so far by every compatible batch. -/
def batchWorklistEmitted
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    List (DFTerm M N K) :=
  worklist.flatMap fun item => item.ledger.emitted

/--
One compatible worklist emission appends the selected concrete term up to
permutation of terms emitted by later heterogeneous batches.
-/
lemma worklist_emitted_emit
    {M N K : ℕ}
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    List.Perm
      (batchWorklistEmitted
        (pre ++ item.emit before term after hpending :: post))
      (batchWorklistEmitted
        (pre ++ item :: post) ++ [term]) := by
  simp only [batchWorklistEmitted,
    List.flatMap_append, List.flatMap_cons,
    BWItem.emit,
    CTLedger.emit]
  have hcomm :
      List.Perm
        (([term] : List (DFTerm M N K)) ++
          (post.flatMap fun item => item.ledger.emitted))
        ((post.flatMap fun item => item.ledger.emitted) ++ [term]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    hcomm.append_left
      ((pre.flatMap fun item => item.ledger.emitted) ++ item.ledger.emitted)

/-- Sequential routing state for one compatible operational correction prefix. -/
structure CRState
    (M N K : ℕ) where
  worklist :
    CBWork M N K
  routedTerms :
    List (DFTerm M N K)
  emitted_perm :
    List.Perm
      (batchWorklistEmitted worklist)
      routedTerms

namespace CRState

/-- Empty compatible routing state before any operational correction is routed. -/
def nil
    (M N K : ℕ) :
    CRState M N K where
  worklist := []
  routedTerms := []
  emitted_perm := List.Perm.refl []

/-- Open one represented compatible batch without changing the routed prefix. -/
noncomputable def openBatch
    {M N K : ℕ}
    (state : CRState M N K)
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    CRState M N K where
  worklist :=
    state.worklist ++ [BWItem.initial left right]
  routedTerms := state.routedTerms
  emitted_perm := by
    simpa [batchWorklistEmitted,
      BWItem.initial,
      CTLedger.initial] using state.emitted_perm

/-- Route one selected compatible slot and append its correction operationally. -/
noncomputable def route
    {M N K : ℕ}
    (state : CRState M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    CRState M N K where
  worklist := pre ++ emission.emitItem :: post
  routedTerms :=
    state.routedTerms ++
      [emission.leftTerm.correction emission.rightTerm]
  emitted_perm := by
    have hroute :=
      worklist_emitted_emit
        pre post item emission.pendingPrefix
          (emission.leftTerm.correction emission.rightTerm)
          emission.pendingSuffix emission.pending_eq
    apply hroute.trans
    rw [← hworklist]
    exact state.emitted_perm.append_right _

/-- Routing one compatible slot strictly decreases the total pending count. -/
lemma pending_slots_route
    {M N K : ℕ}
    (state : CRState M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    (state.route pre post item hworklist emission).worklist.pendingSlots <
      state.worklist.pendingSlots := by
  apply CBWork.pending_slots_step
  rw [hworklist]
  exact CBWork.stepConcreteEmission
    pre post item emission

/-- Open one represented compatible batch and route its selected occurrence. -/
noncomputable def batchRouteRepresented
    {M N K : ℕ}
    (state : CRState M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    CRState M N K :=
  (state.openBatch left.inventory right.inventory).route state.worklist []
    (BWItem.initial left.inventory right.inventory)
    (by simp [openBatch])
    (CBEmissi.ofInitialCorrection
      left.inventory right.inventory leftTerm rightTerm
      left.term_mem right.term_mem hcompatible)

@[simp]
lemma routed_batch_represented
    {M N K : ℕ}
    (state : CRState M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    (state.batchRouteRepresented
      left right hcompatible).routedTerms =
        state.routedTerms ++ [leftTerm.correction rightTerm] :=
  rfl

/--
One already-open compatible worklist item whose pending grid can route the
specified correction occurrence.
-/
structure EPRoute
    {M N K : ℕ}
    (state : CRState M N K)
    (leftTerm rightTerm : DFTerm M N K) where
  pre :
    CBWork M N K
  post :
    CBWork M N K
  item :
    BWItem M N K
  worklist_eq :
    state.worklist = pre ++ item :: post
  left_mem :
    leftTerm ∈ item.leftTerms
  right_mem :
    rightTerm ∈ item.rightTerms
  compatible :
    correctionPairCompatible leftTerm rightTerm
  correction_mem_pending :
    leftTerm.correction rightTerm ∈ item.ledger.pending

namespace EPRoute

/-- Consume one correction occurrence from its already-open compatible batch. -/
noncomputable def consume
    {M N K : ℕ}
    {state : CRState M N K}
    {leftTerm rightTerm : DFTerm M N K}
    (existing : EPRoute state leftTerm rightTerm) :
    CRState M N K :=
  state.route existing.pre existing.post existing.item existing.worklist_eq
    (CBEmissi.ofMemPending
      existing.item leftTerm rightTerm existing.left_mem existing.right_mem
      existing.compatible existing.correction_mem_pending)

@[simp]
lemma routedTerms_consume
    {M N K : ℕ}
    {state : CRState M N K}
    {leftTerm rightTerm : DFTerm M N K}
    (existing : EPRoute state leftTerm rightTerm) :
    existing.consume.routedTerms =
      state.routedTerms ++ [leftTerm.correction rightTerm] :=
  rfl

end EPRoute

/--
Route one compatible represented correction occurrence by consuming an
existing pending slot whenever possible.
-/
noncomputable def representedReusingPending
    {M N K : ℕ}
    (state : CRState M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    CRState M N K := by
  classical
  exact
    if hroute :
        Nonempty (EPRoute state leftTerm rightTerm) then
      (Classical.choice hroute).consume
    else
      state.batchRouteRepresented left right hcompatible

@[simp]
lemma routed_represented_reusing
    {M N K : ℕ}
    (state : CRState M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    (representedReusingPending
      state left right hcompatible).routedTerms =
        state.routedTerms ++ [leftTerm.correction rightTerm] := by
  classical
  by_cases hroute :
      Nonempty (EPRoute state leftTerm rightTerm)
  · simp [representedReusingPending, hroute]
  · simp [representedReusingPending, hroute]

end CRState

end CTRoutea
end TCTex
end Towers

/-!
# Reuse-first routing of compatible operational corrections

Every actual More3 obstruction emits one concrete support-compatible
correction.  This file traverses that genuine operational recurrence while
consuming an already-open compatible slot whenever possible.  A fresh
compatible filtered grid is opened only as a fallback.

The resulting prefix routes the emitted-correction list exactly.  Closing the
compatible worklist and normalizing its support-compatible histories are
subsequent theorems.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CRRouteb

open HACoeff
open OCClos
open OEAccoun
open FMEnd
open RCRoutea
open CCGrida
open CTRoutea

namespace FInsert.ECorrec

/--
Route every correction occurrence emitted by one actual insertion, reusing
matching pending compatible slots whenever possible.
-/
lemma route_compa_reuse
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (state : CRState M N K)
    (hemits : FInsert.ECorrec hinsert corrections)
    (hrepresented :
      ∀ term ∈ L ++ [A],
        Nonempty (RTInv term)) :
    ∃ final : CRState M N K,
      final.routedTerms = state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil A =>
      exact ⟨state, by simp⟩
  | append P B A hAB =>
      exact ⟨state, by simp⟩
  | @obstruction P B A hAB Q R hcorrection hinsert
      correctionTerms insertTerms hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      have hB : Nonempty (RTInv B) :=
        hrepresented B (by simp)
      have hA : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      rcases hB with ⟨left⟩
      rcases hA with ⟨right⟩
      have hBA : Nonempty (RTInv (B.correction A)) :=
        ⟨left.correction right⟩
      have hcorrectionRepresented :
          ∀ term ∈ P ++ [B.correction A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hrepresented term (by simp [hterm])
        · rcases List.mem_singleton.mp hterm with rfl
          exact hBA
      have hQRepresented :
          ∀ term ∈ Q,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hcorrectionRepresented
            (FInsert.ECorrec.result_corre_gener
              hcorrectionTerms term hterm)
      have hinsertRepresented :
          ∀ term ∈ Q ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hQRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact ⟨right⟩
      let root :=
        CRState.representedReusingPending
          state left right hAB
      rcases ihcorrection root hcorrectionRepresented with
        ⟨afterCorrection, hafterCorrection⟩
      rcases ihinsert afterCorrection hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCorrection]
      simp [root, List.append_assoc]

end FInsert.ECorrec

namespace FCollec.ECorrec

/--
Route every correction occurrence emitted by one complete collection
derivation, reusing matching pending compatible slots whenever possible.
-/
lemma route_compa_reuse
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (state : CRState M N K)
    (hemits : FCollec.ECorrec hcollect corrections)
    (hrepresented :
      ∀ term ∈ L,
        Nonempty (RTInv term)) :
    ∃ final : CRState M N K,
      final.routedTerms = state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil =>
      exact ⟨state, by simp⟩
  | @snoc P A C R hcollect hinsert collectTerms insertTerms
      hcollectTerms hinsertTerms ihcollect =>
      have hPRepresented :
          ∀ term ∈ P,
            Nonempty (RTInv term) := by
        intro term hterm
        exact hrepresented term (by simp [hterm])
      rcases ihcollect state hPRepresented with
        ⟨afterCollect, hafterCollect⟩
      have hCRepresented :
          ∀ term ∈ C,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hPRepresented
            (FCollec.ECorrec.result_corre_gener
              hcollectTerms term hterm)
      have hARepresented : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      have hinsertRepresented :
          ∀ term ∈ C ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hCRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact hARepresented
      rcases
          FInsert.ECorrec.route_compa_reuse
            afterCollect hinsertTerms hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCollect]
      simp [List.append_assoc]

end FCollec.ECorrec

/--
The compatible reuse-first routing prefix of one operational emitted-correction
endpoint.
-/
structure OperationalReuseRouting
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  state :
    CRState M N
      (inverseLabelledCollection M N).factors.length
  routed_eq :
    state.routedTerms = endpoint.corrections

/-- Construct the compatible reuse-first prefix directly from the More3 trace. -/
noncomputable def operationalReuseRouting
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    OperationalReuseRouting endpoint := by
  let initial :=
    CRState.nil M N
      (inverseLabelledCollection M N).factors.length
  let routed :=
    FCollec.ECorrec.route_compa_reuse
      initial endpoint.emits
      (fun _term hterm =>
        ⟨RTInv.ofInverseRaw hterm⟩)
  let state := Classical.choose routed
  have hrouted := Classical.choose_spec routed
  exact {
    state := state
    routed_eq := by
      simpa [initial, CRState.nil] using
        hrouted }

end CRRouteb
end TCTex
end Towers

/-!
# Complete-packet invariant for compatible reuse-first routing

The compatible reuse-first scheduler opens a filtered correction grid only
when no existing pending slot can route the current occurrence.  Every grid it
opens comes from two recursively represented terms.  Those represented terms
carry complete singleton-family packets, and the selected correction pair is
a genuine compatible witness.

This file threads that stronger invariant through the scheduler.  It is the
worklist-level bridge from operational routing to support-sensitive
signed-block grid certificates.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CTRoute

open HACoeff
open CCGrida
open CTRoutea
open
  CRRoutea
open
  CRRoutea.RTPkt
open CCWork
open HSPacket

namespace BWItem

/--
One opened compatible batch has complete singleton-family parent packets and
contains at least one genuinely compatible parent pair.
-/
def HPPacket
    {M N K : ℕ}
    (item : BWItem M N K) :
    Prop :=
  ∃ (leftFamily rightFamily : BFam M N),
    RPFor leftFamily item.leftTerms ∧
      RPFor rightFamily item.rightTerms ∧
        ∃ leftTerm ∈ item.leftTerms, ∃ rightTerm ∈ item.rightTerms,
          correctionPairCompatible leftTerm rightTerm

/-- Consuming one pending slot preserves the complete-parent invariant. -/
lemma complete_parent_emit
    {M N K : ℕ}
    (item : BWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after)
    (hitem : HPPacket item) :
    HPPacket (item.emit before term after hpending) :=
  hitem

/-- A freshly opened batch from complete represented parents has the invariant. -/
lemma complete_parent_initial
    {M N K : ℕ}
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    HPPacket
      (BWItem.initial
        left.representedTermInventory.inventory
        right.representedTermInventory.inventory) := by
  exact
    ⟨leftTerm.family, rightTerm.family, left.packet, right.packet,
      leftTerm, left.term_mem, rightTerm, right.term_mem, hcompatible⟩

end BWItem

namespace CBWork

/-- Every opened compatible batch has complete represented parent packets. -/
def HPPacket
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    Prop :=
  ∀ item ∈ worklist,
    BWItem.HPPacket item

/-- The empty compatible worklist has the complete-parent invariant. -/
lemma complete_parent_nil
    (M N K : ℕ) :
    HPPacket
      ([] : CBWork M N K) := by
  simp [HPPacket]

/-- Appending one complete batch preserves the worklist invariant. -/
lemma HPPacket.append_singleton
    {M N K : ℕ}
    {worklist : CBWork M N K}
    {item : BWItem M N K}
    (hworklist : HPPacket worklist)
    (hitem :
      BWItem.HPPacket item) :
    HPPacket (worklist ++ [item]) := by
  intro next hnext
  rcases List.mem_append.mp hnext with hnext | hnext
  · exact hworklist next hnext
  · rcases List.mem_singleton.mp hnext with rfl
    exact hitem

/-- Replacing one batch by an emitted version preserves the worklist invariant. -/
lemma HPPacket.replace_emit
    {M N K : ℕ}
    {worklist : CBWork M N K}
    (hworklist : HPPacket worklist)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hdecomposition : worklist = pre ++ item :: post)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    HPPacket
      (pre ++ item.emit before term after hpending :: post) := by
  intro next hnext
  rcases List.mem_append.mp hnext with hnext | hnext
  · exact hworklist next <| by
      rw [hdecomposition]
      exact List.mem_append_left _ hnext
  · rcases List.mem_cons.mp hnext with rfl | hnext
    · apply BWItem.complete_parent_emit
      exact hworklist item <| by
        rw [hdecomposition]
        simp
    · exact hworklist next <| by
        rw [hdecomposition]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hnext)

end CBWork

/--
Compatible reuse-first routing state together with the complete-parent
invariant for every batch opened so far.
-/
structure CRStatea
    (M N K : ℕ) where
  state :
    CRState M N K
  complete :
    CBWork.HPPacket
      state.worklist

namespace CRStatea

/-- Empty complete routing state before any correction occurrence is routed. -/
def nil
    (M N K : ℕ) :
    CRStatea M N K where
  state := CRState.nil M N K
  complete := CBWork.complete_parent_nil
    M N K

/-- Consume one route from an already-open pending compatible grid. -/
noncomputable def consume
    {M N K : ℕ}
    {state : CRStatea M N K}
    {leftTerm rightTerm : DFTerm M N K}
    (existing :
      CRState.EPRoute
        state.state leftTerm rightTerm) :
    CRStatea M N K where
  state := existing.consume
  complete := by
    let emission :=
      CBEmissi.ofMemPending
        existing.item leftTerm rightTerm existing.left_mem existing.right_mem
          existing.compatible existing.correction_mem_pending
    change CBWork.HPPacket
      (existing.pre ++ emission.emitItem :: existing.post)
    exact CBWork.HPPacket.replace_emit
      state.complete
      existing.pre existing.post existing.item existing.worklist_eq
      emission.pendingPrefix
      (emission.leftTerm.correction emission.rightTerm)
      emission.pendingSuffix emission.pending_eq

/--
Open a new complete represented grid and consume its selected compatible
correction occurrence.
-/
noncomputable def batchRoute
    {M N K : ℕ}
    (state : CRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    CRStatea M N K where
  state :=
    state.state.batchRouteRepresented
      left.representedTermInventory right.representedTermInventory
      hcompatible
  complete := by
    let emission :=
      CBEmissi.ofInitialCorrection
        left.representedTermInventory.inventory
        right.representedTermInventory.inventory
        leftTerm rightTerm left.term_mem right.term_mem hcompatible
    change CBWork.HPPacket
      (state.state.worklist ++ [emission.emitItem])
    apply
      CBWork.HPPacket.append_singleton
        state.complete
    exact
      BWItem.complete_parent_emit
        (BWItem.initial
          left.representedTermInventory.inventory
          right.representedTermInventory.inventory)
        emission.pendingPrefix
        (emission.leftTerm.correction emission.rightTerm)
        emission.pendingSuffix emission.pending_eq
        (BWItem.complete_parent_initial
          left right hcompatible)

/--
Route one compatible represented occurrence, reusing an existing pending slot
whenever possible.
-/
noncomputable def representedReusingPending
    {M N K : ℕ}
    (state : CRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    CRStatea M N K := by
  classical
  exact
    if hroute :
        Nonempty
          (CRState.EPRoute
            state.state leftTerm rightTerm) then
      state.consume (Classical.choice hroute)
    else
      state.batchRoute left right hcompatible

@[simp]
lemma routed_represented_reusing
    {M N K : ℕ}
    (state : CRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    (state.representedReusingPending
      left right hcompatible).state.routedTerms =
        state.state.routedTerms ++ [leftTerm.correction rightTerm] := by
  classical
  by_cases hroute :
      Nonempty
        (CRState.EPRoute
          state.state leftTerm rightTerm)
  · simp [representedReusingPending, hroute, consume]
  · simp [representedReusingPending, hroute, batchRoute]

end CRStatea

end CTRoute
end TCTex
end Towers

/-!
# Compatible reuse-first operational closure boundary

The genuine More3 trace now routes only support-compatible correction slots.
The remaining global combinatorial theorem is that this compatible reuse-first
traversal exhausts every batch it opens.

Unlike the older Cartesian closure prototypes, this boundary does not claim
that operational collection emits every pair in a full represented grid.
Closed compatible histories still need a separate symbolic normalization
theorem before they produce polynomial recipe counts.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RGClosa

open HACoeff
open FMEnd
open HOCollec
open CCGrida
open CCWork
open CTRoutea
open CRRouteb

/--
Global compatible reuse-first closure law: after traversing every actual
operational correction, every opened compatible grid is exhausted.
-/
structure OCReuse : Prop where
  closed :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      (operationalReuseRouting endpoint).state.worklist.Closed

namespace OCReuse

/--
Exhausting a compatible worklist identifies its flattened emitted terms with
the flattened support-compatible grids it opened.
-/
lemma emitted_grids_closed
    {M N K : ℕ}
    (worklist : CBWork M N K)
    (hclosed : worklist.Closed) :
    List.Perm
      (batchWorklistEmitted worklist)
      worklist.compatibleGrids := by
  induction worklist with
  | nil =>
      rfl
  | cons item worklist ih =>
      apply List.Perm.append
      · exact item.ledger.emitted_perm_closed
          (hclosed item (by simp))
      · exact ih (fun next hnext => hclosed next (by simp [hnext]))

/--
Under compatible closure, the flattened emitted history of every opened batch
is exactly the operational correction list up to permutation.
-/
lemma emitted_perm_corrections
    (_kernel : OCReuse)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm
      (batchWorklistEmitted
        (operationalReuseRouting endpoint).state.worklist)
      endpoint.corrections := by
  let routingPrefix := operationalReuseRouting endpoint
  rw [← routingPrefix.routed_eq]
  exact routingPrefix.state.emitted_perm

/--
Under compatible closure, the flattened compatible grids opened by the trace
are exactly the operational correction list up to permutation.
-/
lemma compatible_perm_corrections
    (kernel : OCReuse)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm
      (operationalReuseRouting
        endpoint).state.worklist.compatibleGrids
      endpoint.corrections := by
  apply List.Perm.trans
    (emitted_grids_closed
      (operationalReuseRouting endpoint).state.worklist
      (kernel.closed endpoint)).symm
  exact kernel.emitted_perm_corrections endpoint

/--
Every batch in a closed compatible operational history emits exactly its
support-compatible correction grid up to permutation.
-/
lemma emitted_perm_grid
    (kernel : OCReuse)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (item : BWItem M N
      (inverseLabelledCollection M N).factors.length)
    (hitem :
      item ∈
        (operationalReuseRouting endpoint).state.worklist) :
    List.Perm item.ledger.emitted
      (compatibleCorrectionGrid item.leftTerms item.rightTerms) := by
  exact item.ledger.emitted_perm_closed
    (kernel.closed endpoint item hitem)

end OCReuse

end RGClosa
end TCTex
end Towers

/-!
# Complete-packet reuse-first routing of compatible operational corrections

Every actual More3 obstruction emits one concrete support-compatible
correction.  This file traverses that genuine operational recurrence while
retaining complete singleton-family packets around the parent terms of every
opened compatible batch.

The resulting prefix routes the emitted-correction list exactly and records
the packet invariant needed by retained-grid homogeneous cancellation.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CRRoutec

open HACoeff
open OCClos
open OEAccoun
open FMEnd
open
  CRRoutea
open
  CRRoutea.RTPkt
open CTRoutea
open
  CTRoute

namespace FInsert.ECorrec

/--
Route every correction occurrence emitted by one actual insertion while
preserving complete represented parent packets for each opened batch.
-/
lemma route_reuse_prefix
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (state : CRStatea M N K)
    (hemits : FInsert.ECorrec hinsert corrections)
    (hrepresented :
      ∀ term ∈ L ++ [A],
        Nonempty (RTPkt term)) :
    ∃ final : CRStatea M N K,
      final.state.routedTerms = state.state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil A =>
      exact ⟨state, by simp⟩
  | append P B A hAB =>
      exact ⟨state, by simp⟩
  | @obstruction P B A hAB Q R hcorrection hinsert
      correctionTerms insertTerms hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      have hB : Nonempty (RTPkt B) :=
        hrepresented B (by simp)
      have hA : Nonempty (RTPkt A) :=
        hrepresented A (by simp)
      rcases hB with ⟨left⟩
      rcases hA with ⟨right⟩
      have hBA :
          Nonempty (RTPkt (B.correction A)) :=
        ⟨left.correction right⟩
      have hcorrectionRepresented :
          ∀ term ∈ P ++ [B.correction A],
            Nonempty (RTPkt term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hrepresented term (by simp [hterm])
        · rcases List.mem_singleton.mp hterm with rfl
          exact hBA
      have hQRepresented :
          ∀ term ∈ Q,
            Nonempty (RTPkt term) := by
        intro term hterm
        exact
          RTPkt.nonempty_correction_generated
            hcorrectionRepresented
            (FInsert.ECorrec.result_corre_gener
              hcorrectionTerms term hterm)
      have hinsertRepresented :
          ∀ term ∈ Q ++ [A],
            Nonempty (RTPkt term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hQRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact ⟨right⟩
      let root :=
        CRStatea.representedReusingPending
          state left right hAB
      rcases ihcorrection root hcorrectionRepresented with
        ⟨afterCorrection, hafterCorrection⟩
      rcases ihinsert afterCorrection hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCorrection]
      simp [root, List.append_assoc]

end FInsert.ECorrec

namespace FCollec.ECorrec

/--
Route every correction occurrence emitted by one complete collection
derivation while preserving complete represented parent packets.
-/
lemma route_reuse_prefix
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (state : CRStatea M N K)
    (hemits : FCollec.ECorrec hcollect corrections)
    (hrepresented :
      ∀ term ∈ L,
        Nonempty (RTPkt term)) :
    ∃ final : CRStatea M N K,
      final.state.routedTerms = state.state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil =>
      exact ⟨state, by simp⟩
  | @snoc P A C R hcollect hinsert collectTerms insertTerms
      hcollectTerms hinsertTerms ihcollect =>
      have hPRepresented :
          ∀ term ∈ P,
            Nonempty (RTPkt term) := by
        intro term hterm
        exact hrepresented term (by simp [hterm])
      rcases ihcollect state hPRepresented with
        ⟨afterCollect, hafterCollect⟩
      have hCRepresented :
          ∀ term ∈ C,
            Nonempty (RTPkt term) := by
        intro term hterm
        exact
          RTPkt.nonempty_correction_generated
            hPRepresented
            (FCollec.ECorrec.result_corre_gener
              hcollectTerms term hterm)
      have hARepresented : Nonempty (RTPkt A) :=
        hrepresented A (by simp)
      have hinsertRepresented :
          ∀ term ∈ C ++ [A],
            Nonempty (RTPkt term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hCRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact hARepresented
      rcases
          FInsert.ECorrec.route_reuse_prefix
            afterCollect hinsertTerms hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCollect]
      simp [List.append_assoc]

end FCollec.ECorrec

/--
The complete-packet compatible reuse-first routing prefix of one operational
emitted-correction endpoint.
-/
structure ReuseRoutingPrefix
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  state :
    CRStatea M N
      (inverseLabelledCollection M N).factors.length
  routed_eq :
    state.state.routedTerms = endpoint.corrections

/--
Construct the complete-packet compatible reuse-first prefix directly from the
More3 trace.
-/
noncomputable def reuseRoutingPrefix
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ReuseRoutingPrefix endpoint := by
  let initial :=
    CRStatea.nil M N
      (inverseLabelledCollection M N).factors.length
  let routed :=
    FCollec.ECorrec.route_reuse_prefix
        initial endpoint.emits
        (fun _term hterm =>
          ⟨RTPkt.ofInverseRaw hterm⟩)
  let state := Classical.choose routed
  have hrouted := Classical.choose_spec routed
  exact {
    state := state
    routed_eq := by
      simpa [initial, CRStatea.nil,
        CRState.nil] using hrouted }

end CRRoutec
end TCTex
end Towers

/-!
# Compatible operational shape-block normalization

The genuine More3 collector opens only support-compatible correction grids.
Closing those grids is therefore separate from the symbolic normalization
step: compatible histories still have to be aggregated into complete
same-shape realization inventories.

This file records that remaining aggregation theorem at its exact boundary.
Once supplied, the existing multiplicity-preserving shape-block compressor
constructs a finite `BFam.Expansion`, and the natural polynomial
identity follows automa.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSNorm

open scoped commutatorElement

open HACoeff
open RNCompre.BFam.Expansion
open BRSpec
open IMPropag
open ISPropag
open HSInvent
open HOCollec
open OEAccoun
open FMEnd
open RGClosa
open CRRouteb

/--
Support-sensitive symbolic aggregation law: every maximal same-shape block in
an operational endpoint with extracted correction emissions is an exact
unordered inventory of nonempty block families.

The families may repeat.  Repeated compatible histories contribute repeated
polynomial multiplicity and must not be deduplicated.
-/
structure OCNorm : Prop where
  inventory :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks endpoint.collected.factors →
        ∃ families : List (BFam M N),
          RIFor families block ∧
            ∀ F ∈ families, F.realizations ≠ []

namespace OCNorm

/--
Forget the extracted emission witness after using it to invoke compatible
shape-block normalization.
-/
def shapeInventoryPropagation
    (kernel : OCNorm) :
    SIPropag where
  inventory collected block hblock := by
    rcases FCollec.exists_emitsCorrections collected.family_collects with
      ⟨corrections, hemits⟩
    let endpoint : ODEmissi _ _ := {
      collected := collected
      corrections := corrections
      emits := hemits }
    exact kernel.inventory endpoint block hblock

/--
Compatible shape-block normalization constructs a finite counted-family
expansion for every pair of natural source multiplicities.
-/
noncomputable def expansion
    (kernel : OCNorm)
    (M N : ℕ) :
    BFam.Expansion M N :=
  kernel.shapeInventoryPropagation.expansion M N

/--
The normalized counted-family expansion satisfies the natural Hall-Petresco
polynomial identity.
-/
lemma recipe_commutator_power
    (kernel : OCNorm)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G) :
    ((((kernel.expansion M N).families.map BFam.recipe).map fun R =>
      R.erasedShape.eval (HPAtom.eval x y) ^
        coefficientValue R (M : ℤ) (N : ℤ)).prod) =
      ⁅x ^ M, y ^ N⁆ :=
  recipe_cast_pow (kernel.expansion M N) x y

end OCNorm

/--
The corrected operational Hall-Petresco boundary consists of two independent
obligations:

* actual support-compatible correction grids are exhausted by routing;
* the resulting support-sensitive histories normalize into shape inventories.

Keeping these fields separate prevents accidental replacement of the genuine
compatible grids by over-large Cartesian correction grids.
-/
structure OCKern : Prop where
  compatibleClosure :
    OCReuse
  shapeNormalization :
    OCNorm

namespace OCKern

/--
Closed compatible routing identifies the opened support-sensitive grids with
the actual emitted correction list.
-/
lemma compatible_perm_corrections
    (kernel : OCKern)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm
      (operationalReuseRouting
        endpoint).state.worklist.compatibleGrids
      endpoint.corrections :=
  kernel.compatibleClosure.compatible_perm_corrections endpoint

/--
The complete compatibility-aware boundary constructs the natural counted
family expansion.
-/
noncomputable def expansion
    (kernel : OCKern)
    (M N : ℕ) :
    BFam.Expansion M N :=
  kernel.shapeNormalization.expansion M N

/--
The complete compatibility-aware boundary supplies the natural polynomial
Hall-Petresco identity consumed by the later signed-extension layer.
-/
lemma recipe_cast_pow
    (kernel : OCKern)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G) :
    ((((kernel.expansion M N).families.map BFam.recipe).map fun R =>
      R.erasedShape.eval (HPAtom.eval x y) ^
        coefficientValue R (M : ℤ) (N : ℤ)).prod) =
      ⁅x ^ M, y ^ N⁆ :=
  kernel.shapeNormalization.recipe_commutator_power M N x y

end OCKern

end CSNorm
end TCTex
end Towers

/-!
# Finite completion of complete-packet compatible routing states

The genuine More3 trace routes only the corrections it actually emits.  Its
compatible reuse-first worklist may therefore retain pending slots.  This file
does not assume those slots are absent.  Instead, it drains any opened
compatible worklist through finitely many concrete corrections while preserving
the complete-parent invariant required by retained-grid cancellation.

For an operational endpoint, the resulting closed schedule is the genuine
correction list followed by an explicit residual suffix.  Thus the residual,
rather than an unjustified closure hypothesis, is the precise remaining
normalization boundary.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CRCompa

open HACoeff
open RGClosa
open CCGrida
open CTRoutea
open CCWork
open
  CRRoutec
open
  CTRoute
open FMEnd
open HSPacket

/-- Route one selected pending compatible slot while retaining complete parents. -/
noncomputable def routeCompletePending
    {M N K : ℕ}
    (state : CRStatea M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    CRStatea M N K where
  state := state.state.route pre post item hworklist emission
  complete := by
    change CBWork.HPPacket
      (pre ++ emission.emitItem :: post)
    exact CBWork.HPPacket.replace_emit
      state.complete pre post item hworklist emission.pendingPrefix
      (emission.leftTerm.correction emission.rightTerm)
      emission.pendingSuffix emission.pending_eq

@[simp]
lemma routedTerms_route
    {M N K : ℕ}
    (state : CRStatea M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    (routeCompletePending state pre post item hworklist emission).state.routedTerms =
      state.state.routedTerms ++
        [emission.leftTerm.correction emission.rightTerm] :=
  rfl

/-- Routing one selected pending compatible slot strictly lowers open slots. -/
lemma pending_slots_route
    {M N K : ℕ}
    (state : CRStatea M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    (routeCompletePending state pre post item hworklist emission).state.worklist.pendingSlots <
      state.state.worklist.pendingSlots :=
  state.state.pending_slots_route pre post item hworklist emission

/-- Draining one pending slot does not change the flattened opened grids. -/
@[simp]
lemma compatible_grids_pending
    {M N K : ℕ}
    (state : CRStatea M N K)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hworklist : state.state.worklist = pre ++ item :: post)
    (emission : CBEmissi item) :
    (routeCompletePending state pre post item hworklist emission).state.worklist.compatibleGrids =
      state.state.worklist.compatibleGrids := by
  rw [hworklist]
  simp [routeCompletePending, CRState.route,
    CBEmissi.emitItem,
    BWItem.emit,
    CBWork.compatibleGrids]

/--
Any complete-packet compatible routing prefix extends through finitely many
concrete emissions to a closed worklist state.
-/
lemma closed_complete_extension
    {M N K : ℕ}
    (state : CRStatea M N K) :
    ∃ final : CRStatea M N K,
      final.state.worklist.Closed ∧
        state.state.routedTerms <+: final.state.routedTerms ∧
          final.state.worklist.compatibleGrids =
            state.state.worklist.compatibleGrids := by
  by_cases hclosed : state.state.worklist.Closed
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
        let next := routeCompletePending state pre post item hworklist emission
        rcases closed_complete_extension next with
          ⟨final, hfinalClosed, hprefix, hgrids⟩
        refine ⟨final, hfinalClosed, ?_, ?_⟩
        · apply (List.prefix_append state.state.routedTerms
            [leftTerm.correction rightTerm]).trans
          simpa [next, emission] using hprefix
        · calc
            final.state.worklist.compatibleGrids =
                next.state.worklist.compatibleGrids :=
              hgrids
            _ = state.state.worklist.compatibleGrids :=
              compatible_grids_pending
                state pre post item hworklist emission
termination_by state.state.worklist.pendingSlots
decreasing_by
  exact pending_slots_route state pre post item hworklist emission

/--
A closed complete-packet extension of one genuine operational compatible
routing prefix.
-/
structure OCRoute
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  state :
    CRStatea M N
      (inverseLabelledCollection M N).factors.length
  closed :
    state.state.worklist.Closed
  corrections_prefix :
    endpoint.corrections <+: state.state.routedTerms
  compatible_grids_prefix :
    state.state.worklist.compatibleGrids =
      (reuseRoutingPrefix
        endpoint).state.state.worklist.compatibleGrids

/-- Every genuine operational compatible prefix has a finite closed extension. -/
noncomputable def operationalCompleteRouting
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    OCRoute endpoint := by
  let routingPrefix := reuseRoutingPrefix endpoint
  by_cases hclosed : routingPrefix.state.state.worklist.Closed
  · exact {
      state := routingPrefix.state
      closed := hclosed
      corrections_prefix := by
        rw [routingPrefix.routed_eq]
      compatible_grids_prefix := rfl }
  · let completion := closed_complete_extension routingPrefix.state
    let final := Classical.choose completion
    have hfinal := Classical.choose_spec completion
    exact {
      state := final
      closed := hfinal.1
      corrections_prefix := by
        rw [← routingPrefix.routed_eq]
        exact hfinal.2.1
      compatible_grids_prefix := hfinal.2.2 }

namespace OCRoute

/-- The residual corrections added only to drain the compatible schedule. -/
def residualCorrections
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint) :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length) :=
  extension.state.state.routedTerms.drop endpoint.corrections.length

/-- A closed extension is the genuine emitted trace followed by its residual. -/
lemma routed_corrections_append
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint) :
    extension.state.state.routedTerms =
      endpoint.corrections ++ extension.residualCorrections :=
  List.prefix_append_drop extension.corrections_prefix

/--
The compatible grids of a closed extension are exactly the genuine corrections
followed by the residual suffix, up to permutation.
-/
lemma compatible_grids_perm
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint) :
    List.Perm extension.state.state.worklist.compatibleGrids
      (endpoint.corrections ++ extension.residualCorrections) := by
  apply List.Perm.trans
    (OCReuse.emitted_grids_closed
      extension.state.state.worklist extension.closed).symm
  rw [← extension.routed_corrections_append]
  exact extension.state.state.emitted_perm

/-- Every residual correction still belongs to one opened compatible grid. -/
lemma compatible_grids_corrections
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ extension.residualCorrections) :
    term ∈ extension.state.state.worklist.compatibleGrids := by
  apply
    extension.compatible_grids_perm.symm.subset
  exact List.mem_append_right endpoint.corrections hterm

/--
Every residual correction carries a complete represented singleton-family
packet inherited from the two complete parent packets of its opened grid.
-/
lemma nonemp_repre_corre
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ extension.residualCorrections) :
    Nonempty
      (CRRoutea.RTPkt
        term) := by
  have hgrid := extension.compatible_grids_corrections hterm
  rcases List.mem_flatMap.mp hgrid with ⟨item, hitem, htermItem⟩
  rcases extension.state.complete item hitem with
    ⟨leftFamily, rightFamily, leftPacket, rightPacket,
      _leftWitness, _hleftWitness, _rightWitness, _hrightWitness,
      _hcompatibleWitness⟩
  rcases compatible_grid.mp htermItem with
    ⟨leftTerm, hleftTerm, rightTerm, hrightTerm, _hcompatible, rfl⟩
  exact ⟨{
    terms := DFTerm.correctionGrid item.leftTerms item.rightTerms
    packet := by
      change
        RPFor (leftTerm.family.correction rightTerm.family)
          (DFTerm.correctionGrid item.leftTerms item.rightTerms)
      rw [leftPacket.family_eq_mem hleftTerm,
        rightPacket.family_eq_mem hrightTerm]
      exact leftPacket.correctionGrid rightPacket
    term_mem := by
      apply List.mem_flatMap.mpr
      exact
        ⟨leftTerm, hleftTerm,
          List.mem_map.mpr ⟨rightTerm, hrightTerm, rfl⟩⟩ }⟩

/--
Raw source terms plus a closed compatible schedule differ from the operational
endpoint factors by exactly the residual suffix.
-/
lemma grids_perm_corrections
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (extension : OCRoute endpoint) :
    List.Perm
      (inverseDecoratedTerms M N ++
        extension.state.state.worklist.compatibleGrids)
      (endpoint.collected.factors ++ extension.residualCorrections) := by
  apply List.Perm.trans
  · exact
      (extension.compatible_grids_perm).append_left _
  · simpa [List.append_assoc] using
      endpoint.perm_append_corrections.symm.append_right
        extension.residualCorrections

end OCRoute

end CRCompa
end TCTex
end Towers

/-!
# Productive complete-packet reuse-first routing

Every compatible batch opened by the operational reuse-first router is
immediately used to emit its selected correction occurrence.  Thus every
batch retained in the worklist has already emitted at least one term.

The existing complete-packet routing state intentionally records only parent
packet completeness.  This file packages the stronger productive invariant
in a separate isolated layer and threads it through the genuine recurrence.
-/

namespace Towers
namespace TCTex
namespace
  CPRoute

open HACoeff
open CCGrida
open CRRouteb
open CTRoutea
open CCWork
open
  CRRoutec
open
  CTRoute
open
  CRRoutea
open
  CRRoutea.RTPkt
open OCClos
open OEAccoun
open FMEnd

namespace BWItem

/-- A compatible batch is productive once it has emitted at least one term. -/
def Productive
    {M N K : ℕ}
    (item : BWItem M N K) :
    Prop :=
  item.ledger.emitted ≠ []

/-- Consuming any pending slot makes the resulting compatible batch productive. -/
lemma productive_emit
    {M N K : ℕ}
    (item : BWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    Productive (item.emit before term after hpending) := by
  simp [Productive, BWItem.emit,
    CTLedger.emit]

end BWItem

namespace CBWork

/-- Every retained compatible batch has emitted at least one term. -/
def Productive
    {M N K : ℕ}
    (worklist : CBWork M N K) :
    Prop :=
  ∀ item ∈ worklist, BWItem.Productive item

/-- The empty compatible worklist is productive. -/
lemma productive_nil
    (M N K : ℕ) :
    Productive ([] : CBWork M N K) := by
  simp [Productive]

/-- Appending one productive compatible batch preserves productivity. -/
lemma Productive.append_singleton
    {M N K : ℕ}
    {worklist : CBWork M N K}
    {item : BWItem M N K}
    (hworklist : Productive worklist)
    (hitem : BWItem.Productive item) :
    Productive (worklist ++ [item]) := by
  intro next hnext
  rcases List.mem_append.mp hnext with hnext | hnext
  · exact hworklist next hnext
  · rcases List.mem_singleton.mp hnext with rfl
    exact hitem

/-- Replacing one batch by an emitted version preserves productivity. -/
lemma Productive.replace_emit
    {M N K : ℕ}
    {worklist : CBWork M N K}
    (hworklist : Productive worklist)
    (pre post : CBWork M N K)
    (item : BWItem M N K)
    (hdecomposition : worklist = pre ++ item :: post)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    Productive (pre ++ item.emit before term after hpending :: post) := by
  intro next hnext
  rcases List.mem_append.mp hnext with hnext | hnext
  · exact hworklist next <| by
      rw [hdecomposition]
      exact List.mem_append_left _ hnext
  · rcases List.mem_cons.mp hnext with rfl | hnext
    · exact BWItem.productive_emit
        item before term after hpending
    · exact hworklist next <| by
        rw [hdecomposition]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hnext)

/--
A productive worklist with no emitted terms has no opened batches.
-/
lemma nil_productive_emitted
    {M N K : ℕ}
    (worklist : CBWork M N K)
    (hproductive : Productive worklist)
    (hemitted :
      batchWorklistEmitted worklist = []) :
    worklist = [] := by
  cases worklist with
  | nil =>
      rfl
  | cons item rest =>
      have hitem : item.ledger.emitted ≠ [] :=
        hproductive item (by simp)
      change item.ledger.emitted ++ batchWorklistEmitted rest = [] at hemitted
      exact False.elim (hitem (List.append_eq_nil_iff.mp hemitted).1)

/--
The number of productive compatible batches is bounded by the number of
terms they have emitted.
-/
lemma length_emitted_terms
    {M N K : ℕ}
    (worklist : CBWork M N K)
    (hproductive : Productive worklist) :
    worklist.length ≤
      (batchWorklistEmitted worklist).length := by
  induction worklist with
  | nil =>
      simp [batchWorklistEmitted]
  | cons item rest ih =>
      have hitem : item.ledger.emitted ≠ [] :=
        hproductive item (by simp)
      have hrest : Productive rest := by
        intro next hnext
        exact hproductive next (by simp [hnext])
      have ih := ih hrest
      have hlength : 0 < item.ledger.emitted.length := by
        cases hemitted : item.ledger.emitted with
        | nil =>
            exact False.elim (hitem hemitted)
        | cons term terms =>
            simp
      rw [batchWorklistEmitted,
        List.flatMap_cons, List.length_append]
      simp only [List.length_cons]
      change rest.length + 1 ≤
        item.ledger.emitted.length +
          (batchWorklistEmitted rest).length
      omega

end CBWork

namespace CSProduc

/-- Every compatible batch retained by a complete routing state is productive. -/
def Productive
    {M N K : ℕ}
    (state : CRStatea M N K) :
    Prop :=
  CBWork.Productive state.state.worklist

/-- The empty complete compatible routing state is productive. -/
lemma productive_nil
    (M N K : ℕ) :
    Productive
      (CRStatea.nil M N K) := by
  exact CBWork.productive_nil M N K

/-- Reusing an already-open pending slot preserves productivity. -/
lemma productive_consume
    {M N K : ℕ}
    {state : CRStatea M N K}
    (hproductive : Productive state)
    {leftTerm rightTerm : DFTerm M N K}
    (existing :
      CRState.EPRoute
        state.state leftTerm rightTerm) :
    Productive
      (CRStatea.consume existing) := by
  let emission :=
    CBEmissi.ofMemPending
      existing.item leftTerm rightTerm existing.left_mem existing.right_mem
        existing.compatible existing.correction_mem_pending
  change CBWork.Productive
    (existing.pre ++ emission.emitItem :: existing.post)
  exact hproductive.replace_emit
    existing.pre existing.post existing.item existing.worklist_eq
    emission.pendingPrefix
    (emission.leftTerm.correction emission.rightTerm)
    emission.pendingSuffix emission.pending_eq

/-- Opening and immediately routing a fresh complete batch preserves productivity. -/
lemma productive_batch_route
    {M N K : ℕ}
    {state : CRStatea M N K}
    (hproductive : Productive state)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    Productive
      (CRStatea.batchRoute
        state left right hcompatible) := by
  let emission :=
    CBEmissi.ofInitialCorrection
      left.representedTermInventory.inventory
      right.representedTermInventory.inventory
      leftTerm rightTerm left.term_mem right.term_mem hcompatible
  change CBWork.Productive
    (state.state.worklist ++ [emission.emitItem])
  exact hproductive.append_singleton <|
    BWItem.productive_emit
      (BWItem.initial
        left.representedTermInventory.inventory
        right.representedTermInventory.inventory)
      emission.pendingPrefix
      (emission.leftTerm.correction emission.rightTerm)
      emission.pendingSuffix emission.pending_eq

/-- Reuse-first routing of one represented correction preserves productivity. -/
lemma productive_represented_reusing
    {M N K : ℕ}
    {state : CRStatea M N K}
    (hproductive : Productive state)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    Productive
      (CRStatea.representedReusingPending
        state left right hcompatible) := by
  classical
  by_cases hroute :
      Nonempty
        (CRState.EPRoute
          state.state leftTerm rightTerm)
  · simpa [CRStatea.representedReusingPending,
      hroute] using
      productive_consume hproductive (Classical.choice hroute)
  · simpa [CRStatea.representedReusingPending,
      hroute] using
      productive_batch_route hproductive left right hcompatible

end CSProduc

/--
A complete compatible routing state equipped with the operational fact that
every opened batch has already emitted a term.
-/
structure PRState
    (M N K : ℕ) where
  state :
    CRStatea M N K
  productive :
    CSProduc.Productive state

namespace PRState

/-- Empty productive complete routing state before any correction is routed. -/
def nil
    (M N K : ℕ) :
    PRState M N K where
  state := CRStatea.nil M N K
  productive := CSProduc.productive_nil
    M N K

/-- Route one represented correction while retaining productivity. -/
noncomputable def representedReusingPending
    {M N K : ℕ}
    (state : PRState M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    PRState M N K where
  state :=
    state.state.representedReusingPending
      left right hcompatible
  productive :=
    CSProduc.productive_represented_reusing
      state.productive left right hcompatible

@[simp]
lemma routed_represented_reusing
    {M N K : ℕ}
    (state : PRState M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    (state.representedReusingPending
      left right hcompatible).state.state.routedTerms =
        state.state.state.routedTerms ++ [leftTerm.correction rightTerm] := by
  simp [representedReusingPending]

/--
A productive complete routing state with no routed corrections has no opened
compatible batches.
-/
lemma worklist_nil_routed
    {M N K : ℕ}
    (state : PRState M N K)
    (hrouted : state.state.state.routedTerms = []) :
    state.state.state.worklist = [] := by
  apply
    CBWork.nil_productive_emitted
      state.state.state.worklist state.productive
  apply List.eq_nil_of_length_eq_zero
  have hlength := state.state.state.emitted_perm.length_eq
  rw [hrouted] at hlength
  simpa using hlength

/--
The number of opened batches in a productive routing state is bounded by the
number of routed correction occurrences.
-/
lemma worklistRoutedTerms
    {M N K : ℕ}
    (state : PRState M N K) :
    state.state.state.worklist.length ≤
      state.state.state.routedTerms.length := by
  rw [← state.state.state.emitted_perm.length_eq]
  exact CBWork.length_emitted_terms
    state.state.state.worklist state.productive

end PRState

namespace FInsert.ECorrec

/--
Route every correction occurrence emitted by one insertion while retaining
complete represented packets and productivity of every opened batch.
-/
lemma route_productive_reuse
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (state : PRState M N K)
    (hemits : FInsert.ECorrec hinsert corrections)
    (hrepresented :
      ∀ term ∈ L ++ [A],
        Nonempty (RTPkt term)) :
    ∃ final : PRState M N K,
      final.state.state.routedTerms =
        state.state.state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil A =>
      exact ⟨state, by simp⟩
  | append P B A hAB =>
      exact ⟨state, by simp⟩
  | @obstruction P B A hAB Q R hcorrection hinsert
      correctionTerms insertTerms hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      have hB : Nonempty (RTPkt B) :=
        hrepresented B (by simp)
      have hA : Nonempty (RTPkt A) :=
        hrepresented A (by simp)
      rcases hB with ⟨left⟩
      rcases hA with ⟨right⟩
      have hBA :
          Nonempty (RTPkt (B.correction A)) :=
        ⟨left.correction right⟩
      have hcorrectionRepresented :
          ∀ term ∈ P ++ [B.correction A],
            Nonempty (RTPkt term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hrepresented term (by simp [hterm])
        · rcases List.mem_singleton.mp hterm with rfl
          exact hBA
      have hQRepresented :
          ∀ term ∈ Q,
            Nonempty (RTPkt term) := by
        intro term hterm
        exact
          RTPkt.nonempty_correction_generated
            hcorrectionRepresented
            (FInsert.ECorrec.result_corre_gener
              hcorrectionTerms term hterm)
      have hinsertRepresented :
          ∀ term ∈ Q ++ [A],
            Nonempty (RTPkt term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hQRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact ⟨right⟩
      let root :=
        state.representedReusingPending left right hAB
      rcases ihcorrection root hcorrectionRepresented with
        ⟨afterCorrection, hafterCorrection⟩
      rcases ihinsert afterCorrection hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCorrection]
      simp [root, List.append_assoc]

end FInsert.ECorrec

namespace FCollec.ECorrec

/--
Route every correction occurrence emitted by one collection derivation while
retaining complete represented packets and productivity.
-/
lemma route_productive_reuse
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (state : PRState M N K)
    (hemits : FCollec.ECorrec hcollect corrections)
    (hrepresented :
      ∀ term ∈ L,
        Nonempty (RTPkt term)) :
    ∃ final : PRState M N K,
      final.state.state.routedTerms =
        state.state.state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil =>
      exact ⟨state, by simp⟩
  | @snoc P A C R hcollect hinsert collectTerms insertTerms
      hcollectTerms hinsertTerms ihcollect =>
      have hPRepresented :
          ∀ term ∈ P,
            Nonempty (RTPkt term) := by
        intro term hterm
        exact hrepresented term (by simp [hterm])
      rcases ihcollect state hPRepresented with
        ⟨afterCollect, hafterCollect⟩
      have hCRepresented :
          ∀ term ∈ C,
            Nonempty (RTPkt term) := by
        intro term hterm
        exact
          RTPkt.nonempty_correction_generated
            hPRepresented
            (FCollec.ECorrec.result_corre_gener
              hcollectTerms term hterm)
      have hARepresented : Nonempty (RTPkt A) :=
        hrepresented A (by simp)
      have hinsertRepresented :
          ∀ term ∈ C ++ [A],
            Nonempty (RTPkt term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hCRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact hARepresented
      rcases
          FInsert.ECorrec.route_productive_reuse
            afterCollect hinsertTerms hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCollect]
      simp [List.append_assoc]

end FCollec.ECorrec

/--
The productive complete-packet reuse-first routing prefix of one operational
emitted-correction endpoint.
-/
structure ProductiveReuseRouting
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  state :
    PRState M N
      (inverseLabelledCollection M N).factors.length
  routed_eq :
    state.state.state.routedTerms = endpoint.corrections

/--
Construct the productive complete-packet prefix directly from the genuine
More3 trace.
-/
noncomputable def productiveReuseRouting
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ProductiveReuseRouting endpoint := by
  let initial :=
    PRState.nil M N
      (inverseLabelledCollection M N).factors.length
  let routed :=
    FCollec.ECorrec.route_productive_reuse
      initial endpoint.emits
      (fun _term hterm =>
        ⟨RTPkt.ofInverseRaw hterm⟩)
  let state := Classical.choose routed
  have hrouted := Classical.choose_spec routed
  exact {
    state := state
    routed_eq := by
      simpa [initial,
        PRState.nil,
        CRStatea.nil,
        CRState.nil] using hrouted }

/--
If an operational endpoint emitted no corrections, its productive routing
prefix opened no compatible batches.
-/
theorem
  productive_reuse_corrections
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hcorrections : endpoint.corrections = []) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist = [] := by
  apply
    PRState.worklist_nil_routed
  rw [(productiveReuseRouting
    endpoint).routed_eq, hcorrections]

/--
The number of compatible batches opened by the productive endpoint prefix is
bounded by the number of genuine operational correction occurrences.
-/
theorem
  reuse_worklist_corrections
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist.length ≤
        endpoint.corrections.length := by
  rw [← (productiveReuseRouting
    endpoint).routed_eq]
  exact
    PRState.worklistRoutedTerms
      (productiveReuseRouting endpoint).state

/--
If an operational endpoint emitted no corrections, its productive routing
prefix is already closed.
-/
theorem productive_reuse_nil
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hcorrections : endpoint.corrections = []) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist.Closed := by
  rw [
    productive_reuse_corrections
      endpoint hcorrections]
  simp [CBWork.Closed]

/--
If an operational endpoint emitted no corrections, the compatible-grid
flattening opened by its productive prefix is empty as well.
-/
theorem compat_reuse_nil
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (hcorrections : endpoint.corrections = []) :
    (productiveReuseRouting
      endpoint).state.state.state.worklist.compatibleGrids = [] := by
  rw [
    productive_reuse_corrections
      endpoint hcorrections]
  rfl

end
  CPRoute
end TCTex
end Towers

/-!
# Compatible operational shape-block admissibility

Support-sensitive More3 collection does not generally emit a complete
Cartesian `BFam.correction` grid: overlapping histories remain in their
existing relative order.  The bare Hall-Petresco endpoint needs less.  For
each maximal same-shape block, it is enough to prove that the concrete block
length is an admissible coefficient at that Hall bidegree.

This file packages that weaker boundary and constructs the resulting bare
`FExp`.  The diagonal equality-class lemmas in the older collector
are intended to prove this admissibility law.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSAdmiss

open scoped commutatorElement

open HACoeff
open ISEnd
open HOCollec
open FMEnd
open RGClosa
open CRRouteb
open CSNorm
open PPColl
open PPColl.RCColl.RPAggreg

/--
The support-sensitive polynomial aggregation law: the length of every maximal
same-shape operational block is an admissible coefficient at its erased Hall
bidegree.
-/
structure OCAdmiss : Prop where
  coefficient_admissible :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks endpoint.collected.factors →
        ∀ word : CWord HPAtom,
          (∀ term ∈ block, term.erasedShape = word) →
            (block.length : ℤ) ∈
              submodule M N word.pairLeftDegree word.pairRightDegree

namespace OCAdmiss

/-- Choose the common erased Hall shape of one canonical maximal block. -/
noncomputable def shapeOfMem
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    CWord HPAtom :=
  Classical.choose
    (same_erased_blocks
      endpoint.collected.factors block hblock)

/-- Every term in a canonical maximal block has its chosen erased Hall shape. -/
lemma erased_shape
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm : term ∈ block) :
    term.erasedShape = shapeOfMem endpoint block hblock :=
  Classical.choose_spec
    (same_erased_blocks
      endpoint.collected.factors block hblock) term hterm

/-- Canonical maximal same-shape blocks are nonempty. -/
lemma nil_same_blocks
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    block ≠ [] := by
  intro hnil
  apply List.ne_nil_of_mem_splitBy
    (show
      block ∈ endpoint.collected.factors.splitBy
        fun left right => decide (left.erasedShape = right.erasedShape) by
      simpa [sameErasedBlocks] using hblock)
  exact hnil

/-- Compress one admissible maximal shape block to one bare Hall factor. -/
noncomputable def factorOfMem
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    Factor M N :=
  let shape := shapeOfMem endpoint block hblock
  let term := block.head (nil_same_blocks endpoint block hblock)
  {
    word := shape
    coefficient := block.length
    positive := by
      change (shapeOfMem endpoint block hblock).PBPos
      rw [← erased_shape endpoint block hblock term
        (List.head_mem
          (nil_same_blocks endpoint block hblock))]
      exact term.positive
    coefficient_admissible :=
      kernel.coefficient_admissible endpoint block hblock shape
        (erased_shape endpoint block hblock) }

@[simp]
lemma factor_word
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    (kernel.factorOfMem endpoint block hblock).word =
      shapeOfMem endpoint block hblock :=
  rfl

@[simp]
lemma factor_coefficient
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    (kernel.factorOfMem endpoint block hblock).coefficient =
      block.length :=
  rfl

/-- One admissible maximal block has the same collapsed value as its factor. -/
lemma factor_eval
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks endpoint.collected.factors) :
    (kernel.factorOfMem endpoint block hblock).eval universalLeft universalRight =
      decoratedCollapsedEval (block.map DFTerm.decorated) := by
  rw [Factor.eval, factor_word, factor_coefficient,
    decorated_collapsed_same
      block (shapeOfMem endpoint block hblock)
      (erased_shape endpoint block hblock),
    zpow_natCast]

/-- Compress a list of canonical maximal blocks to bare Hall factors. -/
noncomputable def factorsOfBlocks
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ∀ blocks : List (List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      (∀ block ∈ blocks,
        block ∈ sameErasedBlocks endpoint.collected.factors) →
          List (Factor M N)
  | [], _ => []
  | block :: blocks, hblocks =>
      kernel.factorOfMem endpoint block (hblocks block (by simp)) ::
        kernel.factorsOfBlocks endpoint blocks
          (fun next hnext => hblocks next (by simp [hnext]))

/-- Blockwise compression preserves the collapsed evaluation. -/
lemma list_factors_blocks
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    ∀ (blocks : List (List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)))
      (hblocks : ∀ block ∈ blocks,
        block ∈ sameErasedBlocks endpoint.collected.factors),
      listEval universalLeft universalRight
          (kernel.factorsOfBlocks endpoint blocks hblocks) =
        decoratedCollapsedEval
          (blocks.flatten.map DFTerm.decorated)
  | [], _ => rfl
  | block :: blocks, hblocks => by
      rw [factorsOfBlocks, HACoeff.listEval_cons,
        factor_eval,
        List.flatten_cons, List.map_append,
        decorated_collapsed_append,
        list_factors_blocks kernel endpoint blocks]

/-- Compress the canonical maximal partition of one endpoint. -/
noncomputable def factors
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List (Factor M N) :=
  kernel.factorsOfBlocks endpoint
    (sameErasedBlocks endpoint.collected.factors)
    (fun _block hblock => hblock)

/-- The compressed maximal blocks evaluate to the endpoint factors. -/
lemma eval_factors
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    listEval universalLeft universalRight (kernel.factors endpoint) =
      decoratedCollapsedEval
        (endpoint.collected.factors.map DFTerm.decorated) := by
  rw [factors,
    kernel.list_factors_blocks endpoint
      (sameErasedBlocks endpoint.collected.factors)
      (fun _block hblock => hblock),
    flatten_same_blocks]

/-- One endpoint with admissible maximal blocks produces a bare expansion. -/
noncomputable def freeExpansion
    (kernel : OCAdmiss)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    FExp M N where
  factors := kernel.factors endpoint
  eval_eq := by
    rw [kernel.eval_factors endpoint]
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

end OCAdmiss

/--
The stronger realization-inventory normalization boundary implies bare
shape-block admissibility.
-/
def shapeBlockNormalization
    (kernel : OCNorm) :
    OCAdmiss where
  coefficient_admissible endpoint block hblock word hterms := by
    rcases kernel.inventory endpoint block hblock with
      ⟨families, hinventory, hnonempty⟩
    exact length_submodule_realization
      families block word
        (RIFor.realization_list_lengtheq hinventory)
        (fun family hfamily =>
          RIFor.recipe_shape_eqmem
            hinventory hnonempty hterms hfamily)

/--
The corrected bare operational boundary consists of compatible-grid closure
and admissibility of the resulting maximal shape-block lengths.
-/
structure OCAdmissa : Prop where
  compatibleClosure :
    OCReuse
  shapeBlockAdmissibility :
    OCAdmiss

namespace OCAdmissa

/-- Closed routing identifies opened support-sensitive grids with emissions. -/
lemma compatible_perm_corrections
    (kernel : OCAdmissa)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm
      (operationalReuseRouting
        endpoint).state.worklist.compatibleGrids
      endpoint.corrections :=
  kernel.compatibleClosure.compatible_perm_corrections endpoint

/-- Resolve one canonical operational endpoint with emission data. -/
noncomputable def endpoint
    (M N : ℕ) :
    ODEmissi M N :=
  Classical.choice
    (nonempty_decorated_emissions M N)

/-- The weaker compatibility-aware boundary constructs a bare expansion. -/
noncomputable def freeExpansion
    (kernel : OCAdmissa)
    (M N : ℕ) :
    FExp M N :=
  kernel.shapeBlockAdmissibility.freeExpansion (endpoint M N)

end OCAdmissa

end CSAdmiss
end TCTex
end Towers

/-!
# Uniform natural Hall-Petresco packets from compatible collection

Compatible operational collection constructs one counted-family expansion for
each pair of natural source multiplicities.  The signed Hall-Petresco layer
needs one cutoff-specific recipe list independent of those multiplicities.

This file records the exact normalization boundary between the two layers:
the fixed recipe product must agree, at every natural pair, with the product
of the corresponding operational expansion.  Once that is supplied, the
uniform natural packet follows immediately.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSNorm
namespace OCKern

universe u

open scoped commutatorElement

open HACoeff
open BRSpec

/--
A fixed recipe list uniformly normalizes the multiplicity-dependent
operational expansions at all natural source multiplicities.
-/
structure URNorm
    (kernel : OCKern)
    (recipes : List BRecipe) : Prop where
  recipe_prod_expansion :
    ∀ (M N : ℕ)
      {G : Type*}
      [Group G]
      (x y : G),
        ((recipes.map fun R =>
          R.erasedShape.eval (HPAtom.eval x y) ^
            coefficientValue R (M : ℤ) (N : ℤ)).prod) =
          ((((kernel.expansion M N).families.map BFam.recipe).map
            fun R =>
              R.erasedShape.eval (HPAtom.eval x y) ^
                coefficientValue R (M : ℤ) (N : ℤ)).prod)

namespace URNorm

/--
Literal stabilization of the operational recipe lists is a sufficient
uniform normalization witness.
-/
def expansion_recipes
    {kernel : OCKern}
    {recipes : List BRecipe}
    (hexpansionRecipes :
      ∀ M N : ℕ,
        (kernel.expansion M N).families.map BFam.recipe = recipes) :
    URNorm kernel recipes where
  recipe_prod_expansion M N _ _ x y := by
    rw [hexpansionRecipes M N]

/--
A uniform recipe normalization witness is exactly the natural packet needed
before proving the signed extension theorem.
-/
def truncatedNaturalPacket
    {kernel : OCKern}
    {recipes : List BRecipe}
    (uniform : URNorm kernel recipes)
    (d n : ℕ) :
    FNPkt.TNPkt.{u}
      d n where
  recipes := recipes
  list_nat_cast left right M N :=
    (uniform.recipe_prod_expansion M N left right).trans
      (kernel.recipe_cast_pow M N left right)

end URNorm

end OCKern
end CSNorm
end TCTex
end Towers

/-!
# Diagonal aggregation for compatible shape blocks

Support-compatible history counts are obtained by inclusion-exclusion over
source-label equality classes.  Each equality class contributes one diagonal
count (`M` on the left or `N` on the right), while an integer multiplicity
records the inclusion-exclusion sign and any finite combinatorial coefficient.

The older Newton lemmas already prove that every such homogeneous diagonal
count is admissible.  This file packages finite signed sums of those counts and
reduces compatible shape-block admissibility to a concrete finite
equality-class certificate for each maximal block.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CDAggreg

open HACoeff
open FMEnd
open RGClosa
open CSAdmiss

/-- One pair of positive source-label equality-class profiles. -/
structure DCProf where
  leftDegrees :
    List ℕ
  rightDegrees :
    List ℕ
  leftDegrees_pos :
    ∀ degree ∈ leftDegrees, 0 < degree
  rightDegrees_pos :
    ∀ degree ∈ rightDegrees, 0 < degree

namespace DCProf

/-- Total left Hall degree recorded by one equality-class profile. -/
def leftDegree
    (profile : DCProf) :
    ℕ :=
  profile.leftDegrees.sum

/-- Total right Hall degree recorded by one equality-class profile. -/
def rightDegree
    (profile : DCProf) :
    ℕ :=
  profile.rightDegrees.sum

/-- Number of assignments realizing one diagonal equality-class profile. -/
def coefficient
    (profile : DCProf)
    (M N : ℕ) :
    ℤ :=
  diagonalLeftProduct M profile.leftDegrees *
    diagonalRightProduct N profile.rightDegrees

/-- Every diagonal equality-class profile has homogeneous admissible count. -/
lemma coefficient_mem_submodule
    (profile : DCProf)
    (M N : ℕ) :
    profile.coefficient M N ∈
      submodule M N profile.leftDegree profile.rightDegree := by
  exact diagonal_products_submodule
    M N profile.leftDegrees profile.rightDegrees
      profile.leftDegrees_pos profile.rightDegrees_pos

end DCProf

/-- One inclusion-exclusion-weighted diagonal equality-class profile. -/
structure WDProf where
  multiplicity :
    ℤ
  profile :
    DCProf

namespace WDProf

/-- Signed contribution of one weighted equality-class profile. -/
def coefficient
    (weighted : WDProf)
    (M N : ℕ) :
    ℤ :=
  weighted.multiplicity * weighted.profile.coefficient M N

/-- Integer weighting preserves homogeneous admissibility. -/
lemma coefficient_mem_submodule
    (weighted : WDProf)
    (M N : ℕ) :
    weighted.coefficient M N ∈
      submodule M N weighted.profile.leftDegree
        weighted.profile.rightDegree := by
  simpa [coefficient, smul_eq_mul] using
    (submodule M N weighted.profile.leftDegree weighted.profile.rightDegree)
      |>.smul_mem weighted.multiplicity
        (weighted.profile.coefficient_mem_submodule M N)

end WDProf

/-- Finite signed sum of homogeneous diagonal equality-class contributions. -/
def weightedDiagonalSum
    (M N : ℕ)
    (profiles : List WDProf) :
    ℤ :=
  (profiles.map fun profile => profile.coefficient M N).sum

/-- A finite signed sum with one common bidegree remains admissible. -/
lemma weighted_diagonal_submodule
    (M N leftDegree rightDegree : ℕ) :
    ∀ profiles : List WDProf,
      (∀ profile ∈ profiles, profile.profile.leftDegree = leftDegree) →
        (∀ profile ∈ profiles, profile.profile.rightDegree = rightDegree) →
          weightedDiagonalSum M N profiles ∈
            submodule M N leftDegree rightDegree
  | [], _, _ => by
      simp [weightedDiagonalSum]
  | profile :: profiles, hleft, hright => by
      have hhead :
          profile.coefficient M N ∈
            submodule M N leftDegree rightDegree := by
        simpa [hleft profile (by simp), hright profile (by simp)] using
          profile.coefficient_mem_submodule M N
      have htail :
          weightedDiagonalSum M N profiles ∈
            submodule M N leftDegree rightDegree :=
        weighted_diagonal_submodule
          M N leftDegree rightDegree profiles
            (fun next hnext => hleft next (by simp [hnext]))
            (fun next hnext => hright next (by simp [hnext]))
      simpa [weightedDiagonalSum] using
        (submodule M N leftDegree rightDegree).add_mem hhead htail

/--
A finite equality-class certificate for one same-shape operational block.
Its signed profile sum is exactly the concrete block length.
-/
structure SDCert
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (word : CWord HPAtom) where
  profiles :
    List WDProf
  profiles_leftDegree :
    ∀ profile ∈ profiles,
      profile.profile.leftDegree = word.pairLeftDegree
  profiles_rightDegree :
    ∀ profile ∈ profiles,
      profile.profile.rightDegree = word.pairRightDegree
  length_eq :
    (block.length : ℤ) =
      weightedDiagonalSum M N profiles

namespace SDCert

/-- A diagonal certificate proves admissibility of its concrete block length. -/
lemma length_mem_submodule
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SDCert block word) :
    (block.length : ℤ) ∈
      submodule M N word.pairLeftDegree word.pairRightDegree := by
  rw [certificate.length_eq]
  exact weighted_diagonal_submodule
    M N word.pairLeftDegree word.pairRightDegree
      certificate.profiles certificate.profiles_leftDegree
        certificate.profiles_rightDegree

/-- Concatenate two certified chunks carrying the same erased Hall shape. -/
def append
    {M N K : ℕ}
    {left right : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (leftCertificate : SDCert left word)
    (rightCertificate : SDCert right word) :
    SDCert (left ++ right) word where
  profiles := leftCertificate.profiles ++ rightCertificate.profiles
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact leftCertificate.profiles_leftDegree profile hprofile
    · exact rightCertificate.profiles_leftDegree profile hprofile
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact leftCertificate.profiles_rightDegree profile hprofile
    · exact rightCertificate.profiles_rightDegree profile hprofile
  length_eq := by
    rw [List.length_append, Int.natCast_add,
      leftCertificate.length_eq, rightCertificate.length_eq]
    simp [weightedDiagonalSum, List.sum_append]

/-- Reordering concrete terms preserves a diagonal length certificate. -/
def permTerms
    {M N K : ℕ}
    {terms terms' : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SDCert terms word)
    (hterms : List.Perm terms terms') :
    SDCert terms' word where
  profiles := certificate.profiles
  profiles_leftDegree := certificate.profiles_leftDegree
  profiles_rightDegree := certificate.profiles_rightDegree
  length_eq := by
    rw [← hterms.length_eq]
    exact certificate.length_eq

end SDCert

/--
Remaining finite support-pattern theorem: every maximal compatible shape block
admits a homogeneous signed diagonal equality-class certificate.
-/
structure OCDiagon : Prop where
  certificate :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks endpoint.collected.factors →
        ∀ word : CWord HPAtom,
          (∀ term ∈ block, term.erasedShape = word) →
            Nonempty (SDCert block word)

namespace OCDiagon

/-- Diagonal support-pattern certificates resolve block-length admissibility. -/
def shapeAdmissibilityKernel
    (kernel : OCDiagon) :
    OCAdmiss where
  coefficient_admissible endpoint block hblock word hterms :=
    (Classical.choice
      (kernel.certificate endpoint block hblock word hterms)).length_mem_submodule

end OCDiagon

/--
Compatible routing plus diagonal support-pattern certificates resolve the bare
Hall-Petresco expansion boundary.
-/
structure ODColl : Prop where
  compatibleClosure :
    OCReuse
  shapeBlockDiagonal :
    OCDiagon

namespace ODColl

/-- Forget diagonal witnesses after compiling them to admissible block lengths. -/
def admissibleCollectionKernel
    (kernel : ODColl) :
    OCAdmissa where
  compatibleClosure := kernel.compatibleClosure
  shapeBlockAdmissibility :=
    kernel.shapeBlockDiagonal.shapeAdmissibilityKernel

/-- Diagonal support-pattern certificates construct a bare expansion. -/
noncomputable def freeExpansion
    (kernel : ODColl)
    (M N : ℕ) :
    FExp M N :=
  kernel.admissibleCollectionKernel.freeExpansion M N

end ODColl

end CDAggreg
end TCTex
end Towers

/-!
# Local aggregation of compatible correction grids

The support-compatible grid opened by one More3 obstruction is filtered at
the concrete-history level.  Although that filtering changes multiplicities,
it does not change the erased Hall shape or weighted Hall degree of a
correction once the two parent batches are shape-homogeneous.

This file proves those local structural facts.  They are the input needed to
count one compatible correction chunk by finite support-pattern certificates.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CCAggreg

open HACoeff
open BRSpec
open CCGrida
open OCPartit

/-- Erasing family provenance turns one concrete correction into a shape commutator. -/
lemma DFTerm.erasedShape_corr
    {M N K : ℕ}
    (left right : DFTerm M N K) :
    (left.correction right).erasedShape =
      CWord.commutator left.erasedShape right.erasedShape := by
  exact DTerm.erasedShape_corr left.decorated right.decorated

/-- Weighted Hall degree is additive under one concrete correction. -/
lemma decorated_family_correction
    {M N K leftWeight rightWeight : ℕ}
    (left right : DFTerm M N K) :
    decoratedFamilyWeight leftWeight rightWeight (left.correction right) =
      decoratedFamilyWeight leftWeight rightWeight left +
        decoratedFamilyWeight leftWeight rightWeight right := by
  change
    weightedWordWeight leftWeight rightWeight
        (left.family.recipe.correction right.family.recipe) =
      weightedWordWeight leftWeight rightWeight left.family.recipe +
        weightedWordWeight leftWeight rightWeight right.family.recipe
  exact weighted_weight_correction
    leftWeight rightWeight left.family.recipe right.family.recipe

/--
Every term of a support-compatible correction grid has the commutator of the
two parent batch shapes.
-/
lemma erased_compatible_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftShape rightShape : CWord HPAtom}
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape)
    {term : DFTerm M N K}
    (hterm : term ∈ compatibleCorrectionGrid leftTerms rightTerms) :
    term.erasedShape =
      CWord.commutator leftShape rightShape := by
  rcases compatible_grid.mp hterm with
    ⟨left, hleftMem, right, hrightMem, _hcompatible, rfl⟩
  rw [DFTerm.erasedShape_corr,
    hleft left hleftMem, hright right hrightMem]

/-- One compatible correction grid is a same-erased-shape chunk. -/
lemma same_compatible_grid
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (leftShape rightShape : CWord HPAtom)
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape) :
    SameErasedBlock
      (compatibleCorrectionGrid leftTerms rightTerms) := by
  exact
    ⟨CWord.commutator leftShape rightShape,
      fun _term hterm =>
        erased_compatible_grid
          hleft hright hterm⟩

/--
Every term of a compatible correction grid has the sum of the fixed parent
batch weights.
-/
lemma decorated_compatible_grid
    {M N K leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftDegree rightDegree : ℕ}
    (hleft :
      ∀ left ∈ leftTerms,
        decoratedFamilyWeight leftWeight rightWeight left = leftDegree)
    (hright :
      ∀ right ∈ rightTerms,
        decoratedFamilyWeight leftWeight rightWeight right = rightDegree)
    {term : DFTerm M N K}
    (hterm : term ∈ compatibleCorrectionGrid leftTerms rightTerms) :
    decoratedFamilyWeight leftWeight rightWeight term =
      leftDegree + rightDegree := by
  rcases compatible_grid.mp hterm with
    ⟨left, hleftMem, right, hrightMem, _hcompatible, rfl⟩
  rw [decorated_family_correction,
    hleft left hleftMem, hright right hrightMem]

end CCAggreg
end TCTex
end Towers

/-!
# Signed-block aggregation for compatible shape blocks

The admissible coefficient submodule is generated by products of generalized
binomial coefficients attached to signed source blocks.  Compatible
support-pattern counts naturally produce these generators: independent label
classes give positive blocks, while inclusion-exclusion can introduce
negative blocks and integral multiplicities.

This file records explicit finite signed-block certificates for concrete
same-shape operational blocks and compiles them to the weaker admissibility
boundary used by the bare Hall-Petresco expansion.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSAggreg

open HACoeff
open FMEnd
open RGClosa
open CSAdmiss

/-- One explicit generator profile for the admissible coefficient submodule. -/
structure SBProf where
  leftBlocks :
    List Block
  rightBlocks :
    List Block

namespace SBProf

/-- Total left Hall degree recorded by one signed-block profile. -/
def leftDegree
    (profile : SBProf) :
    ℕ :=
  degreeSum profile.leftBlocks

/-- Total right Hall degree recorded by one signed-block profile. -/
def rightDegree
    (profile : SBProf) :
    ℕ :=
  degreeSum profile.rightBlocks

/-- Generalized-binomial coefficient represented by one signed-block profile. -/
def coefficient
    (profile : SBProf)
    (M N : ℕ) :
    ℤ :=
  blockProduct M profile.leftBlocks * blockProduct N profile.rightBlocks

/-- Every explicit signed-block profile is an admissible homogeneous generator. -/
lemma coefficient_mem_submodule
    (profile : SBProf)
    (M N : ℕ) :
    profile.coefficient M N ∈
      submodule M N profile.leftDegree profile.rightDegree := by
  apply Submodule.subset_span
  exact ⟨profile.leftBlocks, profile.rightBlocks, rfl, rfl, rfl⟩

end SBProf

/-- One integral multiple of an explicit signed-block generator profile. -/
structure WBProf where
  multiplicity :
    ℤ
  profile :
    SBProf

namespace WBProf

/-- Signed contribution of one weighted signed-block profile. -/
def coefficient
    (weighted : WBProf)
    (M N : ℕ) :
    ℤ :=
  weighted.multiplicity * weighted.profile.coefficient M N

/-- Integral weighting preserves homogeneous admissibility. -/
lemma coefficient_mem_submodule
    (weighted : WBProf)
    (M N : ℕ) :
    weighted.coefficient M N ∈
      submodule M N weighted.profile.leftDegree
        weighted.profile.rightDegree := by
  simpa [coefficient, smul_eq_mul] using
    (submodule M N weighted.profile.leftDegree weighted.profile.rightDegree)
      |>.smul_mem weighted.multiplicity
        (weighted.profile.coefficient_mem_submodule M N)

end WBProf

/-- Finite integral sum of explicit signed-block generator contributions. -/
def weightedCoefficientSum
    (M N : ℕ)
    (profiles : List WBProf) :
    ℤ :=
  (profiles.map fun profile => profile.coefficient M N).sum

/-- A finite signed-block sum with one common bidegree remains admissible. -/
lemma weighted_coefficient_submodule
    (M N leftDegree rightDegree : ℕ) :
    ∀ profiles : List WBProf,
      (∀ profile ∈ profiles, profile.profile.leftDegree = leftDegree) →
        (∀ profile ∈ profiles, profile.profile.rightDegree = rightDegree) →
          weightedCoefficientSum M N profiles ∈
            submodule M N leftDegree rightDegree
  | [], _, _ => by
      simp [weightedCoefficientSum]
  | profile :: profiles, hleft, hright => by
      have hhead :
          profile.coefficient M N ∈
            submodule M N leftDegree rightDegree := by
        simpa [hleft profile (by simp), hright profile (by simp)] using
          profile.coefficient_mem_submodule M N
      have htail :
          weightedCoefficientSum M N profiles ∈
            submodule M N leftDegree rightDegree :=
        weighted_coefficient_submodule
          M N leftDegree rightDegree profiles
            (fun next hnext => hleft next (by simp [hnext]))
            (fun next hnext => hright next (by simp [hnext]))
      simpa [weightedCoefficientSum] using
        (submodule M N leftDegree rightDegree).add_mem hhead htail

/--
An explicit generalized-binomial certificate for one same-shape operational
block.  Its finite signed-block sum is exactly the concrete block length.
-/
structure SBCert
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (word : CWord HPAtom) where
  profiles :
    List WBProf
  profiles_leftDegree :
    ∀ profile ∈ profiles,
      profile.profile.leftDegree = word.pairLeftDegree
  profiles_rightDegree :
    ∀ profile ∈ profiles,
      profile.profile.rightDegree = word.pairRightDegree
  length_eq :
    (block.length : ℤ) =
      weightedCoefficientSum M N profiles

namespace SBCert

/-- The empty concrete chunk has the empty signed-block certificate. -/
def nil
    {M N K : ℕ}
    (word : CWord HPAtom) :
    SBCert
      ([] : List (DFTerm M N K)) word where
  profiles := []
  profiles_leftDegree := by simp
  profiles_rightDegree := by simp
  length_eq := by simp [weightedCoefficientSum]

/-- Package one explicit weighted generator whose value is the chunk length. -/
def ofProfile
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (profile : WBProf)
    (hleft :
      profile.profile.leftDegree = word.pairLeftDegree)
    (hright :
      profile.profile.rightDegree = word.pairRightDegree)
    (hlength :
      (block.length : ℤ) = profile.coefficient M N) :
    SBCert block word where
  profiles := [profile]
  profiles_leftDegree := by
    intro next hnext
    have hnext_eq : next = profile := by
      simpa using hnext
    subst next
    exact hleft
  profiles_rightDegree := by
    intro next hnext
    have hnext_eq : next = profile := by
      simpa using hnext
    subst next
    exact hright
  length_eq := by
    simpa [weightedCoefficientSum] using hlength

/-- A signed-block certificate proves admissibility of its concrete length. -/
lemma length_mem_submodule
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SBCert block word) :
    (block.length : ℤ) ∈
      submodule M N word.pairLeftDegree word.pairRightDegree := by
  rw [certificate.length_eq]
  exact weighted_coefficient_submodule
    M N word.pairLeftDegree word.pairRightDegree
      certificate.profiles certificate.profiles_leftDegree
        certificate.profiles_rightDegree

/-- Concatenate two certified chunks carrying the same erased Hall shape. -/
def append
    {M N K : ℕ}
    {left right : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (leftCertificate : SBCert left word)
    (rightCertificate : SBCert right word) :
    SBCert (left ++ right) word where
  profiles := leftCertificate.profiles ++ rightCertificate.profiles
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact leftCertificate.profiles_leftDegree profile hprofile
    · exact rightCertificate.profiles_leftDegree profile hprofile
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact leftCertificate.profiles_rightDegree profile hprofile
    · exact rightCertificate.profiles_rightDegree profile hprofile
  length_eq := by
    rw [List.length_append, Int.natCast_add,
      leftCertificate.length_eq, rightCertificate.length_eq]
    simp [weightedCoefficientSum, List.sum_append]

/-- Reordering concrete terms preserves a signed-block length certificate. -/
def permTerms
    {M N K : ℕ}
    {terms terms' : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SBCert terms word)
    (hterms : List.Perm terms terms') :
    SBCert terms' word where
  profiles := certificate.profiles
  profiles_leftDegree := certificate.profiles_leftDegree
  profiles_rightDegree := certificate.profiles_rightDegree
  length_eq := by
    rw [← hterms.length_eq]
    exact certificate.length_eq

end SBCert

/--
Remaining finite support-pattern theorem: every maximal compatible shape block
admits an explicit homogeneous signed-block certificate.
-/
structure OCShape : Prop where
  certificate :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks endpoint.collected.factors →
        ∀ word : CWord HPAtom,
          (∀ term ∈ block, term.erasedShape = word) →
            Nonempty (SBCert block word)

namespace OCShape

/-- Explicit signed-block certificates resolve block-length admissibility. -/
def shapeAdmissibilityKernel
    (kernel : OCShape) :
    OCAdmiss where
  coefficient_admissible endpoint block hblock word hterms :=
    (Classical.choice
      (kernel.certificate endpoint block hblock word hterms)).length_mem_submodule

end OCShape

/--
Compatible routing plus explicit signed-block certificates resolve the bare
Hall-Petresco expansion boundary.
-/
structure OCColl : Prop where
  compatibleClosure :
    OCReuse
  shapeBlockSigned :
    OCShape

namespace OCColl

/-- Forget explicit witnesses after compiling them to admissible lengths. -/
def admissibleCollectionKernel
    (kernel : OCColl) :
    OCAdmissa where
  compatibleClosure := kernel.compatibleClosure
  shapeBlockAdmissibility :=
    kernel.shapeBlockSigned.shapeAdmissibilityKernel

/-- Explicit signed-block support-pattern certificates construct an expansion. -/
noncomputable def freeExpansion
    (kernel : OCColl)
    (M N : ℕ) :
    FExp M N :=
  kernel.admissibleCollectionKernel.freeExpansion M N

end OCColl

end CSAggreg
end TCTex
end Towers

/-!
# Elementary signed-block certificates for operational chunks

Complete `BFam` packets are the base cases of the compatible
support-pattern aggregation theorem.  Their lengths are positive signed-block
generators.  Lists of such families give finite signed-block sums, and exact
realization inventories therefore produce explicit certificates.

The final section records the compatible-grid case in which every parent pair
is support-compatible.  The genuinely filtered case still needs a
support-pattern decomposition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSChunks

open HACoeff
open ISEnd
open CCGrida
open CSNorm
open CSAggreg
open HSInvent
open HSPacket

/-- A positive signed-block profile attached to one ordinary block recipe. -/
def positiveBlockProfile
    (recipe : BRecipe) :
    SBProf where
  leftBlocks := positiveBlocks recipe.leftBlocks
  rightBlocks := positiveBlocks recipe.rightBlocks

@[simp]
lemma positive_block_degree
    (recipe : BRecipe) :
    (positiveBlockProfile recipe).leftDegree =
      recipe.erasedShape.pairLeftDegree := by
  rw [positiveBlockProfile, SBProf.leftDegree,
    sum_positive_blocks, recipe.erased_left_degree]
  rfl

@[simp]
lemma positive_profile_degree
    (recipe : BRecipe) :
    (positiveBlockProfile recipe).rightDegree =
      recipe.erasedShape.pairRightDegree := by
  rw [positiveBlockProfile, SBProf.rightDegree,
    sum_positive_blocks, recipe.erased_shape_degree]
  rfl

@[simp]
lemma positive_profile_coefficient
    (recipe : BRecipe)
    (M N : ℕ) :
    (positiveBlockProfile recipe).coefficient M N =
      (recipe.factor M N).coefficient := by
  simp [positiveBlockProfile, SBProf.coefficient,
    block_product_blocks, BRecipe.factor]

/-- One counted family contributes one positive signed-block generator. -/
def weightedBlockProfile
    {M N : ℕ}
    (family : BFam M N) :
  WBProf where
  multiplicity := 1
  profile := positiveBlockProfile family.recipe

@[simp]
lemma weighted_block_degree
    {M N : ℕ}
    (family : BFam M N) :
    (weightedBlockProfile family).profile.leftDegree =
      family.recipe.erasedShape.pairLeftDegree := by
  simp [weightedBlockProfile]

@[simp]
lemma weighted_profile_degree
    {M N : ℕ}
    (family : BFam M N) :
    (weightedBlockProfile family).profile.rightDegree =
      family.recipe.erasedShape.pairRightDegree := by
  simp [weightedBlockProfile]

@[simp]
lemma weighted_profile_coefficient
    {M N : ℕ}
    (family : BFam M N) :
    (weightedBlockProfile family).coefficient M N =
      (family.realizations.length : ℤ) := by
  rw [weightedBlockProfile, WBProf.coefficient]
  simp only [one_mul, positive_profile_coefficient]
  rw [BRecipe.factor_coefficient_embeddings, family.length_eq]
  norm_num

/-- Explicit positive signed-block profiles contributed by a family list. -/
def weightedBlockProfiles
    {M N : ℕ}
    (families : List (BFam M N)) :
    List WBProf :=
  families.map weightedBlockProfile

/-- The profile sum of a family list is its total number of realization slots. -/
lemma profiles_realization_length
    {M N : ℕ} :
    ∀ families : List (BFam M N),
      weightedCoefficientSum M N
          (weightedBlockProfiles families) =
        ((BFam.realizationList families).length : ℤ)
  | [] => by
      simp [weightedBlockProfiles, weightedCoefficientSum,
        BFam.realizationList]
  | family :: families => by
      rw [weightedBlockProfiles, List.map_cons,
        weightedCoefficientSum, List.map_cons, List.sum_cons,
        weighted_profile_coefficient family,
        BFam.realizationList_cons, List.length_append, Int.natCast_add]
      congr 1
      exact
        profiles_realization_length
          families

/--
A family list with one erased shape gives a signed-block certificate for any
concrete list with the same total realization-slot count.
-/
def signedCertificateLength
    {M N K : ℕ}
    (families : List (BFam M N))
    (terms : List (DFTerm M N K))
    (word : CWord HPAtom)
    (hfamilies :
      ∀ family ∈ families, family.recipe.erasedShape = word)
    (hlength :
      (BFam.realizationList families).length = terms.length) :
    SBCert terms word where
  profiles := weightedBlockProfiles families
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_map.mp hprofile with ⟨family, hfamily, rfl⟩
    rw [weighted_block_degree family, hfamilies family hfamily]
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_map.mp hprofile with ⟨family, hfamily, rfl⟩
    rw [weighted_profile_degree family, hfamilies family hfamily]
  length_eq := by
    rw [← hlength]
    exact
      (profiles_realization_length
        families).symm

/-- Every same-shape exact family inventory has an explicit signed-block certificate. -/
def realizationInventoryCertificate
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (hinventory : RIFor families terms)
    (hfamilies :
      ∀ family ∈ families, family.recipe.erasedShape = word) :
    SBCert terms word :=
  signedCertificateLength families terms word hfamilies
    (RIFor.realization_list_lengtheq hinventory)

/-- Every complete singleton-family packet has an explicit signed-block certificate. -/
def realizationBlockCertificate
    {M N K : ℕ}
    {family : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor family terms) :
    SBCert terms family.recipe.erasedShape :=
  realizationInventoryCertificate
    (RIFor.ofPacket hpacket)
    (by simp)

/-- The full Cartesian correction grid has the correction recipe certificate. -/
noncomputable def correctionGridCertificate
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RPFor leftFamily leftTerms)
    (hright : RPFor rightFamily rightTerms) :
    SBCert
      (DFTerm.correctionGrid leftTerms rightTerms)
      (leftFamily.correction rightFamily).recipe.erasedShape :=
  realizationBlockCertificate
    (RPFor.correctionGrid hleft hright)

/--
If every parent pair is operationally compatible, the filtered compatible
grid is the full Cartesian correction grid.
-/
lemma compatible_grid_forall
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (hcompatible :
      ∀ left ∈ leftTerms, ∀ right ∈ rightTerms,
        correctionPairCompatible left right) :
    compatibleCorrectionGrid leftTerms rightTerms =
      DFTerm.correctionGrid leftTerms rightTerms := by
  simp only [compatibleCorrectionGrid, DFTerm.correctionGrid]
  apply List.flatMap_congr
  intro left hleft
  rw [List.filter_eq_self.2]
  intro right hright
  simpa only [decide_eq_true_eq] using hcompatible left hleft right hright

/--
An all-compatible parent pair of complete packets gives a compatible-grid
signed-block certificate.  Properly filtered grids require the remaining
support-pattern decomposition theorem.
-/
noncomputable def compatibleGridCertificate
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RPFor leftFamily leftTerms)
    (hright : RPFor rightFamily rightTerms)
    (hcompatible :
      ∀ left ∈ leftTerms, ∀ right ∈ rightTerms,
        correctionPairCompatible left right) :
    SBCert
      (compatibleCorrectionGrid leftTerms rightTerms)
      (leftFamily.correction rightFamily).recipe.erasedShape := by
  rw [compatible_grid_forall
    leftTerms rightTerms hcompatible]
  exact correctionGridCertificate hleft hright

/--
The older strong inventory normalization boundary factors through explicit
positive signed-block certificates.
-/
def shapeBlockNormalization
    (kernel : OCNorm) :
    OCShape where
  certificate endpoint block hblock word hterms := by
    rcases kernel.inventory endpoint block hblock with
      ⟨families, hinventory, hnonempty⟩
    exact ⟨realizationInventoryCertificate hinventory
      (fun family hfamily =>
        RIFor.recipe_shape_eqmem
          hinventory hnonempty hterms hfamily)⟩

end CSChunks
end TCTex
end Towers

/-!
# Signed-block subtraction for filtered compatible grids

An operationally compatible correction grid is obtained from the full
Cartesian correction grid by discarding parent pairs with overlapping raw
support.  Signed-block certificates are closed under subtracting a certified
rejected sublist.  This is the finite inclusion-exclusion step needed before
recursing through overlap strata.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSFilter

open HACoeff
open CCAggreg
open CCGrida
open CSAggreg
open CSChunks
open OCPartit
open HSPacket

/-- Negate the integral multiplicity of one explicit signed-block profile. -/
def negateWeightedProfile
    (profile : WBProf) :
    WBProf where
  multiplicity := -profile.multiplicity
  profile := profile.profile

@[simp]
lemma coefficient_negate_profile
    (profile : WBProf)
    (M N : ℕ) :
    (negateWeightedProfile profile).coefficient M N =
      -profile.coefficient M N := by
  simp [negateWeightedProfile,
    WBProf.coefficient]

/-- Negate every multiplicity in a finite signed-block profile list. -/
def negateWeightedProfiles
    (profiles : List WBProf) :
    List WBProf :=
  profiles.map negateWeightedProfile

@[simp]
lemma weighted_coefficient_append
    (M N : ℕ)
    (left right : List WBProf) :
    weightedCoefficientSum M N (left ++ right) =
      weightedCoefficientSum M N left +
        weightedCoefficientSum M N right := by
  simp [weightedCoefficientSum, List.sum_append]

@[simp]
lemma weighted_coefficient_negate
    (M N : ℕ) :
    ∀ profiles : List WBProf,
      weightedCoefficientSum M N
          (negateWeightedProfiles profiles) =
        -weightedCoefficientSum M N profiles
  | [] => by
      simp [negateWeightedProfiles,
        weightedCoefficientSum]
  | profile :: profiles => by
      change
        (negateWeightedProfile profile).coefficient M N +
            weightedCoefficientSum M N
              (negateWeightedProfiles profiles) =
          -(profile.coefficient M N +
            weightedCoefficientSum M N profiles)
      rw [coefficient_negate_profile,
        weighted_coefficient_negate M N profiles]
      ring

/--
Subtract a certified rejected sublist from a certified whole list.  The
retained list inherits the same homogeneous signed-block certificate.
-/
def shapeCertificatePartition
    {M N K : ℕ}
    {whole retained rejected : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (wholeCertificate : SBCert whole word)
    (rejectedCertificate : SBCert rejected word)
    (hpartition : List.Perm whole (retained ++ rejected)) :
    SBCert retained word where
  profiles :=
    wholeCertificate.profiles ++
      negateWeightedProfiles rejectedCertificate.profiles
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact wholeCertificate.profiles_leftDegree profile hprofile
    · rcases List.mem_map.mp hprofile with ⟨original, horiginal, rfl⟩
      exact rejectedCertificate.profiles_leftDegree original horiginal
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact wholeCertificate.profiles_rightDegree profile hprofile
    · rcases List.mem_map.mp hprofile with ⟨original, horiginal, rfl⟩
      exact rejectedCertificate.profiles_rightDegree original horiginal
  length_eq := by
    rw [weighted_coefficient_append,
      weighted_coefficient_negate,
      ← wholeCertificate.length_eq, ← rejectedCertificate.length_eq]
    have hlength :=
      congrArg (fun length : ℕ => (length : ℤ)) hpartition.length_eq
    simp only [List.length_append, Int.natCast_add] at hlength
    omega

/--
The discarded complement of the support-compatible correction grid.
-/
noncomputable def incompatibleCorrectionGrid
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    List (DFTerm M N K) :=
  leftTerms.flatMap fun left =>
    (rightTerms.filter fun right =>
      !decide (correctionPairCompatible left right)).map fun right =>
        left.correction right

@[simp]
lemma incompatible_correction_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {term : DFTerm M N K} :
    term ∈ incompatibleCorrectionGrid leftTerms rightTerms ↔
      ∃ left ∈ leftTerms, ∃ right ∈ rightTerms,
        ¬ correctionPairCompatible left right ∧
          term = left.correction right := by
  constructor
  · intro hterm
    rcases List.mem_flatMap.mp hterm with ⟨left, hleft, hterm⟩
    rcases List.mem_map.mp hterm with ⟨right, hright, rfl⟩
    refine ⟨left, hleft, right, (List.mem_filter.mp hright).1, ?_, rfl⟩
    simpa only [Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] using
      (List.mem_filter.mp hright).2
  · rintro ⟨left, hleft, right, hright, hincompatible, rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨left, hleft, List.mem_map.mpr ⟨right, ?_, rfl⟩⟩
    exact List.mem_filter.mpr
      ⟨hright, by
        simpa only [Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] using
          hincompatible⟩

/--
The full Cartesian correction grid is a permutation of its compatible and
overlapping-support parts.
-/
lemma grid_perm_incompatible
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    List.Perm
      (DFTerm.correctionGrid leftTerms rightTerms)
      (compatibleCorrectionGrid leftTerms rightTerms ++
        incompatibleCorrectionGrid leftTerms rightTerms) := by
  apply
    (List.Perm.flatMap_left leftTerms fun left _hleft => ?_).trans
  · exact
      (List.flatMap_append_perm leftTerms
        (fun left =>
          (rightTerms.filter fun right =>
            decide (correctionPairCompatible left right)).map fun right =>
              left.correction right)
        (fun left =>
          (rightTerms.filter fun right =>
            !decide (correctionPairCompatible left right)).map fun right =>
              left.correction right)).symm
  · simpa [DFTerm.correctionGrid, compatibleCorrectionGrid,
      incompatibleCorrectionGrid] using
      (List.perm_filterappend_filternot
        (fun right => decide (correctionPairCompatible left right))
        rightTerms).map fun right => left.correction right

/-- Every rejected correction has the same commutator shape as its parents. -/
lemma erased_incompatible_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftShape rightShape : CWord HPAtom}
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape)
    {term : DFTerm M N K}
    (hterm : term ∈ incompatibleCorrectionGrid leftTerms rightTerms) :
    term.erasedShape =
      CWord.commutator leftShape rightShape := by
  rcases incompatible_correction_grid.mp hterm with
    ⟨left, hleftMem, right, hrightMem, _hincompatible, rfl⟩
  rw [DFTerm.erasedShape_corr,
    hleft left hleftMem, hright right hrightMem]

/--
Once the overlapping-support complement is certified, subtraction from the
full Cartesian packet certifies the operationally compatible grid.
-/
noncomputable def compatibleCertificateIncompatible
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (fullCertificate :
      SBCert
        (DFTerm.correctionGrid leftTerms rightTerms) word)
    (incompatibleCertificate :
      SBCert
        (incompatibleCorrectionGrid leftTerms rightTerms) word) :
    SBCert
      (compatibleCorrectionGrid leftTerms rightTerms) word :=
  shapeCertificatePartition
    fullCertificate incompatibleCertificate
      (grid_perm_incompatible leftTerms rightTerms)

/--
For complete singleton-family packets, the only remaining certificate is the
overlapping-support complement.
-/
noncomputable def realizationGridCertificate
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RPFor leftFamily leftTerms)
    (hright : RPFor rightFamily rightTerms)
    (incompatibleCertificate :
      SBCert
        (incompatibleCorrectionGrid leftTerms rightTerms)
        (leftFamily.correction rightFamily).recipe.erasedShape) :
    SBCert
      (compatibleCorrectionGrid leftTerms rightTerms)
      (leftFamily.correction rightFamily).recipe.erasedShape :=
  compatibleCertificateIncompatible
    (correctionGridCertificate hleft hright)
      incompatibleCertificate

end CSFilter
end TCTex
end Towers

/-!
# Overlap strata for filtered compatible grids

Compatibility combines the deterministic shape order with disjoint raw
support.  A batch is opened by one genuine obstruction.  When both represented
parent packets are shape-homogeneous, that witness forces the shape-order
condition for every parent pair.  The rejected complement is therefore
exactly the grid of overlapping-support pairs.

This file isolates the remaining recursive inclusion-exclusion problem as an
overlap-grid certificate.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSOverla

open HACoeff
open CCGrida
open CSAggreg
open CSFilter
open HSPacket

/-- Equal erased shapes give equal total Hall degrees. -/
lemma erased_degree_shape
    {M N K : ℕ}
    {left right : DTerm M N K}
    (hshape : left.erasedShape = right.erasedShape) :
    left.erasedDegree = right.erasedDegree := by
  simp [DTerm.erasedDegree, hshape]

/-- Shape precedence depends only on the erased Hall shapes. -/
lemma shape_before_erased
    {M N K : ℕ}
    {left left' right right' : DTerm M N K}
    (hleft : left.erasedShape = left'.erasedShape)
    (hright : right.erasedShape = right'.erasedShape) :
    left.shapeBefore right ↔ left'.shapeBefore right' := by
  have hleftDegree := erased_degree_shape hleft
  have hrightDegree := erased_degree_shape hright
  have hleftCode :=
    DTerm.erased_shape_code hleft
  have hrightCode :=
    DTerm.erased_shape_code hright
  simp only [DTerm.shapeBefore, DTerm.higherDegreeBefore]
  rw [hleftDegree, hrightDegree, hleftCode, hrightCode]

/-- Once shape precedence is known, compatibility is exactly support disjointness. -/
lemma compatible_disjoint_before
    {M N K : ℕ}
    {left right : DFTerm M N K}
    (hbefore : right.decorated.shapeBefore left.decorated) :
    correctionPairCompatible left right ↔
      Disjoint right.decorated.support left.decorated.support := by
  simp [correctionPairCompatible, DTerm.independentBefore, hbefore]

/--
One compatible witness propagates shape precedence across homogeneous parent
packets.
-/
lemma before_homogeneous_witness
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftShape rightShape : CWord HPAtom}
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness)
    {left right : DFTerm M N K}
    (hleftMem : left ∈ leftTerms)
    (hrightMem : right ∈ rightTerms) :
    right.decorated.shapeBefore left.decorated := by
  apply
    (shape_before_erased
      (show right.decorated.erasedShape =
          rightWitness.decorated.erasedShape by
        change right.erasedShape = rightWitness.erasedShape
        rw [hright right hrightMem, hright rightWitness hrightWitness])
      (show left.decorated.erasedShape =
          leftWitness.decorated.erasedShape by
        change left.erasedShape = leftWitness.erasedShape
        rw [hleft left hleftMem, hleft leftWitness hleftWitness])).mpr
  exact hcompatible.1

/--
Across homogeneous packets with one genuine obstruction witness,
compatibility is exactly support disjointness.
-/
lemma disjoint_homogeneous_witness
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftShape rightShape : CWord HPAtom}
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness)
    {left right : DFTerm M N K}
    (hleftMem : left ∈ leftTerms)
    (hrightMem : right ∈ rightTerms) :
    correctionPairCompatible left right ↔
      Disjoint right.decorated.support left.decorated.support :=
  compatible_disjoint_before
    (before_homogeneous_witness
      hleft hright hleftWitness hrightWitness hcompatible hleftMem hrightMem)

/-- The grid of parent pairs rejected specifically because their raw supports overlap. -/
noncomputable def overlappingCorrectionGrid
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    List (DFTerm M N K) :=
  leftTerms.flatMap fun left =>
    (rightTerms.filter fun right =>
      !decide (Disjoint right.decorated.support left.decorated.support)).map
        fun right => left.correction right

/--
For a genuine homogeneous compatible batch, the generic rejected complement
is exactly the overlapping-support grid.
-/
lemma incompatible_grid_overlapping
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftShape rightShape : CWord HPAtom}
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness) :
    incompatibleCorrectionGrid leftTerms rightTerms =
      overlappingCorrectionGrid leftTerms rightTerms := by
  simp only [incompatibleCorrectionGrid, overlappingCorrectionGrid]
  apply List.flatMap_congr
  intro left hleftMem
  congr 1
  apply List.filter_congr
  intro right hrightMem
  apply congrArg Bool.not
  exact Bool.decide_congr
    (disjoint_homogeneous_witness
      hleft hright hleftWitness hrightWitness hcompatible hleftMem hrightMem)

/--
Certifying the overlap stratum is enough to certify one genuine homogeneous
compatible grid.
-/
noncomputable def compatibleCertificateOverlap
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftShape rightShape word : CWord HPAtom}
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness)
    (fullCertificate :
      SBCert
        (DFTerm.correctionGrid leftTerms rightTerms) word)
    (overlapCertificate :
      SBCert
        (overlappingCorrectionGrid leftTerms rightTerms) word) :
    SBCert
      (compatibleCorrectionGrid leftTerms rightTerms) word :=
  compatibleCertificateIncompatible
    fullCertificate <| by
      rw [incompatible_grid_overlapping
        hleft hright hleftWitness hrightWitness hcompatible]
      exact overlapCertificate

end CSOverla
end TCTex
end Towers

/-!
# Inclusion-exclusion for overlap strata

The overlapping correction grid is indexed by pairs of parent occurrences.
Such a pair is rejected exactly when the two raw-support finsets share at
least one slot.  This file decomposes rejected occurrence pairs as a finite
union of fixed-slot strata and applies cardinal inclusion-exclusion.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace OIExclus

open HACoeff
open CCGrida
open CSOverla
open HSPacket

/-- Filtering after a map counts the corresponding filtered source terms. -/
lemma filter_map_eq
    {α β : Type*}
    (terms : List α)
    (termMap : α → β)
    (predicate : β → Bool) :
    ((terms.map termMap).filter predicate).length =
      (terms.filter fun term => predicate (termMap term)).length := by
  induction terms with
  | nil =>
      rfl
  | cons term terms ih =>
      by_cases hterm : predicate (termMap term) = true
      · simp [hterm, ih]
      · simp [hterm, ih]

/--
Mapping an emitted payload over each retained Cartesian row does not affect
the number of retained occurrence pairs.
-/
lemma length_flat_filter
    {α β γ : Type*}
    (leftTerms : List α)
    (rightTerms : List β)
    (predicate : α → β → Bool)
    (emit : α → β → γ) :
    (leftTerms.flatMap fun left =>
      (rightTerms.filter fun right => predicate left right).map fun right =>
        emit left right).length =
      ((leftTerms.product rightTerms).filter fun pair =>
        predicate pair.1 pair.2).length := by
  induction leftTerms with
  | nil =>
      rfl
  | cons left leftTerms ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map]
      change
        (rightTerms.filter fun right => predicate left right).length +
            (leftTerms.flatMap fun left =>
              (rightTerms.filter fun right => predicate left right).map
                fun right => emit left right).length =
          (((rightTerms.map (Prod.mk left)) ++
            leftTerms.product rightTerms).filter fun pair =>
              predicate pair.1 pair.2).length
      rw [List.filter_append, List.length_append, ih, filter_map_eq]

/-- Mapping both Cartesian axes maps the Cartesian list occurrence by occurrence. -/
lemma map_map_eq
    {α β γ δ : Type*}
    (leftTerms : List α)
    (rightTerms : List β)
    (leftMap : α → γ)
    (rightMap : β → δ) :
    (leftTerms.map leftMap).product (rightTerms.map rightMap) =
      (leftTerms.product rightTerms).map fun pair =>
        (leftMap pair.1, rightMap pair.2) := by
  induction leftTerms with
  | nil =>
      rfl
  | cons left leftTerms ih =>
      change
        (rightTerms.map rightMap).map (Prod.mk (leftMap left)) ++
            (leftTerms.map leftMap).product (rightTerms.map rightMap) =
          (rightTerms.map (Prod.mk left) ++
            leftTerms.product rightTerms).map fun pair =>
              (leftMap pair.1, rightMap pair.2)
      rw [List.map_append, ih]
      congr 1
      simp [Function.comp_def]

/-- Filtered Cartesian occurrence counts are preserved by mapping both axes. -/
lemma length_filter_product
    {α β γ δ : Type*}
    (leftTerms : List α)
    (rightTerms : List β)
    (leftMap : α → γ)
    (rightMap : β → δ)
    (predicate : γ → δ → Bool) :
    (((leftTerms.map leftMap).product (rightTerms.map rightMap)).filter
      fun pair => predicate pair.1 pair.2).length =
      ((leftTerms.product rightTerms).filter fun pair =>
        predicate (leftMap pair.1) (rightMap pair.2)).length := by
  rw [map_map_eq]
  exact filter_map_eq
    (leftTerms.product rightTerms)
    (fun pair => (leftMap pair.1, rightMap pair.2))
    (fun pair => predicate pair.1 pair.2)

/-- Occurrence indices for a Cartesian pair of represented parent packets. -/
abbrev CorrectionPairIndex
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :=
  Fin leftTerms.length × Fin rightTerms.length

/-- Raw slots shared by one pair of represented parent occurrences. -/
def commonSupport
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (pair : CorrectionPairIndex leftTerms rightTerms) :
    Finset (Fin K) :=
  (rightTerms.get pair.2).decorated.support ∩
    (leftTerms.get pair.1).decorated.support

/-- Parent occurrence pairs rejected because their raw supports overlap. -/
def overlappingPairIndices
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    Finset (CorrectionPairIndex leftTerms rightTerms) :=
  Finset.univ.filter fun pair =>
    (commonSupport leftTerms rightTerms pair).Nonempty

/-- Parent occurrence pairs whose raw supports meet at a specified slot. -/
def overlapIndicesSlot
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slot : Fin K) :
    Finset (CorrectionPairIndex leftTerms rightTerms) :=
  Finset.univ.filter fun pair =>
    slot ∈ commonSupport leftTerms rightTerms pair

/--
Occurrence-pair traversal in the same left-major order as the concrete
overlap grid.
-/
def overlappingPairList
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    List (CorrectionPairIndex leftTerms rightTerms) :=
  ((List.finRange leftTerms.length).product
      (List.finRange rightTerms.length)).filter fun pair =>
    decide (commonSupport leftTerms rightTerms pair).Nonempty

@[simp]
lemma overlapping_pair_list
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {pair : CorrectionPairIndex leftTerms rightTerms} :
    pair ∈ overlappingPairList leftTerms rightTerms ↔
      pair ∈ overlappingPairIndices leftTerms rightTerms := by
  rcases pair with ⟨leftIndex, rightIndex⟩
  simp [overlappingPairList, overlappingPairIndices]

/-- Occurrence pairs remain distinct after overlap filtering. -/
lemma overlapping_pair_nodup
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    (overlappingPairList leftTerms rightTerms).Nodup := by
  apply List.Nodup.filter
  exact (List.nodup_finRange _).product (List.nodup_finRange _)

/-- The overlap-pair finset is the deduplication of its ordered traversal. -/
lemma finset_overlapping_pair
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    (overlappingPairList leftTerms rightTerms).toFinset =
      overlappingPairIndices leftTerms rightTerms := by
  ext pair
  simp

/--
The concrete overlapping correction grid and its occurrence-index traversal
have the same length.
-/
lemma length_overlapping_grid
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    (overlappingCorrectionGrid leftTerms rightTerms).length =
      (overlappingPairList leftTerms rightTerms).length := by
  calc
    (overlappingCorrectionGrid leftTerms rightTerms).length =
        ((leftTerms.product rightTerms).filter fun pair =>
          !decide
            (Disjoint pair.2.decorated.support
              pair.1.decorated.support)).length := by
      exact length_flat_filter
        leftTerms rightTerms
        (fun left right =>
          !decide
            (Disjoint right.decorated.support left.decorated.support))
        (fun left right => left.correction right)
    _ =
        (((List.finRange leftTerms.length).product
          (List.finRange rightTerms.length)).filter fun pair =>
            !decide
              (Disjoint
                (rightTerms.get pair.2).decorated.support
                (leftTerms.get pair.1).decorated.support)).length := by
      simpa [← List.ofFn_eq_map] using
        length_filter_product
          (List.finRange leftTerms.length)
          (List.finRange rightTerms.length)
          leftTerms.get rightTerms.get
          (fun left right =>
            !decide
              (Disjoint right.decorated.support left.decorated.support))
    _ = (overlappingPairList leftTerms rightTerms).length := by
      simp [overlappingPairList, commonSupport,
        ← Finset.not_disjoint_iff_nonempty_inter]

/-- The concrete overlap-grid length is the finite overlap-pair cardinality. -/
lemma length_overlapping_indices
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    (overlappingCorrectionGrid leftTerms rightTerms).length =
      (overlappingPairIndices leftTerms rightTerms).card := by
  rw [length_overlapping_grid,
    ← finset_overlapping_pair]
  exact (List.toFinset_card_of_nodup
    (overlapping_pair_nodup leftTerms rightTerms)).symm

/--
Every overlapping occurrence pair belongs to at least one fixed-slot
stratum, and every fixed-slot stratum consists of overlapping pairs.
-/
lemma overlapping_indices_bi
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    overlappingPairIndices leftTerms rightTerms =
      (Finset.univ : Finset (Fin K)).biUnion
        (overlapIndicesSlot leftTerms rightTerms) := by
  classical
  ext pair
  simp [overlappingPairIndices, overlapIndicesSlot, commonSupport,
    Finset.Nonempty]

/--
The number of overlapping occurrence pairs is the alternating sum of the
cardinalities of finite intersections of fixed-slot overlap strata.
-/
lemma overlapping_indices_exclusion
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    ((overlappingPairIndices leftTerms rightTerms).card : ℤ) =
      ∑ slots :
          (Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty),
        (-1 : ℤ) ^ (slots.1.card + 1) *
          (slots.1.inf' (Finset.mem_filter.1 slots.2).2
            (overlapIndicesSlot leftTerms rightTerms)).card := by
  rw [overlapping_indices_bi]
  exact Finset.inclusion_exclusion_card_biUnion
    (Finset.univ : Finset (Fin K))
    (overlapIndicesSlot leftTerms rightTerms)

/--
The concrete overlap-grid length is the alternating sum of finite
intersections of fixed-slot overlap strata.
-/
lemma overlapping_inclusion_exclusion
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    ((overlappingCorrectionGrid leftTerms rightTerms).length : ℤ) =
      ∑ slots :
          (Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty),
        (-1 : ℤ) ^ (slots.1.card + 1) *
          (slots.1.inf' (Finset.mem_filter.1 slots.2).2
            (overlapIndicesSlot leftTerms rightTerms)).card := by
  rw [length_overlapping_indices]
  exact overlapping_indices_exclusion leftTerms rightTerms

end OIExclus
end TCTex
end Towers

/-!
# Fixed-slot overlap strata

Each inclusion-exclusion term for an overlap grid fixes a nonempty set of raw
slots and asks for parent occurrence pairs sharing every slot in that set.
This file factors such a stratum into independent left and right
support-containment counts.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace OFSlots

open HACoeff
open CSOverla
open OIExclus

/-- Terms in one represented packet whose raw support contains every prescribed slot. -/
def termsContainingSlots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    List (DFTerm M N K) :=
  terms.filter fun term =>
    decide (slots ⊆ term.decorated.support)

/-- Ordered occurrence indices for one support-containment subpacket. -/
def termContainingSlots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    List (Fin terms.length) :=
  (List.finRange terms.length).filter fun index =>
    decide (slots ⊆ (terms.get index).decorated.support)

/-- Occurrences in one represented packet whose raw support contains every prescribed slot. -/
def termIndicesContaining
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    Finset (Fin terms.length) :=
  Finset.univ.filter fun index =>
    slots ⊆ (terms.get index).decorated.support

lemma containing_slots_nodup
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termContainingSlots terms slots).Nodup :=
  (List.nodup_finRange _).filter _

lemma finset_containing_slots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termContainingSlots terms slots).toFinset =
      termIndicesContaining terms slots := by
  ext index
  simp [termContainingSlots, termIndicesContaining]

/--
Filtering packet terms and filtering their occurrence indices produce lists
of the same length.
-/
lemma length_containing_slots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termsContainingSlots terms slots).length =
      (termContainingSlots terms slots).length := by
  simpa [termsContainingSlots, termContainingSlots,
    ← List.ofFn_eq_map] using
      filter_map_eq
        (List.finRange terms.length) terms.get
        (fun term => decide (slots ⊆ term.decorated.support))

/-- One-sided support-containment cardinality is a concrete filtered packet length. -/
lemma containing_slots_indices
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termsContainingSlots terms slots).length =
      (termIndicesContaining terms slots).card := by
  rw [length_containing_slots,
    ← finset_containing_slots]
  exact (List.toFinset_card_of_nodup
    (containing_slots_nodup terms slots)).symm

/-- Parent occurrence pairs sharing every prescribed raw slot. -/
def indicesContainingSlots
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    Finset (CorrectionPairIndex leftTerms rightTerms) :=
  Finset.univ.filter fun pair =>
    slots ⊆ commonSupport leftTerms rightTerms pair

/--
Requiring every prescribed slot in a parent pair is equivalent to requiring
those slots independently in both parent occurrences.
-/
lemma indices_containing_slots
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    indicesContainingSlots leftTerms rightTerms slots =
      (termIndicesContaining leftTerms slots).product
        (termIndicesContaining rightTerms slots) := by
  ext pair
  rcases pair with ⟨leftIndex, rightIndex⟩
  simp only [indicesContainingSlots, termIndicesContaining,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.product_eq_sprod,
    Finset.mem_product, commonSupport]
  constructor
  · intro hslots
    exact
      ⟨fun slot hslot => (Finset.mem_inter.mp (hslots hslot)).2,
        fun slot hslot => (Finset.mem_inter.mp (hslots hslot)).1⟩
  · rintro ⟨hleft, hright⟩ slot hslot
    exact Finset.mem_inter.mpr ⟨hright hslot, hleft hslot⟩

/-- The cardinality of a fixed-slot pair stratum factors into one-sided counts. -/
lemma card_containing_slots
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (indicesContainingSlots leftTerms rightTerms slots).card =
      (termIndicesContaining leftTerms slots).card *
        (termIndicesContaining rightTerms slots).card := by
  rw [indices_containing_slots]
  exact Finset.card_product _ _

/--
The finite intersection appearing in inclusion-exclusion is the direct
fixed-slot containment stratum.
-/
lemma overlap_containing_slots
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K))
    (hslots : slots.Nonempty) :
    slots.inf' hslots (overlapIndicesSlot leftTerms rightTerms) =
      indicesContainingSlots leftTerms rightTerms slots := by
  ext pair
  rcases pair with ⟨leftIndex, rightIndex⟩
  simp [overlapIndicesSlot, indicesContainingSlots, commonSupport,
    Finset.subset_iff]

/--
Every multi-slot intersection in the overlap inclusion-exclusion formula
factors into independent one-sided support-containment counts.
-/
lemma overlap_indices_slot
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K))
    (hslots : slots.Nonempty) :
    (slots.inf' hslots
      (overlapIndicesSlot leftTerms rightTerms)).card =
      (termIndicesContaining leftTerms slots).card *
        (termIndicesContaining rightTerms slots).card := by
  rw [overlap_containing_slots,
    card_containing_slots]

/--
The overlap-grid length is an alternating sum of products of concrete
one-sided support-containment packet lengths.
-/
lemma overlapping_factored_exclusion
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K)) :
    ((overlappingCorrectionGrid leftTerms rightTerms).length : ℤ) =
      ∑ slots :
          (Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty),
        (-1 : ℤ) ^ (slots.1.card + 1) *
          ((termsContainingSlots leftTerms slots.1).length : ℤ) *
          (termsContainingSlots rightTerms slots.1).length := by
  rw [overlapping_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro slots hslots
  rw [overlap_indices_slot leftTerms rightTerms slots.1
    (Finset.mem_filter.1 slots.2).2]
  simp [containing_slots_indices,
    mul_assoc]

end OFSlots
end TCTex
end Towers

/-!
# Support avoidance for fixed-slot overlap strata

Fixed-slot containment is recovered by inclusion-exclusion from support
avoidance.  Avoidance is the recursively convenient predicate: a Cartesian
correction term avoids a slot set exactly when both of its parents avoid that
set, because correction support is the union of parent supports.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace COAvoida

open HACoeff
open OFSlots
open OIExclus
open HSPacket

/-- Terms in one represented packet whose raw support avoids every prescribed slot. -/
def termsAvoidingSlots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    List (DFTerm M N K) :=
  terms.filter fun term =>
    decide (Disjoint slots term.decorated.support)

/-- Ordered occurrence indices for one support-avoidance subpacket. -/
def termAvoidingSlots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    List (Fin terms.length) :=
  (List.finRange terms.length).filter fun index =>
    decide (Disjoint slots (terms.get index).decorated.support)

/-- Occurrences in one represented packet whose raw support avoids every prescribed slot. -/
def indicesAvoidingSlots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    Finset (Fin terms.length) :=
  Finset.univ.filter fun index =>
    Disjoint slots (terms.get index).decorated.support

lemma avoiding_slots_nodup
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termAvoidingSlots terms slots).Nodup :=
  (List.nodup_finRange _).filter _

lemma finset_avoiding_slots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termAvoidingSlots terms slots).toFinset =
      indicesAvoidingSlots terms slots := by
  ext index
  simp [termAvoidingSlots, indicesAvoidingSlots]

/-- Filtering packet terms and occurrence indices by avoidance gives equal lengths. -/
lemma length_avoiding_slots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termsAvoidingSlots terms slots).length =
      (termAvoidingSlots terms slots).length := by
  simpa [termsAvoidingSlots, termAvoidingSlots,
    ← List.ofFn_eq_map] using
      filter_map_eq
        (List.finRange terms.length) terms.get
        (fun term => decide (Disjoint slots term.decorated.support))

/-- One-sided support-avoidance cardinality is a concrete filtered packet length. -/
lemma avoiding_slots_indices
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termsAvoidingSlots terms slots).length =
      (indicesAvoidingSlots terms slots).card := by
  rw [length_avoiding_slots,
    ← finset_avoiding_slots]
  exact (List.toFinset_card_of_nodup
    (avoiding_slots_nodup terms slots)).symm

/-- Avoidance distributes over concatenation of concrete term packets. -/
@[simp]
lemma avoiding_slots_append
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    termsAvoidingSlots (leftTerms ++ rightTerms) slots =
      termsAvoidingSlots leftTerms slots ++
        termsAvoidingSlots rightTerms slots := by
  simp [termsAvoidingSlots, List.filter_append]

/-- A correction avoids prescribed slots exactly when both parents avoid them. -/
lemma disjoint_support_correction
    {M N K : ℕ}
    (slots : Finset (Fin K))
    (left right : DFTerm M N K) :
    Disjoint slots (left.correction right).decorated.support ↔
      Disjoint slots left.decorated.support ∧
        Disjoint slots right.decorated.support := by
  simp [DFTerm.correction, DTerm.correction,
    Finset.disjoint_union_right]

/-- The avoidance count in one Cartesian row is either the right count or zero. -/
lemma terms_avoiding_slots
    {M N K : ℕ}
    (left : DFTerm M N K)
    (rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termsAvoidingSlots
      (rightTerms.map fun right => left.correction right) slots).length =
      if Disjoint slots left.decorated.support then
        (termsAvoidingSlots rightTerms slots).length
      else
        0 := by
  rw [termsAvoidingSlots,
    filter_map_eq]
  by_cases hleft : Disjoint slots left.decorated.support
  · simp [termsAvoidingSlots, hleft]
  · simp [hleft]

/--
Avoidance multiplies across a full Cartesian correction grid.
-/
lemma avoiding_slots_grid
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    (termsAvoidingSlots
      (DFTerm.correctionGrid leftTerms rightTerms) slots).length =
      (termsAvoidingSlots leftTerms slots).length *
        (termsAvoidingSlots rightTerms slots).length := by
  induction leftTerms with
  | nil =>
      simp [termsAvoidingSlots]
  | cons left leftTerms ih =>
      change
        (termsAvoidingSlots
          ((rightTerms.map fun right => left.correction right) ++
            DFTerm.correctionGrid leftTerms rightTerms)
          slots).length =
            (termsAvoidingSlots (left :: leftTerms) slots).length *
              (termsAvoidingSlots rightTerms slots).length
      rw [avoiding_slots_append, List.length_append,
        terms_avoiding_slots, ih]
      by_cases hleft : Disjoint slots left.decorated.support
      · simp [termsAvoidingSlots, hleft, Nat.add_mul, Nat.add_comm]
      · simp [termsAvoidingSlots, hleft]

/--
Containing every prescribed slot is the intersection of the complements of
the singleton-avoidance conditions.
-/
lemma containing_compl_avoiding
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    termIndicesContaining terms slots =
      slots.inf fun slot => (indicesAvoidingSlots terms {slot})ᶜ := by
  ext index
  simp [termIndicesContaining, indicesAvoidingSlots,
    Finset.mem_inf, Finset.subset_iff]

/-- Avoiding every singleton in a finite slot set is the same as avoiding the set. -/
lemma inf_avoiding_slots
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    slots.inf (fun slot => indicesAvoidingSlots terms {slot}) =
      indicesAvoidingSlots terms slots := by
  ext index
  simp [indicesAvoidingSlots, Finset.mem_inf, Finset.disjoint_left]

/--
One-sided support containment is an alternating sum of one-sided support
avoidance cardinalities.
-/
lemma containing_exclusion_avoiding
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    ((termIndicesContaining terms slots).card : ℤ) =
      ∑ avoidedSlots ∈ slots.powerset,
        (-1 : ℤ) ^ avoidedSlots.card *
          (indicesAvoidingSlots terms avoidedSlots).card := by
  rw [containing_compl_avoiding,
    Finset.inclusion_exclusion_card_inf_compl]
  apply Finset.sum_congr rfl
  intro avoidedSlots _hslots
  rw [inf_avoiding_slots]

/--
Concrete one-sided support containment length is an alternating sum of
concrete support-avoidance packet lengths.
-/
lemma slots_exclusion_avoiding
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    ((termsContainingSlots terms slots).length : ℤ) =
      ∑ avoidedSlots ∈ slots.powerset,
        (-1 : ℤ) ^ avoidedSlots.card *
          (termsAvoidingSlots terms avoidedSlots).length := by
  rw [containing_slots_indices,
    containing_exclusion_avoiding]
  apply Finset.sum_congr rfl
  intro avoidedSlots _hslots
  rw [avoiding_slots_indices]

end COAvoida
end TCTex
end Towers

/-!
# Algebra of explicit signed-block profiles

Support-pattern inclusion-exclusion produces sums, integral scalar
multiples, and products of symbolic packet counts.  Explicit signed-block
profiles are closed under all three operations.  Multiplication concatenates
left and right block lists, so homogeneous bidegrees add exactly as Hall
commutator degrees do.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSAlg

open HACoeff
open CSAggreg
open CSFilter

/-- Product of two explicit generator profiles, formed by concatenating block lists. -/
def multiplyBlockProfile
    (left right : SBProf) :
    SBProf where
  leftBlocks := left.leftBlocks ++ right.leftBlocks
  rightBlocks := left.rightBlocks ++ right.rightBlocks

@[simp]
lemma multiply_block_degree
    (left right : SBProf) :
    (multiplyBlockProfile left right).leftDegree =
      left.leftDegree + right.leftDegree := by
  simp [multiplyBlockProfile, SBProf.leftDegree, degreeSum]

@[simp]
lemma multiply_profile_degree
    (left right : SBProf) :
    (multiplyBlockProfile left right).rightDegree =
      left.rightDegree + right.rightDegree := by
  simp [multiplyBlockProfile, SBProf.rightDegree, degreeSum]

@[simp]
lemma multiply_profile_coefficient
    (left right : SBProf)
    (M N : ℕ) :
    (multiplyBlockProfile left right).coefficient M N =
      left.coefficient M N * right.coefficient M N := by
  simp [multiplyBlockProfile, SBProf.coefficient,
    blockProduct]
  ring

/-- Product of two integrally weighted signed-block profiles. -/
def multiplyWeightedProfile
    (left right : WBProf) :
    WBProf where
  multiplicity := left.multiplicity * right.multiplicity
  profile := multiplyBlockProfile left.profile right.profile

@[simp]
lemma multiply_weighted_profile
    (left right : WBProf) :
    (multiplyWeightedProfile left right).profile.leftDegree =
      left.profile.leftDegree + right.profile.leftDegree := by
  simp [multiplyWeightedProfile]

@[simp]
lemma multiply_weighted_degree
    (left right : WBProf) :
    (multiplyWeightedProfile left right).profile.rightDegree =
      left.profile.rightDegree + right.profile.rightDegree := by
  simp [multiplyWeightedProfile]

@[simp]
lemma multiply_weighted_coefficient
    (left right : WBProf)
    (M N : ℕ) :
    (multiplyWeightedProfile left right).coefficient M N =
      left.coefficient M N * right.coefficient M N := by
  simp [multiplyWeightedProfile,
    WBProf.coefficient]
  ring

/-- Scale one weighted profile by an additional integral multiplicity. -/
def scaleWeightedProfile
    (scale : ℤ)
    (profile : WBProf) :
    WBProf where
  multiplicity := scale * profile.multiplicity
  profile := profile.profile

@[simp]
lemma scale_weighted_profile
    (scale : ℤ)
    (profile : WBProf) :
    (scaleWeightedProfile scale profile).profile.leftDegree =
      profile.profile.leftDegree :=
  rfl

@[simp]
lemma scale_weighted_degree
    (scale : ℤ)
    (profile : WBProf) :
    (scaleWeightedProfile scale profile).profile.rightDegree =
      profile.profile.rightDegree :=
  rfl

@[simp]
lemma scale_weighted_coefficient
    (scale : ℤ)
    (profile : WBProf)
    (M N : ℕ) :
    (scaleWeightedProfile scale profile).coefficient M N =
      scale * profile.coefficient M N := by
  simp [scaleWeightedProfile,
    WBProf.coefficient, mul_assoc]

/-- Scale a finite profile sum by an additional integral multiplicity. -/
def scaleWeightedProfiles
    (scale : ℤ)
    (profiles : List WBProf) :
    List WBProf :=
  profiles.map (scaleWeightedProfile scale)

@[simp]
lemma weighted_coefficient_scale
    (scale : ℤ)
    (M N : ℕ) :
    ∀ profiles : List WBProf,
      weightedCoefficientSum M N
          (scaleWeightedProfiles scale profiles) =
        scale * weightedCoefficientSum M N profiles
  | [] => by
      simp [scaleWeightedProfiles,
        weightedCoefficientSum]
  | profile :: profiles => by
      change
        (scaleWeightedProfile scale profile).coefficient M N +
            weightedCoefficientSum M N
              (scaleWeightedProfiles scale profiles) =
          scale *
            (profile.coefficient M N +
              weightedCoefficientSum M N profiles)
      rw [scale_weighted_coefficient,
        weighted_coefficient_scale scale M N profiles]
      ring

/-- Cartesian products of weighted profile lists. -/
def multiplyWeightedProfiles
    (left right : List WBProf) :
    List WBProf :=
  left.flatMap fun leftProfile =>
    right.map (multiplyWeightedProfile leftProfile)

@[simp]
lemma weighted_coefficient_multiply
    (left : WBProf)
    (M N : ℕ) :
    ∀ right : List WBProf,
      weightedCoefficientSum M N
          (right.map (multiplyWeightedProfile left)) =
        left.coefficient M N *
          weightedCoefficientSum M N right
  | [] => by
      simp [weightedCoefficientSum]
  | profile :: profiles => by
      change
        (multiplyWeightedProfile left profile).coefficient M N +
            weightedCoefficientSum M N
              (profiles.map (multiplyWeightedProfile left)) =
          left.coefficient M N *
            (profile.coefficient M N +
              weightedCoefficientSum M N profiles)
      rw [multiply_weighted_coefficient,
        weighted_coefficient_multiply left M N profiles]
      ring

@[simp]
lemma weighted_block_multiply
    (M N : ℕ) :
    ∀ left right : List WBProf,
      weightedCoefficientSum M N
          (multiplyWeightedProfiles left right) =
        weightedCoefficientSum M N left *
          weightedCoefficientSum M N right
  | [], right => by
      simp [multiplyWeightedProfiles,
        weightedCoefficientSum]
  | profile :: profiles, right => by
      rw [multiplyWeightedProfiles, List.flatMap_cons,
        weighted_coefficient_append]
      change
        weightedCoefficientSum M N
              (right.map (multiplyWeightedProfile profile)) +
            weightedCoefficientSum M N
              (multiplyWeightedProfiles profiles right) =
          (profile.coefficient M N +
              weightedCoefficientSum M N profiles) *
            weightedCoefficientSum M N right
      rw [weighted_coefficient_multiply,
        weighted_block_multiply M N profiles right]
      ring

/-- Products of homogeneous profile lists remain homogeneous in the summed bidegree. -/
lemma multiply_profiles_degree
    (left right : List WBProf)
    (leftDegree rightDegree : ℕ)
    (hleft :
      ∀ profile ∈ left,
        profile.profile.leftDegree = leftDegree)
    (hright :
      ∀ profile ∈ right,
        profile.profile.leftDegree = rightDegree) :
    ∀ profile ∈ multiplyWeightedProfiles left right,
      profile.profile.leftDegree = leftDegree + rightDegree := by
  intro profile hprofile
  rcases List.mem_flatMap.mp hprofile with
    ⟨leftProfile, hleftProfile, hprofile⟩
  rcases List.mem_map.mp hprofile with
    ⟨rightProfile, hrightProfile, rfl⟩
  simp [hleft leftProfile hleftProfile, hright rightProfile hrightProfile]

/-- Products of homogeneous profile lists remain homogeneous in the summed bidegree. -/
lemma multiply_weighted_profiles
    (left right : List WBProf)
    (leftDegree rightDegree : ℕ)
    (hleft :
      ∀ profile ∈ left,
        profile.profile.rightDegree = leftDegree)
    (hright :
      ∀ profile ∈ right,
        profile.profile.rightDegree = rightDegree) :
    ∀ profile ∈ multiplyWeightedProfiles left right,
      profile.profile.rightDegree = leftDegree + rightDegree := by
  intro profile hprofile
  rcases List.mem_flatMap.mp hprofile with
    ⟨leftProfile, hleftProfile, hprofile⟩
  rcases List.mem_map.mp hprofile with
    ⟨rightProfile, hrightProfile, rfl⟩
  simp [hleft leftProfile hleftProfile, hright rightProfile hrightProfile]

/-- Scaling preserves a homogeneous left-degree condition. -/
lemma scale_profiles_degree
    (scale : ℤ)
    (profiles : List WBProf)
    (degree : ℕ)
    (hprofiles :
      ∀ profile ∈ profiles,
        profile.profile.leftDegree = degree) :
    ∀ profile ∈ scaleWeightedProfiles scale profiles,
      profile.profile.leftDegree = degree := by
  intro profile hprofile
  rcases List.mem_map.mp hprofile with ⟨original, horiginal, rfl⟩
  exact hprofiles original horiginal

/-- Scaling preserves a homogeneous right-degree condition. -/
lemma scale_weighted_profiles
    (scale : ℤ)
    (profiles : List WBProf)
    (degree : ℕ)
    (hprofiles :
      ∀ profile ∈ profiles,
        profile.profile.rightDegree = degree) :
    ∀ profile ∈ scaleWeightedProfiles scale profiles,
      profile.profile.rightDegree = degree := by
  intro profile hprofile
  rcases List.mem_map.mp hprofile with ⟨original, horiginal, rfl⟩
  exact hprofiles original horiginal

end CSAlg
end TCTex
end Towers

/-!
# Homogeneous signed-block expressions

Profile lists are the concrete representation of admissible coefficients.
This file packages a profile list together with its integer value and common
bidegree, then supplies the algebraic constructors used by support-pattern
compilation.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CEAlg

open HACoeff
open CSAggreg
open CSFilter
open CSAlg

/-- One explicit homogeneous signed-block expression and its evaluated value. -/
structure HBExpr
    (M N leftDegree rightDegree : ℕ) where
  value :
    ℤ
  profiles :
    List WBProf
  profiles_leftDegree :
    ∀ profile ∈ profiles,
      profile.profile.leftDegree = leftDegree
  profiles_rightDegree :
    ∀ profile ∈ profiles,
      profile.profile.rightDegree = rightDegree
  value_eq :
    value = weightedCoefficientSum M N profiles

namespace HBExpr

/--
Package profiles at specified multiplicities.  This is the constructor used
by concrete packet-count compilers.
-/
def ofProfiles
    {leftDegree rightDegree M N : ℕ}
    (profiles : List WBProf)
    (hleft :
      ∀ profile ∈ profiles,
        profile.profile.leftDegree = leftDegree)
    (hright :
      ∀ profile ∈ profiles,
        profile.profile.rightDegree = rightDegree) :
    HBExpr M N leftDegree rightDegree where
  value := weightedCoefficientSum M N profiles
  profiles := profiles
  profiles_leftDegree := hleft
  profiles_rightDegree := hright
  value_eq := by
    rfl

/-- Zero expression in any homogeneous bidegree. -/
def zero
    (M N leftDegree rightDegree : ℕ) :
    HBExpr M N leftDegree rightDegree where
  value := 0
  profiles := []
  profiles_leftDegree := by simp
  profiles_rightDegree := by simp
  value_eq := by simp [weightedCoefficientSum]

/-- Sum of two homogeneous signed-block expressions. -/
def add
    {M N leftDegree rightDegree : ℕ}
    (left right :
      HBExpr M N leftDegree rightDegree) :
    HBExpr M N leftDegree rightDegree where
  value := left.value + right.value
  profiles := left.profiles ++ right.profiles
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact left.profiles_leftDegree profile hprofile
    · exact right.profiles_leftDegree profile hprofile
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact left.profiles_rightDegree profile hprofile
    · exact right.profiles_rightDegree profile hprofile
  value_eq := by
    rw [weighted_coefficient_append,
      ← left.value_eq, ← right.value_eq]

/-- Integral scalar multiple of one homogeneous signed-block expression. -/
def scale
    {M N leftDegree rightDegree : ℕ}
    (factor : ℤ)
    (expression :
      HBExpr M N leftDegree rightDegree) :
    HBExpr M N leftDegree rightDegree where
  value := factor * expression.value
  profiles := scaleWeightedProfiles factor expression.profiles
  profiles_leftDegree :=
    scale_profiles_degree
      factor expression.profiles leftDegree expression.profiles_leftDegree
  profiles_rightDegree :=
    scale_weighted_profiles
      factor expression.profiles rightDegree expression.profiles_rightDegree
  value_eq := by
    rw [weighted_coefficient_scale, ← expression.value_eq]

/-- Product of two homogeneous expressions, with summed source bidegree. -/
def multiply
    {M N leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      HBExpr M N leftLeftDegree leftRightDegree)
    (right :
      HBExpr M N rightLeftDegree rightRightDegree) :
    HBExpr
      M N (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) where
  value := left.value * right.value
  profiles :=
    multiplyWeightedProfiles left.profiles right.profiles
  profiles_leftDegree :=
    multiply_profiles_degree
      left.profiles right.profiles leftLeftDegree rightLeftDegree
        left.profiles_leftDegree right.profiles_leftDegree
  profiles_rightDegree :=
    multiply_weighted_profiles
      left.profiles right.profiles leftRightDegree rightRightDegree
        left.profiles_rightDegree right.profiles_rightDegree
  value_eq := by
    rw [weighted_block_multiply,
      ← left.value_eq, ← right.value_eq]

/-- Finite sum of homogeneous expressions. -/
def sum
    {M N leftDegree rightDegree : ℕ} :
    List (HBExpr M N leftDegree rightDegree) →
      HBExpr M N leftDegree rightDegree
  | [] =>
      zero M N leftDegree rightDegree
  | expression :: expressions =>
      expression.add (sum expressions)

@[simp]
lemma value_sum
    {M N leftDegree rightDegree : ℕ} :
    ∀ expressions :
        List (HBExpr M N leftDegree rightDegree),
      (sum expressions).value =
        (expressions.map HBExpr.value).sum
  | [] => by
      rfl
  | expression :: expressions => by
      simp [sum, value_sum expressions, add]

/-- Finite sum of a homogeneous expression family indexed by a finset. -/
noncomputable def finsetSum
    {ι : Type*}
    {M N leftDegree rightDegree : ℕ}
    (indices : Finset ι)
    (expression :
      ι → HBExpr M N leftDegree rightDegree) :
    HBExpr M N leftDegree rightDegree :=
  sum (indices.toList.map expression)

@[simp]
lemma value_finsetSum
    {ι : Type*}
    {M N leftDegree rightDegree : ℕ}
    (indices : Finset ι)
    (expression :
      ι → HBExpr M N leftDegree rightDegree) :
    (finsetSum indices expression).value =
      ∑ index ∈ indices, (expression index).value := by
  simp [finsetSum]

/-- Convert a homogeneous expression with a concrete length value into a shape-block certificate. -/
def shapeBlockCertificate
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (expression :
      HBExpr
        M N word.pairLeftDegree word.pairRightDegree)
    (hlength :
      (block.length : ℤ) =
        expression.value) :
    SBCert block word where
  profiles := expression.profiles
  profiles_leftDegree := expression.profiles_leftDegree
  profiles_rightDegree := expression.profiles_rightDegree
  length_eq := hlength.trans expression.value_eq

end HBExpr

end CEAlg
end TCTex
end Towers

/-!
# Compiling diagonal admissibility into explicit signed blocks

Diagonal equality-class counting proves membership in the Hall-Petresco
admissible coefficient span.  For symbolic recollection it is useful to
retain an explicit finite packet of signed generalized-binomial generators.
This file extracts such a packet by induction on span membership and upgrades
the diagonal operational boundary to the explicit signed-block boundary.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace DSComp

open HACoeff
open CDAggreg
open CSAggreg
open CEAlg

/--
Every coefficient in the admissible span admits an explicit finite
homogeneous signed-block expression.
-/
lemma homogeneous_expression_submodule
    {M N leftDegree rightDegree : ℕ}
    {coefficient : ℤ}
    (hcoefficient :
      coefficient ∈ submodule M N leftDegree rightDegree) :
    ∃ expression :
        HBExpr M N leftDegree rightDegree,
      expression.value = coefficient := by
  induction hcoefficient using Submodule.span_induction with
  | mem coefficient hcoefficient =>
      rcases hcoefficient with
        ⟨leftBlocks, rightBlocks, hleftDegree, hrightDegree, rfl⟩
      let profile : WBProf := {
        multiplicity := 1
        profile := {
          leftBlocks := leftBlocks
          rightBlocks := rightBlocks } }
      refine
        ⟨HBExpr.ofProfiles [profile] ?_ ?_, ?_⟩
      · intro next hnext
        have hnextEq : next = profile := by
          simpa using hnext
        subst next
        simpa [profile, SBProf.leftDegree] using hleftDegree
      · intro next hnext
        have hnextEq : next = profile := by
          simpa using hnext
        subst next
        simpa [profile, SBProf.rightDegree] using hrightDegree
      · simp [HBExpr.ofProfiles,
          weightedCoefficientSum, profile,
          WBProf.coefficient,
          SBProf.coefficient]
  | zero =>
      exact
        ⟨HBExpr.zero
          M N leftDegree rightDegree, rfl⟩
  | add left right _hleft _hright ihleft ihright =>
      rcases ihleft with ⟨leftExpression, hleftExpression⟩
      rcases ihright with ⟨rightExpression, hrightExpression⟩
      refine ⟨leftExpression.add rightExpression, ?_⟩
      exact congrArg₂ (· + ·) hleftExpression hrightExpression
  | smul scalar coefficient _hcoefficient ih =>
      rcases ih with ⟨expression, hexpression⟩
      refine ⟨expression.scale scalar, ?_⟩
      exact congrArg (scalar * ·) hexpression

/-- Chosen explicit signed-block expression for one admissible coefficient. -/
noncomputable def homogeneousExpressionSubmodule
    {M N leftDegree rightDegree : ℕ}
    {coefficient : ℤ}
    (hcoefficient :
      coefficient ∈ submodule M N leftDegree rightDegree) :
    HBExpr M N leftDegree rightDegree :=
  Classical.choose
    (homogeneous_expression_submodule hcoefficient)

@[simp]
lemma homogeneous_expression_value
    {M N leftDegree rightDegree : ℕ}
    {coefficient : ℤ}
    (hcoefficient :
      coefficient ∈ submodule M N leftDegree rightDegree) :
    (homogeneousExpressionSubmodule hcoefficient).value =
      coefficient :=
  Classical.choose_spec
    (homogeneous_expression_submodule hcoefficient)

/--
Forget the equality-class presentation of a diagonal certificate while
retaining an explicit finite signed generalized-binomial packet.
-/
noncomputable def shapeCertificateDiagonal
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (certificate : SDCert block word) :
    SBCert block word :=
  let expression :=
    homogeneousExpressionSubmodule
      certificate.length_mem_submodule
  expression.shapeBlockCertificate <| by
    exact
      (homogeneous_expression_value
        certificate.length_mem_submodule).symm

/-- Compile diagonal block certificates into explicit signed-block packets. -/
noncomputable def shapeSignedDiagonal
    (kernel : OCDiagon) :
    OCShape where
  certificate endpoint block hblock word hterms := by
    rcases kernel.certificate endpoint block hblock word hterms with
      ⟨certificate⟩
    exact ⟨shapeCertificateDiagonal certificate⟩

/-- Upgrade diagonal compatible collection to the explicit signed-block boundary. -/
noncomputable def signedCollectionDiagonal
    (kernel : ODColl) :
    OCColl where
  compatibleClosure := kernel.compatibleClosure
  shapeBlockSigned :=
    shapeSignedDiagonal kernel.shapeBlockDiagonal

end DSComp
end TCTex
end Towers

/-!
# Support-pattern signed-block expression compiler

Support avoidance is the recursively convenient packet statistic: it
multiplies across a full Cartesian correction grid.  Fixed-slot containment
and parent-support overlap are recovered from avoidance by the two finite
inclusion-exclusion formulas proved in the preceding modules.

This file packages that recursion as homogeneous signed-block expressions.
It is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace SEComp

open HACoeff
open CCGrida
open CSAggreg
open CEAlg
open CSOverla
open COAvoida
open OFSlots
open HSPacket

/-- A homogeneous signed-block expression for one support-avoidance count. -/
structure SAExpr
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K))
    (leftDegree rightDegree : ℕ) where
  expression :
    HBExpr M N leftDegree rightDegree
  length_eq :
    ((termsAvoidingSlots terms slots).length : ℤ) = expression.value

/-- A homogeneous signed-block expression for one fixed-slot containment count. -/
structure SCExpr
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K))
    (leftDegree rightDegree : ℕ) where
  expression :
    HBExpr M N leftDegree rightDegree
  length_eq :
    ((termsContainingSlots terms slots).length : ℤ) = expression.value

/-- A homogeneous signed-block expression for the overlapping part of a correction grid. -/
structure OBExpr
    {M N K : ℕ}
    (leftTerms rightTerms : List (DFTerm M N K))
    (leftDegree rightDegree : ℕ) where
  expression :
    HBExpr M N leftDegree rightDegree
  length_eq :
    ((overlappingCorrectionGrid leftTerms rightTerms).length : ℤ) =
      expression.value

namespace SAExpr

/-- Avoidance expressions multiply across a full Cartesian correction grid. -/
def correctionGrid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {slots : Finset (Fin K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      SAExpr
        leftTerms slots leftLeftDegree leftRightDegree)
    (right :
      SAExpr
        rightTerms slots rightLeftDegree rightRightDegree) :
    SAExpr
      (DFTerm.correctionGrid leftTerms rightTerms) slots
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) where
  expression := left.expression.multiply right.expression
  length_eq := by
    rw [avoiding_slots_grid, Int.natCast_mul,
      left.length_eq, right.length_eq]
    rfl

end SAExpr

namespace SCExpr

/--
Compile fixed-slot containment from a homogeneous avoidance expression for
every finite slot set.
-/
noncomputable def ofAvoidance
    {M N K leftDegree rightDegree : ℕ}
    {terms : List (DFTerm M N K)}
    (slots : Finset (Fin K))
    (avoidance :
      ∀ avoidedSlots : Finset (Fin K),
        SAExpr
          terms avoidedSlots leftDegree rightDegree) :
    SCExpr
      terms slots leftDegree rightDegree where
  expression :=
    HBExpr.finsetSum slots.powerset fun avoidedSlots =>
      HBExpr.scale
        ((-1 : ℤ) ^ avoidedSlots.card)
        (avoidance avoidedSlots).expression
  length_eq := by
    rw [slots_exclusion_avoiding,
      HBExpr.value_finsetSum]
    apply Finset.sum_congr rfl
    intro avoidedSlots _hslots
    rw [(avoidance avoidedSlots).length_eq]
    rfl

end SCExpr

namespace OBExpr

/--
Compile the overlapping part of a correction grid from homogeneous
fixed-slot containment expressions for both parent packets.
-/
noncomputable def ofContainment
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ slots : Finset (Fin K),
        SCExpr
          leftTerms slots leftLeftDegree leftRightDegree)
    (right :
      ∀ slots : Finset (Fin K),
        SCExpr
          rightTerms slots rightLeftDegree rightRightDegree) :
    OBExpr
      leftTerms rightTerms
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) where
  expression :=
    HBExpr.finsetSum
      (Finset.univ :
        Finset
          ((Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty)))
      fun slots =>
      HBExpr.scale
        ((-1 : ℤ) ^ (slots.1.card + 1))
        ((left slots.1).expression.multiply (right slots.1).expression)
  length_eq := by
    rw [overlapping_factored_exclusion,
      HBExpr.value_finsetSum]
    apply Finset.sum_congr rfl
    intro slots _hslots
    rw [(left slots.1).length_eq, (right slots.1).length_eq]
    simp [HBExpr.scale,
      HBExpr.multiply, mul_assoc]

/-- Convert a compiled overlap expression into the certificate consumed by grid filtering. -/
noncomputable def shapeBlockCertificate
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (compiled :
      OBExpr
        leftTerms rightTerms
        word.pairLeftDegree word.pairRightDegree) :
    SBCert
      (overlappingCorrectionGrid leftTerms rightTerms) word :=
  compiled.expression.shapeBlockCertificate compiled.length_eq

end OBExpr

end SEComp
end TCTex
end Towers

/-!
# Compiling signed shape-block profiles to Claim 8 formulas

Explicit signed-block profiles are the combinatorial output of compatible
shape-block counting.  Claim 8 uses a different language: finite integer
linear combinations of products of positive-index generalized binomial
coefficients in Hall coordinates.

This file connects the two languages.  Zero-degree blocks are erased, each
remaining signed block is normalized by the finite-grid Newton compiler, and
the resulting formulas are multiplied and summed.  The final constructor
turns any positive-bidegree admissible-span certificate directly into a
Claim 8 formula.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CEComp

universe u

open HACoeff
open CSAggreg
open CEAlg
open DSComp

/-- Erase signed blocks of degree zero before constructing Claim 8 formulas. -/
def positiveSignedBlocks
    (blocks : List Block) :
    List Block :=
  match blocks with
  | [] => []
  | block :: blocks =>
      if 0 < block.degree then
        block :: positiveSignedBlocks blocks
      else
        positiveSignedBlocks blocks

/-- Every retained signed block has positive degree. -/
lemma degree_pos_blocks
    {blocks : List Block}
    {block : Block}
    (hblock : block ∈ positiveSignedBlocks blocks) :
    0 < block.degree := by
  induction blocks with
  | nil =>
      simp [positiveSignedBlocks] at hblock
  | cons head blocks ih =>
      by_cases hdegree : 0 < head.degree
      · simp only [positiveSignedBlocks, if_pos hdegree,
          List.mem_cons] at hblock
        rcases hblock with rfl | hblock
        · exact hdegree
        · exact ih hblock
      · simp only [positiveSignedBlocks, if_neg hdegree] at hblock
        exact ih hblock

/-- Erasing degree-zero signed blocks preserves total degree. -/
@[simp]
lemma degree_positive_blocks
    (blocks : List Block) :
    degreeSum (positiveSignedBlocks blocks) = degreeSum blocks := by
  induction blocks with
  | nil =>
      simp [positiveSignedBlocks, degreeSum]
  | cons block blocks ih =>
      by_cases hdegree : 0 < block.degree
      · rw [positiveSignedBlocks, if_pos hdegree]
        change
          block.degree + degreeSum (positiveSignedBlocks blocks) =
            block.degree + degreeSum blocks
        rw [ih]
      · have hdegreeZero : block.degree = 0 :=
          Nat.eq_zero_of_not_pos hdegree
        rw [positiveSignedBlocks, if_neg hdegree]
        change
          degreeSum (positiveSignedBlocks blocks) =
            block.degree + degreeSum blocks
        rw [ih, hdegreeZero, zero_add]

/-- Erasing degree-zero signed blocks preserves their generalized-binomial product. -/
@[simp]
lemma block_positive_blocks
    (M : ℕ)
    (blocks : List Block) :
    blockProduct M (positiveSignedBlocks blocks) =
      blockProduct M blocks := by
  induction blocks with
  | nil =>
      simp [positiveSignedBlocks, blockProduct]
  | cons block blocks ih =>
      by_cases hdegree : 0 < block.degree
      · rw [positiveSignedBlocks, if_pos hdegree]
        change
          signedChoose block.sign M block.degree *
              blockProduct M (positiveSignedBlocks blocks) =
            signedChoose block.sign M block.degree *
              blockProduct M blocks
        rw [ih]
      · have hdegreeZero : block.degree = 0 :=
          Nat.eq_zero_of_not_pos hdegree
        rw [positiveSignedBlocks, if_neg hdegree]
        change
          blockProduct M (positiveSignedBlocks blocks) =
            signedChoose block.sign M block.degree * blockProduct M blocks
        rw [hdegreeZero, ← ih]
        cases block.sign <;>
          simp [signedChoose]

/-- Signed generalized-binomial product evaluated at an arbitrary integer. -/
def signedBlockProduct
    (z : ℤ)
    (blocks : List Block) :
    ℤ :=
  (blocks.map fun block =>
    Ring.choose (block.sign.intValue * z) block.degree).prod

/-- At natural inputs, the integer evaluator is the original block product. -/
@[simp]
lemma signed_block_cast
    (M : ℕ)
    (blocks : List Block) :
    signedBlockProduct (M : ℤ) blocks =
      blockProduct M blocks := by
  simp [signedBlockProduct, blockProduct, signed_choose_ring]

/-- Degree-zero erasure also preserves the arbitrary-integer evaluator. -/
@[simp]
lemma signed_positive_blocks
    (z : ℤ)
    (blocks : List Block) :
    signedBlockProduct z (positiveSignedBlocks blocks) =
      signedBlockProduct z blocks := by
  induction blocks with
  | nil =>
      simp [positiveSignedBlocks, signedBlockProduct]
  | cons block blocks ih =>
      by_cases hdegree : 0 < block.degree
      · rw [positiveSignedBlocks, if_pos hdegree]
        change
          Ring.choose (block.sign.intValue * z) block.degree *
              signedBlockProduct z (positiveSignedBlocks blocks) =
            Ring.choose (block.sign.intValue * z) block.degree *
              signedBlockProduct z blocks
        rw [ih]
      · have hdegreeZero : block.degree = 0 :=
          Nat.eq_zero_of_not_pos hdegree
        rw [positiveSignedBlocks, if_neg hdegree]
        change
          signedBlockProduct z (positiveSignedBlocks blocks) =
            Ring.choose (block.sign.intValue * z) block.degree *
              signedBlockProduct z blocks
        rw [hdegreeZero, Ring.choose_zero_right, one_mul, ih]

/-- One signed Hall-coordinate source exponent as a Claim 8 formula. -/
def signedInputExponent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (input : ι)
    (address : HEAddres H)
    (sign : Sign) :
    WBForm H ι address.1 :=
  (WBForm.inputExponent input address).scaleForChoose
    sign.intValue

@[simp]
lemma signed_input_exponent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (input : ι)
    (address : HEAddres H)
    (sign : Sign) :
    (signedInputExponent input address sign).eval e =
      sign.intValue * e input address.1 address.2 := by
  simp [signedInputExponent]

/--
Compile a nonempty list of positive-degree signed blocks to a Claim 8
formula.  The source coordinate is shared, while signs may vary by block.
-/
noncomputable def positiveBlockFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (input : ι)
    (address : HEAddres H) :
    (blocks : List Block) →
      blocks ≠ [] →
        (∀ block ∈ blocks, 0 < block.degree) →
          WBForm H ι (degreeSum blocks * address.1)
  | [], hnonempty, _ =>
      False.elim (hnonempty rfl)
  | [block], _, hpositive =>
      normalizer.ringChoose
        (signedInputExponent input address block.sign)
        block.degree
        (hpositive block (by simp))
  | block :: nextBlock :: blocks, _, hpositive =>
      (normalizer.ringChoose
        (signedInputExponent input address block.sign)
        block.degree
        (hpositive block (by simp))).mul
          (positiveBlockFormula normalizer input address
            (nextBlock :: blocks) (by simp)
            (fun next hnext => hpositive next (by simp [hnext])))
          (by simp [degreeSum, Nat.add_mul])
termination_by blocks => blocks.length

@[simp]
lemma positive_block_formula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (input : ι)
    (address : HEAddres H) :
    ∀ (blocks : List Block)
      (hnonempty : blocks ≠ [])
      (hpositive : ∀ block ∈ blocks, 0 < block.degree)
      (e : ι → HEFam H),
      (positiveBlockFormula normalizer input address
        blocks hnonempty hpositive).eval e =
        signedBlockProduct (e input address.1 address.2) blocks
  | [], hnonempty, _, _ =>
      False.elim (hnonempty rfl)
  | [block], _, hpositive, e => by
      simpa only [positiveBlockFormula, signedBlockProduct,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        signed_input_exponent] using
        normalizer.eval_ringChoose
          (signedInputExponent input address block.sign)
          block.degree (hpositive block (by simp)) e
  | block :: nextBlock :: blocks, _, hpositive, e => by
      rw [positiveBlockFormula,
        WBForm.eval_mul,
        normalizer.eval_ringChoose,
        signed_input_exponent,
        positive_block_formula normalizer input address
          (nextBlock :: blocks) (by simp)
          (fun next hnext => hpositive next (by simp [hnext])) e]
      simp [signedBlockProduct]
termination_by blocks => blocks.length

/-- Compile any positive-total-degree signed block list to a Claim 8 formula. -/
noncomputable def signedBlockFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (input : ι)
    (address : HEAddres H)
    (blocks : List Block)
    (hdegree : 0 < degreeSum blocks) :
    WBForm H ι (degreeSum blocks * address.1) :=
  (positiveBlockFormula normalizer input address
    (positiveSignedBlocks blocks)
    (by
      intro hnil
      have hzero : degreeSum blocks = 0 := by
        rw [← degree_positive_blocks blocks, hnil]
        rfl
      omega)
    (fun block hblock =>
      degree_pos_blocks hblock)).weaken
        (by rw [degree_positive_blocks])

@[simp]
lemma signed_block_formula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (input : ι)
    (address : HEAddres H)
    (blocks : List Block)
    (hdegree : 0 < degreeSum blocks)
    (e : ι → HEFam H) :
    (signedBlockFormula normalizer input address blocks hdegree).eval e =
      signedBlockProduct (e input address.1 address.2) blocks := by
  rw [signedBlockFormula, WBForm.eval_weaken,
    positive_block_formula,
    signed_positive_blocks]

/-- Compile one weighted signed-block profile to a Claim 8 formula. -/
noncomputable def weightedProfileFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (profile : WBProf)
    (hleft : 0 < profile.profile.leftDegree)
    (hright : 0 < profile.profile.rightDegree) :
    WBForm H ι
      (profile.profile.leftDegree * leftAddress.1 +
        profile.profile.rightDegree * rightAddress.1) :=
  ((signedBlockFormula normalizer leftInput leftAddress
      profile.profile.leftBlocks
      (by simpa [SBProf.leftDegree] using hleft)).mul
    (signedBlockFormula normalizer rightInput rightAddress
      profile.profile.rightBlocks
      (by simpa [SBProf.rightDegree] using hright))
    (by
      simp [SBProf.leftDegree,
        SBProf.rightDegree])).scaleForChoose profile.multiplicity

@[simp]
lemma weighted_profile_formula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (profile : WBProf)
    (hleft : 0 < profile.profile.leftDegree)
    (hright : 0 < profile.profile.rightDegree)
    (e : ι → HEFam H) :
    (weightedProfileFormula normalizer leftInput rightInput
      leftAddress rightAddress profile hleft hright).eval e =
      profile.multiplicity *
        (signedBlockProduct (e leftInput leftAddress.1 leftAddress.2)
          profile.profile.leftBlocks *
        signedBlockProduct (e rightInput rightAddress.1 rightAddress.2)
          profile.profile.rightBlocks) := by
  simp [weightedProfileFormula]

/-- Specializing the two sources to naturals recovers the signed profile coefficient. -/
lemma weighted_formula_cast
    {d M N : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (profile : WBProf)
    (hleft : 0 < profile.profile.leftDegree)
    (hright : 0 < profile.profile.rightDegree)
    (e : ι → HEFam H)
    (heleft : e leftInput leftAddress.1 leftAddress.2 = (M : ℤ))
    (heright : e rightInput rightAddress.1 rightAddress.2 = (N : ℤ)) :
    (weightedProfileFormula normalizer leftInput rightInput
      leftAddress rightAddress profile hleft hright).eval e =
      profile.coefficient M N := by
  rw [weighted_profile_formula, heleft, heright,
    signed_block_cast, signed_block_cast]
  rfl

/-- Sum a homogeneous list of weighted signed-block profiles as one Claim 8 formula. -/
noncomputable def weightedProfilesFormula
    {d leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    (profiles : List WBProf) →
      (∀ profile ∈ profiles,
        profile.profile.leftDegree = leftDegree) →
      (∀ profile ∈ profiles,
        profile.profile.rightDegree = rightDegree) →
      WBForm H ι
        (leftDegree * leftAddress.1 + rightDegree * rightAddress.1)
  | [], _, _ =>
      WBForm.zero H ι
        (leftDegree * leftAddress.1 + rightDegree * rightAddress.1)
  | profile :: profiles, hprofilesLeft, hprofilesRight =>
      ((weightedProfileFormula normalizer leftInput rightInput
        leftAddress rightAddress profile
        (by rw [hprofilesLeft profile (by simp)]; exact hleft)
        (by rw [hprofilesRight profile (by simp)]; exact hright)).weaken
          (by
            rw [hprofilesLeft profile (by simp),
              hprofilesRight profile (by simp)]))
        |>.append
          (weightedProfilesFormula normalizer leftInput rightInput
            leftAddress rightAddress hleft hright profiles
            (fun next hnext => hprofilesLeft next (by simp [hnext]))
            (fun next hnext => hprofilesRight next (by simp [hnext])))

@[simp]
lemma profiles_formula_cast
    {d M N leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    ∀ (profiles : List WBProf)
      (hprofilesLeft :
        ∀ profile ∈ profiles,
          profile.profile.leftDegree = leftDegree)
      (hprofilesRight :
        ∀ profile ∈ profiles,
          profile.profile.rightDegree = rightDegree)
      (e : ι → HEFam H),
      e leftInput leftAddress.1 leftAddress.2 = (M : ℤ) →
      e rightInput rightAddress.1 rightAddress.2 = (N : ℤ) →
      (weightedProfilesFormula normalizer leftInput rightInput
        leftAddress rightAddress hleft hright profiles hprofilesLeft
          hprofilesRight).eval e =
        weightedCoefficientSum M N profiles
  | [], _, _, _, _, _ => by
      simp [weightedProfilesFormula,
        weightedCoefficientSum]
  | profile :: profiles, hprofilesLeft, hprofilesRight, e, heleft, heright => by
      rw [weightedProfilesFormula,
        WBForm.eval_append,
        WBForm.eval_weaken,
        weighted_formula_cast
          normalizer leftInput rightInput leftAddress rightAddress profile
          (by rw [hprofilesLeft profile (by simp)]; exact hleft)
          (by rw [hprofilesRight profile (by simp)]; exact hright)
          e heleft heright,
        profiles_formula_cast
          normalizer leftInput rightInput leftAddress rightAddress hleft hright
          profiles
          (fun next hnext => hprofilesLeft next (by simp [hnext]))
          (fun next hnext => hprofilesRight next (by simp [hnext]))
          e heleft heright]
      rfl

/-- Compile one explicit homogeneous signed-block expression to a Claim 8 formula. -/
noncomputable def claimEightFormula
    {d M N leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (expression :
      HBExpr M N leftDegree rightDegree)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    WBForm H ι
      (leftDegree * leftAddress.1 + rightDegree * rightAddress.1) :=
  weightedProfilesFormula
    (WBForm.chooseNormalizerFamily H
      |>.normalizer ι)
    leftInput rightInput leftAddress rightAddress hleft hright
    expression.profiles expression.profiles_leftDegree
      expression.profiles_rightDegree

@[simp]
lemma claim_eight_formula
    {d M N leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (expression :
      HBExpr M N leftDegree rightDegree)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree)
    (e : ι → HEFam H)
    (heleft : e leftInput leftAddress.1 leftAddress.2 = (M : ℤ))
    (heright : e rightInput rightAddress.1 rightAddress.2 = (N : ℤ)) :
    (claimEightFormula expression leftInput rightInput leftAddress
      rightAddress hleft hright).eval e =
      expression.value := by
  rw [claimEightFormula,
    profiles_formula_cast
      _ leftInput rightInput leftAddress rightAddress hleft hright
      expression.profiles expression.profiles_leftDegree
      expression.profiles_rightDegree e heleft heright]
  exact expression.value_eq.symm

/--
Compile any positive-bidegree admissible-span coefficient directly to a
Claim 8 formula.
-/
noncomputable def claimEightSubmodule
    {d M N leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coefficient : ℤ}
    (hcoefficient :
      coefficient ∈ submodule M N leftDegree rightDegree)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    WBForm H ι
      (leftDegree * leftAddress.1 + rightDegree * rightAddress.1) :=
  claimEightFormula
    (homogeneousExpressionSubmodule hcoefficient)
    leftInput rightInput leftAddress rightAddress hleft hright

@[simp]
lemma claim_eight_cast
    {d M N leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coefficient : ℤ}
    (hcoefficient :
      coefficient ∈ submodule M N leftDegree rightDegree)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree)
    (e : ι → HEFam H)
    (heleft : e leftInput leftAddress.1 leftAddress.2 = (M : ℤ))
    (heright : e rightInput rightAddress.1 rightAddress.2 = (N : ℤ)) :
    (claimEightSubmodule hcoefficient leftInput rightInput
      leftAddress rightAddress hleft hright).eval e =
      coefficient := by
  rw [claimEightSubmodule,
    claim_eight_formula
      _ leftInput rightInput leftAddress rightAddress hleft hright e heleft
        heright,
    homogeneous_expression_value]

end CEComp
end TCTex
end Towers

/-!
# Compiling support avoidance into compatible-grid certificates

The support-expression compiler reduces an overlapping correction grid to
one-sided support-avoidance counts.  This file composes that compiler with
signed-block subtraction: recursively supplied avoidance expressions produce
the certificate for the actual support-compatible correction grid.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CGCompa

open HACoeff
open CCGrida
open CSAggreg
open CSChunks
open CSOverla
open SEComp
open HSPacket

/--
Compile the overlap expression of two represented packets from recursively
supplied support-avoidance expressions.
-/
noncomputable def overlapExpressionAvoidance
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftLeftDegree leftRightDegree)
    (right :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots rightLeftDegree rightRightDegree) :
    OBExpr
      leftTerms rightTerms
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) :=
  OBExpr.ofContainment
    (fun slots =>
      SCExpr.ofAvoidance slots left)
    (fun slots =>
      SCExpr.ofAvoidance slots right)

/--
Compile the rejected overlap packet into the certificate consumed by
support-compatible grid filtering.
-/
noncomputable def overlapCertificateAvoidance
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
    SBCert
      (overlappingCorrectionGrid leftTerms rightTerms)
      (CWord.commutator leftShape rightShape) := by
  apply OBExpr.shapeBlockCertificate
  simpa only [CWord.pair_left_commutator,
    CWord.pair_degree_commutator] using
      overlapExpressionAvoidance left right

/--
For homogeneous parent packets with one genuine compatible witness,
recursive support-avoidance expressions certify the actual filtered
compatible correction grid.
-/
noncomputable def compatibleCertificateAvoidance
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (leftShape rightShape : CWord HPAtom)
    (hleft : ∀ left ∈ leftTerms, left.erasedShape = leftShape)
    (hright : ∀ right ∈ rightTerms, right.erasedShape = rightShape)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness)
    (fullCertificate :
      SBCert
        (DFTerm.correctionGrid leftTerms rightTerms)
        (CWord.commutator leftShape rightShape))
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
    SBCert
      (compatibleCorrectionGrid leftTerms rightTerms)
      (CWord.commutator leftShape rightShape) :=
  compatibleCertificateOverlap
    hleft hright hleftWitness hrightWitness hcompatible fullCertificate
      (overlapCertificateAvoidance leftShape rightShape left right)

/--
Specialization to complete singleton-family packets.  The full Cartesian
certificate is automatic; only recursively compiled one-sided support
avoidance expressions remain as inputs.
-/
noncomputable def realizationCertificateAvoidance
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RPFor leftFamily leftTerms)
    (hright : RPFor rightFamily rightTerms)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness)
    (left :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftFamily.recipe.erasedShape.pairLeftDegree
            leftFamily.recipe.erasedShape.pairRightDegree)
    (right :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots rightFamily.recipe.erasedShape.pairLeftDegree
            rightFamily.recipe.erasedShape.pairRightDegree) :
    SBCert
      (compatibleCorrectionGrid leftTerms rightTerms)
      (leftFamily.correction rightFamily).recipe.erasedShape := by
  rw [BFam.recipe_correction, BRecipe.erasedShape_corr]
  apply compatibleCertificateAvoidance
  · intro leftTerm hleftTerm
    rw [leftTerm.erased_shape_family,
      hleft.family_eq_mem hleftTerm]
  · intro rightTerm hrightTerm
    rw [rightTerm.erased_shape_family,
      hright.family_eq_mem hrightTerm]
  · exact hleftWitness
  · exact hrightWitness
  · exact hcompatible
  · simpa only [BFam.recipe_correction,
      BRecipe.erasedShape_corr] using
        correctionGridCertificate hleft hright
  · exact left
  · exact right

end CGCompa
end TCTex
end Towers

/-!
# Substituting arbitrary formulas into homogeneous signed-block packets

Compatible support-pattern counting naturally produces finite lists of
signed generalized-binomial profiles independent of the source
multiplicities.  This file packages that global object and substitutes
arbitrary Claim 8 formulas for its two abstract sources.

The result is the signed-profile analogue of positive `BRecipe`
substitution.  It also attaches the compiled coefficient to the corresponding
bound Hall word as one symbolic polynomial factor.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CFSubsti

universe u

open HACoeff
open CSAggreg
open CEAlg
open CEComp

/-- Scale one parent formula by the sign of a source block. -/
def signedFormula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (sign : Sign) :
    WBForm H ι targetWeight :=
  formula.scaleForChoose sign.intValue

@[simp]
lemma eval_signedFormula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (sign : Sign)
    (e : ι → HEFam H) :
    (signedFormula formula sign).eval e =
      sign.intValue * formula.eval e := by
  simp [signedFormula]

/--
Substitute one parent formula into a nonempty list of positive-degree signed
blocks.
-/
noncomputable def positiveSubstitutionFormula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (formula : WBForm H ι targetWeight) :
    (blocks : List Block) →
      blocks ≠ [] →
        (∀ block ∈ blocks, 0 < block.degree) →
          WBForm H ι (degreeSum blocks * targetWeight)
  | [], hnonempty, _ =>
      False.elim (hnonempty rfl)
  | [block], _, hpositive =>
      normalizer.ringChoose
        (signedFormula formula block.sign)
        block.degree
        (hpositive block (by simp))
  | block :: nextBlock :: blocks, _, hpositive =>
      (normalizer.ringChoose
        (signedFormula formula block.sign)
        block.degree
        (hpositive block (by simp))).mul
          (positiveSubstitutionFormula normalizer formula
            (nextBlock :: blocks) (by simp)
            (fun next hnext => hpositive next (by simp [hnext])))
          (by simp [degreeSum, Nat.add_mul])
termination_by blocks => blocks.length

@[simp]
lemma positive_substitution_formula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (formula : WBForm H ι targetWeight) :
    ∀ (blocks : List Block)
      (hnonempty : blocks ≠ [])
      (hpositive : ∀ block ∈ blocks, 0 < block.degree)
      (e : ι → HEFam H),
      (positiveSubstitutionFormula normalizer formula
        blocks hnonempty hpositive).eval e =
        signedBlockProduct (formula.eval e) blocks
  | [], hnonempty, _, _ =>
      False.elim (hnonempty rfl)
  | [block], _, hpositive, e => by
      simpa only [positiveSubstitutionFormula, signedBlockProduct,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        eval_signedFormula] using
        normalizer.eval_ringChoose
          (signedFormula formula block.sign)
          block.degree (hpositive block (by simp)) e
  | block :: nextBlock :: blocks, _, hpositive, e => by
      rw [positiveSubstitutionFormula,
        WBForm.eval_mul,
        normalizer.eval_ringChoose,
        eval_signedFormula,
        positive_substitution_formula normalizer formula
          (nextBlock :: blocks) (by simp)
          (fun next hnext => hpositive next (by simp [hnext])) e]
      simp [signedBlockProduct]
termination_by blocks => blocks.length

/-- Substitute one parent formula into any positive-total-degree signed block list. -/
noncomputable def signedSubstitutionFormula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (formula : WBForm H ι targetWeight)
    (blocks : List Block)
    (hdegree : 0 < degreeSum blocks) :
    WBForm H ι (degreeSum blocks * targetWeight) :=
  (positiveSubstitutionFormula normalizer formula
    (positiveSignedBlocks blocks)
    (by
      intro hnil
      have hzero : degreeSum blocks = 0 := by
        rw [← degree_positive_blocks blocks, hnil]
        rfl
      omega)
    (fun block hblock =>
      degree_pos_blocks hblock)).weaken
        (by rw [degree_positive_blocks])

@[simp]
lemma block_substitution_formula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (formula : WBForm H ι targetWeight)
    (blocks : List Block)
    (hdegree : 0 < degreeSum blocks)
    (e : ι → HEFam H) :
    (signedSubstitutionFormula normalizer formula blocks hdegree).eval e =
      signedBlockProduct (formula.eval e) blocks := by
  rw [signedSubstitutionFormula,
    WBForm.eval_weaken,
    positive_substitution_formula,
    signed_positive_blocks]

/-- Evaluate one weighted signed profile at arbitrary integral source values. -/
def weightedProfileValue
    (profile : WBProf)
    (left right : ℤ) :
    ℤ :=
  profile.multiplicity *
    (signedBlockProduct left profile.profile.leftBlocks *
      signedBlockProduct right profile.profile.rightBlocks)

/-- A multiplicity-independent homogeneous packet of signed profiles. -/
structure HFPkt
    (leftDegree rightDegree : ℕ) where
  profiles :
    List WBProf
  profiles_leftDegree :
    ∀ profile ∈ profiles,
      profile.profile.leftDegree = leftDegree
  profiles_rightDegree :
    ∀ profile ∈ profiles,
      profile.profile.rightDegree = rightDegree

namespace HFPkt

/-- Evaluate a global homogeneous signed-profile packet. -/
def value
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    ℤ :=
  (packet.profiles.map fun profile =>
    weightedProfileValue profile left right).sum

@[simp]
lemma value_natCast
    {leftDegree rightDegree M N : ℕ}
    (packet : HFPkt leftDegree rightDegree) :
    packet.value (M : ℤ) (N : ℤ) =
      weightedCoefficientSum M N packet.profiles := by
  simp [value, weightedProfileValue,
    weightedCoefficientSum,
    WBProf.coefficient,
    SBProf.coefficient]

/-- Forget the concrete multiplicities of one explicit homogeneous expression. -/
def ofExpression
    {M N leftDegree rightDegree : ℕ}
    (expression :
      HBExpr M N leftDegree rightDegree) :
    HFPkt leftDegree rightDegree where
  profiles := expression.profiles
  profiles_leftDegree := expression.profiles_leftDegree
  profiles_rightDegree := expression.profiles_rightDegree

@[simp]
lemma value_expression_cast
    {M N leftDegree rightDegree : ℕ}
    (expression :
      HBExpr M N leftDegree rightDegree) :
    (ofExpression expression).value (M : ℤ) (N : ℤ) =
      expression.value := by
  rw [value_natCast]
  exact expression.value_eq.symm

end HFPkt

/-- Substitute two parent formulas into one weighted signed profile. -/
noncomputable def weightedSubstitutionFormula
    {d leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (profile : WBProf)
    (hleft : 0 < profile.profile.leftDegree)
    (hright : 0 < profile.profile.rightDegree) :
    WBForm H ι
      (profile.profile.leftDegree * leftWeight +
        profile.profile.rightDegree * rightWeight) :=
  ((signedSubstitutionFormula normalizer left
      profile.profile.leftBlocks
      (by simpa [SBProf.leftDegree] using hleft)).mul
    (signedSubstitutionFormula normalizer right
      profile.profile.rightBlocks
      (by simpa [SBProf.rightDegree] using hright))
    (by
      simp [SBProf.leftDegree,
        SBProf.rightDegree])).scaleForChoose profile.multiplicity

@[simp]
lemma weighted_substitution_formula
    {d leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (profile : WBProf)
    (hleft : 0 < profile.profile.leftDegree)
    (hright : 0 < profile.profile.rightDegree)
    (e : ι → HEFam H) :
    (weightedSubstitutionFormula normalizer left right
      profile hleft hright).eval e =
      weightedProfileValue profile (left.eval e) (right.eval e) := by
  simp [weightedSubstitutionFormula,
    weightedProfileValue]

/-- Sum a homogeneous signed-profile list after substituting two parent formulas. -/
noncomputable def profilesSubstitutionFormula
    {d leftDegree rightDegree leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    (profiles : List WBProf) →
      (∀ profile ∈ profiles,
        profile.profile.leftDegree = leftDegree) →
      (∀ profile ∈ profiles,
        profile.profile.rightDegree = rightDegree) →
      WBForm H ι
        (leftDegree * leftWeight + rightDegree * rightWeight)
  | [], _, _ =>
      WBForm.zero H ι
        (leftDegree * leftWeight + rightDegree * rightWeight)
  | profile :: profiles, hprofilesLeft, hprofilesRight =>
      ((weightedSubstitutionFormula normalizer left right
        profile
        (by rw [hprofilesLeft profile (by simp)]; exact hleft)
        (by rw [hprofilesRight profile (by simp)]; exact hright)).weaken
          (by
            rw [hprofilesLeft profile (by simp),
              hprofilesRight profile (by simp)]))
        |>.append
          (profilesSubstitutionFormula normalizer left right
            hleft hright profiles
            (fun next hnext => hprofilesLeft next (by simp [hnext]))
            (fun next hnext => hprofilesRight next (by simp [hnext])))

@[simp]
lemma profiles_substitution_formula
    {d leftDegree rightDegree leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    ∀ (profiles : List WBProf)
      (hprofilesLeft :
        ∀ profile ∈ profiles,
          profile.profile.leftDegree = leftDegree)
      (hprofilesRight :
        ∀ profile ∈ profiles,
          profile.profile.rightDegree = rightDegree)
      (e : ι → HEFam H),
      (profilesSubstitutionFormula normalizer left right
        hleft hright profiles hprofilesLeft hprofilesRight).eval e =
        (profiles.map fun profile =>
          weightedProfileValue profile
            (left.eval e) (right.eval e)).sum
  | [], _, _, _ => by
      simp [profilesSubstitutionFormula]
  | profile :: profiles, hprofilesLeft, hprofilesRight, e => by
      rw [profilesSubstitutionFormula,
        WBForm.eval_append,
        WBForm.eval_weaken,
        weighted_substitution_formula,
        profiles_substitution_formula
          normalizer left right hleft hright profiles
          (fun next hnext => hprofilesLeft next (by simp [hnext]))
          (fun next hnext => hprofilesRight next (by simp [hnext])) e]
      rfl

namespace HFPkt

/-- Substitute arbitrary parent formulas into one global homogeneous packet. -/
noncomputable def toFormula
    {d leftDegree rightDegree leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : HFPkt leftDegree rightDegree)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    WBForm H ι
      (leftDegree * leftWeight + rightDegree * rightWeight) :=
  profilesSubstitutionFormula normalizer left right
    hleft hright packet.profiles packet.profiles_leftDegree
      packet.profiles_rightDegree

@[simp]
lemma eval_toFormula
    {d leftDegree rightDegree leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : HFPkt leftDegree rightDegree)
    (normalizer : WBForm.RCNormal H ι)
    (left : WBForm H ι leftWeight)
    (right : WBForm H ι rightWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree)
    (e : ι → HEFam H) :
    (packet.toFormula normalizer left right hleft hright).eval e =
      packet.value (left.eval e) (right.eval e) := by
  rw [toFormula, profiles_substitution_formula]
  rfl

end HFPkt

/-- One erased Hall word together with its global homogeneous signed-profile packet. -/
structure RFPkt where
  word :
    CWord HPAtom
  positive :
    word.PBPos
  profiles :
    HFPkt
      word.pairLeftDegree word.pairRightDegree

namespace RFPkt

/-- Substitute two symbolic parent words into the erased Hall word. -/
def boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (left right : SPFactor H ι) :
    CWord (HEAddres H) :=
  CWord.hallPairBind left.word right.word packet.word

@[simp]
lemma weight_boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (left right : SPFactor H ι) :
    (packet.boundWord left right).weight HEAddres.weight =
      packet.word.pairLeftDegree *
          left.word.weight HEAddres.weight +
        packet.word.pairRightDegree *
          right.word.weight HEAddres.weight := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree]

/-- Compile the signed-profile coefficient after substituting two symbolic parents. -/
noncomputable def coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    WBForm H ι
      ((packet.boundWord left right).weight HEAddres.weight) :=
  (packet.profiles.toFormula normalizer left.coefficient right.coefficient
    packet.positive.1 packet.positive.2).weaken (by
      rw [packet.weight_boundWord])

@[simp]
lemma eval_coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (e : ι → HEFam H) :
    (packet.coefficientFormula normalizer left right).eval e =
      packet.profiles.value
        (left.coefficient.eval e) (right.coefficient.eval e) := by
  simp [coefficientFormula]

/-- Attach a global signed-profile packet as one symbolic Hall polynomial factor. -/
noncomputable def symbolicFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    SPFactor H ι where
  word := packet.boundWord left right
  coefficient := packet.coefficientFormula normalizer left right

@[simp]
lemma word_symbolicFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    (packet.symbolicFactor normalizer left right).word =
      packet.boundWord left right :=
  rfl

@[simp]
lemma coefficient_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (e : ι → HEFam H) :
    (packet.symbolicFactor normalizer left right).coefficient.eval e =
      packet.profiles.value
        (left.coefficient.eval e) (right.coefficient.eval e) :=
  packet.eval_coefficientFormula normalizer left right e

end RFPkt

end CFSubsti
end TCTex
end Towers

/-!
# Algebra of multiplicity-independent signed-block formula packets

Concrete support-pattern compilation packages profile lists together with their
value at one natural multiplicity pair.  The profile lists themselves are
global formulas.  This file gives those formulas the same zero, addition,
scaling, multiplication, and finite-sum operations as concrete expressions,
then proves that forgetting a concrete expression commutes with the algebra.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CFAlg

open CEAlg
open CFSubsti
open CSAlg
open CSAggreg
open CEComp

namespace FPkt

/-- Zero multiplicity-independent packet in any homogeneous bidegree. -/
def zero
    (leftDegree rightDegree : ℕ) :
    HFPkt leftDegree rightDegree where
  profiles := []
  profiles_leftDegree := by simp
  profiles_rightDegree := by simp

/-- Sum of two multiplicity-independent packets in the same bidegree. -/
def add
    {leftDegree rightDegree : ℕ}
    (left right :
      HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree where
  profiles := left.profiles ++ right.profiles
  profiles_leftDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact left.profiles_leftDegree profile hprofile
    · exact right.profiles_leftDegree profile hprofile
  profiles_rightDegree := by
    intro profile hprofile
    rcases List.mem_append.mp hprofile with hprofile | hprofile
    · exact left.profiles_rightDegree profile hprofile
    · exact right.profiles_rightDegree profile hprofile

/-- Integral scalar multiple of one multiplicity-independent packet. -/
def scale
    {leftDegree rightDegree : ℕ}
    (factor : ℤ)
    (packet :
      HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree where
  profiles := scaleWeightedProfiles factor packet.profiles
  profiles_leftDegree :=
    scale_profiles_degree
      factor packet.profiles leftDegree packet.profiles_leftDegree
  profiles_rightDegree :=
    scale_weighted_profiles
      factor packet.profiles rightDegree packet.profiles_rightDegree

/-- Product of two multiplicity-independent packets, with summed bidegree. -/
def multiply
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      HFPkt leftLeftDegree leftRightDegree)
    (right :
      HFPkt rightLeftDegree rightRightDegree) :
    HFPkt
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) where
  profiles :=
    multiplyWeightedProfiles left.profiles right.profiles
  profiles_leftDegree :=
    multiply_profiles_degree
      left.profiles right.profiles leftLeftDegree rightLeftDegree
        left.profiles_leftDegree right.profiles_leftDegree
  profiles_rightDegree :=
    multiply_weighted_profiles
      left.profiles right.profiles leftRightDegree rightRightDegree
        left.profiles_rightDegree right.profiles_rightDegree

/-- Finite sum of multiplicity-independent packets in one bidegree. -/
def sum
    {leftDegree rightDegree : ℕ} :
    List (HFPkt leftDegree rightDegree) →
      HFPkt leftDegree rightDegree
  | [] =>
      zero leftDegree rightDegree
  | packet :: packets =>
      add packet (sum packets)

/-- Finite sum of a multiplicity-independent packet family indexed by a finset. -/
noncomputable def finsetSum
    {ι : Type*}
    {leftDegree rightDegree : ℕ}
    (indices : Finset ι)
    (packet :
      ι → HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree :=
  sum (indices.toList.map packet)

@[simp]
lemma value_zero
    (leftDegree rightDegree : ℕ)
    (left right : ℤ) :
    (zero leftDegree rightDegree).value left right = 0 := by
  rfl

@[simp]
lemma value_add
    {leftDegree rightDegree : ℕ}
    (leftPacket rightPacket :
      HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (add leftPacket rightPacket).value left right =
      leftPacket.value left right + rightPacket.value left right := by
  simp [add, HFPkt.value, List.sum_append]

@[simp]
lemma weighted_value_scale
    (factor : ℤ)
    (profile : WBProf)
    (left right : ℤ) :
    weightedProfileValue
        (scaleWeightedProfile factor profile) left right =
      factor * weightedProfileValue profile left right := by
  simp [weightedProfileValue, scaleWeightedProfile,
    mul_assoc]

@[simp]
lemma weighted_profile_scale
    (factor : ℤ)
    (left right : ℤ) :
    ∀ profiles : List WBProf,
      ((scaleWeightedProfiles factor profiles).map fun profile =>
          weightedProfileValue profile left right).sum =
        factor *
          (profiles.map fun profile =>
            weightedProfileValue profile left right).sum
  | [] => by simp [scaleWeightedProfiles]
  | profile :: profiles => by
      change
        weightedProfileValue
              (scaleWeightedProfile factor profile) left right +
            ((scaleWeightedProfiles factor profiles).map
              fun next =>
                weightedProfileValue next left right).sum =
          factor *
            (weightedProfileValue profile left right +
              (profiles.map fun next =>
                weightedProfileValue next left right).sum)
      rw [
        weighted_value_scale,
        weighted_profile_scale factor left right profiles]
      ring

@[simp]
lemma value_scale
    {leftDegree rightDegree : ℕ}
    (factor : ℤ)
    (packet :
      HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (scale factor packet).value left right =
      factor * packet.value left right := by
  exact weighted_profile_scale
    factor left right packet.profiles

@[simp]
lemma weighted_value_multiply
    (leftProfile rightProfile : WBProf)
    (left right : ℤ) :
    weightedProfileValue
        (multiplyWeightedProfile leftProfile rightProfile)
        left right =
      weightedProfileValue leftProfile left right *
        weightedProfileValue rightProfile left right := by
  simp [weightedProfileValue, multiplyWeightedProfile,
    multiplyBlockProfile, signedBlockProduct, List.map_append,
    List.prod_append]
  ring

@[simp]
lemma weighted_multiply_left
    (leftProfile : WBProf)
    (left right : ℤ) :
    ∀ profiles : List WBProf,
      ((profiles.map (multiplyWeightedProfile leftProfile)).map
          fun profile =>
            weightedProfileValue profile left right).sum =
        weightedProfileValue leftProfile left right *
          (profiles.map fun profile =>
            weightedProfileValue profile left right).sum
  | [] => by simp
  | profile :: profiles => by
      rw [List.map_cons, List.map_cons, List.sum_cons, List.map_cons,
        List.sum_cons, weighted_value_multiply,
        weighted_multiply_left
          leftProfile left right profiles]
      ring

@[simp]
lemma weighted_profile_multiply
    (left right : ℤ)
    (leftProfiles rightProfiles : List WBProf) :
    ((multiplyWeightedProfiles leftProfiles rightProfiles).map
        fun profile =>
          weightedProfileValue profile left right).sum =
      (leftProfiles.map fun profile =>
          weightedProfileValue profile left right).sum *
        (rightProfiles.map fun profile =>
          weightedProfileValue profile left right).sum := by
  induction leftProfiles with
  | nil =>
      simp [multiplyWeightedProfiles]
  | cons leftProfile leftProfiles ih =>
      have htail :
          ((leftProfiles.flatMap fun next =>
              rightProfiles.map
                (multiplyWeightedProfile next)).map
                fun profile =>
                  weightedProfileValue profile left right).sum =
            (leftProfiles.map fun profile =>
                weightedProfileValue profile left right).sum *
              (rightProfiles.map fun profile =>
                weightedProfileValue profile left right).sum := by
        simpa only [multiplyWeightedProfiles] using ih
      simp only [multiplyWeightedProfiles, List.flatMap_cons,
        List.map_append, List.sum_append,
        weighted_multiply_left,
        htail, List.map_cons, List.sum_cons]
      ring

@[simp]
lemma value_multiply
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (leftPacket :
      HFPkt leftLeftDegree leftRightDegree)
    (rightPacket :
      HFPkt rightLeftDegree rightRightDegree)
    (left right : ℤ) :
    (multiply leftPacket rightPacket).value left right =
      leftPacket.value left right * rightPacket.value left right := by
  exact weighted_profile_multiply
    left right leftPacket.profiles rightPacket.profiles

@[simp]
lemma value_sum
    {leftDegree rightDegree : ℕ}
    (packets :
      List (HFPkt leftDegree rightDegree))
    (left right : ℤ) :
    (sum packets).value left right =
      (packets.map fun packet => packet.value left right).sum := by
  induction packets with
  | nil =>
      rfl
  | cons packet packets ih =>
      simp [sum, ih]

@[simp]
lemma value_finsetSum
    {ι : Type*}
    {leftDegree rightDegree : ℕ}
    (indices : Finset ι)
    (packet :
      ι → HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (finsetSum indices packet).value left right =
      ∑ index ∈ indices, (packet index).value left right := by
  simp [finsetSum]

@[simp]
lemma ofExpression_zero
    (M N leftDegree rightDegree : ℕ) :
    HFPkt.ofExpression
        (HBExpr.zero M N leftDegree rightDegree) =
      zero leftDegree rightDegree := by
  rfl

@[simp]
lemma ofExpression_add
    {M N leftDegree rightDegree : ℕ}
    (left right :
      HBExpr M N leftDegree rightDegree) :
    HFPkt.ofExpression (left.add right) =
      add
        (HFPkt.ofExpression left)
        (HFPkt.ofExpression right) := by
  rfl

@[simp]
lemma ofExpression_scale
    {M N leftDegree rightDegree : ℕ}
    (factor : ℤ)
    (expression :
      HBExpr M N leftDegree rightDegree) :
    HFPkt.ofExpression
        (expression.scale factor) =
      scale factor
        (HFPkt.ofExpression expression) := by
  rfl

@[simp]
lemma ofExpression_multiply
    {M N leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      HBExpr M N leftLeftDegree leftRightDegree)
    (right :
      HBExpr M N rightLeftDegree rightRightDegree) :
    HFPkt.ofExpression
        (left.multiply right) =
      multiply
        (HFPkt.ofExpression left)
        (HFPkt.ofExpression right) := by
  rfl

@[simp]
lemma ofExpression_sum
    {M N leftDegree rightDegree : ℕ}
    (expressions :
      List (HBExpr M N leftDegree rightDegree)) :
    HFPkt.ofExpression
        (HBExpr.sum expressions) =
      sum
        (expressions.map
          HFPkt.ofExpression) := by
  induction expressions with
  | nil =>
      rfl
  | cons expression expressions ih =>
      simp [HBExpr.sum, sum, ih]

@[simp]
lemma expression_finset_sum
    {ι : Type*}
    {M N leftDegree rightDegree : ℕ}
    (indices : Finset ι)
    (expression :
      ι → HBExpr M N leftDegree rightDegree) :
    HFPkt.ofExpression
        (HBExpr.finsetSum indices expression) =
      finsetSum indices fun index =>
        HFPkt.ofExpression
          (expression index) := by
  simp [HBExpr.finsetSum, finsetSum,
    List.map_map, Function.comp_def]

end FPkt

end CFAlg
end TCTex
end Towers

/-!
# Signed-profile packet expansions

A global Hall-Petresco recollection packet can be expressed directly as an
ordered list of erased Hall words carrying homogeneous signed-profile
packets.  This is more general than a positive `BRecipe` list and is the
natural symbolic output of support-pattern inclusion-exclusion.

This file compiles such packets into the arbitrary-parent correction
expansions consumed by signed semantic collection.  The strict higher-weight
bounds follow from the positive Hall bidegree recorded by each erased word.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CFExp

universe u v

open scoped commutatorElement

open HACoeff
open CFSubsti

/-- Evaluate an attached signed-profile symbolic factor. -/
@[simp]
lemma eval_symbolicFactor
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (e : ι → HEFam H) :
    (packet.symbolicFactor normalizer left right).eval (n := n) e =
      packet.word.eval
          (HPAtom.eval
            (left.wordValue (n := n)) (right.wordValue (n := n))) ^
        packet.profiles.value
          (left.coefficient.eval e) (right.coefficient.eval e) := by
  rw [SPFactor.eval,
    packet.coefficient_symbolic_factor]
  exact congrArg
    (fun g =>
      g ^
        packet.profiles.value
          (left.coefficient.eval e) (right.coefficient.eval e))
    (CWord.eval_pair_bind
      HEAddres.freeLowerTruncation
      left.word right.word packet.word)

/-- Every attached signed-profile factor is strictly above its left parent. -/
lemma left_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    left.word.weight HEAddres.weight <
      (packet.symbolicFactor normalizer left right).word.weight
        HEAddres.weight := by
  rw [packet.word_symbolicFactor, packet.weight_boundWord]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ packet.positive.1) ?_
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos packet.positive.2 right.word_weight_pos)

/-- Every attached signed-profile factor is strictly above its right parent. -/
lemma right_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : RFPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    right.word.weight HEAddres.weight <
      (packet.symbolicFactor normalizer left right).word.weight
        HEAddres.weight := by
  rw [packet.word_symbolicFactor, packet.weight_boundWord]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ packet.positive.2) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos packet.positive.1 left.word_weight_pos)

/-- Attach an ordered list of global signed-profile packets to two symbolic parents. -/
noncomputable def symbolicFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (packets : List RFPkt)
    (left right : SPFactor H ι) :
    List (SPFactor H ι) :=
  packets.map fun packet => packet.symbolicFactor normalizer left right

/-- Evaluate an attached ordered signed-profile packet list. -/
lemma listSymbolicFactors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (packets : List RFPkt)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (symbolicFactors normalizer packets left right) =
      (packets.map fun packet =>
        packet.word.eval
            (HPAtom.eval
              (left.wordValue (n := n)) (right.wordValue (n := n))) ^
          packet.profiles.value
            (left.coefficient.eval e) (right.coefficient.eval e)).prod := by
  induction packets with
  | nil =>
      rfl
  | cons packet packets ih =>
      change
        (packet.symbolicFactor normalizer left right).eval e *
            SPFactor.listEval e
              (symbolicFactors normalizer packets left right) =
          _ * _
      rw [eval_symbolicFactor packet, ih]
      rfl

/-- Every attached symbolic factor remembers its signed-profile packet. -/
lemma packet_symbolic_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {normalizer : WBForm.RCNormal H ι}
    {packets : List RFPkt}
    {left right x : SPFactor H ι}
    (hx : x ∈ symbolicFactors normalizer packets left right) :
    ∃ packet ∈ packets,
      x = packet.symbolicFactor normalizer left right := by
  rcases List.mem_map.mp hx with ⟨packet, hpacket, rfl⟩
  exact ⟨packet, hpacket, rfl⟩

/--
A universal ordered signed-profile Hall-Petresco packet valid for arbitrary
integral source exponents in every group.
-/
structure UAPkt where
  packets :
    List RFPkt
  listEval_eq :
    ∀ {G : Type v} [Group G]
      (left right : G)
      (leftExponent rightExponent : ℤ),
        (packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
A cutoff-specific ordered signed-profile Hall-Petresco packet in one free
lower-central truncation.
-/
structure TAInt
    (d n : ℕ) where
  packets :
    List RFPkt
  listEval_eq :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
        (packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace TAInt

/--
Signed-profile substitution compiles one cutoff packet into an
arbitrary-parent polynomial correction expansion.
-/
noncomputable def toCorrectionExpansion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : TAInt d n)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    SCExp (n := n) left right where
  factors := symbolicFactors normalizer packet.packets left right
  listEval_eq e := by
    rw [listSymbolicFactors]
    simpa [SPFactor.eval] using
      packet.listEval_eq (left.wordValue (n := n)) (right.wordValue (n := n))
        (left.coefficient.eval e) (right.coefficient.eval e)
  word_weight_left := by
    intro x hx
    rcases packet_symbolic_factors hx with
      ⟨nextPacket, _hnextPacket, rfl⟩
    exact left_symbolic_factor
      nextPacket normalizer left right
  word_weight_right := by
    intro x hx
    rcases packet_symbolic_factors hx with
      ⟨nextPacket, _hnextPacket, rfl⟩
    exact right_symbolic_factor
      nextPacket normalizer left right

/--
A cutoff signed-profile packet and uniform formula arithmetic supply the
correction factory used in every signed support stratum.
-/
noncomputable def supportedWordFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : TAInt d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (lowerWeight : ℕ) :
    SSFtrya
      (n := n) H lowerWeight where
  expansion left right _hleft _hright :=
    packet.toCorrectionExpansion (normalizers.normalizer _) left right

end TAInt

namespace UAPkt

/-- Every universal signed-profile packet specializes to each lower-central cutoff. -/
def truncatedAllIntegral
    {d n : ℕ}
    (packet : UAPkt) :
    TAInt d n where
  packets := packet.packets
  listEval_eq left right leftExponent rightExponent :=
    packet.listEval_eq left right leftExponent rightExponent

/--
Universal signed-profile substitution compiles directly to an
arbitrary-parent polynomial correction expansion.
-/
noncomputable def toCorrectionExpansion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : UAPkt)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    SCExp (n := n) left right :=
  (packet.truncatedAllIntegral (d := d) (n := n))
    |>.toCorrectionExpansion normalizer left right

end UAPkt

end CFExp
end TCTex
end Towers

/-!
# Integral extensionality for homogeneous signed-block packets

Signed-block profile packets are syntax for bivariate integer-valued
polynomials.  Their syntax is not canonical: different finite profile lists
can define the same coefficient function.  This file records the semantic
extensionality theorem needed by the cutoff-full collector: agreement on the
natural quadrant implies agreement at every pair of integral exponents.

The proof is deliberately elementary.  After fixing either source exponent,
each block product is represented by a finite product of generalized-choose
polynomials over `ℚ`.  Polynomial extensionality on natural inputs can then be
applied once in each variable.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  CFSubsti

open
  HACoeff
open
  CSAggreg
open
  CEAlg
open
  CEComp
open
  CFSubsti

/--
The rational polynomial represented by a signed block list in one source
exponent.
-/
noncomputable def signedBlockPolynomial
    (blocks : List Block) :
    Polynomial ℚ :=
  match blocks with
  | [] => 1
  | block :: blocks =>
      chooseScalePolynomial block.sign.intValue block.degree *
        signedBlockPolynomial blocks

/--
The signed block-list polynomial evaluates to the corresponding generalized
binomial product at every integral input.
-/
@[simp]
lemma signed_block_int
    (blocks : List Block)
    (z : ℤ) :
    (signedBlockPolynomial blocks).eval (z : ℚ) =
      ((signedBlockProduct z blocks : ℤ) : ℚ) := by
  induction blocks with
  | nil =>
      simp [signedBlockPolynomial, signedBlockProduct]
  | cons block blocks ih =>
      rw [signedBlockPolynomial, Polynomial.eval_mul,
        ring_scale_int, ih]
      simp [signedBlockProduct]

/--
The degree of a signed block-list polynomial is bounded by the total number
of selected labels recorded by its blocks.
-/
lemma nat_degree_block
    (blocks : List Block) :
    (signedBlockPolynomial blocks).natDegree ≤ degreeSum blocks := by
  induction blocks with
  | nil =>
      simp [signedBlockPolynomial, degreeSum]
  | cons block blocks ih =>
      rw [signedBlockPolynomial]
      exact Polynomial.natDegree_mul_le.trans
        (by
          calc
            (chooseScalePolynomial
                  block.sign.intValue block.degree).natDegree +
                (signedBlockPolynomial blocks).natDegree ≤
              block.degree + degreeSum blocks :=
                Nat.add_le_add
                  (choose_scale_polynomial
                    block.sign.intValue block.degree)
                  ih
            _ = degreeSum (block :: blocks) := by
              simp [degreeSum])

namespace HFPkt

/--
After fixing the right source exponent, a homogeneous packet is a rational
polynomial in the left source exponent.
-/
noncomputable def leftPolynomial
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (right : ℤ) :
    Polynomial ℚ :=
  (packet.profiles.map fun profile =>
    Polynomial.C
        ((profile.multiplicity *
          signedBlockProduct right profile.profile.rightBlocks : ℤ) : ℚ) *
      signedBlockPolynomial profile.profile.leftBlocks).sum

/--
The left-variable polynomial of a finite homogeneous profile list has degree
bounded by its common left degree.
-/
lemma nat_sum_terms
    (profiles : List WBProf)
    (leftDegree : ℕ)
    (hprofiles :
      ∀ profile ∈ profiles,
        profile.profile.leftDegree = leftDegree)
    (right : ℤ) :
    ((profiles.map fun profile =>
      Polynomial.C
          ((profile.multiplicity *
            signedBlockProduct right profile.profile.rightBlocks : ℤ) : ℚ) *
        signedBlockPolynomial profile.profile.leftBlocks).sum).natDegree ≤
      leftDegree := by
  induction profiles with
  | nil =>
      simp
  | cons profile profiles ih =>
      rw [List.map_cons, List.sum_cons]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le
          (Polynomial.natDegree_mul_le.trans
            (by
              calc
                (Polynomial.C
                      ((profile.multiplicity *
                        signedBlockProduct right
                          profile.profile.rightBlocks : ℤ) : ℚ)).natDegree +
                    (signedBlockPolynomial
                      profile.profile.leftBlocks).natDegree ≤
                  0 + degreeSum profile.profile.leftBlocks :=
                    Nat.add_le_add
                      (by rw [Polynomial.natDegree_C])
                      (nat_degree_block
                        profile.profile.leftBlocks)
                _ = leftDegree := by
                  simpa [SBProf.leftDegree] using
                    hprofiles profile (by simp)))
          (ih (fun next hnext =>
            hprofiles next (by simp [hnext]))))

/--
The packet polynomial in the left source exponent has degree bounded by the
packet's Hall left degree.
-/
lemma nat_degree_left
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (right : ℤ) :
    (packet.leftPolynomial right).natDegree ≤ leftDegree := by
  exact
    nat_sum_terms packet.profiles leftDegree
      packet.profiles_leftDegree right

/--
The left-variable packet polynomial evaluates to the signed packet value.
-/
@[simp]
lemma eval_left_int
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (packet.leftPolynomial right).eval (left : ℚ) =
      ((packet.value left right : ℤ) : ℚ) := by
  unfold leftPolynomial value
  induction packet.profiles with
  | nil =>
      simp
  | cons profile profiles ih =>
      simp only [List.map_cons, List.sum_cons, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C,
        signed_block_int,
        Int.cast_add]
      rw [ih]
      simp only [weightedProfileValue, Int.cast_mul]
      ring

/--
After fixing the left source exponent, a homogeneous packet is a rational
polynomial in the right source exponent.
-/
noncomputable def rightPolynomial
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (left : ℤ) :
    Polynomial ℚ :=
  (packet.profiles.map fun profile =>
    Polynomial.C
        ((profile.multiplicity *
          signedBlockProduct left profile.profile.leftBlocks : ℤ) : ℚ) *
      signedBlockPolynomial profile.profile.rightBlocks).sum

/--
The right-variable polynomial of a finite homogeneous profile list has degree
bounded by its common right degree.
-/
lemma nat_degree_terms
    (profiles : List WBProf)
    (rightDegree : ℕ)
    (hprofiles :
      ∀ profile ∈ profiles,
        profile.profile.rightDegree = rightDegree)
    (left : ℤ) :
    ((profiles.map fun profile =>
      Polynomial.C
          ((profile.multiplicity *
            signedBlockProduct left profile.profile.leftBlocks : ℤ) : ℚ) *
        signedBlockPolynomial profile.profile.rightBlocks).sum).natDegree ≤
      rightDegree := by
  induction profiles with
  | nil =>
      simp
  | cons profile profiles ih =>
      rw [List.map_cons, List.sum_cons]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le
          (Polynomial.natDegree_mul_le.trans
            (by
              calc
                (Polynomial.C
                      ((profile.multiplicity *
                        signedBlockProduct left
                          profile.profile.leftBlocks : ℤ) : ℚ)).natDegree +
                    (signedBlockPolynomial
                      profile.profile.rightBlocks).natDegree ≤
                  0 + degreeSum profile.profile.rightBlocks :=
                    Nat.add_le_add
                      (by rw [Polynomial.natDegree_C])
                      (nat_degree_block
                        profile.profile.rightBlocks)
                _ = rightDegree := by
                  simpa [SBProf.rightDegree] using
                    hprofiles profile (by simp)))
          (ih (fun next hnext =>
            hprofiles next (by simp [hnext]))))

/--
The packet polynomial in the right source exponent has degree bounded by the
packet's Hall right degree.
-/
lemma nat_degree_polynomial
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (left : ℤ) :
    (packet.rightPolynomial left).natDegree ≤ rightDegree := by
  exact
    nat_degree_terms packet.profiles rightDegree
      packet.profiles_rightDegree left

/--
The right-variable packet polynomial evaluates to the signed packet value.
-/
@[simp]
lemma eval_right_int
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (packet.rightPolynomial left).eval (right : ℚ) =
      ((packet.value left right : ℤ) : ℚ) := by
  unfold rightPolynomial value
  induction packet.profiles with
  | nil =>
      simp
  | cons profile profiles ih =>
      simp only [List.map_cons, List.sum_cons, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C,
        signed_block_int,
        Int.cast_add]
      rw [ih]
      simp only [weightedProfileValue, Int.cast_mul]
      ring

/--
For a fixed natural right exponent, equality of packet values on all natural
left exponents identifies the left-variable polynomials.
-/
lemma left_nat_cast
    {leftDegree rightDegree : ℕ}
    (first second :
      HFPkt leftDegree rightDegree)
    (right : ℕ)
    (hvalue :
      ∀ left : ℕ,
        first.value (left : ℤ) (right : ℤ) =
          second.value (left : ℤ) (right : ℤ)) :
    first.leftPolynomial (right : ℤ) =
      second.leftPolynomial (right : ℤ) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem
    (Nat.cast_injective :
      Function.Injective (fun left : ℕ => (left : ℚ)))
  intro left
  change
    Polynomial.eval (left : ℚ) (first.leftPolynomial (right : ℤ)) =
      Polynomial.eval (left : ℚ) (second.leftPolynomial (right : ℤ))
  calc
    _ = ((first.value (left : ℤ) (right : ℤ) : ℤ) : ℚ) :=
      eval_left_int first (left : ℤ) (right : ℤ)
    _ = ((second.value (left : ℤ) (right : ℤ) : ℤ) : ℚ) := by
      exact_mod_cast hvalue left
    _ = _ :=
      (eval_left_int second (left : ℤ) (right : ℤ)).symm

/--
For a fixed natural right exponent, natural-left agreement extends to every
integral left exponent.
-/
lemma value_cast_left
    {leftDegree rightDegree : ℕ}
    (first second :
      HFPkt leftDegree rightDegree)
    (right : ℕ)
    (hvalue :
      ∀ left : ℕ,
        first.value (left : ℤ) (right : ℤ) =
          second.value (left : ℤ) (right : ℤ))
    (left : ℤ) :
    first.value left (right : ℤ) =
      second.value left (right : ℤ) := by
  have hpolynomial :=
    left_nat_cast first second right hvalue
  have hcast :
      ((first.value left (right : ℤ) : ℤ) : ℚ) =
        ((second.value left (right : ℤ) : ℤ) : ℚ) := by
    calc
      _ = Polynomial.eval (left : ℚ)
            (first.leftPolynomial (right : ℤ)) :=
        (eval_left_int first left (right : ℤ)).symm
      _ = Polynomial.eval (left : ℚ)
            (second.leftPolynomial (right : ℤ)) := by
        rw [hpolynomial]
      _ = _ :=
        eval_left_int second left (right : ℤ)
  exact_mod_cast hcast

/--
For a fixed integral left exponent, equality of packet values on all natural
right exponents identifies the right-variable polynomials.
-/
lemma value_nat_cast
    {leftDegree rightDegree : ℕ}
    (first second :
      HFPkt leftDegree rightDegree)
    (left : ℤ)
    (hvalue :
      ∀ right : ℕ,
        first.value left (right : ℤ) =
          second.value left (right : ℤ)) :
    first.rightPolynomial left =
      second.rightPolynomial left := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem
    (Nat.cast_injective :
      Function.Injective (fun right : ℕ => (right : ℚ)))
  intro right
  change
    Polynomial.eval (right : ℚ) (first.rightPolynomial left) =
      Polynomial.eval (right : ℚ) (second.rightPolynomial left)
  calc
    _ = ((first.value left (right : ℤ) : ℤ) : ℚ) :=
      eval_right_int first left (right : ℤ)
    _ = ((second.value left (right : ℤ) : ℤ) : ℚ) := by
      exact_mod_cast hvalue right
    _ = _ :=
      (eval_right_int second left (right : ℤ)).symm

/--
Two homogeneous signed-block packets which agree on the natural quadrant
agree at every pair of integral exponents.
-/
theorem value_cast
    {leftDegree rightDegree : ℕ}
    (first second :
      HFPkt leftDegree rightDegree)
    (hvalue :
      ∀ left right : ℕ,
        first.value (left : ℤ) (right : ℤ) =
          second.value (left : ℤ) (right : ℤ))
    (left right : ℤ) :
    first.value left right =
      second.value left right := by
  have hrightNat :
      ∀ nextRight : ℕ,
        first.value left (nextRight : ℤ) =
          second.value left (nextRight : ℤ) := by
    intro nextRight
    exact
      value_cast_left first second nextRight
        (fun nextLeft => hvalue nextLeft nextRight) left
  have hpolynomial :=
    value_nat_cast first second left hrightNat
  have hcast :
      ((first.value left right : ℤ) : ℚ) =
        ((second.value left right : ℤ) : ℚ) := by
    calc
      _ = Polynomial.eval (right : ℚ) (first.rightPolynomial left) :=
        (eval_right_int first left right).symm
      _ = Polynomial.eval (right : ℚ) (second.rightPolynomial left) := by
        rw [hpolynomial]
      _ = _ :=
        eval_right_int second left right
  exact_mod_cast hcast

end HFPkt

end
  CFSubsti
end TCTex
end Towers

/-!
# Root-swap inversion for signed-block formula packets

Swapping the two children of the root bracket of a positive Hall-pair word
evaluates to group inversion while preserving its Hall-pair bidegree.  A
signed-profile packet can therefore retain its coefficient profiles while
root-swapping its support word.

Reversing a packet list and root-swapping every support word gives an ordered
packet whose evaluated product is the inverse of the original product.  This
is the packet-level inversion operation needed by signed recollection.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

open HACoeff

/--
Root-swapping a word twice restores the original word.
-/
@[simp]
lemma root_swap_word
    {α : Type*}
    (word : CWord α) :
    rootSwapWord (rootSwapWord word) = word := by
  cases word <;> rfl

namespace
  CFSubsti

namespace HFPkt

/--
A homogeneous signed-profile packet is determined by its profile list.  Its
remaining fields only certify the common bidegree.
-/
@[ext]
lemma ext
    {leftDegree rightDegree : ℕ}
    {first second :
      HFPkt leftDegree rightDegree}
    (hprofiles : first.profiles = second.profiles) :
    first = second := by
  cases first
  cases second
  cases hprofiles
  rfl

end HFPkt

namespace RFPkt

/--
Root-swap the support word of a signed-profile packet while retaining its
coefficient profiles.
-/
def rootSwap
    (packet : RFPkt) :
    RFPkt where
  word :=
    rootSwapWord packet.word
  positive :=
    rootSwap_positive packet.positive
  profiles :=
    {
      profiles :=
        packet.profiles.profiles
      profiles_leftDegree := by
        intro profile hprofile
        rw [root_swap_positive packet.positive]
        exact packet.profiles.profiles_leftDegree profile hprofile
      profiles_rightDegree := by
        intro profile hprofile
        rw [pair_swap_positive packet.positive]
        exact packet.profiles.profiles_rightDegree profile hprofile
    }

@[simp]
lemma word_rootSwap
    (packet : RFPkt) :
    packet.rootSwap.word = rootSwapWord packet.word :=
  rfl

@[simp]
lemma value_profiles_swap
    (packet : RFPkt)
    (leftExponent rightExponent : ℤ) :
    packet.rootSwap.profiles.value leftExponent rightExponent =
      packet.profiles.value leftExponent rightExponent :=
  rfl

/--
Root-swapping a signed-profile packet twice restores the original packet.
-/
@[simp]
lemma root_swap
    (packet : RFPkt) :
    packet.rootSwap.rootSwap = packet := by
  cases packet with
  | mk word positive profiles =>
      cases word <;> simp only [rootSwap, rootSwapWord]

/--
One root-swapped signed-profile packet evaluates to the inverse of the
original evaluated factor.
-/
@[simp]
lemma eval_rootSwap
    (packet : RFPkt)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    packet.rootSwap.word.eval (HPAtom.eval left right) ^
          packet.rootSwap.profiles.value leftExponent rightExponent =
      (packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent)⁻¹ := by
  change
    (rootSwapWord packet.word).eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent =
      (packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent)⁻¹
  rw [swap_bidegree_positive
    (HPAtom.eval left right) packet.positive]
  exact inv_zpow _ _

end RFPkt
end
  CFSubsti

namespace
  FRSwap

open
  CFSubsti

/--
Reverse an ordered packet list and root-swap each support word.  Coefficient
profiles remain attached occurrence-for-occurrence.
-/
def rootSwapPackets
    (packets : List RFPkt) :
    List RFPkt :=
  packets.reverse.map RFPkt.rootSwap

@[simp]
lemma length_swap_packets
    (packets : List RFPkt) :
    (rootSwapPackets packets).length = packets.length := by
  simp [rootSwapPackets]

/--
Reversing and root-swapping twice restores the original packet list.
-/
@[simp]
lemma root_swap_packets
    (packets : List RFPkt) :
    rootSwapPackets (rootSwapPackets packets) = packets := by
  rw [rootSwapPackets, rootSwapPackets, ← List.map_reverse,
    List.reverse_reverse, List.map_map]
  induction packets with
  | nil =>
      rfl
  | cons packet packets ih =>
      simp only [List.map_cons, Function.comp_apply,
        RFPkt.root_swap, ih]

/--
The reverse root-swap packet list evaluates to the inverse ordered product of
the original list.
-/
lemma prod_swap_packets
    (packets : List RFPkt)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((rootSwapPackets packets).map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent).prod =
      ((packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod)⁻¹ := by
  rw [rootSwapPackets, List.map_map, List.map_reverse]
  change
    (packets.map fun packet =>
      packet.rootSwap.word.eval (HPAtom.eval left right) ^
        packet.rootSwap.profiles.value leftExponent rightExponent).reverse.prod =
      _
  have hmap :
      (packets.map fun packet =>
        packet.rootSwap.word.eval (HPAtom.eval left right) ^
          packet.rootSwap.profiles.value leftExponent rightExponent) =
        (packets.map fun packet =>
          (packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent)⁻¹) := by
    apply List.map_congr_left
    intro packet _hpacket
    exact packet.eval_rootSwap left right leftExponent rightExponent
  rw [hmap]
  simpa only [List.map_map, Function.comp_apply] using
    (List.prod_inv_reverse
      (packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent)).symm

end
  FRSwap
end TCTex
end Towers

/-!
# Inhomogeneous support-avoidance formula packets

Deleting a fixed physical raw slot from a complete source family introduces a
degree-zero correction.  For example, deleting one slot from the basic family
has count `M * N - 1`, which is not homogeneous of bidegree `(1, 1)`.

This file records the unrestricted signed-profile packet algebra needed before
the later support-pattern cancellations recover homogeneous correction
coefficients.  It also constructs the atomic avoidance packet for every
complete realization family and closes the construction under empty packets,
append, and Cartesian correction grids.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CSComp

open HACoeff
open CCGrida
open CSAggreg
open CEComp
open CSChunks
open CSFilter
open CFAlg
open CFSubsti
open CSOverla
open COAvoida
open OFSlots
open CSAlg
open HSPacket

/-- A positive-degree signed block product vanishes when its input is zero. -/
lemma signed_block_pos :
    ∀ blocks : List Block,
      0 < degreeSum blocks →
        signedBlockProduct 0 blocks = 0
  | [], hdegree => by
      simp [degreeSum] at hdegree
  | block :: blocks, hdegree => by
      by_cases hblock : 0 < block.degree
      · simp [signedBlockProduct, Ring.choose_zero_pos ℤ hblock]
      · have hblockZero : block.degree = 0 :=
          Nat.eq_zero_of_not_pos hblock
        change
          Ring.choose (block.sign.intValue * 0) block.degree *
              signedBlockProduct 0 blocks =
            0
        rw [hblockZero]
        simp only [Ring.choose_zero_right, one_mul]
        exact signed_block_pos blocks <| by
          simpa [degreeSum, hblockZero] using hdegree

/--
Every positive-left-degree homogeneous packet vanishes when the left source
exponent is zero.
-/
lemma homogeneous_formula_pos
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (hdegree : 0 < leftDegree)
    (right : ℤ) :
    packet.value 0 right = 0 := by
  rw [HFPkt.value]
  have hprofiles :
      ∀ profiles : List WBProf,
        (∀ profile ∈ profiles, 0 < profile.profile.leftDegree) →
          (profiles.map fun profile =>
            weightedProfileValue profile 0 right).sum = 0 := by
    intro profiles hprofiles
    induction profiles with
    | nil =>
        rfl
    | cons profile profiles ih =>
        rw [List.map_cons, List.sum_cons]
        have hprofileDegree :
            0 < degreeSum profile.profile.leftBlocks := by
          simpa [SBProf.leftDegree] using
            hprofiles profile (by simp)
        have hprofileZero :
            weightedProfileValue profile 0 right = 0 := by
          unfold weightedProfileValue
          rw [signed_block_pos _ hprofileDegree]
          ring
        rw [hprofileZero, zero_add]
        exact ih fun next hnext => hprofiles next (by simp [hnext])
  apply hprofiles packet.profiles
  intro profile hprofile
  rw [packet.profiles_leftDegree profile hprofile]
  exact hdegree

/--
Deleting one physical slot from the basic `(1, 1)` family cannot be represented
by a homogeneous `(1, 1)` formula packet.
-/
lemma not_homogeneous_formula :
    ¬ ∃ packet : HFPkt 1 1,
      ∀ left right : ℤ,
        packet.value left right = left * right - 1 := by
  rintro ⟨packet, hpacket⟩
  have hzero := hpacket 0 0
  rw [homogeneous_formula_pos
    packet (by omega)] at hzero
  norm_num at hzero

/--
An unrestricted multiplicity-independent signed-profile packet.  Unlike
`HFPkt`, its profiles may have different
bidegrees.
-/
structure IFPkt where
  profiles :
    List WBProf

namespace IFPkt

/-- Evaluate an unrestricted packet at arbitrary integral source values. -/
def value
    (packet : IFPkt)
    (left right : ℤ) :
    ℤ :=
  (packet.profiles.map fun profile =>
    weightedProfileValue profile left right).sum

/-- The empty unrestricted packet. -/
def zero :
    IFPkt where
  profiles := []

/-- Regard one homogeneous packet as an unrestricted packet. -/
def ofHomogeneous
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree) :
    IFPkt where
  profiles := packet.profiles

/-- One degree-zero constant profile. -/
def constantProfile
    (coefficient : ℤ) :
    WBProf where
  multiplicity := coefficient
  profile :=
    { leftBlocks := []
      rightBlocks := [] }

/-- One degree-zero constant packet. -/
def constant
    (coefficient : ℤ) :
    IFPkt where
  profiles := [constantProfile coefficient]

/-- Add two unrestricted packets. -/
def add
    (left right : IFPkt) :
    IFPkt where
  profiles := left.profiles ++ right.profiles

/-- Scale an unrestricted packet by an integer. -/
def scale
    (coefficient : ℤ)
    (packet : IFPkt) :
    IFPkt where
  profiles := scaleWeightedProfiles coefficient packet.profiles

/-- Negate an unrestricted packet. -/
def negate
    (packet : IFPkt) :
    IFPkt :=
  scale (-1) packet

/-- Subtract two unrestricted packets. -/
def subtract
    (left right : IFPkt) :
    IFPkt :=
  add left right.negate

/-- Multiply two unrestricted packets. -/
def multiply
    (left right : IFPkt) :
    IFPkt where
  profiles := multiplyWeightedProfiles left.profiles right.profiles

/-- Finite sum of unrestricted packets. -/
def sum :
    List IFPkt →
      IFPkt
  | [] =>
      zero
  | packet :: packets =>
      add packet (sum packets)

/-- Finite sum of an unrestricted packet family indexed by a finset. -/
noncomputable def finsetSum
    {ι : Type*}
    (indices : Finset ι)
    (packet : ι → IFPkt) :
    IFPkt :=
  sum (indices.toList.map packet)

@[simp]
lemma value_zero
    (left right : ℤ) :
    zero.value left right = 0 := by
  rfl

@[simp]
lemma value_ofHomogeneous
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (ofHomogeneous packet).value left right =
      packet.value left right := by
  rfl

@[simp]
lemma value_constant
    (coefficient left right : ℤ) :
    (constant coefficient).value left right = coefficient := by
  simp [constant, constantProfile, value, weightedProfileValue,
    signedBlockProduct]

@[simp]
lemma value_add
    (leftPacket rightPacket : IFPkt)
    (left right : ℤ) :
    (add leftPacket rightPacket).value left right =
      leftPacket.value left right + rightPacket.value left right := by
  simp [add, value, List.sum_append]

@[simp]
lemma value_scale
    (coefficient : ℤ)
    (packet : IFPkt)
    (left right : ℤ) :
    (scale coefficient packet).value left right =
      coefficient * packet.value left right := by
  exact FPkt.weighted_profile_scale
    coefficient left right packet.profiles

@[simp]
lemma value_negate
    (packet : IFPkt)
    (left right : ℤ) :
    packet.negate.value left right = -packet.value left right := by
  simp [negate]

@[simp]
lemma value_subtract
    (leftPacket rightPacket : IFPkt)
    (left right : ℤ) :
    (subtract leftPacket rightPacket).value left right =
      leftPacket.value left right - rightPacket.value left right := by
  simp [subtract, sub_eq_add_neg]

@[simp]
lemma value_multiply
    (leftPacket rightPacket : IFPkt)
    (left right : ℤ) :
    (multiply leftPacket rightPacket).value left right =
      leftPacket.value left right * rightPacket.value left right := by
  exact FPkt.weighted_profile_multiply
    left right leftPacket.profiles rightPacket.profiles

@[simp]
lemma value_sum
    (packets : List IFPkt)
    (left right : ℤ) :
    (sum packets).value left right =
      (packets.map fun packet => packet.value left right).sum := by
  induction packets with
  | nil =>
      rfl
  | cons packet packets ih =>
      simp [sum, ih]

@[simp]
lemma value_finsetSum
    {ι : Type*}
    (indices : Finset ι)
    (packet : ι → IFPkt)
    (left right : ℤ) :
    (finsetSum indices packet).value left right =
      ∑ index ∈ indices, (packet index).value left right := by
  simp [finsetSum]

/-- The positive unrestricted packet represented by one complete family. -/
def ofFamily
    {M N : ℕ}
    (family : BFam M N) :
    IFPkt where
  profiles := [weightedBlockProfile family]

@[simp]
lemma value_family_cast
    {M N : ℕ}
    (family : BFam M N) :
    (ofFamily family).value (M : ℤ) (N : ℤ) =
      (family.realizations.length : ℤ) := by
  simp only [ofFamily, value, List.map_singleton, List.sum_singleton,
    weightedProfileValue, signed_block_cast]
  change
    (weightedBlockProfile family).coefficient M N =
      (family.realizations.length : ℤ)
  exact weighted_profile_coefficient family

end IFPkt

open IFPkt

namespace ISForm

/-- Recover fixed-slot containment from unrestricted avoidance packets. -/
noncomputable def containmentOfAvoidance
    {K : ℕ}
    (slots : Finset (Fin K))
    (avoidance :
      ∀ _avoidedSlots : Finset (Fin K),
        IFPkt) :
    IFPkt :=
  finsetSum slots.powerset fun avoidedSlots =>
    scale ((-1 : ℤ) ^ avoidedSlots.card) (avoidance avoidedSlots)

/-- Recover overlap from unrestricted fixed-slot containment packets. -/
noncomputable def overlapOfContainment
    {K : ℕ}
    (left right :
      ∀ _slots : Finset (Fin K),
        IFPkt) :
    IFPkt :=
  finsetSum
    (Finset.univ :
      Finset
        ((Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty)))
    fun slots =>
      scale ((-1 : ℤ) ^ (slots.1.card + 1))
        (multiply (left slots.1) (right slots.1))

/-- Recover overlap directly from unrestricted avoidance packets. -/
noncomputable def overlapOfAvoidance
    {K : ℕ}
    (left right :
      ∀ _slots : Finset (Fin K),
        IFPkt) :
    IFPkt :=
  overlapOfContainment
    (fun slots => containmentOfAvoidance slots left)
    (fun slots => containmentOfAvoidance slots right)

/--
The operationally retained grid is the full Cartesian grid minus its
overlapping-support complement.
-/
noncomputable def compatibleAvoidance
    {K : ℕ}
    (left right :
      ∀ _slots : Finset (Fin K),
        IFPkt) :
    IFPkt :=
  subtract (multiply (left ∅) (right ∅))
    (overlapOfAvoidance left right)

@[simp]
lemma value_containment_avoidance
    {K : ℕ}
    (slots : Finset (Fin K))
    (avoidance :
      ∀ _avoidedSlots : Finset (Fin K),
        IFPkt)
    (left right : ℤ) :
    (containmentOfAvoidance slots avoidance).value left right =
      ∑ avoidedSlots ∈ slots.powerset,
        (-1 : ℤ) ^ avoidedSlots.card *
          (avoidance avoidedSlots).value left right := by
  simp [containmentOfAvoidance]

@[simp]
lemma value_overlap_containment
    {K : ℕ}
    (left right :
      ∀ _slots : Finset (Fin K),
        IFPkt)
    (leftExponent rightExponent : ℤ) :
    (overlapOfContainment left right).value leftExponent rightExponent =
      ∑ slots :
          ((Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty)),
        (-1 : ℤ) ^ (slots.1.card + 1) *
          ((left slots.1).value leftExponent rightExponent *
            (right slots.1).value leftExponent rightExponent) := by
  simp [overlapOfContainment]

end ISForm

/--
A pointwise unrestricted formula family specializing support avoidance for one
concrete packet.
-/
structure AISpec
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (packets :
      ∀ _slots : Finset (Fin K),
        IFPkt) : Prop where
  value_cast_length :
    ∀ slots : Finset (Fin K),
      (packets slots).value (M : ℤ) (N : ℤ) =
        ((termsAvoidingSlots terms slots).length : ℤ)

namespace AISpec

open ISForm

/--
The unrestricted avoidance formula for one complete family packet: retain the
full family polynomial and subtract the concretely rejected physical slots.
-/
def packetAvoidance
    {M N K : ℕ}
    (family : BFam M N)
    (terms : List (DFTerm M N K))
    (slots : Finset (Fin K)) :
    IFPkt :=
  subtract (ofFamily family)
    (constant
      ((terms.length - (termsAvoidingSlots terms slots).length : ℕ) : ℤ))

/--
For one complete family packet, support avoidance is the full family polynomial
minus the number of concretely rejected physical slots.
-/
def ofPacket
    {M N K : ℕ}
    {family : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor family terms) :
    AISpec terms
      (packetAvoidance family terms) where
  value_cast_length slots := by
    rw [packetAvoidance, value_subtract, value_family_cast, value_constant,
      ← hpacket.terms_length_eq]
    have hle :
        (termsAvoidingSlots terms slots).length ≤ terms.length := by
      exact List.length_filter_le _ _
    omega

/-- The empty concrete packet specializes the zero unrestricted packet. -/
def nil
    (M N K : ℕ) :
    AISpec
      ([] : List (DFTerm M N K))
      (fun _slots => zero) where
  value_cast_length _slots := by
    rfl

/-- Pointwise unrestricted specialization is closed under append. -/
def append
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftPackets rightPackets :
      ∀ _slots : Finset (Fin K),
        IFPkt}
    (left :
      AISpec
        leftTerms leftPackets)
    (right :
      AISpec
        rightTerms rightPackets) :
    AISpec
      (leftTerms ++ rightTerms)
      (fun slots => add (leftPackets slots) (rightPackets slots)) where
  value_cast_length slots := by
    rw [value_add, avoiding_slots_append, List.length_append,
      Int.natCast_add, left.value_cast_length,
      right.value_cast_length]

/-- Pointwise unrestricted specialization multiplies across correction grids. -/
def correctionGrid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftPackets rightPackets :
      ∀ _slots : Finset (Fin K),
        IFPkt}
    (left :
      AISpec
        leftTerms leftPackets)
    (right :
      AISpec
        rightTerms rightPackets) :
    AISpec
      (DFTerm.correctionGrid leftTerms rightTerms)
      (fun slots => multiply (leftPackets slots) (rightPackets slots)) where
  value_cast_length slots := by
    rw [value_multiply, avoiding_slots_grid,
      Int.natCast_mul, left.value_cast_length,
      right.value_cast_length]

/--
Containment recovered from unrestricted avoidance packets evaluates to the
concrete one-sided containment count.
-/
lemma containment_containing_slots
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    {packets :
      ∀ _slots : Finset (Fin K),
        IFPkt}
    (specialization :
      AISpec terms packets)
    (slots : Finset (Fin K)) :
    (containmentOfAvoidance slots packets).value (M : ℤ) (N : ℤ) =
      ((termsContainingSlots terms slots).length : ℤ) := by
  rw [value_containment_avoidance,
    slots_exclusion_avoiding]
  apply Finset.sum_congr rfl
  intro avoidedSlots _hslots
  rw [specialization.value_cast_length]

/--
Overlap recovered from unrestricted avoidance packets evaluates to the
concrete overlapping-support grid length.
-/
lemma overlap_avoidance_overlapping
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftPackets rightPackets :
      ∀ _slots : Finset (Fin K),
        IFPkt}
    (left :
      AISpec
        leftTerms leftPackets)
    (right :
      AISpec
        rightTerms rightPackets) :
    (overlapOfAvoidance leftPackets rightPackets).value (M : ℤ) (N : ℤ) =
      ((overlappingCorrectionGrid leftTerms rightTerms).length : ℤ) := by
  rw [overlapOfAvoidance, value_overlap_containment,
    overlapping_factored_exclusion]
  apply Finset.sum_congr rfl
  intro slots _hslots
  rw [left.containment_containing_slots,
    right.containment_containing_slots]
  ring

/--
For a genuine homogeneous operational batch, unrestricted support compilation
evaluates to the retained compatible-grid length.
-/
lemma compatible_grid_avoidance
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftPackets rightPackets :
      ∀ _slots : Finset (Fin K),
        IFPkt}
    (left :
      AISpec
        leftTerms leftPackets)
    (right :
      AISpec
        rightTerms rightPackets)
    {leftShape rightShape : CWord HPAtom}
    (hleft : ∀ leftTerm ∈ leftTerms, leftTerm.erasedShape = leftShape)
    (hright : ∀ rightTerm ∈ rightTerms, rightTerm.erasedShape = rightShape)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness) :
    (ISForm.compatibleAvoidance
        leftPackets rightPackets).value (M : ℤ) (N : ℤ) =
      ((compatibleCorrectionGrid leftTerms rightTerms).length : ℤ) := by
  rw [ISForm.compatibleAvoidance,
    value_subtract, value_multiply,
    left.value_cast_length, right.value_cast_length,
    overlap_avoidance_overlapping
      (left := left) (right := right)]
  simp only [termsAvoidingSlots, Finset.disjoint_empty_left, decide_true,
    List.filter_true]
  have hpartition :=
    grid_perm_incompatible leftTerms rightTerms
  rw [incompatible_grid_overlapping
    hleft hright hleftWitness hrightWitness hcompatible] at hpartition
  have hlength :=
    congrArg (fun length : ℕ => (length : ℤ)) hpartition.length_eq
  simp only [List.length_append, Int.natCast_add] at hlength
  have hgrid :
      (DFTerm.correctionGrid leftTerms rightTerms).length =
        leftTerms.length * rightTerms.length := by
    simp [DFTerm.correctionGrid, List.length_flatMap]
  rw [hgrid, Int.natCast_mul] at hlength
  omega

/-- The retained unrestricted grid packet attached to two complete families. -/
noncomputable def compatibleGridPackets
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (_hleft : RPFor leftFamily leftTerms)
    (_hright : RPFor rightFamily rightTerms) :
    IFPkt :=
  ISForm.compatibleAvoidance
    (packetAvoidance leftFamily leftTerms)
    (packetAvoidance rightFamily rightTerms)

/--
The retained unrestricted grid packet of two complete families evaluates to
the concrete operationally compatible grid length.
-/
lemma compat_grid_length
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RPFor leftFamily leftTerms)
    (hright : RPFor rightFamily rightTerms)
    {leftShape rightShape : CWord HPAtom}
    (hleftShape : ∀ leftTerm ∈ leftTerms, leftTerm.erasedShape = leftShape)
    (hrightShape : ∀ rightTerm ∈ rightTerms, rightTerm.erasedShape = rightShape)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness) :
    (compatibleGridPackets hleft hright).value (M : ℤ) (N : ℤ) =
      ((compatibleCorrectionGrid leftTerms rightTerms).length : ℤ) := by
  exact
    compatible_grid_avoidance
      (ofPacket hleft) (ofPacket hright)
      hleftShape hrightShape hleftWitness hrightWitness hcompatible

end AISpec

end CSComp
end TCTex
end Towers

/-!
# Multiplicity-independent support-pattern formula packets

Support-pattern compilation uses only finite sums, integral scaling, and
products of homogeneous signed-profile expressions.  The same construction
therefore exists before specializing the two source multiplicities.  This file
defines that global packet compiler and proves that forgetting a concrete
support expression commutes with its containment and overlap constructors.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace SFComp

open HACoeff
open CEAlg
open CFAlg
open CFSubsti
open SEComp
open HSPacket

namespace SFPkt

/--
Compile fixed-slot containment from a multiplicity-independent avoidance
packet for every finite slot set.
-/
noncomputable def containmentOfAvoidance
    {K leftDegree rightDegree : ℕ}
    (slots : Finset (Fin K))
    (avoidance :
      ∀ _avoidedSlots : Finset (Fin K),
        HFPkt leftDegree rightDegree) :
    HFPkt leftDegree rightDegree :=
  FPkt.finsetSum slots.powerset fun avoidedSlots =>
    FPkt.scale
      ((-1 : ℤ) ^ avoidedSlots.card)
      (avoidance avoidedSlots)

/--
Compile parent-support overlap from multiplicity-independent fixed-slot
containment packets for the two parent packets.
-/
noncomputable def overlapOfContainment
    {K : ℕ}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftLeftDegree leftRightDegree)
    (right :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightLeftDegree rightRightDegree) :
    HFPkt
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) :=
  FPkt.finsetSum
    (Finset.univ :
      Finset
        ((Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty)))
    fun slots =>
      FPkt.scale
        ((-1 : ℤ) ^ (slots.1.card + 1))
        (FPkt.multiply (left slots.1) (right slots.1))

/--
Compile parent-support overlap directly from multiplicity-independent
avoidance packets for the two parent packets.
-/
noncomputable def overlapOfAvoidance
    {K : ℕ}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftLeftDegree leftRightDegree)
    (right :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightLeftDegree rightRightDegree) :
    HFPkt
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) :=
  overlapOfContainment
    (fun slots => containmentOfAvoidance slots left)
    (fun slots => containmentOfAvoidance slots right)

@[simp]
lemma value_containment_avoidance
    {K leftDegree rightDegree : ℕ}
    (slots : Finset (Fin K))
    (avoidance :
      ∀ _avoidedSlots : Finset (Fin K),
        HFPkt leftDegree rightDegree)
    (left right : ℤ) :
    (containmentOfAvoidance slots avoidance).value left right =
      ∑ avoidedSlots ∈ slots.powerset,
        (-1 : ℤ) ^ avoidedSlots.card *
          (avoidance avoidedSlots).value left right := by
  simp [containmentOfAvoidance]

@[simp]
lemma value_overlap_containment
    {K : ℕ}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftLeftDegree leftRightDegree)
    (right :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightLeftDegree rightRightDegree)
    (leftExponent rightExponent : ℤ) :
    (overlapOfContainment left right).value leftExponent rightExponent =
      ∑ slots :
          ((Finset.univ : Finset (Fin K)).powerset.filter (·.Nonempty)),
        (-1 : ℤ) ^ (slots.1.card + 1) *
          ((left slots.1).value leftExponent rightExponent *
            (right slots.1).value leftExponent rightExponent) := by
  simp [overlapOfContainment]

@[simp]
lemma expression_containment_avoidance
    {M N K leftDegree rightDegree : ℕ}
    {terms : List (DFTerm M N K)}
    (slots : Finset (Fin K))
    (avoidance :
      ∀ avoidedSlots : Finset (Fin K),
        SAExpr
          terms avoidedSlots leftDegree rightDegree) :
    HFPkt.ofExpression
        (SCExpr.ofAvoidance
          slots avoidance).expression =
      containmentOfAvoidance slots fun avoidedSlots =>
        HFPkt.ofExpression
          (avoidance avoidedSlots).expression := by
  simp [SCExpr.ofAvoidance,
    containmentOfAvoidance]

@[simp]
lemma expression_overlap_containment
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ slots : Finset (Fin K),
        SCExpr
          leftTerms slots leftLeftDegree leftRightDegree)
    (right :
      ∀ slots : Finset (Fin K),
        SCExpr
          rightTerms slots rightLeftDegree rightRightDegree) :
    HFPkt.ofExpression
        (OBExpr.ofContainment left right).expression =
      overlapOfContainment
        (fun slots =>
          HFPkt.ofExpression
            (left slots).expression)
        (fun slots =>
          HFPkt.ofExpression
            (right slots).expression) := by
  simp [OBExpr.ofContainment, overlapOfContainment]

@[simp]
lemma overlap_avoidance
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    (left :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftLeftDegree leftRightDegree)
    (right :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots rightLeftDegree rightRightDegree) :
    HFPkt.ofExpression
        (OBExpr.ofContainment
          (fun slots =>
            SCExpr.ofAvoidance slots left)
          (fun slots =>
            SCExpr.ofAvoidance slots right)
          |>.expression) =
      overlapOfAvoidance
        (fun slots =>
          HFPkt.ofExpression
            (left slots).expression)
        (fun slots =>
          HFPkt.ofExpression
            (right slots).expression) := by
  simp [overlapOfAvoidance]

end SFPkt

end SFComp
end TCTex
end Towers

/-!
# Uniform natural packets from signed-profile operational normalization

Support-sensitive operational collection naturally stabilizes to a finite
ordered list of erased Hall words carrying homogeneous signed-profile
packets, rather than to a positive `BRecipe` list.  This file records the
corresponding multiplicity-independent normalization boundary.

Once a fixed signed-profile packet list agrees with every natural
operational expansion, it gives a cutoff-specific natural Hall-Petresco
packet.  A universal all-integral signed-profile packet supplies such a
normalization witness automa.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace UNPkt

universe u v

open scoped commutatorElement

open HACoeff
open BRSpec
open CSNorm
open CFSubsti
open CFExp

/--
One ordered cutoff-specific signed-profile packet whose Hall-Petresco
identity is known uniformly at natural source multiplicities.
-/
structure TBPkt
    (d n : ℕ) where
  packets :
    List RFPkt
  list_nat_cast :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℕ),
        (packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value
              (leftExponent : ℤ) (rightExponent : ℤ)).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace TBPkt

/-- The remaining signed extension theorem for one natural signed-profile packet. -/
structure AILift
    {d n : ℕ}
    (packet : TBPkt.{u} d n) :
    Prop where
  listEval_eq :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace AILift

/-- A signed lift is exactly the cutoff packet consumed by signed-profile substitution. -/
def truncatedAllIntegral
    {d n : ℕ}
    {packet : TBPkt.{u} d n}
    (lift : packet.AILift) :
    TAInt.{u} d n where
  packets := packet.packets
  listEval_eq := lift.listEval_eq

end AILift
end TBPkt

/--
A fixed signed-profile packet list uniformly normalizes every
multiplicity-dependent operational expansion.
-/
structure UPNorm
    (kernel : OCKern)
    (packets : List RFPkt) :
    Prop where
  packet_prod_expansion :
    ∀ (M N : ℕ)
      {G : Type*}
      [Group G]
      (left right : G),
        (packets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value (M : ℤ) (N : ℤ)).prod =
          ((((kernel.expansion M N).families.map BFam.recipe).map
            fun recipe =>
              recipe.erasedShape.eval (HPAtom.eval left right) ^
                coefficientValue recipe (M : ℤ) (N : ℤ)).prod)

namespace UPNorm

/-- A uniform signed-profile normalization is the required natural packet. -/
def truncNaturalPacket
    {kernel : OCKern}
    {packets : List RFPkt}
    (uniform : UPNorm kernel packets)
    (d n : ℕ) :
    TBPkt.{u} d n where
  packets := packets
  list_nat_cast left right M N :=
    (uniform.packet_prod_expansion M N left right).trans
      (kernel.recipe_cast_pow M N left right)

end UPNorm

/-- Every universal signed-profile packet forgets to its natural specialization. -/
def truncatedNaturalUniversal
    {d n : ℕ}
    (packet : UAPkt) :
    TBPkt.{u} d n where
  packets := packet.packets
  list_nat_cast left right leftExponent rightExponent := by
    simpa only [zpow_natCast] using
      packet.listEval_eq left right
        (leftExponent : ℤ) (rightExponent : ℤ)

/-- The universal all-integral law supplies the signed lift of its natural packet. -/
def allLiftUniversal
    {d n : ℕ}
    (packet : UAPkt) :
    (truncatedNaturalUniversal
      (d := d) (n := n) packet).AILift where
  listEval_eq := packet.listEval_eq

/--
A universal signed-profile packet automa normalizes every compatible
operational kernel at natural multiplicities.
-/
def uniformNormalizationUniversal
    (packet : UAPkt.{v})
    (kernel : OCKern) :
    UPNorm.{v} kernel packet.packets where
  packet_prod_expansion := by
    intro M N G _inst left right
    exact
      (packet.listEval_eq left right (M : ℤ) (N : ℤ)).trans
        (by
          simpa only [zpow_natCast] using
            (kernel.recipe_cast_pow
              M N left right).symm)

end UNPkt
end TCTex
end Towers

/-!
# Homogeneous presentations of unrestricted support packets

Physical-slot deletion requires inhomogeneous intermediate packets.  The
existing Hall-Petresco coefficient compiler should only be re-entered after the
lower-degree terms cancel.  This file packages that cancellation boundary: an
unrestricted packet has a homogeneous presentation when it agrees, at every
integral source pair, with one homogeneous signed-profile packet.

The elementary packet algebra preserves homogeneous presentations.  The final
section isolates the remaining retained-grid cancellation theorem as a kernel
and converts any such kernel back into the existing concrete signed-block
certificate.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  SHPres

open HACoeff
open CCGrida
open CSAggreg
open CSChunks
open CFAlg
open CFSubsti
open CSComp
open CSComp.IFPkt
open CSComp.AISpec
open HSPacket


/--
An unrestricted packet together with an equivalent homogeneous signed-profile
packet of one specified bidegree.
-/
structure HPres
    (packet : IFPkt)
    (leftDegree rightDegree : ℕ) where
  homogeneous :
    HFPkt leftDegree rightDegree
  value_eq :
    ∀ left right : ℤ,
      homogeneous.value left right = packet.value left right

namespace HPres

/-- Regard one homogeneous packet as its own unrestricted presentation. -/
def ofHomogeneous
    {leftDegree rightDegree : ℕ}
    (packet : HFPkt leftDegree rightDegree) :
    HPres
      (IFPkt.ofHomogeneous packet)
      leftDegree rightDegree where
  homogeneous := packet
  value_eq := by
    intro left right
    rfl

/-- The empty unrestricted packet has a homogeneous presentation in any bidegree. -/
def zero
    (leftDegree rightDegree : ℕ) :
    HPres
      IFPkt.zero leftDegree rightDegree where
  homogeneous := FPkt.zero leftDegree rightDegree
  value_eq := by
    intro left right
    simp

/-- Homogeneous presentations in one common bidegree add. -/
def add
    {leftDegree rightDegree : ℕ}
    {leftPacket rightPacket : IFPkt}
    (left :
      HPres leftPacket leftDegree rightDegree)
    (right :
      HPres rightPacket leftDegree rightDegree) :
    HPres
      (IFPkt.add leftPacket rightPacket)
      leftDegree rightDegree where
  homogeneous := FPkt.add left.homogeneous right.homogeneous
  value_eq := by
    intro leftExponent rightExponent
    simp [left.value_eq, right.value_eq]

/-- Integral scaling preserves a homogeneous presentation. -/
def scale
    {leftDegree rightDegree : ℕ}
    {packet : IFPkt}
    (coefficient : ℤ)
    (presentation :
      HPres packet leftDegree rightDegree) :
    HPres
      (IFPkt.scale coefficient packet)
      leftDegree rightDegree where
  homogeneous := FPkt.scale coefficient presentation.homogeneous
  value_eq := by
    intro left right
    simp [presentation.value_eq]

/-- Negation preserves a homogeneous presentation. -/
def negate
    {leftDegree rightDegree : ℕ}
    {packet : IFPkt}
    (presentation :
      HPres packet leftDegree rightDegree) :
    HPres packet.negate leftDegree rightDegree :=
  presentation.scale (-1)

/-- Homogeneous presentations in one common bidegree subtract. -/
def subtract
    {leftDegree rightDegree : ℕ}
    {leftPacket rightPacket : IFPkt}
    (left :
      HPres leftPacket leftDegree rightDegree)
    (right :
      HPres rightPacket leftDegree rightDegree) :
    HPres
      (IFPkt.subtract leftPacket rightPacket)
      leftDegree rightDegree :=
  left.add right.negate

/-- Products of homogeneous presentations have summed bidegree. -/
def multiply
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    {leftPacket rightPacket : IFPkt}
    (left :
      HPres leftPacket leftLeftDegree leftRightDegree)
    (right :
      HPres rightPacket rightLeftDegree rightRightDegree) :
    HPres
      (IFPkt.multiply leftPacket rightPacket)
      (leftLeftDegree + rightLeftDegree)
      (leftRightDegree + rightRightDegree) where
  homogeneous := FPkt.multiply left.homogeneous right.homogeneous
  value_eq := by
    intro leftExponent rightExponent
    simp [left.value_eq, right.value_eq]

/-- Degree-zero constants have homogeneous degree-zero presentations. -/
def constant
    (coefficient : ℤ) :
    HPres
      (IFPkt.constant coefficient) 0 0 where
  homogeneous :=
    { profiles :=
        [IFPkt.constantProfile coefficient]
      profiles_leftDegree := by
        intro profile hprofile
        rcases List.mem_singleton.mp hprofile with rfl
        rfl
      profiles_rightDegree := by
        intro profile hprofile
        rcases List.mem_singleton.mp hprofile with rfl
        rfl }
  value_eq := by
    intro left right
    rfl

/-- One complete family polynomial has its expected homogeneous presentation. -/
def ofFamily
    {M N : ℕ}
    (family : BFam M N) :
    HPres
      (IFPkt.ofFamily family)
      family.recipe.erasedShape.pairLeftDegree
      family.recipe.erasedShape.pairRightDegree where
  homogeneous :=
    { profiles := [weightedBlockProfile family]
      profiles_leftDegree := by
        intro profile hprofile
        rcases List.mem_singleton.mp hprofile with rfl
        exact weighted_block_degree family
      profiles_rightDegree := by
        intro profile hprofile
        rcases List.mem_singleton.mp hprofile with rfl
        exact weighted_profile_degree family }
  value_eq := by
    intro left right
    rfl

/--
At natural multiplicities, a homogeneous presentation whose unrestricted value
is a concrete block length yields the existing signed-block certificate.
-/
def shapeBlockCertificate
    {M N K : ℕ}
    {packet : IFPkt}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (presentation :
      HPres packet
        word.pairLeftDegree word.pairRightDegree)
    (hlength :
      packet.value (M : ℤ) (N : ℤ) = (block.length : ℤ)) :
    SBCert block word where
  profiles := presentation.homogeneous.profiles
  profiles_leftDegree := presentation.homogeneous.profiles_leftDegree
  profiles_rightDegree := presentation.homogeneous.profiles_rightDegree
  length_eq := by
    rw [← hlength, ← presentation.value_eq,
      HFPkt.value_natCast]

end HPres

/--
The remaining cancellation obligation for physical-slot support compilation:
every retained compatible grid of complete families has a homogeneous
presentation in its correction-family bidegree.
-/
structure CHCancel : Prop where
  presentation :
    ∀ {M N K : ℕ}
      {leftFamily rightFamily : BFam M N}
      {leftTerms rightTerms : List (DFTerm M N K)}
      (hleft : RPFor leftFamily leftTerms)
      (hright : RPFor rightFamily rightTerms)
      {leftWitness rightWitness : DFTerm M N K},
      leftWitness ∈ leftTerms →
        rightWitness ∈ rightTerms →
          correctionPairCompatible leftWitness rightWitness →
            Nonempty
              (HPres
                (compatibleGridPackets hleft hright)
                (leftFamily.correction rightFamily).recipe.erasedShape.pairLeftDegree
                (leftFamily.correction rightFamily).recipe.erasedShape.pairRightDegree)

namespace CHCancel

/--
A homogeneous retained-grid cancellation kernel gives the concrete signed-block
certificate consumed by the operational collector.
-/
noncomputable def certificate
    (kernel : CHCancel)
    {M N K : ℕ}
    {leftFamily rightFamily : BFam M N}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RPFor leftFamily leftTerms)
    (hright : RPFor rightFamily rightTerms)
    {leftWitness rightWitness : DFTerm M N K}
    (hleftWitness : leftWitness ∈ leftTerms)
    (hrightWitness : rightWitness ∈ rightTerms)
    (hcompatible : correctionPairCompatible leftWitness rightWitness) :
    SBCert
      (compatibleCorrectionGrid leftTerms rightTerms)
      (leftFamily.correction rightFamily).recipe.erasedShape := by
  let presentation :=
    Classical.choice <|
      kernel.presentation hleft hright
        hleftWitness hrightWitness hcompatible
  apply presentation.shapeBlockCertificate
  exact
    compat_grid_length
      hleft hright
      (fun leftTerm hleftTerm => by
        rw [leftTerm.erased_shape_family,
          hleft.family_eq_mem hleftTerm])
      (fun rightTerm hrightTerm => by
        rw [rightTerm.erased_shape_family,
          hright.family_eq_mem hrightTerm])
      hleftWitness hrightWitness hcompatible

end CHCancel

end SHPres
end TCTex
end Towers

/-!
# Specializing multiplicity-independent support formula packets

The support-pattern compiler has a global formula-packet layer and a concrete
length-expression layer.  This file records the relation between them.  A
fixed avoidance packet family specializes a concrete avoidance expression
family when forgetting each concrete expression returns the corresponding
fixed packet.  The relation is closed under Cartesian correction grids, and
the concrete overlap compiler forgets to the global overlap packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  SFSpec

open HACoeff
open CGCompa
open CEAlg
open CFAlg
open CFSubsti
open COAvoida
open SEComp
open SFComp
open HSPacket

/--
A fixed avoidance formula packet family specializing one concrete packet's
support-avoidance expressions at every finite slot set.
-/
structure SASpec
    {M N K leftDegree rightDegree : ℕ}
    (terms : List (DFTerm M N K))
    (packets :
      ∀ _slots : Finset (Fin K),
        HFPkt leftDegree rightDegree)
    (expressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          terms slots leftDegree rightDegree) : Prop where
  ofExpression_eq :
    ∀ slots : Finset (Fin K),
      HFPkt.ofExpression
          (expressions slots).expression =
        packets slots

namespace SASpec

/-- Fixed avoidance formulas evaluate to the corresponding concrete filtered length. -/
lemma cast_avoiding_slots
    {M N K leftDegree rightDegree : ℕ}
    {terms : List (DFTerm M N K)}
    {packets :
      ∀ _slots : Finset (Fin K),
        HFPkt leftDegree rightDegree}
    {expressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          terms slots leftDegree rightDegree}
    (specialization :
      SASpec
        terms packets expressions)
    (slots : Finset (Fin K)) :
    (packets slots).value (M : ℤ) (N : ℤ) =
      ((termsAvoidingSlots terms slots).length : ℤ) := by
  rw [← specialization.ofExpression_eq slots,
    HFPkt.value_expression_cast]
  exact (expressions slots).length_eq.symm

/--
Specialization is closed under Cartesian correction grids.  The fixed global
packet family multiplies pointwise, exactly as concrete avoidance lengths do.
-/
def correctionGrid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    {leftPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftLeftDegree leftRightDegree}
    {rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightLeftDegree rightRightDegree}
    {leftExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftLeftDegree leftRightDegree}
    {rightExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots rightLeftDegree rightRightDegree}
    (left :
      SASpec
        leftTerms leftPackets leftExpressions)
    (right :
      SASpec
        rightTerms rightPackets rightExpressions) :
    SASpec
      (DFTerm.correctionGrid leftTerms rightTerms)
      (fun slots =>
        FPkt.multiply (leftPackets slots) (rightPackets slots))
      (fun slots =>
        SAExpr.correctionGrid
          (leftExpressions slots) (rightExpressions slots)) where
  ofExpression_eq slots := by
    rw [SAExpr.correctionGrid,
      FPkt.ofExpression_multiply,
      left.ofExpression_eq slots, right.ofExpression_eq slots]

/--
For specialized avoidance families, the concrete overlap expression forgets
to the fixed global overlap formula packet.
-/
lemma expression_overlap_avoidance
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftLeftDegree leftRightDegree rightLeftDegree rightRightDegree : ℕ}
    {leftPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          leftLeftDegree leftRightDegree}
    {rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt
          rightLeftDegree rightRightDegree}
    {leftExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftLeftDegree leftRightDegree}
    {rightExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots rightLeftDegree rightRightDegree}
    (left :
      SASpec
        leftTerms leftPackets leftExpressions)
    (right :
      SASpec
        rightTerms rightPackets rightExpressions) :
    HFPkt.ofExpression
        (overlapExpressionAvoidance
          leftExpressions rightExpressions).expression =
      SFPkt.overlapOfAvoidance leftPackets rightPackets := by
  rw [overlapExpressionAvoidance,
    SFPkt.overlap_avoidance]
  congr 1
  · funext slots
    exact left.ofExpression_eq slots
  · funext slots
    exact right.ofExpression_eq slots

end SASpec

end SFSpec
end TCTex
end Towers

/-!
# Integer-quadrant reduction for uniform natural signed-block packets

A natural signed-block packet already proves its powered-commutator law when
both source exponents are natural.  Extending that law to arbitrary integer
exponents is therefore exactly the conjunction of the other three sign
quadrants.

This file packages that reduction without assuming any polynomial identity
principle for noncommutative products.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace UNPkt

universe u

open scoped commutatorElement

namespace TBPkt

/--
The three genuinely new sign quadrants needed to extend a natural packet to
arbitrary integer source exponents.
-/
structure NegativeQuadrantLaws
    {d n : ℕ}
    (packet : TBPkt.{u} d n) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (leftExponent : ℤ) (Int.negSucc rightMagnitude)).prod =
          ⁅left ^ (leftExponent : ℤ), right ^ Int.negSucc rightMagnitude⁆
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (Int.negSucc leftMagnitude) (rightExponent : ℤ)).prod =
          ⁅left ^ Int.negSucc leftMagnitude, right ^ (rightExponent : ℤ)⁆
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)).prod =
          ⁅left ^ Int.negSucc leftMagnitude,
            right ^ Int.negSucc rightMagnitude⁆

/--
The natural packet law and its three negative quadrants cover every pair of
integer source exponents.
-/
def allQuadrantLaws
    {d n : ℕ}
    {packet : TBPkt.{u} d n}
    (laws : packet.NegativeQuadrantLaws) :
    packet.AILift where
  listEval_eq left right leftExponent rightExponent := by
    cases leftExponent with
    | ofNat leftExponent =>
        cases rightExponent with
        | ofNat rightExponent =>
            simpa only [zpow_natCast] using
              packet.list_nat_cast
                left right leftExponent rightExponent
        | negSucc rightMagnitude =>
            exact laws.rightNegative
              left right leftExponent rightMagnitude
    | negSucc leftMagnitude =>
        cases rightExponent with
        | ofNat rightExponent =>
            exact laws.leftNegative
              left right leftMagnitude rightExponent
        | negSucc rightMagnitude =>
            exact laws.bothNegative
              left right leftMagnitude rightMagnitude

namespace AILift

/--
Every all-integral lift restricts to the three negative sign quadrants.
-/
def negativeQuadrantLaws
    {d n : ℕ}
    {packet : TBPkt.{u} d n}
    (lift : packet.AILift) :
    packet.NegativeQuadrantLaws where
  rightNegative left right leftExponent rightMagnitude :=
    lift.listEval_eq
      left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)
  leftNegative left right leftMagnitude rightExponent :=
    lift.listEval_eq
      left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)
  bothNegative left right leftMagnitude rightMagnitude :=
    lift.listEval_eq
      left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)

end AILift

/--
For one natural signed-block packet, an all-integral lift is equivalent to the
three negative sign-quadrant laws.
-/
theorem all_quadrant_laws
    {d n : ℕ}
    {packet : TBPkt.{u} d n} :
    packet.AILift ↔ packet.NegativeQuadrantLaws :=
  ⟨AILift.negativeQuadrantLaws,
    allQuadrantLaws⟩

end TBPkt
end UNPkt
end TCTex
end Towers

/-!
# Signed-block certificates for generated compatible grids

Every correction-tree term generated from the inverse raw trace carries a
complete represented singleton-family packet.  If retained compatible grids
satisfy homogeneous cancellation, two such generated parent terms therefore
produce an explicit signed-block certificate for their genuine filtered grid.

This is a schedule-local normalization result.  It does not replace filtered
grids by a full Cartesian inventory and does not use the conservative finite
closure as a collection schedule.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace CRGrid

open HACoeff
open CCGrida
open
  CRRoutea
open
  CRRoutea.RTPkt
open
  CSAggreg
open
  SHPres
open OCClos

/--
Homogeneous retained-grid cancellation certifies the genuine filtered grid of
two complete represented parent packets.
-/
noncomputable def compatibleBlockCertificate
    (kernel : CHCancel)
    {M N K : ℕ}
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTPkt leftTerm)
    (right : RTPkt rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    SBCert
      (compatibleCorrectionGrid left.terms right.terms)
      (leftTerm.family.correction rightTerm.family).recipe.erasedShape :=
  kernel.certificate left.packet right.packet
    left.term_mem right.term_mem hcompatible

/--
Choose the schedule-local signed-block certificate for a compatible pair of
terms recursively generated from the inverse raw trace.
-/
noncomputable def generatedCompatibleCertificate
    (kernel : CHCancel)
    {M N : ℕ}
    {leftTerm rightTerm : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hleft :
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) leftTerm)
    (hright :
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) rightTerm)
    (hcompatible : correctionPairCompatible leftTerm rightTerm) :
    SBCert
      (compatibleCorrectionGrid
        (correctionGeneratedRaw hleft).terms
        (correctionGeneratedRaw hright).terms)
      (leftTerm.family.correction rightTerm.family).recipe.erasedShape :=
  compatibleBlockCertificate kernel
    (correctionGeneratedRaw hleft)
    (correctionGeneratedRaw hright)
    hcompatible

end CRGrid
end TCTex
end Towers

/-!
# Empty and appended support-avoidance formula packets

Support avoidance distributes over list concatenation.  This file packages
that elementary fact at both layers of the support compiler: concrete
avoidance expressions are closed under empty packets and append, and fixed
formula-packet specialization is closed under the same operations.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace SFAppend

open HACoeff
open CEAlg
open CFAlg
open CFSubsti
open COAvoida
open SEComp
open SFSpec

/-- The empty concrete packet has the zero avoidance expression. -/
def nilExpression
    (M N K leftDegree rightDegree : ℕ)
    (slots : Finset (Fin K)) :
    SAExpr
      ([] : List (DFTerm M N K))
      slots leftDegree rightDegree where
  expression :=
    HBExpr.zero M N leftDegree rightDegree
  length_eq := by
    rfl

/-- Append two concrete avoidance expressions in the same bidegree. -/
def appendExpression
    {M N K leftDegree rightDegree : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {slots : Finset (Fin K)}
    (left :
      SAExpr
        leftTerms slots leftDegree rightDegree)
    (right :
      SAExpr
        rightTerms slots leftDegree rightDegree) :
    SAExpr
      (leftTerms ++ rightTerms) slots leftDegree rightDegree where
  expression := left.expression.add right.expression
  length_eq := by
    rw [avoiding_slots_append, List.length_append, Int.natCast_add,
      left.length_eq, right.length_eq]
    rfl

/-- The fixed zero packet specializes the empty concrete avoidance family. -/
def nilSpecialization
    (M N K leftDegree rightDegree : ℕ) :
    SASpec
      ([] : List (DFTerm M N K))
      (fun _slots => FPkt.zero leftDegree rightDegree)
      (fun slots => nilExpression M N K leftDegree rightDegree slots) where
  ofExpression_eq _slots := by
    rfl

/-- Pointwise fixed-packet addition specializes appended concrete avoidance families. -/
def appendSpecialization
    {M N K leftDegree rightDegree : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {leftPackets rightPackets :
      ∀ _slots : Finset (Fin K),
        HFPkt leftDegree rightDegree}
    {leftExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          leftTerms slots leftDegree rightDegree}
    {rightExpressions :
      ∀ slots : Finset (Fin K),
        SAExpr
          rightTerms slots leftDegree rightDegree}
    (left :
      SASpec
        leftTerms leftPackets leftExpressions)
    (right :
      SASpec
        rightTerms rightPackets rightExpressions) :
    SASpec
      (leftTerms ++ rightTerms)
      (fun slots =>
        FPkt.add (leftPackets slots) (rightPackets slots))
      (fun slots =>
        appendExpression (leftExpressions slots) (rightExpressions slots)) where
  ofExpression_eq slots := by
    rw [appendExpression, FPkt.ofExpression_add,
      left.ofExpression_eq slots, right.ofExpression_eq slots]

end SFAppend
end TCTex
end Towers

/-!
# Negative-input naturalization for uniform natural signed-block packets

A natural signed-block packet already evaluates correctly at arbitrary group
bases and natural source multiplicities.  For a negative integer exponent,
the target powered commutator can therefore be obtained by replacing the
corresponding group base by its inverse and using a positive natural
magnitude.

The remaining signed theorem is exactly the compatibility of the packet
product with those inverted substitutions.  This file packages that
recollection obligation and proves it equivalent to the all-integral lift.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace UNPkt

universe u

open scoped commutatorElement

namespace TBPkt

/--
The packet-product compatibility laws that naturalize negative integer inputs
by inverting the corresponding group bases.
-/
structure NegativeNaturalizationLaws
    {d n : ℕ}
    (packet : TBPkt.{u} d n) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (leftExponent : ℤ) (Int.negSucc rightMagnitude)).prod =
          (packet.packets.map fun nextPacket =>
            nextPacket.word.eval (HPAtom.eval left right⁻¹) ^
              nextPacket.profiles.value
                (leftExponent : ℤ) ((rightMagnitude + 1 : ℕ) : ℤ)).prod
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (Int.negSucc leftMagnitude) (rightExponent : ℤ)).prod =
          (packet.packets.map fun nextPacket =>
            nextPacket.word.eval (HPAtom.eval left⁻¹ right) ^
              nextPacket.profiles.value
                ((leftMagnitude + 1 : ℕ) : ℤ) (rightExponent : ℤ)).prod
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
        (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)).prod =
          (packet.packets.map fun nextPacket =>
            nextPacket.word.eval (HPAtom.eval left⁻¹ right⁻¹) ^
              nextPacket.profiles.value
                ((leftMagnitude + 1 : ℕ) : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).prod

/--
Negative-input naturalization and the known natural packet law prove the
three negative sign quadrants.
-/
def quadrantInputNaturalization
    {d n : ℕ}
    {packet : TBPkt.{u} d n}
    (laws : packet.NegativeNaturalizationLaws) :
    packet.NegativeQuadrantLaws where
  rightNegative left right leftExponent rightMagnitude := by
    rw [laws.rightNegative left right leftExponent rightMagnitude]
    simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
      packet.list_nat_cast
        left right⁻¹ leftExponent (rightMagnitude + 1)
  leftNegative left right leftMagnitude rightExponent := by
    rw [laws.leftNegative left right leftMagnitude rightExponent]
    simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
      packet.list_nat_cast
        left⁻¹ right (leftMagnitude + 1) rightExponent
  bothNegative left right leftMagnitude rightMagnitude := by
    rw [laws.bothNegative left right leftMagnitude rightMagnitude]
    simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
      packet.list_nat_cast
        left⁻¹ right⁻¹ (leftMagnitude + 1) (rightMagnitude + 1)

/--
Negative-input naturalization is sufficient for the full all-integral packet
law.
-/
def allNaturalizationLaws
    {d n : ℕ}
    {packet : TBPkt.{u} d n}
    (laws : packet.NegativeNaturalizationLaws) :
    packet.AILift :=
  allQuadrantLaws
    (quadrantInputNaturalization laws)

namespace AILift

/--
Every all-integral packet law supplies negative-input naturalization by
comparing its signed value with the natural packet law at inverted bases.
-/
def negativeNaturalizationLaws
    {d n : ℕ}
    {packet : TBPkt.{u} d n}
    (lift : packet.AILift) :
    packet.NegativeNaturalizationLaws where
  rightNegative left right leftExponent rightMagnitude := by
    calc
      (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (leftExponent : ℤ) (Int.negSucc rightMagnitude)).prod =
          ⁅left ^ (leftExponent : ℤ),
            right ^ Int.negSucc rightMagnitude⁆ :=
        lift.listEval_eq
          left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)
      _ =
          ⁅left ^ leftExponent, right⁻¹ ^ (rightMagnitude + 1)⁆ := by
        simp only [zpow_natCast, zpow_negSucc, ← inv_pow]
      _ =
          (packet.packets.map fun nextPacket =>
            nextPacket.word.eval (HPAtom.eval left right⁻¹) ^
              nextPacket.profiles.value
                (leftExponent : ℤ) ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
        (packet.list_nat_cast
          left right⁻¹ leftExponent (rightMagnitude + 1)).symm
  leftNegative left right leftMagnitude rightExponent := by
    calc
      (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (Int.negSucc leftMagnitude) (rightExponent : ℤ)).prod =
          ⁅left ^ Int.negSucc leftMagnitude,
            right ^ (rightExponent : ℤ)⁆ :=
        lift.listEval_eq
          left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)
      _ =
          ⁅left⁻¹ ^ (leftMagnitude + 1), right ^ rightExponent⁆ := by
        simp only [zpow_natCast, zpow_negSucc, ← inv_pow]
      _ =
          (packet.packets.map fun nextPacket =>
            nextPacket.word.eval (HPAtom.eval left⁻¹ right) ^
              nextPacket.profiles.value
                ((leftMagnitude + 1 : ℕ) : ℤ) (rightExponent : ℤ)).prod :=
        (packet.list_nat_cast
          left⁻¹ right (leftMagnitude + 1) rightExponent).symm
  bothNegative left right leftMagnitude rightMagnitude := by
    calc
      (packet.packets.map fun nextPacket =>
          nextPacket.word.eval (HPAtom.eval left right) ^
            nextPacket.profiles.value
              (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)).prod =
          ⁅left ^ Int.negSucc leftMagnitude,
            right ^ Int.negSucc rightMagnitude⁆ :=
        lift.listEval_eq
          left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)
      _ =
          ⁅left⁻¹ ^ (leftMagnitude + 1),
            right⁻¹ ^ (rightMagnitude + 1)⁆ := by
        simp only [zpow_negSucc, ← inv_pow]
      _ =
          (packet.packets.map fun nextPacket =>
            nextPacket.word.eval (HPAtom.eval left⁻¹ right⁻¹) ^
              nextPacket.profiles.value
                ((leftMagnitude + 1 : ℕ) : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
        (packet.list_nat_cast
          left⁻¹ right⁻¹ (leftMagnitude + 1) (rightMagnitude + 1)).symm

end AILift

/--
For one natural packet, its all-integral lift is equivalent to compatibility
with naturalizing every negative input by an inverted base substitution.
-/
theorem input_naturalization_laws
    {d n : ℕ}
    {packet : TBPkt.{u} d n} :
    packet.AILift ↔ packet.NegativeNaturalizationLaws :=
  ⟨AILift.negativeNaturalizationLaws,
    allNaturalizationLaws⟩

end TBPkt
end UNPkt
end TCTex
end Towers

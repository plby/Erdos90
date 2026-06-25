import Towers.Group.Zassenhaus.FamilySlotPackets

/-!
# Decorated-term worklists for exact Hall-Petresco realization slots

The word-level packet ledger records the correction words emitted by concrete
swaps.  More3 collection carries additional decorated-family provenance.  This
file lifts the same permutation-aware accounting to decorated terms and proves
that forgetting provenance recovers the existing word ledger.

This is the local state needed to propagate complete realization packets
through operational insertion traces.  It deliberately permits arbitrary
emission order: collection order is operational, while packet compression is
canonical only after the finite ledger closes.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace HSWork

open HACoeff
open HPWork
open HSPacket

/-- Permutation-aware exact-slot accounting for decorated correction terms. -/
structure PTLedger
    {M N K : ℕ}
    (B A : BFam M N)
    (left right : List (DFTerm M N K)) where
  emitted :
    List (DFTerm M N K)
  pending :
    List (DFTerm M N K)
  accounting :
    List.Perm (emitted ++ pending)
      (DFTerm.correctionGrid left right)

namespace PTLedger

/-- Start with every decorated Cartesian correction slot pending. -/
noncomputable def initial
    {M N K : ℕ}
    (B A : BFam M N)
    (left right : List (DFTerm M N K)) :
    PTLedger B A left right where
  emitted := []
  pending := DFTerm.correctionGrid left right
  accounting := by simp

/-- Consume any selected pending decorated correction term. -/
def emit
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    PTLedger B A left right where
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

/-- Emitting one term removes exactly one pending realization slot. -/
lemma pending_length_emit
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    (ledger.emit before term after hpending).pending.length + 1 =
      ledger.pending.length := by
  simp [emit, hpending]
  omega

/-- Every selected pending term admits an operational emission step. -/
lemma emit_pending
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ before after,
      ledger.pending = before ++ term :: after :=
  List.mem_iff_append.mp hterm

/--
When the decorated ledger closes, its emitted terms form the exact canonical
correction packet.
-/
lemma realization_emitted_nil
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right)
    (ledger : PTLedger B A left right)
    (hpending : ledger.pending = []) :
    RPFor (B.correction A) ledger.emitted := by
  apply (hleft.correctionGrid hright).trans
  simpa [hpending] using
    ledger.accounting.symm.map DFTerm.realizationToken

/--
Forgetting decorated provenance maps the term ledger into the existing
word-level permutation-aware slot ledger.
-/
noncomputable def toWordLedger
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right) :
    PSLedger B A
      (decoratedFamilyList left)
      (decoratedFamilyList right) where
  emitted := decoratedFamilyList ledger.emitted
  pending := decoratedFamilyList ledger.pending
  accounting := by
    have hwords :=
      ledger.accounting.map fun T => T.decorated.word
    calc
      List.Perm
          (decoratedFamilyList ledger.emitted ++
            decoratedFamilyList ledger.pending)
          (decoratedFamilyList
            (DFTerm.correctionGrid left right)) := by
        simpa [decoratedFamilyList, List.map_append] using hwords
      _ = PCCounti.correctionWords
          (decoratedFamilyList left)
          (decoratedFamilyList right) :=
        DFTerm.decorated_family_grid left right

@[simp]
lemma word_ledger_emitted
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right) :
    ledger.toWordLedger.emitted =
      decoratedFamilyList ledger.emitted :=
  rfl

@[simp]
lemma ledger_pending
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right) :
    ledger.toWordLedger.pending =
      decoratedFamilyList ledger.pending :=
  rfl

/--
Exact parent packets turn a decorated ledger into a work item for the
word-level permutation-aware scheduler.
-/
noncomputable def packetWorkItem
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right)
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    PWItem M N where
  leftFamily := B
  rightFamily := A
  leftWords := decoratedFamilyList left
  rightWords := decoratedFamilyList right
  leftPacket := hleft.toCollapsedFor
  rightPacket := hright.toCollapsedFor
  ledger := ledger.toWordLedger

@[simp]
lemma work_item_ledger
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right)
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    (ledger.packetWorkItem hleft hright).ledger =
      ledger.toWordLedger :=
  rfl

/-- The arithmetic decorated ledger can always be drained. -/
lemma exists_drain
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right) :
    ∃ final : PTLedger B A left right,
      final.pending = [] := by
  generalize hpending : ledger.pending = pending
  induction pending generalizing ledger with
  | nil =>
      exact ⟨ledger, hpending⟩
  | cons term pending ih =>
      let next := ledger.emit [] term pending (by simpa using hpending)
      exact ih next rfl

end PTLedger

/-- One concrete decorated correction selected for emission. -/
structure TSEmissi
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right) where
  leftTerm :
    DFTerm M N K
  rightTerm :
    DFTerm M N K
  left_mem :
    leftTerm ∈ left
  right_mem :
    rightTerm ∈ right
  pendingPrefix :
    List (DFTerm M N K)
  pendingSuffix :
    List (DFTerm M N K)
  pending_eq :
    ledger.pending =
      pendingPrefix ++ leftTerm.correction rightTerm :: pendingSuffix

namespace TSEmissi

/-- Build one decorated emission from a selected pending Cartesian term. -/
noncomputable def ofMemPending
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right)
    (leftTerm rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ left)
    (hright : rightTerm ∈ right)
    (hpending : leftTerm.correction rightTerm ∈ ledger.pending) :
    TSEmissi ledger := by
  let hdecomposition := List.mem_iff_append.mp hpending
  let before := hdecomposition.choose
  let after := hdecomposition.choose_spec.choose
  have hafter :
      ledger.pending =
        before ++ leftTerm.correction rightTerm :: after :=
    hdecomposition.choose_spec.choose_spec
  exact {
    leftTerm := leftTerm
    rightTerm := rightTerm
    left_mem := hleft
    right_mem := hright
    pendingPrefix := before
    pendingSuffix := after
    pending_eq := hafter }

/-- The selected decorated term belongs to the canonical Cartesian grid. -/
lemma correction_mem
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    {ledger : PTLedger B A left right}
    (emission : TSEmissi ledger) :
    emission.leftTerm.correction emission.rightTerm ∈
      DFTerm.correctionGrid left right := by
  apply List.mem_flatMap.mpr
  refine ⟨emission.leftTerm, emission.left_mem, ?_⟩
  exact List.mem_map.mpr
    ⟨emission.rightTerm, emission.right_mem, rfl⟩

/-- Consume the selected decorated realization slot. -/
noncomputable def emitLedger
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    {ledger : PTLedger B A left right}
    (emission : TSEmissi ledger) :
    PTLedger B A left right :=
  ledger.emit emission.pendingPrefix
    (emission.leftTerm.correction emission.rightTerm)
    emission.pendingSuffix emission.pending_eq

/-- Forgetting provenance preserves the selected pending-slot equation. -/
lemma word_ledger_pending
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    {ledger : PTLedger B A left right}
    (emission : TSEmissi ledger) :
    ledger.toWordLedger.pending =
      decoratedFamilyList emission.pendingPrefix ++
        .commutator emission.leftTerm.decorated.word
          emission.rightTerm.decorated.word ::
        decoratedFamilyList emission.pendingSuffix := by
  have hpending :=
    congrArg decoratedFamilyList emission.pending_eq
  simpa [decoratedFamilyList, List.map_append,
    DTerm.correction] using hpending

/-- Forgetting provenance turns one term emission into one word-ledger emission. -/
noncomputable def emitWordLedger
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    {ledger : PTLedger B A left right}
    (emission : TSEmissi ledger) :
    PSLedger B A
      (decoratedFamilyList left)
      (decoratedFamilyList right) :=
  ledger.toWordLedger.emit
    (decoratedFamilyList emission.pendingPrefix)
    (.commutator emission.leftTerm.decorated.word
      emission.rightTerm.decorated.word)
    (decoratedFamilyList emission.pendingSuffix)
    emission.word_ledger_pending

/--
With exact parent packets attached, the selected decorated term is an
emission accepted by the existing word-level work item.
-/
noncomputable def concreteSlotEmission
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    {ledger : PTLedger B A left right}
    (emission : TSEmissi ledger)
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    HPWork.CSEmissi
      (ledger.packetWorkItem hleft hright) where
  leftWord := emission.leftTerm.decorated.word
  rightWord := emission.rightTerm.decorated.word
  left_mem := List.mem_map.mpr ⟨emission.leftTerm, emission.left_mem, rfl⟩
  right_mem := List.mem_map.mpr ⟨emission.rightTerm, emission.right_mem, rfl⟩
  pendingPrefix := decoratedFamilyList emission.pendingPrefix
  pendingSuffix := decoratedFamilyList emission.pendingSuffix
  pending_eq := emission.word_ledger_pending

/-- One decorated slot emission therefore supplies one exact adjacent word rewrite. -/
def labelledWordStep
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    {ledger : PTLedger B A left right}
    (emission : TSEmissi ledger)
    (pre post :
      List (CWord (LabelledAtom M N))) :
    BBSched.LWStep
      (pre ++
        [emission.leftTerm.decorated.word,
          emission.rightTerm.decorated.word] ++ post)
      (pre ++
        [(emission.leftTerm.correction emission.rightTerm).decorated.word,
          emission.rightTerm.decorated.word,
          emission.leftTerm.decorated.word] ++ post) := by
  simpa [DTerm.correction] using
    (BBSched.LWStep.obstruction
      pre post emission.leftTerm.decorated.word
        emission.rightTerm.decorated.word)

end TSEmissi

namespace PTLedger

/-- One exact decorated-slot consumption transition. -/
inductive Step
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)} :
    PTLedger B A left right →
      PTLedger B A left right →
        Prop where
  | emit
      {ledger : PTLedger B A left right}
      (emission : TSEmissi ledger) :
      Step ledger emission.emitLedger

/-- Finite exact-slot consumption run for one decorated packet ledger. -/
abbrev Rewrites
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger final : PTLedger B A left right) :
    Prop :=
  Relation.ReflTransGen Step ledger final

/-- Every still-pending decorated term belongs to a parent Cartesian pair. -/
lemma parent_terms_pending
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ leftTerm ∈ left, ∃ rightTerm ∈ right,
      term = leftTerm.correction rightTerm := by
  have hgrid : term ∈ DFTerm.correctionGrid left right :=
    ledger.accounting.subset (List.mem_append_right ledger.emitted hterm)
  rcases List.mem_flatMap.mp hgrid with ⟨leftTerm, hleft, hterm⟩
  rcases List.mem_map.mp hterm with ⟨rightTerm, hright, rfl⟩
  exact ⟨leftTerm, hleft, rightTerm, hright, rfl⟩

/--
The decorated arithmetic ledger can always be drained by exact selected-slot
emissions.  This does not yet assert that a global collector encounters the
slots in this freely chosen order.
-/
lemma rewrites_pending_nil
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (ledger : PTLedger B A left right) :
    ∃ final, Rewrites ledger final ∧ final.pending = [] := by
  generalize hpending : ledger.pending = pending
  induction pending generalizing ledger with
  | nil =>
      exact ⟨ledger, Relation.ReflTransGen.refl, hpending⟩
  | cons term pending ih =>
      have hterm : term ∈ ledger.pending := by
        rw [hpending]
        simp
      rcases ledger.parent_terms_pending hterm with
        ⟨leftTerm, hleft, rightTerm, hright, htermEq⟩
      subst term
      let emission : TSEmissi ledger := {
        leftTerm := leftTerm
        rightTerm := rightTerm
        left_mem := hleft
        right_mem := hright
        pendingPrefix := []
        pendingSuffix := pending
        pending_eq := by simpa using hpending }
      rcases ih emission.emitLedger rfl with ⟨final, hrewrites, hclosed⟩
      exact ⟨final, hrewrites.head (Step.emit emission), hclosed⟩

end PTLedger

end HSWork
end TCTex
end Towers

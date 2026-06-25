import Towers.Group.Zassenhaus.RecursiveObstructions

/-!
# Permutation-aware Hall-Petresco packet worklists

A concrete collector does not have to emit the Cartesian correction slots in
the row-major order used by `BFam.correction`.  It may select any still
pending slot while it moves concrete words.  Since collapsed packets remember
only one erased shape and an exact count, the accounting invariant should be a
permutation rather than an equality of lists.

This file packages that invariant, connects one consumed slot to the exact
concrete-word rewrite, and proves that a closed finite worklist compresses to
canonical family endpoints.  The remaining nonterminal theorem is to build a
worklist run whose concrete swaps reach such a closed state.  This file is
intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace HPWork

open HACoeff
open BBSched

/--
Slot accounting for one correction packet when concrete swaps may emit the
Cartesian slots in an arbitrary order.
-/
structure PSLedger
    {M N : ℕ}
    (B A : BFam M N)
    (left right : List (CWord (LabelledAtom M N))) where
  emitted :
    List (CWord (LabelledAtom M N))
  pending :
    List (CWord (LabelledAtom M N))
  accounting :
    List.Perm (emitted ++ pending)
      (PCCounti.correctionWords left right)

namespace PSLedger

/-- Start with every Cartesian correction slot pending. -/
def initial
    {M N : ℕ}
    (B A : BFam M N)
    (left right : List (CWord (LabelledAtom M N))) :
    PSLedger B A left right where
  emitted := []
  pending := PCCounti.correctionWords left right
  accounting := by simp

/--
Consume any selected pending slot.  The emitted prefix grows in operational
order while the accounting theorem forgets that order by permutation.
-/
def emit
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (ledger : PSLedger B A left right)
    (before : List (CWord (LabelledAtom M N)))
    (w : CWord (LabelledAtom M N))
    (after : List (CWord (LabelledAtom M N)))
    (hpending : ledger.pending = before ++ w :: after) :
    PSLedger B A left right where
  emitted := ledger.emitted ++ [w]
  pending := before ++ after
  accounting := by
    apply List.Perm.trans _ ledger.accounting
    rw [hpending]
    simp only [List.append_assoc]
    apply List.Perm.append_left
    have hcomm :
        List.Perm
          (([w] : List (CWord (LabelledAtom M N))) ++ before)
          (before ++ [w]) :=
      List.perm_append_comm
    simpa [List.append_assoc] using hcomm.append_right after

/-- Every selected pending word can be consumed. -/
lemma emit_pending
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (ledger : PSLedger B A left right)
    {w : CWord (LabelledAtom M N)}
    (hw : w ∈ ledger.pending) :
    ∃ before after,
      ledger.pending = before ++ w :: after := by
  exact List.mem_iff_append.mp hw

/-- Emitting one slot removes exactly one pending position. -/
lemma pending_length_emit
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (ledger : PSLedger B A left right)
    (before : List (CWord (LabelledAtom M N)))
    (w : CWord (LabelledAtom M N))
    (after : List (CWord (LabelledAtom M N)))
    (hpending : ledger.pending = before ++ w :: after) :
    (ledger.emit before w after hpending).pending.length + 1 =
      ledger.pending.length := by
  simp [emit, hpending]
  omega

/--
Permuted emitted and pending words still form a closed collapsed correction
packet.  The common erased shape makes slot order irrelevant.
-/
lemma closed_append_pending
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : PSLedger B A left right) :
    PCCounti.CPFor
      (B.correction A) (ledger.emitted ++ ledger.pending) := by
  have hcanonical :
      PCCounti.CPFor
        (B.correction A)
        (PCCounti.correctionWords left right) :=
    hleft.correctionWords hright
  exact {
    same_shape := fun w hw =>
      hcanonical.same_shape w (ledger.accounting.subset hw)
    length_eq := by
      rw [ledger.accounting.length_eq]
      exact hcanonical.length_eq }

/-- The emitted words of a permuted ledger always form a valid partial packet. -/
def partialCollapsedPacket
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : PSLedger B A left right) :
    HPCollap.PCPkt M N where
  family := B.correction A
  words := ledger.emitted
  same_shape := by
    intro w hw
    exact (ledger.closed_append_pending hleft hright).same_shape w
      (List.mem_append_left _ hw)
  length_le := by
    have hlength := (ledger.closed_append_pending hleft hright).length_eq
    simp only [List.length_append] at hlength
    omega

/-- No pending slots means that the operationally emitted prefix is closed. -/
lemma emitted_pending_nil
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : PSLedger B A left right)
    (hpending : ledger.pending = []) :
    PCCounti.CPFor
      (B.correction A) ledger.emitted := by
  simpa [hpending] using ledger.closed_append_pending hleft hright

/-- One arithmetic slot-consumption transition. -/
inductive Step
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))} :
    PSLedger B A left right →
      PSLedger B A left right →
        Prop where
  | emit
      (ledger : PSLedger B A left right)
      (before : List (CWord (LabelledAtom M N)))
      (w : CWord (LabelledAtom M N))
      (after : List (CWord (LabelledAtom M N)))
      (hpending : ledger.pending = before ++ w :: after) :
      Step ledger (ledger.emit before w after hpending)

/-- Finite slot-consumption run for one packet ledger. -/
abbrev Rewrites
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (ledger final : PSLedger B A left right) :
    Prop :=
  Relation.ReflTransGen Step ledger final

/--
The arithmetic ledger can always be drained.  This does not claim that an
arbitrary concrete collection schedule emits slots in this order.
-/
lemma rewrites_pending_nil
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (ledger : PSLedger B A left right) :
    ∃ final, Rewrites ledger final ∧ final.pending = [] := by
  generalize hpending : ledger.pending = pending
  induction pending generalizing ledger with
  | nil =>
      exact ⟨ledger, Relation.ReflTransGen.refl, hpending⟩
  | cons w pending ih =>
      let next := ledger.emit [] w pending (by simpa using hpending)
      rcases ih next rfl with ⟨final, hrewrites, hclosed⟩
      refine ⟨final, ?_, hclosed⟩
      exact hrewrites.head
        (Step.emit ledger [] w pending (by simpa using hpending))

end PSLedger

/-- One open packet in the finite operational worklist. -/
structure PWItem
    (M N : ℕ) where
  leftFamily :
    BFam M N
  rightFamily :
    BFam M N
  leftWords :
    List (CWord (LabelledAtom M N))
  rightWords :
    List (CWord (LabelledAtom M N))
  leftPacket :
    PCCounti.CPFor leftFamily leftWords
  rightPacket :
    PCCounti.CPFor rightFamily rightWords
  ledger :
    PSLedger leftFamily rightFamily leftWords rightWords

namespace PWItem

/-- Canonical parent families begin with one open Cartesian correction packet. -/
def initial
    {M N : ℕ}
    (B A : BFam M N) :
    PWItem M N where
  leftFamily := B
  rightFamily := A
  leftWords := B.realizations
  rightWords := A.realizations
  leftPacket := PCCounti.CPFor.realizations B
  rightPacket := PCCounti.CPFor.realizations A
  ledger :=
    PSLedger.initial B A B.realizations A.realizations

/-- Consume one selected correction slot in one work item. -/
def emit
    {M N : ℕ}
    (item : PWItem M N)
    (before : List (CWord (LabelledAtom M N)))
    (w : CWord (LabelledAtom M N))
    (after : List (CWord (LabelledAtom M N)))
    (hpending : item.ledger.pending = before ++ w :: after) :
    PWItem M N where
  leftFamily := item.leftFamily
  rightFamily := item.rightFamily
  leftWords := item.leftWords
  rightWords := item.rightWords
  leftPacket := item.leftPacket
  rightPacket := item.rightPacket
  ledger := item.ledger.emit before w after hpending

/-- One work item is closed when it has no pending Cartesian slots. -/
def Closed
    {M N : ℕ}
    (item : PWItem M N) :
    Prop :=
  item.ledger.pending = []

/-- A closed work item compresses to its canonical correction family. -/
lemma closedPacket
    {M N : ℕ}
    (item : PWItem M N)
    (hclosed : item.Closed) :
    PCCounti.CPFor
      (item.leftFamily.correction item.rightFamily)
      item.ledger.emitted :=
  item.ledger.emitted_pending_nil
    item.leftPacket item.rightPacket hclosed

/-- Number of still-open Cartesian slots in one packet work item. -/
def pendingSlots
    {M N : ℕ}
    (item : PWItem M N) :
    ℕ :=
  item.ledger.pending.length

lemma pendingSlots_emit
    {M N : ℕ}
    (item : PWItem M N)
    (before : List (CWord (LabelledAtom M N)))
    (w : CWord (LabelledAtom M N))
    (after : List (CWord (LabelledAtom M N)))
    (hpending : item.ledger.pending = before ++ w :: after) :
    (item.emit before w after hpending).pendingSlots + 1 =
      item.pendingSlots :=
  item.ledger.pending_length_emit before w after hpending

end PWItem

/-- A finite list of open or closed correction packets. -/
abbrev PWork
    (M N : ℕ) :=
  List (PWItem M N)

namespace PWork

/-- Total number of pending Cartesian slots in a packet worklist. -/
def pendingSlots
    {M N : ℕ}
    (worklist : PWork M N) :
    ℕ :=
  (worklist.map PWItem.pendingSlots).sum

/-- Every packet in a worklist has been exhausted. -/
def Closed
    {M N : ℕ}
    (worklist : PWork M N) :
    Prop :=
  ∀ item ∈ worklist, item.Closed

/-- Consuming one selected slot inside one worklist item. -/
inductive Step
    {M N : ℕ} :
    PWork M N → PWork M N → Prop where
  | emit
      (pre post : PWork M N)
      (item : PWItem M N)
      (before : List (CWord (LabelledAtom M N)))
      (w : CWord (LabelledAtom M N))
      (after : List (CWord (LabelledAtom M N)))
      (hpending : item.ledger.pending = before ++ w :: after) :
      Step
        (pre ++ item :: post)
        (pre ++ item.emit before w after hpending :: post)

/-- Every worklist slot-consumption step strictly decreases the open-slot count. -/
lemma pending_slots_step
    {M N : ℕ}
    {before after : PWork M N}
    (hstep : Step before after) :
    pendingSlots after < pendingSlots before := by
  cases hstep with
  | emit pre post item before w after hpending =>
      simp only [pendingSlots, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons]
      have hlength := item.pendingSlots_emit before w after hpending
      omega

/-- Closed worklists compress to consecutive canonical correction-family endpoints. -/
lemma packeted_closed
    {M N : ℕ}
    (worklist : PWork M N)
    (hclosed : worklist.Closed) :
    PCCounti.CPBy
      (worklist.map fun item =>
        item.leftFamily.correction item.rightFamily)
      (worklist.flatMap fun item => item.ledger.emitted) := by
  induction worklist with
  | nil =>
      exact PCCounti.CPBy.nil
  | cons item worklist ih =>
      apply PCCounti.CPBy.cons
        (item.leftFamily.correction item.rightFamily)
        (worklist.map fun item =>
          item.leftFamily.correction item.rightFamily)
        item.ledger.emitted
        (worklist.flatMap fun item => item.ledger.emitted)
      · exact item.closedPacket (hclosed item (by simp))
      · apply ih
        intro next hnext
        exact hclosed next (by simp [hnext])

end PWork

/--
One concrete word swap paired with the pending correction slot it consumes.
The scheduler still has to arrange these swaps into a closed worklist run.
-/
structure CSEmissi
    {M N : ℕ}
    (item : PWItem M N) where
  leftWord :
    CWord (LabelledAtom M N)
  rightWord :
    CWord (LabelledAtom M N)
  left_mem :
    leftWord ∈ item.leftWords
  right_mem :
    rightWord ∈ item.rightWords
  pendingPrefix :
    List (CWord (LabelledAtom M N))
  pendingSuffix :
    List (CWord (LabelledAtom M N))
  pending_eq :
    item.ledger.pending =
      pendingPrefix ++ .commutator leftWord rightWord :: pendingSuffix

namespace CSEmissi

/-- Consume the selected pending slot in the corresponding arithmetic ledger. -/
def emitItem
    {M N : ℕ}
    {item : PWItem M N}
    (emission : CSEmissi item) :
    PWItem M N :=
  item.emit emission.pendingPrefix
    (.commutator emission.leftWord emission.rightWord)
    emission.pendingSuffix emission.pending_eq

/-- The selected concrete correction really belongs to the Cartesian packet. -/
lemma correction_mem
    {M N : ℕ}
    {item : PWItem M N}
    (emission : CSEmissi item) :
    CWord.commutator emission.leftWord emission.rightWord ∈
      PCCounti.correctionWords
        item.leftWords item.rightWords := by
  apply List.mem_flatMap.mpr
  refine ⟨emission.leftWord, emission.left_mem, ?_⟩
  exact List.mem_map.mpr
    ⟨emission.rightWord, emission.right_mem, rfl⟩

/-- The consumed slot is exactly the correction emitted by one concrete rewrite. -/
def labelledWordStep
    {M N : ℕ}
    {item : PWItem M N}
    (emission : CSEmissi item)
    (pre post : List (CWord (LabelledAtom M N))) :
    BBSched.LWStep
      (pre ++ [emission.leftWord, emission.rightWord] ++ post)
      (pre ++
        [.commutator emission.leftWord emission.rightWord,
          emission.rightWord, emission.leftWord] ++ post) :=
  BBSched.LWStep.obstruction
    pre post emission.leftWord emission.rightWord

end CSEmissi

end HPWork
end TCTex
end Towers

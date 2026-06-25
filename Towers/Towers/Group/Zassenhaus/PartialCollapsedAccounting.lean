import Towers.Group.Zassenhaus.CollapsedPacketCounting

/-!
# Partial collapsed Hall-Petresco packet accounting

A concrete collector emits pairwise corrections one slot at a time.  A single
swap therefore does not produce a complete correction family.  This file keeps
the exact arithmetic invariant needed while a collapsed packet is still open:
the words already emitted, followed by the pending words, are precisely the
Cartesian correction list.

When the pending list is empty, the partial packet closes to the canonical
correction-family endpoint.  This file is intentionally not imported by the
existing collection proof.
-/

namespace Towers
namespace TCTex
namespace HPCollap

open HACoeff

/-- A not-yet-closed packet of words of one target family shape. -/
structure PCPkt
    (M N : ℕ) where
  family :
    BFam M N
  words :
    List (CWord (LabelledAtom M N))
  same_shape :
    PCCounti.SCShape
      family.recipe.erasedShape words
  length_le :
    words.length ≤ family.realizations.length

namespace PCPkt

/-- A partial packet is closed exactly when all family slots have been filled. -/
def Closed
    {M N : ℕ}
    (P : PCPkt M N) :
    Prop :=
  P.words.length = P.family.realizations.length

/-- Start an empty partial packet for one target family. -/
def empty
    {M N : ℕ}
    (F : BFam M N) :
    PCPkt M N where
  family := F
  words := []
  same_shape := by
    intro w hw
    simp at hw
  length_le := by
    simp

/-- Regard a closed collapsed packet as a partial packet with no open slots. -/
def collapsedPacket
    {M N : ℕ}
    {F : BFam M N}
    {words : List (CWord (LabelledAtom M N))}
    (hpacket : PCCounti.CPFor F words) :
    PCPkt M N where
  family := F
  words := words
  same_shape := hpacket.same_shape
  length_le := hpacket.length_eq.le

/-- Append a same-shape block while preserving the packet-size bound. -/
def append
    {M N : ℕ}
    (P : PCPkt M N)
    (extra : List (CWord (LabelledAtom M N)))
    (hextra :
      PCCounti.SCShape
        P.family.recipe.erasedShape extra)
    (hlength :
      P.words.length + extra.length ≤ P.family.realizations.length) :
    PCPkt M N where
  family := P.family
  words := P.words ++ extra
  same_shape := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact P.same_shape w hw
    · exact hextra w hw
  length_le := by
    simpa using hlength

/-- Append one same-shape word while preserving the packet-size bound. -/
def push
    {M N : ℕ}
    (P : PCPkt M N)
    (w : CWord (LabelledAtom M N))
    (hw : collapseWord w = P.family.recipe.erasedShape)
    (hlength :
      P.words.length + 1 ≤ P.family.realizations.length) :
    PCPkt M N :=
  P.append [w] (by
    intro u hu
    rw [List.mem_singleton] at hu
    subst u
    exact hw) (by
      simpa using hlength)

/-- A closed partial packet is a genuine collapsed packet. -/
lemma collapsed_packet_closed
    {M N : ℕ}
    (P : PCPkt M N)
    (hclosed : P.Closed) :
    PCCounti.CPFor P.family P.words where
  same_shape := P.same_shape
  length_eq := hclosed

@[simp]
lemma empty_words
    {M N : ℕ}
    (F : BFam M N) :
    (empty F).words = [] :=
  rfl

@[simp]
lemma append_words
    {M N : ℕ}
    (P : PCPkt M N)
    (extra : List (CWord (LabelledAtom M N)))
    (hextra hlength) :
    (P.append extra hextra hlength).words = P.words ++ extra :=
  rfl

@[simp]
lemma push_words
    {M N : ℕ}
    (P : PCPkt M N)
    (w : CWord (LabelledAtom M N))
    (hw hlength) :
    (P.push w hw hlength).words = P.words ++ [w] :=
  rfl

end PCPkt

/--
Exact slot ledger for one Cartesian correction family.  `emitted` is the prefix
already produced by concrete swaps; `pending` is the suffix still to emit.
-/
structure CSLedger
    {M N : ℕ}
    (B A : BFam M N)
    (left right : List (CWord (LabelledAtom M N))) where
  emitted :
    List (CWord (LabelledAtom M N))
  pending :
    List (CWord (LabelledAtom M N))
  accounting :
    emitted ++ pending =
      PCCounti.correctionWords left right

namespace CSLedger

/-- Start with every Cartesian correction slot pending. -/
def initial
    {M N : ℕ}
    (B A : BFam M N)
    (left right : List (CWord (LabelledAtom M N))) :
    CSLedger B A left right where
  emitted := []
  pending := PCCounti.correctionWords left right
  accounting := by simp

/-- Move one known head slot from the pending suffix to the emitted prefix. -/
def emitHead
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (ledger : CSLedger B A left right)
    (w : CWord (LabelledAtom M N))
    (pending : List (CWord (LabelledAtom M N)))
    (hpending : ledger.pending = w :: pending) :
    CSLedger B A left right where
  emitted := ledger.emitted ++ [w]
  pending := pending
  accounting := by
    calc
      (ledger.emitted ++ [w]) ++ pending =
          ledger.emitted ++ (w :: pending) := by simp [List.append_assoc]
      _ = ledger.emitted ++ ledger.pending := by rw [hpending]
      _ = PCCounti.correctionWords left right :=
        ledger.accounting

/-- Ledger words, both emitted and pending, form the full closed correction packet. -/
lemma closed_append_pending
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : CSLedger B A left right) :
    PCCounti.CPFor (B.correction A)
      (ledger.emitted ++ ledger.pending) := by
  rw [ledger.accounting]
  exact hleft.correctionWords hright

/-- The emitted prefix of an exact ledger is always a valid partial packet. -/
def partialCollapsedPacket
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : CSLedger B A left right) :
    PCPkt M N where
  family := B.correction A
  words := ledger.emitted
  same_shape := by
    intro w hw
    exact (ledger.closed_append_pending hleft hright).same_shape w
      (List.mem_append_left _ hw)
  length_le := by
    have hlength :=
      (ledger.closed_append_pending hleft hright).length_eq
    simp only [List.length_append] at hlength
    omega

/-- The ledger suffix length is exactly the number of still-open packet slots. -/
lemma remaining_slots_pending
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : CSLedger B A left right) :
    (B.correction A).realizations.length -
          (ledger.partialCollapsedPacket hleft hright).words.length =
      ledger.pending.length := by
  have hlength :=
    (ledger.closed_append_pending hleft hright).length_eq
  change
    (B.correction A).realizations.length - ledger.emitted.length =
      ledger.pending.length
  simp only [List.length_append] at hlength
  omega

/-- With no pending suffix, the emitted prefix closes to the correction family. -/
lemma emitted_pending_nil
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : CSLedger B A left right)
    (hpending : ledger.pending = []) :
    PCCounti.CPFor
      (B.correction A) ledger.emitted := by
  simpa [hpending] using ledger.closed_append_pending hleft hright

/-- Exhausting the ledger suffix is equivalent to closing its emitted packet. -/
lemma partial_pending_nil
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : PCCounti.CPFor B left)
    (hright : PCCounti.CPFor A right)
    (ledger : CSLedger B A left right) :
    (ledger.partialCollapsedPacket hleft hright).Closed ↔
      ledger.pending = [] := by
  constructor
  · intro hclosed
    have hremaining := ledger.remaining_slots_pending hleft hright
    have hpendingLength : ledger.pending.length = 0 := by
      rw [← hremaining]
      exact Nat.sub_eq_zero_of_le hclosed.ge
    exact List.length_eq_zero_iff.mp hpendingLength
  · intro hpending
    have hpacket :=
      emitted_pending_nil hleft hright ledger hpending
    exact hpacket.length_eq

end CSLedger

/-- A list of open or closed collapsed packets. -/
abbrev PartialCollapsedState
    (M N : ℕ) :=
  List (PCPkt M N)

/-- Every packet in a partial state has reached its exact family size. -/
def PartialPacketsClosed
    {M N : ℕ}
    (state : PartialCollapsedState M N) :
    Prop :=
  ∀ P ∈ state, P.Closed

/-- Fully closed partial states compress to consecutive canonical family endpoints. -/
lemma PCCounti.CPBy.closed_partial_state
    {M N : ℕ}
    (state : PartialCollapsedState M N)
    (hclosed : PartialPacketsClosed state) :
    PCCounti.CPBy
      (state.map PCPkt.family)
      (state.flatMap PCPkt.words) := by
  induction state with
  | nil =>
      exact PCCounti.CPBy.nil
  | cons P state ih =>
      apply PCCounti.CPBy.cons P.family
        (state.map PCPkt.family)
        P.words (state.flatMap PCPkt.words)
      · exact P.collapsed_packet_closed (hclosed P (by simp))
      · apply ih
        intro Q hQ
        exact hclosed Q (by simp [hQ])

end HPCollap
end TCTex
end Towers

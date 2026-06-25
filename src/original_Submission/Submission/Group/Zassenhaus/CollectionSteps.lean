import Submission.Group.Zassenhaus.Factors

/-!
# Symbolic steps for repeated-power Hall collection

The hard part of repeated-power collection is constructing the finite packet of
higher-weight corrections emitted when two adjacent symbolic power factors are
swapped.  This file isolates that constructor obligation.  Once a correction
packet is available, the exact noncommutative rewrite and its truncation
behavior are formal consequences.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

/--
The symbolic output required to move one evaluated power factor `B` to the
right of one evaluated power factor `A`.

Every emitted factor has strictly larger word weight than both inputs.  This is
the termination invariant used by a repeated-block Hall collector.
-/
structure SHPkt
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (n : ℕ)
    (B A : SPFactora H inputWeight) where
  factors :
    List (SPFactora H inputWeight)
  listEval_eq :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q factors =
        ⁅B.eval (n := n) q, A.eval (n := n) q⁆
  word_weight_left :
    ∀ x ∈ factors,
      B.word.weight PEAddres.weight <
        x.word.weight PEAddres.weight
  word_weight_right :
    ∀ x ∈ factors,
      A.word.weight PEAddres.weight <
        x.word.weight PEAddres.weight

namespace SHPkt

/-- A trivial commutator needs no emitted correction factors. -/
def empty_commutator_one
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (B A : SPFactora H inputWeight)
    (hcommutator :
      ∀ q : ℕ, ⁅B.eval (n := n) q, A.eval (n := n) q⁆ = 1) :
    SHPkt n B A where
  factors := []
  listEval_eq q := by
    simpa using (hcommutator q).symm
  word_weight_left x hx := by
    simp at hx
  word_weight_right x hx := by
    simp at hx

/-- If the left input has reached the truncation cutoff, its correction is empty. -/
def empty_n_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (B A : SPFactora H inputWeight)
    (hB : n ≤ B.word.weight PEAddres.weight) :
    SHPkt n B A :=
  empty_commutator_one B A fun q => by
    rw [B.eval_n_weight q hB]
    simp

/-- If the right input has reached the truncation cutoff, its correction is empty. -/
def empty_n_right
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (B A : SPFactora H inputWeight)
    (hA : n ≤ A.word.weight PEAddres.weight) :
    SHPkt n B A :=
  empty_commutator_one B A fun q => by
    rw [A.eval_n_weight q hA]
    simp

/--
When powered commutators reduce to the leading Hall bracket, that bracket is a
one-factor correction packet.
-/
def singletonBracket
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (B A : SPFactora H inputWeight)
    (heval :
      ∀ q : ℕ,
        (B.bracket A).eval (n := n) q =
          ⁅B.eval (n := n) q, A.eval (n := n) q⁆) :
    SHPkt n B A where
  factors := [B.bracket A]
  listEval_eq q := by
    simpa using heval q
  word_weight_left x hx := by
    rcases List.mem_singleton.mp hx with rfl
    exact B.word_bracket_left A
  word_weight_right x hx := by
    rcases List.mem_singleton.mp hx with rfl
    exact B.word_bracket_right A

/-- Packet evaluation is exactly the correction needed for the adjacent swap. -/
lemma list_mul_swap
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A)
    (q : ℕ) :
    SPFactora.listEval (n := n) q C.factors *
          A.eval (n := n) q * B.eval (n := n) q =
      B.eval (n := n) q * A.eval (n := n) q := by
  rw [C.listEval_eq]
  simp [commutatorElement_def, mul_assoc]

/-- Left-input weight growth in a form convenient for arithmetic bounds. -/
lemma succ_weight_left
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    {n : ℕ}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    B.word.weight PEAddres.weight + 1 ≤
      x.word.weight PEAddres.weight :=
  C.word_weight_left x hx

/-- Right-input weight growth in a form convenient for arithmetic bounds. -/
lemma succ_weight_right
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    {n : ℕ}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    A.word.weight PEAddres.weight + 1 ≤
      x.word.weight PEAddres.weight :=
  C.word_weight_right x hx

/--
A correction packet emitted one step below the truncation cutoff is already
trivial in the truncation quotient.
-/
lemma n_succ_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A)
    (q : ℕ)
    (hB : n ≤ B.word.weight PEAddres.weight + 1) :
    SPFactora.listEval (n := n) q C.factors = 1 := by
  apply SPFactora.list_n_weight
  intro x hx
  exact hB.trans (C.succ_weight_left hx)

/-- The symmetric truncation criterion using the right packet input. -/
lemma n_succ_right
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A)
    (q : ℕ)
    (hA : n ≤ A.word.weight PEAddres.weight + 1) :
    SPFactora.listEval (n := n) q C.factors = 1 := by
  apply SPFactora.list_n_weight
  intro x hx
  exact hA.trans (C.succ_weight_right hx)

end SHPkt

/-- One sound adjacent repeated-power Hall-collection move. -/
inductive SCStepa
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight n : ℕ) :
    List (SPFactora H inputWeight) →
      List (SPFactora H inputWeight) → Prop where
  | obstruction
      (P S : List (SPFactora H inputWeight))
      (B A : SPFactora H inputWeight)
      (C : SHPkt n B A) :
      SCStepa H inputWeight n
        (P ++ [B, A] ++ S)
        (P ++ C.factors ++ [A, B] ++ S)

/-- Finite sequence of sound adjacent repeated-power Hall-collection moves. -/
abbrev PCRw
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (n : ℕ)
    (L R : List (SPFactora H inputWeight)) :
    Prop :=
  Relation.ReflTransGen (SCStepa H inputWeight n) L R

/-- One repeated-power Hall-collection move preserves the evaluated product. -/
lemma SCStepa.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    {L R : List (SPFactora H inputWeight)}
    (h : SCStepa H inputWeight n L R)
    (q : ℕ) :
    SPFactora.listEval (n := n) q R =
      SPFactora.listEval (n := n) q L := by
  cases h with
  | obstruction P S B A C =>
      calc
        SPFactora.listEval (n := n) q
              (P ++ C.factors ++ [A, B] ++ S) =
            SPFactora.listEval q P *
                (SPFactora.listEval q C.factors *
                  A.eval q * B.eval q) *
              SPFactora.listEval q S := by
            simp [mul_assoc]
        _ =
            SPFactora.listEval q P *
                (B.eval q * A.eval q) *
              SPFactora.listEval q S := by
            rw [C.list_mul_swap]
        _ =
            SPFactora.listEval (n := n) q
              (P ++ [B, A] ++ S) := by
            simp [mul_assoc]

/-- Any finite repeated-power Hall-collection run preserves evaluation. -/
lemma PCRw.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    {L R : List (SPFactora H inputWeight)}
    (h : PCRw n L R)
    (q : ℕ) :
    SPFactora.listEval (n := n) q R =
      SPFactora.listEval (n := n) q L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq q).trans ih

end TCTex
end Submission

import Towers.Group.Zassenhaus.CollectionSteps

/-!
# Truncating symbolic Hall power collection

In the free nilpotent quotient `F_d / gamma_n(F_d)`, every symbolic power
factor of ordinary word weight at least `n` evaluates to the identity.  A
repeated-power Hall collector can erase such factors as soon as they appear.

This file packages physical truncation for repeated-power factor lists and
correction packets.  Retained corrections lie strictly between their parent
weights and the fixed cutoff.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace SPFactora

/-- Remaining room below the nilpotent truncation cutoff. -/
def cutoffDefect
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (x : SPFactora H inputWeight) :
    ℕ :=
  n - x.word.weight PEAddres.weight

/-- Keep precisely the symbolic power factors whose word weight is below `n`. -/
def truncate
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (L : List (SPFactora H inputWeight)) :
    List (SPFactora H inputWeight) :=
  L.filter fun x => x.word.weight PEAddres.weight < n

@[simp]
lemma truncate_nil
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ) :
    truncate n ([] : List (SPFactora H inputWeight)) = [] :=
  rfl

@[simp]
lemma truncate_append
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (L M : List (SPFactora H inputWeight)) :
    truncate n (L ++ M) = truncate n L ++ truncate n M := by
  simp [truncate]

/-- Every retained symbolic power factor is genuinely below the cutoff. -/
lemma word_weight_truncate
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {L : List (SPFactora H inputWeight)}
    {x : SPFactora H inputWeight}
    (hx : x ∈ truncate n L) :
    x.word.weight PEAddres.weight < n := by
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hx).2

/-- Truncating twice at the same cutoff has no further effect. -/
@[simp]
lemma truncate_truncate
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (L : List (SPFactora H inputWeight)) :
    truncate n (truncate n L) = truncate n L := by
  simp [truncate]

/-- Truncation never increases the number of symbolic power factors. -/
lemma length_truncate_le
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (L : List (SPFactora H inputWeight)) :
    (truncate n L).length ≤ L.length := by
  simpa [truncate] using
    (List.length_filter_le
      (fun x : SPFactora H inputWeight =>
        decide (x.word.weight PEAddres.weight < n)) L)

/--
Discarding factors at or above the nilpotent truncation weight leaves the
evaluated list product unchanged.
-/
lemma listEval_truncate
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (L : List (SPFactora H inputWeight)) :
    listEval (n := n) q (truncate n L) = listEval q L := by
  induction L with
  | nil =>
      rfl
  | cons x L ih =>
      by_cases hx : x.word.weight PEAddres.weight < n
      · rw [show truncate n (x :: L) = x :: truncate n L by
              simp [truncate, hx]]
        change
          x.eval (n := n) q * listEval (n := n) q (truncate n L) =
            x.eval (n := n) q * listEval (n := n) q L
        rw [ih]
      · have hnx : n ≤ x.word.weight PEAddres.weight :=
          Nat.le_of_not_gt hx
        rw [show truncate n (x :: L) = truncate n L by
              simp [truncate, hx]]
        change
          listEval (n := n) q (truncate n L) =
            x.eval (n := n) q * listEval (n := n) q L
        rw [ih, eval_n_weight q x hnx, one_mul]

/-- A list is physically truncated when all of its factors lie below `n`. -/
def IsTruncated
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (L : List (SPFactora H inputWeight)) :
    Prop :=
  ∀ x ∈ L, x.word.weight PEAddres.weight < n

/-- Truncation always produces a physically truncated list. -/
lemma isTruncated_truncate
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (L : List (SPFactora H inputWeight)) :
    IsTruncated n (truncate n L) :=
  fun _ hx => word_weight_truncate hx

/-- Physically truncated lists are fixed by truncation. -/
lemma truncate_self_truncated
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {L : List (SPFactora H inputWeight)}
    (hL : IsTruncated n L) :
    truncate n L = L := by
  apply List.filter_eq_self.2
  intro x hx
  simpa only [decide_eq_true_eq] using hL x hx

end SPFactora

/--
A repeated-power correction packet after erasing semantically trivial factors
of weight at least `n`.
-/
structure TCPkt
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
  word_weight_cutoff :
    ∀ x ∈ factors,
      x.word.weight PEAddres.weight < n

namespace SHPkt

/-- Erase semantically trivial repeated-power corrections at or above the cutoff. -/
def truncate
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A) :
    TCPkt n B A where
  factors := SPFactora.truncate n C.factors
  listEval_eq q := by
    rw [SPFactora.listEval_truncate]
    exact C.listEval_eq q
  word_weight_left x hx :=
    C.word_weight_left x (List.mem_filter.mp hx).1
  word_weight_right x hx :=
    C.word_weight_right x (List.mem_filter.mp hx).1
  word_weight_cutoff x hx :=
    SPFactora.word_weight_truncate hx

end SHPkt

namespace TCPkt

/-- A physically truncated power packet is exactly the correction needed for its swap. -/
lemma list_mul_swap
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (q : ℕ) :
    SPFactora.listEval (n := n) q C.factors *
          A.eval (n := n) q * B.eval (n := n) q =
      B.eval (n := n) q * A.eval (n := n) q := by
  rw [C.listEval_eq]
  simp [commutatorElement_def, mul_assoc]

/-- Every retained factor in a truncated power packet lies below the cutoff. -/
lemma weight_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    x.word.weight PEAddres.weight < n :=
  C.word_weight_cutoff x hx

/-- Every retained correction has positive remaining cutoff defect. -/
lemma defect_pos_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    0 < SPFactora.cutoffDefect n x := by
  simp [SPFactora.cutoffDefect,
    C.weight_factors hx]

/-- Retained corrections lie above the left parent and below the cutoff. -/
lemma interval_factors_left
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    B.word.weight PEAddres.weight <
        x.word.weight PEAddres.weight ∧
      x.word.weight PEAddres.weight < n :=
  ⟨C.word_weight_left x hx, C.weight_factors hx⟩

/-- Retained corrections lie above the right parent and below the cutoff. -/
lemma interval_factors_right
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    A.word.weight PEAddres.weight <
        x.word.weight PEAddres.weight ∧
      x.word.weight PEAddres.weight < n :=
  ⟨C.word_weight_right x hx, C.weight_factors hx⟩

/-- Every retained correction strictly lowers the left cutoff defect. -/
lemma defect_left_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    SPFactora.cutoffDefect n x <
      SPFactora.cutoffDefect n B := by
  have hxInterval := C.interval_factors_left hx
  simp only [SPFactora.cutoffDefect]
  omega

/-- Every retained correction strictly lowers the right cutoff defect. -/
lemma cutoff_defect_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    {x : SPFactora H inputWeight}
    (hx : x ∈ C.factors) :
    SPFactora.cutoffDefect n x <
      SPFactora.cutoffDefect n A := by
  have hxInterval := C.interval_factors_right hx
  simp only [SPFactora.cutoffDefect]
  omega

end TCPkt

namespace SHPkt

/-- Corrections one step below the cutoff are all erased by physical truncation. -/
lemma truncate_nil_left
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A)
    (hB : n ≤ B.word.weight PEAddres.weight + 1) :
    C.truncate.factors = [] := by
  apply List.filter_eq_nil_iff.2
  intro x hx hdecide
  exact (not_lt_of_ge (hB.trans (C.succ_weight_left hx)))
    (of_decide_eq_true hdecide)

/-- Symmetric one-step-below-cutoff erasure criterion. -/
lemma truncate_nil_n
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {B A : SPFactora H inputWeight}
    (C : SHPkt n B A)
    (hA : n ≤ A.word.weight PEAddres.weight + 1) :
    C.truncate.factors = [] := by
  apply List.filter_eq_nil_iff.2
  intro x hx hdecide
  exact (not_lt_of_ge (hA.trans (C.succ_weight_right hx)))
    (of_decide_eq_true hdecide)

end SHPkt

/--
One physically truncated repeated-power Hall-collection move.
-/
inductive TSStep
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight : ℕ) :
    List (SPFactora H inputWeight) →
      List (SPFactora H inputWeight) → Prop where
  | obstruction
      (P S : List (SPFactora H inputWeight))
      (B A : SPFactora H inputWeight)
      (C : TCPkt n B A) :
      TSStep H inputWeight
        (P ++ [B, A] ++ S)
        (P ++ C.factors ++ [A, B] ++ S)

/-- A truncated repeated-power move preserves the evaluated product. -/
lemma TSStep.listEval_eq
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {L R : List (SPFactora H inputWeight)}
    (h : TSStep (n := n) H inputWeight L R)
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

/-- Physical truncation is preserved by one cutoff-specific power move. -/
lemma TSStep.isTruncated
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {L R : List (SPFactora H inputWeight)}
    (h : TSStep (n := n) H inputWeight L R)
    (hL : SPFactora.IsTruncated n L) :
    SPFactora.IsTruncated n R := by
  cases h with
  | obstruction P S B A C =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hxS
      · rcases List.mem_append.mp hx with hx | hxAB
        · rcases List.mem_append.mp hx with hxP | hxC
          · exact hL x (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inl hxP))))
          · exact C.word_weight_cutoff x hxC
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr (by simp [hxA])))))
          · exact hL x (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr (by simp [hxB])))))
      · exact hL x (List.mem_append.mpr (.inr hxS))

/-- Finite sequence of physically truncated repeated-power collection moves. -/
abbrev TSRwa
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (L R : List (SPFactora H inputWeight)) :
    Prop :=
  Relation.ReflTransGen
    (TSStep (n := n) H inputWeight) L R

/-- Any finite truncated repeated-power collection run preserves evaluation. -/
lemma TSRwa.listEval_eq
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {L R : List (SPFactora H inputWeight)}
    (h : TSRwa (n := n) L R)
    (q : ℕ) :
    SPFactora.listEval (n := n) q R =
      SPFactora.listEval (n := n) q L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq q).trans ih

/-- Physical truncation is preserved by any finite cutoff-specific power run. -/
lemma TSRwa.isTruncated
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {L R : List (SPFactora H inputWeight)}
    (h : TSRwa (n := n) L R)
    (hL : SPFactora.IsTruncated n L) :
    SPFactora.IsTruncated n R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.isTruncated ih

end TCTex
end Towers

import Towers.Group.Zassenhaus.SemanticCorrectionDelegation

/-!
# Normalized semantic obstruction steps for symbolic Hall powers

A lower-stratum Hall collector swaps two obstructing factors by emitting a
strictly higher-weight correction packet.  Once a semantic normalizer for the
next stratum is available, that packet can immediately be replaced by its
normalized coordinate endpoint.

This file packages the resulting obstruction step.  It proves exact evaluation
preservation, physical truncation, lower-support preservation, and closure
under finite contexts and rewrite runs.  These are the operational invariants
needed by a one-stratum insertion scheduler.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace TSNorma

/--
The normalized correction endpoint performs the same adjacent swap as its raw
truncated packet.
-/
lemma list_mul_swap
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        lowerWeight C)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
          (normalization.coordinates.factors (n := n)) *
        A.eval (n := n) q * B.eval (n := n) q =
      B.eval (n := n) q * A.eval (n := n) q := by
  rw [normalization.list_eval_coordinates]
  simp [commutatorElement_def, mul_assoc]

/-- Normalized correction factors remain in the next support stratum. -/
lemma weight_least_succ
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        lowerWeight C) :
    SPFactora.WordWeightLeast (lowerWeight + 1)
      (normalization.coordinates.factors (n := n)) :=
  CCExpans.no_terms_below
    normalization.coordinates normalization.coordinates_no_below

/-- Canonical normalized correction endpoints are physically truncated. -/
lemma factors_isTruncated
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        lowerWeight C) :
    SPFactora.IsTruncated n
      (normalization.coordinates.factors (n := n)) :=
  normalization.coordinates.isTruncated_factors

end TSNorma

/--
One lower-stratum semantic obstruction step.  The emitted raw packet has
already been normalized one stratum higher.
-/
inductive SSStep
    {d n : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (inputWeight lowerWeight : ℕ) :
    List (SPFactora H inputWeight) →
      List (SPFactora H inputWeight) → Prop where
  | obstruction
      (P S : List (SPFactora H inputWeight))
      (B A : SPFactora H inputWeight)
      (C : TCPkt n B A)
      (normalization :
        TSNorma
          lowerWeight C) :
      SSStep H
        inputWeight lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S)

/-- One normalized semantic obstruction preserves evaluation exactly. -/
lemma SSStep.listEval_eq
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SSStep
        (n := n) H inputWeight lowerWeight L R)
    (q : ℕ) :
    SPFactora.listEval (n := n) q R =
      SPFactora.listEval (n := n) q L := by
  cases h with
  | obstruction P S B A C normalization =>
      calc
        SPFactora.listEval (n := n) q
              (P ++ normalization.coordinates.factors (n := n) ++
                [A, B] ++ S) =
            SPFactora.listEval q P *
                (SPFactora.listEval q
                    (normalization.coordinates.factors (n := n)) *
                  A.eval q * B.eval q) *
              SPFactora.listEval q S := by
            simp [mul_assoc]
        _ =
            SPFactora.listEval q P *
                (B.eval q * A.eval q) *
              SPFactora.listEval q S := by
            rw [normalization.list_mul_swap]
        _ =
            SPFactora.listEval (n := n) q
              (P ++ [B, A] ++ S) := by
            simp [mul_assoc]

/-- One normalized semantic obstruction preserves physical truncation. -/
lemma SSStep.isTruncated
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SSStep
        (n := n) H inputWeight lowerWeight L R)
    (hL : SPFactora.IsTruncated n L) :
    SPFactora.IsTruncated n R := by
  cases h with
  | obstruction P S B A C normalization =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hxS
      · rcases List.mem_append.mp hx with hx | hxAB
        · rcases List.mem_append.mp hx with hxP | hxCorrection
          · exact hL x (by simp [hxP])
          · exact normalization.factors_isTruncated x hxCorrection
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (by simp [hxA])
          · exact hL x (by simp [hxB])
      · exact hL x (by simp [hxS])

/-- One normalized semantic obstruction preserves the current support stratum. -/
lemma SSStep.wordWeightLeast
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SSStep
        (n := n) H inputWeight lowerWeight L R)
    (hL : SPFactora.WordWeightLeast lowerWeight L) :
    SPFactora.WordWeightLeast lowerWeight R := by
  cases h with
  | obstruction P S B A C normalization =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hxS
      · rcases List.mem_append.mp hx with hx | hxAB
        · rcases List.mem_append.mp hx with hxP | hxCorrection
          · exact hL x (by simp [hxP])
          · exact
              (Nat.le_succ lowerWeight).trans
                (normalization.weight_least_succ x hxCorrection)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (by simp [hxA])
          · exact hL x (by simp [hxB])
      · exact hL x (by simp [hxS])

/-- Normalized semantic obstruction steps remain valid inside list contexts. -/
lemma SSStep.context
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SSStep
        (n := n) H inputWeight lowerWeight L R)
    (P S : List (SPFactora H inputWeight)) :
    SSStep
      (n := n) H inputWeight lowerWeight
      (P ++ L ++ S) (P ++ R ++ S) := by
  cases h with
  | obstruction P0 S0 B A C normalization =>
      simpa [List.append_assoc] using
        (SSStep.obstruction
          (P ++ P0) (S0 ++ S) B A C normalization)

/-- Finite runs of normalized semantic obstruction steps. -/
abbrev SCRw
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (L R : List (SPFactora H inputWeight)) :
    Prop :=
  Relation.ReflTransGen
    (SSStep
      (n := n) H inputWeight lowerWeight) L R

namespace SCRw

/-- Any finite normalized semantic obstruction run preserves evaluation. -/
lemma listEval_eq
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SCRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (q : ℕ) :
    SPFactora.listEval (n := n) q R =
      SPFactora.listEval (n := n) q L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq q).trans ih

/-- Finite normalized semantic obstruction runs preserve physical truncation. -/
lemma isTruncated
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SCRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (hL : SPFactora.IsTruncated n L) :
    SPFactora.IsTruncated n R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.isTruncated ih

/-- Finite normalized semantic obstruction runs preserve lower support. -/
lemma wordWeightLeast
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SCRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (hL : SPFactora.WordWeightLeast lowerWeight L) :
    SPFactora.WordWeightLeast lowerWeight R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.wordWeightLeast ih

/-- Finite normalized semantic obstruction runs remain valid inside contexts. -/
lemma context
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SCRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (P S : List (SPFactora H inputWeight)) :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
      (P ++ L ++ S) (P ++ R ++ S) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hLR hstep ih =>
      exact Relation.ReflTransGen.tail ih (hstep.context P S)

end SCRw

namespace TCPkt

/--
Using the support of the left parent, delegate a raw correction packet upward
and obtain one normalized semantic obstruction step.
-/
lemma supported_semantic_left
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (C : TCPkt n B A)
    (hB :
      lowerWeight ≤ B.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H) :
    ∃ normalization :
        TSNorma
          lowerWeight C,
      SSStep
        (n := n) H inputWeight lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S) := by
  rcases C.normalization_left hB normalizer with
    ⟨normalization⟩
  exact ⟨normalization,
    SSStep.obstruction
      P S B A C normalization⟩

/--
Using the support of the right parent, delegate a raw correction packet upward
and obtain one normalized semantic obstruction step.
-/
lemma supported_semantic_right
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (C : TCPkt n B A)
    (hA :
      lowerWeight ≤ A.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H) :
    ∃ normalization :
        TSNorma
          lowerWeight C,
      SSStep
        (n := n) H inputWeight lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S) := by
  rcases C.semantic_normalization hA normalizer with
    ⟨normalization⟩
  exact ⟨normalization,
    SSStep.obstruction
      P S B A C normalization⟩

end TCPkt

end TCTex
end Towers

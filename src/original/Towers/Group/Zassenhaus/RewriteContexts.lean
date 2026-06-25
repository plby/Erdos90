import Towers.Group.Zassenhaus.TruncatedConcretePackets

/-!
# Contexts for truncated symbolic Hall power rewrites

Adjacent truncated power-collection moves can be inserted into list contexts.
This file packages the resulting finite block movements independently of any
particular source construction.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- A truncated power-collection move remains valid inside a list context. -/
lemma TSStep.context
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h : TSStep (n := n) H inputWeight L R)
    (P S : List (SPFactora H inputWeight)) :
    TSStep (n := n) H inputWeight
      (P ++ L ++ S) (P ++ R ++ S) := by
  cases h with
  | obstruction P0 S0 B A C =>
      simpa [List.append_assoc] using
        (TSStep.obstruction
          (P ++ P0) (S0 ++ S) B A C)

namespace TSRwa

/-- A finite truncated power-collection run remains valid inside a list context. -/
lemma context
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h : TSRwa (n := n) L R)
    (P S : List (SPFactora H inputWeight)) :
    TSRwa (n := n)
      (P ++ L ++ S) (P ++ R ++ S) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hLR hstep ih =>
      exact Relation.ReflTransGen.tail ih (hstep.context P S)

/-- Concatenate two independent finite truncated power-collection runs. -/
lemma append
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L₁ R₁ L₂ R₂ : List (SPFactora H inputWeight)}
    (h₁ : TSRwa (n := n) L₁ R₁)
    (h₂ : TSRwa (n := n) L₂ R₂) :
    TSRwa (n := n)
      (L₁ ++ L₂) (R₁ ++ R₂) := by
  have hleft :
      TSRwa (n := n)
        (L₁ ++ L₂) (R₁ ++ L₂) := by
    simpa [List.append_assoc] using h₁.context [] L₂
  have hright :
      TSRwa (n := n)
        (R₁ ++ L₂) (R₁ ++ R₂) := by
    simpa [List.append_assoc] using h₂.context R₁ []
  exact hleft.trans hright

/-- Regard one adjacent truncated move as a finite rewrite run. -/
lemma single
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h : TSStep (n := n) H inputWeight L R) :
    TSRwa (n := n) L R :=
  Relation.ReflTransGen.single h

/-- Bubble one factor rightward across a block using empty adjacent packets. -/
lemma move_left_across
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (B : SPFactora H inputWeight) :
    ∀ (L : List (SPFactora H inputWeight)),
      (∀ A ∈ L,
        n ≤ B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight) →
      TSRwa (n := n)
        (P ++ [B] ++ L ++ S) (P ++ L ++ [B] ++ S) := by
  intro L hL
  induction L generalizing P with
  | nil =>
      simpa using
        (Relation.ReflTransGen.refl :
          TSRwa (n := n)
            (P ++ [B] ++ S) (P ++ [B] ++ S))
  | cons A L ih =>
      have hstep :
          TSStep (n := n) H inputWeight
            (P ++ [B, A] ++ L ++ S)
            (P ++ [A, B] ++ L ++ S) :=
        by
          simpa [List.append_assoc] using
            (TSStep.obstrucempty_nle_addwordweight
              P (L ++ S) B A (hL A (by simp)))
      have htail :
          TSRwa (n := n)
            ((P ++ [A]) ++ [B] ++ L ++ S)
            ((P ++ [A]) ++ L ++ [B] ++ S) :=
        ih (P := P ++ [A]) (by
          intro x hx
          exact hL x (by simp [hx]))
      have htail' :
          TSRwa (n := n)
            (P ++ [A, B] ++ L ++ S)
            (P ++ (A :: L) ++ [B] ++ S) := by
        simpa [List.append_assoc] using htail
      exact (by
        simpa [List.append_assoc] using
          (Relation.ReflTransGen.single hstep).trans htail')

/-- Bubble one factor leftward across a block using empty adjacent packets. -/
lemma move_right_across
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (B : SPFactora H inputWeight) :
    ∀ (L : List (SPFactora H inputWeight)),
      (∀ A ∈ L,
        n ≤ A.word.weight PEAddres.weight +
          B.word.weight PEAddres.weight) →
      TSRwa (n := n)
        (P ++ L ++ [B] ++ S) (P ++ [B] ++ L ++ S) := by
  intro L hL
  induction L generalizing P with
  | nil =>
      simpa using
        (Relation.ReflTransGen.refl :
          TSRwa (n := n)
            (P ++ [B] ++ S) (P ++ [B] ++ S))
  | cons A L ih =>
      have htail :
          TSRwa (n := n)
            ((P ++ [A]) ++ L ++ [B] ++ S)
            ((P ++ [A]) ++ [B] ++ L ++ S) :=
        ih (P := P ++ [A]) (by
          intro x hx
          exact hL x (by simp [hx]))
      have hstep :
          TSStep (n := n) H inputWeight
            (P ++ [A, B] ++ L ++ S)
            (P ++ [B, A] ++ L ++ S) :=
        by
          simpa [List.append_assoc] using
            (TSStep.obstrucempty_nle_addwordweight
              P (L ++ S) A B (hL A (by simp)))
      have htail' :
          TSRwa (n := n)
            (P ++ (A :: L) ++ [B] ++ S)
            (P ++ [A, B] ++ L ++ S) := by
        simpa [List.append_assoc] using htail
      exact (by
        simpa [List.append_assoc] using
          htail'.trans (Relation.ReflTransGen.single hstep))

/--
Move a whole left block rightward across another block when every cross-pair
has an empty adjacent packet.
-/
lemma move_left_block
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight)) :
    ∀ (C L : List (SPFactora H inputWeight)),
      (∀ B ∈ C, ∀ A ∈ L,
        n ≤ B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight) →
      TSRwa (n := n)
        (P ++ C ++ L ++ S) (P ++ L ++ C ++ S) := by
  intro C L hCL
  induction C generalizing P with
  | nil =>
      simpa using
        (Relation.ReflTransGen.refl :
          TSRwa (n := n)
            (P ++ L ++ S) (P ++ L ++ S))
  | cons B C ih =>
      have htail :
          TSRwa (n := n)
            ((P ++ [B]) ++ C ++ L ++ S)
            ((P ++ [B]) ++ L ++ C ++ S) :=
        ih (P := P ++ [B]) (by
          intro x hx A hA
          exact hCL x (by simp [hx]) A hA)
      have htail' :
          TSRwa (n := n)
            (P ++ [B] ++ C ++ L ++ S)
            (P ++ [B] ++ L ++ C ++ S) := by
        simpa [List.append_assoc] using htail
      have hhead :
          TSRwa (n := n)
            (P ++ [B] ++ L ++ C ++ S)
            (P ++ L ++ [B] ++ C ++ S) :=
        by
          simpa [List.append_assoc] using
            (move_left_across P (C ++ S) B L (by
              intro A hA
              exact hCL B (by simp) A hA))
      exact (by
        simpa [List.append_assoc] using htail'.trans hhead)

end TSRwa

end TCTex
end Towers

import Towers.Group.Zassenhaus.RecursiveObstructions

/-!
# Exact movements of labelled Hall-Petresco words

The concrete packet collector is assembled from adjacent rewrites
`B A -> [B, A] A B`.  This file packages the first reusable movement: bubble
one labelled word rightward across a finite list.  It also records the emitted
row-correction weights and the quotient-level terminal case in which every
emitted correction has reached the cutoff.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace PLMoveme

open HACoeff
open BBSched
open BFTrunc
open BRScheda

/-- Concrete labelled word for the standalone batch scheduler. -/
abbrev BatchLabelledWord
    (M N : ℕ) :=
  BBSched.LabelledWord M N

/-- Concrete correction constructor for the standalone batch scheduler. -/
abbrev batchCorrection
    {M N : ℕ}
    (B A : BatchLabelledWord M N) :
    BatchLabelledWord M N :=
  BBSched.labelledWordCorrection B A

/-- Corrections emitted while one fixed word bubbles rightward across a row. -/
def rowCorrections
    {M N : ℕ}
    (B : BatchLabelledWord M N)
    (row : List (BatchLabelledWord M N)) :
    List (BatchLabelledWord M N) :=
  row.map fun A => batchCorrection B A

/--
Concrete endpoint after one fixed word bubbles rightward across a row.  Each
new correction remains immediately before the word it was created from.
-/
def movedRightAcross
    {M N : ℕ}
    (B : BatchLabelledWord M N) :
    List (BatchLabelledWord M N) →
      List (BatchLabelledWord M N)
  | [] =>
      [B]
  | A :: row =>
      batchCorrection B A :: A :: movedRightAcross B row

@[simp]
lemma moved_right_nil
    {M N : ℕ}
    (B : BatchLabelledWord M N) :
    movedRightAcross B [] = [B] :=
  rfl

@[simp]
lemma moved_right_cons
    {M N : ℕ}
    (B A : BatchLabelledWord M N)
    (row : List (BatchLabelledWord M N)) :
    movedRightAcross B (A :: row) =
      batchCorrection B A :: A :: movedRightAcross B row :=
  rfl

/-- Independent exact rewrite runs compose under list append. -/
lemma rewrites_append
    {M N : ℕ}
    {L₁ R₁ L₂ R₂ : List (BatchLabelledWord M N)}
    (h₁ :
      BBSched.LWRw L₁ R₁)
    (h₂ :
      BBSched.LWRw L₂ R₂) :
    BBSched.LWRw
      (L₁ ++ L₂) (R₁ ++ R₂) := by
  have hleft :
      BBSched.LWRw
        (L₁ ++ L₂) (R₁ ++ L₂) := by
    simpa [List.append_assoc] using h₁.context [] L₂
  have hright :
      BBSched.LWRw
        (R₁ ++ L₂) (R₁ ++ R₂) := by
    simpa [List.append_assoc] using h₂.context R₁ []
  exact hleft.trans hright

/-- Regard one concrete adjacent swap as a finite rewrite run. -/
lemma rewrites_single_step
    {M N : ℕ}
    (P S : List (BatchLabelledWord M N))
    (B A : BatchLabelledWord M N) :
    BBSched.LWRw
      (P ++ [B, A] ++ S)
      (P ++ [batchCorrection B A, A, B] ++ S) := by
  exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
    (BBSched.LWStep.obstruction P S B A)

/-- Bubble one concrete labelled word rightward across a finite row. -/
lemma rewrites_moved_right
    {M N : ℕ}
    (B : BatchLabelledWord M N) :
    ∀ row : List (BatchLabelledWord M N),
      BBSched.LWRw
        (B :: row) (movedRightAcross B row)
  | [] =>
      Relation.ReflTransGen.refl
  | A :: row => by
      have hhead :
          BBSched.LWRw
            (B :: A :: row)
            (batchCorrection B A :: A :: B :: row) := by
        simpa using rewrites_single_step [] row B A
      have htail :
          BBSched.LWRw
            (batchCorrection B A :: A :: B :: row)
            (batchCorrection B A :: A :: movedRightAcross B row) := by
        simpa [List.append_assoc] using
          (rewrites_moved_right B row).context
            [batchCorrection B A, A] []
      exact hhead.trans htail

/-- Bubble one word rightward inside an arbitrary concrete list context. -/
lemma moved_right_context
    {M N : ℕ}
    (P S : List (BatchLabelledWord M N))
    (B : BatchLabelledWord M N)
    (row : List (BatchLabelledWord M N)) :
    BBSched.LWRw
      (P ++ (B :: row) ++ S)
      (P ++ movedRightAcross B row ++ S) := by
  exact (rewrites_moved_right B row).context P S

/-- The row corrections are exactly the singleton-left Cartesian corrections. -/
lemma row_words_singleton
    {M N : ℕ}
    (B : BatchLabelledWord M N)
    (row : List (BatchLabelledWord M N)) :
    rowCorrections B row =
      PCCounti.correctionWords [B] row := by
  simp [rowCorrections, PCCounti.correctionWords,
    batchCorrection,
    BBSched.labelledWordCorrection]

/-- Collapse turns one concrete correction weight into the sum of parent weights. -/
lemma collapsed_labelled_correction
    {M N leftWeight rightWeight : ℕ}
    (B A : BatchLabelledWord M N) :
    (collapseWord (batchCorrection B A)).weight
        (HPAtom.weight leftWeight rightWeight) =
      (collapseWord B).weight (HPAtom.weight leftWeight rightWeight) +
        (collapseWord A).weight (HPAtom.weight leftWeight rightWeight) := by
  simp [batchCorrection,
    BBSched.labelledWordCorrection,
    collapseWord, CWord.bind_commutator]

/-- A pairwise correction reaches cutoff whenever the sum of parent weights does. -/
lemma collapsed_least_labelled
    {M N n leftWeight rightWeight : ℕ}
    (B A : BatchLabelledWord M N)
    (hcutoff :
      n ≤
        (collapseWord B).weight (HPAtom.weight leftWeight rightWeight) +
          (collapseWord A).weight (HPAtom.weight leftWeight rightWeight)) :
    CollapsedWeightLeast n leftWeight rightWeight
      (batchCorrection B A) := by
  unfold CollapsedWeightLeast
  rw [collapsed_labelled_correction]
  exact hcutoff

/-- Every correction emitted by a terminal row movement is an above-cutoff residual. -/
lemma words_row_corrections
    {M N n leftWeight rightWeight : ℕ}
    (B : BatchLabelledWord M N)
    (row : List (BatchLabelledWord M N))
    (hcutoff :
      ∀ A ∈ row,
        n ≤
          (collapseWord B).weight (HPAtom.weight leftWeight rightWeight) +
            (collapseWord A).weight
              (HPAtom.weight leftWeight rightWeight)) :
    WordsAboveCutoff n leftWeight rightWeight
      (rowCorrections B row) := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨A, hA, rfl⟩
  exact collapsed_least_labelled B A (hcutoff A hA)

/--
At the cutoff, the interleaved correction words created by a row movement
disappear after collapsed evaluation.
-/
lemma collapsed_moved_append
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (B : BatchLabelledWord M N) :
    ∀ row : List (BatchLabelledWord M N),
      (∀ A ∈ row,
        n ≤
          (collapseWord B).weight (HPAtom.weight leftWeight rightWeight) +
            (collapseWord A).weight
              (HPAtom.weight leftWeight rightWeight)) →
      collapsedList x y (movedRightAcross B row) =
        collapsedList x y (row ++ [B])
  | [], _hcutoff => by
      rfl
  | A :: row, hcutoff => by
      have hcorrection :
          (collapseWord (batchCorrection B A)).eval
              (HPAtom.eval x y) = 1 :=
        collapsed_weight_least
          hleftWeight hrightWeight hx hy hbot
            (batchCorrection B A)
            (collapsed_least_labelled B A
              (hcutoff A (by simp)))
      have ih :=
        collapsed_moved_append
          hleftWeight hrightWeight hx hy hbot B row
            (fun C hC => hcutoff C (by simp [hC]))
      simp only [moved_right_cons, collapsedList,
        List.map_cons, List.prod_cons]
      rw [hcorrection]
      simpa [collapsedList] using ih

/-- One word commutes past a terminal row in the nilpotent quotient. -/
lemma collapsed_append_cons
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (B : BatchLabelledWord M N)
    (row : List (BatchLabelledWord M N))
    (hcutoff :
      ∀ A ∈ row,
        n ≤
          (collapseWord B).weight (HPAtom.weight leftWeight rightWeight) +
            (collapseWord A).weight
              (HPAtom.weight leftWeight rightWeight)) :
    collapsedList x y (row ++ [B]) =
      collapsedList x y (B :: row) := by
  exact
    (collapsed_moved_append
      hleftWeight hrightWeight hx hy hbot B row hcutoff).symm.trans
        (collapsed_labelled_rewrites x y
          (rewrites_moved_right B row))

end PLMoveme
end TCTex
end Towers

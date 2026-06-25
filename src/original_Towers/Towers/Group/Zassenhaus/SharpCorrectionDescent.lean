import Mathlib.Data.Multiset.DershowitzManna
import Towers.Group.Zassenhaus.SemanticObstructionScheduling
import Towers.Group.Zassenhaus.SharpNormalizerFamilies

/-!
# Multiset descent for sharp symbolic Hall-power corrections

When a routed insertion crosses a higher-tail parent, its correction block is
normalized sharply above that actual parent.  Every retained factor in the
normalized endpoint therefore has strictly smaller cutoff defect than the
crossed parent.  Replacing one parent by that finite block decreases the
Dershowitz-Manna order on multisets of cutoff defects.

This is the termination measure needed by a recursive higher-tail collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Multiset

/-- Replacing one multiset element by finitely many smaller elements decreases
the Dershowitz-Manna order. -/
lemma dershowitz_manna_singleton
    {α : Type*}
    [Preorder α]
    {X Y : Multiset α}
    {a : α}
    (hY : ∀ y ∈ Y, y < a) :
    IsDershowitzMannaLT (X + Y) (X + {a}) :=
  ⟨X, Y, {a}, by simp, rfl, rfl, fun y hy => ⟨a, by simp, hY y hy⟩⟩

end Multiset

namespace Towers
namespace TCTex

universe u

namespace SPFactora

/-- The unordered multiset of cutoff defects carried by a symbolic factor list. -/
def cutoffDefectMultiset
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (n : ℕ)
    (L : List (SPFactora H inputWeight)) :
    Multiset ℕ :=
  (L.map (cutoffDefect n) : Multiset ℕ)

@[simp]
lemma defect_multiset_nil
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    cutoffDefectMultiset (H := H) n
      ([] : List (SPFactora H inputWeight)) = ∅ := by
  simp [cutoffDefectMultiset]

@[simp]
lemma defect_multiset_append
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (L R : List (SPFactora H inputWeight)) :
    cutoffDefectMultiset n (L ++ R) =
      cutoffDefectMultiset n L + cutoffDefectMultiset n R := by
  simp [cutoffDefectMultiset]

@[simp]
lemma cutoff_multiset_singleton
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (x : SPFactora H inputWeight) :
    cutoffDefectMultiset n [x] = {cutoffDefect n x} := by
  simp [cutoffDefectMultiset]

/--
The list relation induced by Dershowitz-Manna descent on cutoff-defect
multisets.
-/
def CutoffDefectMultiset
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (n : ℕ)
    (L R : List (SPFactora H inputWeight)) :
    Prop :=
  Multiset.IsDershowitzMannaLT
    (cutoffDefectMultiset n L) (cutoffDefectMultiset n R)

/-- Cutoff-defect multiset descent is well founded on symbolic factor lists. -/
lemma well_founded_defect
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    WellFounded
      (CutoffDefectMultiset (H := H) (inputWeight := inputWeight) n) := by
  exact
    InvImage.wf (cutoffDefectMultiset (H := H) (inputWeight := inputWeight) n)
      Multiset.wellFounded_isDershowitzMannaLT

end SPFactora

namespace TSNorma

/--
Every factor of an endpoint normalized sharply above the left parent has
strictly smaller cutoff defect than that parent.
-/
lemma factors_defect_left
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        (B.word.weight PEAddres.weight) C)
    {x : SPFactora H inputWeight}
    (hx : x ∈ normalization.coordinates.factors (n := n)) :
    SPFactora.cutoffDefect n x <
      SPFactora.cutoffDefect n B := by
  have hxSupported := normalization.weight_least_succ x hx
  have hxTruncated := normalization.factors_isTruncated x hx
  simp only [SPFactora.cutoffDefect]
  omega

/--
Every factor of an endpoint normalized sharply above the right parent has
strictly smaller cutoff defect than that parent.
-/
lemma factors_defect_right
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        (A.word.weight PEAddres.weight) C)
    {x : SPFactora H inputWeight}
    (hx : x ∈ normalization.coordinates.factors (n := n)) :
    SPFactora.cutoffDefect n x <
      SPFactora.cutoffDefect n A := by
  have hxSupported := normalization.weight_least_succ x hx
  have hxTruncated := normalization.factors_isTruncated x hx
  simp only [SPFactora.cutoffDefect]
  omega

/--
Replacing a left parent by its sharply normalized correction endpoint strictly
decreases the cutoff-defect multiset, inside an arbitrary prefix.
-/
lemma multisetAppendSingleton
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        (B.word.weight PEAddres.weight) C)
    (P : List (SPFactora H inputWeight)) :
    SPFactora.CutoffDefectMultiset n
      (P ++ normalization.coordinates.factors (n := n)) (P ++ [B]) := by
  unfold SPFactora.CutoffDefectMultiset
  rw [SPFactora.defect_multiset_append,
    SPFactora.defect_multiset_append,
    SPFactora.cutoff_multiset_singleton]
  apply Multiset.dershowitz_manna_singleton
  intro y hy
  rw [SPFactora.cutoffDefectMultiset] at hy
  rcases List.mem_map.mp (Multiset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
  exact normalization.factors_defect_left hx

/--
Replacing a right parent by its sharply normalized correction endpoint
strictly decreases the cutoff-defect multiset, inside an arbitrary prefix.
-/
lemma defectMultisetSingleton
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        (A.word.weight PEAddres.weight) C)
    (P : List (SPFactora H inputWeight)) :
    SPFactora.CutoffDefectMultiset n
      (P ++ normalization.coordinates.factors (n := n)) (P ++ [A]) := by
  unfold SPFactora.CutoffDefectMultiset
  rw [SPFactora.defect_multiset_append,
    SPFactora.defect_multiset_append,
    SPFactora.cutoff_multiset_singleton]
  apply Multiset.dershowitz_manna_singleton
  intro y hy
  rw [SPFactora.cutoffDefectMultiset] at hy
  rcases List.mem_map.mp (Multiset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
  exact normalization.factors_defect_right hx

end TSNorma

namespace SSNormala

open TSNorma

/--
The sharp left-parent endpoint selected by a normalizer family replaces that
parent by a strictly smaller cutoff-defect multiset.
-/
lemma normalization_cutoff_multiset
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (P : List (SPFactora H inputWeight)) :
    SPFactora.CutoffDefectMultiset n
      (P ++
        (family.normalization_left_weight C).coordinates.factors
          (n := n))
      (P ++ [B]) :=
  multisetAppendSingleton
    (family.normalization_left_weight C) P

/--
Weakly exposing a sharp left-parent endpoint preserves its multiset descent
witness because weakening does not change the coordinate block.
-/
lemma semantic_normalization_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (P : List (SPFactora H inputWeight)) :
    SPFactora.CutoffDefectMultiset n
      (P ++
        (family.semantic_left_sharp C hB).coordinates.factors
          (n := n))
      (P ++ [B]) := by
  simpa [semantic_left_sharp] using
    family.normalization_cutoff_multiset C P

/--
The sharp right-parent endpoint selected by a normalizer family replaces that
parent by a strictly smaller cutoff-defect multiset.
-/
lemma semantic_defect_multiset
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (P : List (SPFactora H inputWeight)) :
    SPFactora.CutoffDefectMultiset n
      (P ++
        (family.semantic_normalization_word C).coordinates.factors
          (n := n))
      (P ++ [A]) :=
  defectMultisetSingleton
    (family.semantic_normalization_word C) P

/--
Weakly exposing a sharp right-parent endpoint preserves its multiset descent
witness because weakening does not change the coordinate block.
-/
lemma semantic_sharp_multiset
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
    (P : List (SPFactora H inputWeight)) :
    SPFactora.CutoffDefectMultiset n
      (P ++
        (family.normalization_right_sharp C hA).coordinates.factors
          (n := n))
      (P ++ [A]) := by
  simpa [normalization_right_sharp] using
    family.semantic_defect_multiset C P

end SSNormala

end TCTex
end Towers

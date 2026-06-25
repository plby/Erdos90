import Mathlib.GroupTheory.Commutator.Basic
import Towers.Group.Edmonton.CentralSeries
import Towers.Group.NilpotentProducts.RankThreeResidues

/-!
# Nilpotency of the equation-(18) coordinate groups

The triangular coordinate law supplies a short filtration proof that the
integral coordinate group, and hence every residue quotient, has nilpotency
class at most three.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open scoped commutatorElement

/-- Tuples with no weight-one coordinates. -/
structure WeightTwo (c : RLCoordi) : Prop where
  c1 : c.c1 = 0
  c2 : c.c2 = 0
  c3 : c.c3 = 0

/-- Tuples supported only in weight three. -/
structure WeightThree (c : RLCoordi) : Prop
    extends WeightTwo c where
  c12 : c.c12 = 0
  c13 : c.c13 = 0
  c23 : c.c23 = 0

/-- The subgroup consisting of coordinates of weight at least two. -/
def weightTwoSubgroup : Subgroup RLCoordi where
  carrier := {c | WeightTwo c}
  one_mem' := by
    exact ⟨rfl, rfl, rfl⟩
  mul_mem' := by
    intro c d hc hd
    change WeightTwo (RLCoordi.mul c d)
    exact ⟨by simp [RLCoordi.mul, hc.c1, hd.c1],
      by simp [RLCoordi.mul, hc.c2, hd.c2],
      by simp [RLCoordi.mul, hc.c3, hd.c3]⟩
  inv_mem' := by
    intro c hc
    change WeightTwo (RLCoordi.rightInv c)
    exact ⟨by simp [RLCoordi.rightInv, hc.c1],
      by simp [RLCoordi.rightInv, hc.c2],
      by simp [RLCoordi.rightInv, hc.c3]⟩

/-- The central subgroup consisting of coordinates of weight at least three. -/
def weightThreeSubgroup : Subgroup RLCoordi where
  carrier := {c | WeightThree c}
  one_mem' := by
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  mul_mem' := by
    intro c d hc hd
    change WeightThree (RLCoordi.mul c d)
    exact
      ⟨⟨by simp [RLCoordi.mul, hc.c1, hd.c1],
          by simp [RLCoordi.mul, hc.c2, hd.c2],
          by simp [RLCoordi.mul, hc.c3, hd.c3]⟩,
        by simp [RLCoordi.mul, hc.c12, hd.c12, hc.c2, hd.c1],
        by simp [RLCoordi.mul, hc.c13, hd.c13, hc.c3, hd.c1],
        by simp [RLCoordi.mul, hc.c23, hd.c23, hc.c3, hd.c2]⟩
  inv_mem' := by
    intro c hc
    change WeightThree (RLCoordi.rightInv c)
    exact
      ⟨⟨by simp [RLCoordi.rightInv, hc.c1],
          by simp [RLCoordi.rightInv, hc.c2],
          by simp [RLCoordi.rightInv, hc.c3]⟩,
        by simp [RLCoordi.rightInv, hc.c12, hc.c2, hc.c1],
        by simp [RLCoordi.rightInv, hc.c13, hc.c3, hc.c1],
        by simp [RLCoordi.rightInv, hc.c23, hc.c3, hc.c2]⟩

private lemma commutator_weight_zero
    (c d : RLCoordi) :
    WeightTwo ⁅c, d⁆ := by
  refine ⟨?_, ?_, ?_⟩
  · change
      (RLCoordi.mul
        (RLCoordi.mul
          (RLCoordi.mul c d) (RLCoordi.rightInv c))
        (RLCoordi.rightInv d)).c1 = 0
    simp [RLCoordi.mul, RLCoordi.rightInv]
  · change
      (RLCoordi.mul
        (RLCoordi.mul
          (RLCoordi.mul c d) (RLCoordi.rightInv c))
        (RLCoordi.rightInv d)).c2 = 0
    simp [RLCoordi.mul, RLCoordi.rightInv]
  · change
      (RLCoordi.mul
        (RLCoordi.mul
          (RLCoordi.mul c d) (RLCoordi.rightInv c))
        (RLCoordi.rightInv d)).c3 = 0
    simp [RLCoordi.mul, RLCoordi.rightInv]

private lemma commutator_two_three
    (c d : RLCoordi)
    (hc : WeightTwo c) :
    WeightThree ⁅c, d⁆ := by
  refine ⟨commutator_weight_zero c d, ?_, ?_, ?_⟩
  · change
      (RLCoordi.mul
        (RLCoordi.mul
          (RLCoordi.mul c d) (RLCoordi.rightInv c))
        (RLCoordi.rightInv d)).c12 = 0
    simp [RLCoordi.mul, RLCoordi.rightInv,
      hc.c1, hc.c2, hc.c3]
  · change
      (RLCoordi.mul
        (RLCoordi.mul
          (RLCoordi.mul c d) (RLCoordi.rightInv c))
        (RLCoordi.rightInv d)).c13 = 0
    simp [RLCoordi.mul, RLCoordi.rightInv,
      hc.c1, hc.c2, hc.c3]
  · change
      (RLCoordi.mul
        (RLCoordi.mul
          (RLCoordi.mul c d) (RLCoordi.rightInv c))
        (RLCoordi.rightInv d)).c23 = 0
    simp [RLCoordi.mul, RLCoordi.rightInv,
      hc.c1, hc.c2, hc.c3]

theorem weight_three_center :
    weightThreeSubgroup ≤ Subgroup.center RLCoordi := by
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro d
  change RLCoordi.mul d c = RLCoordi.mul c d
  ext <;>
    simp [RLCoordi.mul, hc.c1, hc.c2, hc.c3,
      hc.c12, hc.c13, hc.c23] <;>
    ring

theorem lower_general_coordinates :
    Subgroup.lowerCentralSeries RLCoordi 1 ≤ weightTwoSubgroup := by
  rw [show 1 = 0 + 1 by omega, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_zero]
  exact Subgroup.commutator_le.mpr fun c _ d _ =>
    commutator_weight_zero c d

theorem general_coordinates_two :
    Subgroup.lowerCentralSeries RLCoordi 2 ≤ weightThreeSubgroup := by
  rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ]
  exact Subgroup.commutator_le.mpr fun c hc d _ =>
    commutator_two_three c d
      (lower_general_coordinates hc)

/-- The integral equation-(18) coordinate group has trivial fourth
one-based lower-central term. -/
theorem general_coordinates_bot :
    Subgroup.lowerCentralSeries RLCoordi 3 = ⊥ := by
  apply Subgroup.lowerCentralSeries_succ_eq_bot
  exact general_coordinates_two.trans
    weight_three_center

/-- Every odd-or-zero residue quotient of equation (18) also has trivial
fourth one-based lower-central term. -/
theorem lower_residue_bot
    (α₁ α₂ α₃ : ℕ)
    (hα₁ : AOrd α₁)
    (hα₂ : AOrd α₂)
    (hα₃ : AOrd α₃) :
    Subgroup.lowerCentralSeries
      (RankResiduesResidue α₁ α₂ α₃ hα₁ hα₂ hα₃) 3 = ⊥ := by
  let q :=
    (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).mk'
  rw [← central_series_surjective q
    (rankResiduesCon α₁ α₂ α₃ hα₁ hα₂ hα₃).mk'_surjective 3,
    general_coordinates_bot,
    Subgroup.map_bot]

end P1960
end Struik

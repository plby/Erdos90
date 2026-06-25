import Mathlib.GroupTheory.Commutator.Basic
import Towers.Group.Edmonton.CentralSeries
import Towers.Group.NilpotentProducts.GeneralResidues

/-!
# Nilpotency of the arbitrary-rank equation-(18) groups
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open scoped commutatorElement

structure GeneralWeightTwo {t : ℕ}
    (c : GCoordi t) : Prop where
  single : ∀ i, c.single i = 0

structure GeneralWeightThree {t : ℕ}
    (c : GCoordi t) : Prop
    extends GeneralWeightTwo c where
  pair : ∀ q, c.pair q = 0

def generalTwoSubgroup (t : ℕ) :
    Subgroup (GCoordi t) where
  carrier := {c | GeneralWeightTwo c}
  one_mem' := ⟨fun _ => rfl⟩
  mul_mem' := by
    intro c d hc hd
    exact ⟨fun i => by
      change c.single i + d.single i = 0
      simp [hc.single i, hd.single i]⟩
  inv_mem' := by
    intro c hc
    exact ⟨fun i => by
      change -c.single i = 0
      simp [hc.single i]⟩

def generalThreeSubgroup (t : ℕ) :
    Subgroup (GCoordi t) where
  carrier := {c | GeneralWeightThree c}
  one_mem' := ⟨⟨fun _ => rfl⟩, fun _ => rfl⟩
  mul_mem' := by
    intro c d hc hd
    exact
      ⟨⟨fun i => by
          change c.single i + d.single i = 0
          simp [hc.single i, hd.single i]⟩,
        fun q => by
          change
            c.pair q + d.pair q - c.single q.j * d.single q.i = 0
          simp [hc.pair q, hd.pair q, hc.single q.j, hd.single q.i]⟩
  inv_mem' := by
    intro c hc
    exact
      ⟨⟨fun i => by
          change -c.single i = 0
          simp [hc.single i]⟩,
        fun q => by
          change -(c.pair q - c.single q.j * -c.single q.i) = 0
          simp [hc.pair q, hc.single q.i, hc.single q.j]⟩

private lemma general_commutator_zero
    {t : ℕ} (c d : GCoordi t) :
    GeneralWeightTwo ⁅c, d⁆ := by
  refine ⟨fun i => ?_⟩
  change
    (GCoordi.mul
      (GCoordi.mul
        (GCoordi.mul c d)
          (GCoordi.rightInv c))
      (GCoordi.rightInv d)).single i = 0
  simp [GCoordi.mul, GCoordi.rightInv]

private lemma general_commutator_three
    {t : ℕ} (c d : GCoordi t)
    (hc : GeneralWeightTwo c) :
    GeneralWeightThree ⁅c, d⁆ := by
  refine ⟨general_commutator_zero c d, fun q => ?_⟩
  change
    (GCoordi.mul
      (GCoordi.mul
        (GCoordi.mul c d)
          (GCoordi.rightInv c))
      (GCoordi.rightInv d)).pair q = 0
  simp [GCoordi.mul, GCoordi.rightInv,
    hc.single q.i, hc.single q.j]

theorem general_three_center (t : ℕ) :
    generalThreeSubgroup t ≤
      Subgroup.center (GCoordi t) := by
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro d
  change GCoordi.mul d c =
    GCoordi.mul c d
  ext <;>
    simp [GCoordi.mul, hc.single _, hc.pair _,
      Triple.ij, Triple.ik, Triple.jk] <;>
    ring

theorem lower_series_general (t : ℕ) :
    Subgroup.lowerCentralSeries (GCoordi t) 1 ≤
      generalTwoSubgroup t := by
  rw [show 1 = 0 + 1 by omega, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_zero]
  exact Subgroup.commutator_le.mpr fun c _ d _ =>
    general_commutator_zero c d

theorem lower_general_two (t : ℕ) :
    Subgroup.lowerCentralSeries (GCoordi t) 2 ≤
      generalThreeSubgroup t := by
  rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ]
  exact Subgroup.commutator_le.mpr fun c hc d _ =>
    general_commutator_three c d
      (lower_series_general t hc)

theorem series_general_bot (t : ℕ) :
    Subgroup.lowerCentralSeries (GCoordi t) 3 = ⊥ := by
  apply Subgroup.lowerCentralSeries_succ_eq_bot
  exact (lower_general_two t).trans
    (general_three_center t)

theorem lower_general_bot
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Subgroup.lowerCentralSeries (GeneralResidueGroup order horder) 3 = ⊥ := by
  let q := (generalCon order horder).mk'
  rw [← central_series_surjective q
    (generalCon order horder).mk'_surjective 3,
    series_general_bot t,
    Subgroup.map_bot]

end P1960
end Struik

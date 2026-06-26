import Towers.Group.NilpotentProducts.HallRankBasis
import Towers.Group.NilpotentProducts.RankThreeGeneration
import Mathlib.SetTheory.Cardinal.Finite


/-!
# A finite Hall-coordinate cover for Theorem 1
-/

namespace Struik
namespace P1960

open Towers
open Towers.TCTex
open Towers.TCTex

universe u

/-- A chosen integral representative of a residue class. -/
noncomputable def zmodRepresentative {n : ℕ} (x : ZMod n) : ℤ :=
  Classical.choose (ZMod.intCast_surjective x)

@[simp] theorem zmodRepresentative_cast {n : ℕ} (x : ZMod n) :
    (zmodRepresentative x : ZMod n) = x :=
  Classical.choose_spec (ZMod.intCast_surjective x)

/-- Powers agree when their exponents are congruent modulo a known
annihilating exponent. -/
theorem zpow_mod_pow
    {G : Type*} [Group G] (g : G) {m : ℕ} {a b : ℤ}
    (hab : a ≡ b [ZMOD (m : ℤ)])
    (hm : g ^ m = 1) :
    g ^ a = g ^ b := by
  apply orderOf_dvd_sub_iff_zpow_eq_zpow.mp
  have horder : orderOf g ∣ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hm
  have hcast : (orderOf g : ℤ) ∣ (m : ℤ) :=
    Int.natCast_dvd_natCast.mpr horder
  exact hcast.trans ((Int.modEq_iff_dvd).mp hab.symm)

/-- The three weight blocks of Hall residues below the class-four cutoff. -/
abbrev RankHallResidues
    (order : Fin 3 → ℕ) :=
  (∀ i : (standardHallFamily.{u} 3 1).index,
      ZMod (standardFactorOrder order i)) ×
  (∀ i : (standardHallFamily.{u} 3 2).index,
      ZMod (standardFactorOrder order i)) ×
  (∀ i : (standardHallFamily.{u} 3 3).index,
      ZMod (standardFactorOrder order i))

/-- Evaluate one residue-valued Hall weight block in the cyclic nilpotent
product. -/
noncomputable def mappedResidueProduct
    (order : Fin 3 → ℕ) (r : ℕ)
    (z : ∀ i : (standardHallFamily.{u} 3 r).index,
      ZMod (standardFactorOrder order i)) :
    NilpotentCyclicProduct order 4 :=
  ((Finset.univ.sort fun i j :
      (standardHallFamily.{u} 3 r).index => i ≤ j).map fun i =>
    inverseTruncation.{u} order
        ((standardHallFamily.{u} 3 r).commutator i
          |>.freeLowerTruncation (n := 4)) ^
      zmodRepresentative (z i)).prod

/-- Evaluate all Hall residue coordinates in increasing weight. -/
noncomputable def rankResidueEval
    (order : Fin 3 → ℕ) :
    RankHallResidues order →
      NilpotentCyclicProduct order 4
  | ⟨z₁, z₂, z₃⟩ =>
      mappedResidueProduct order 1 z₁ *
        mappedResidueProduct order 2 z₂ *
          mappedResidueProduct order 3 z₃

private theorem mapped_residue_cast
    (order : Fin 3 → ℕ)
    (horder : ∀ i, AOrd (order i))
    (r : ℕ)
    (e : (standardHallFamily.{u} 3 r).index → ℤ) :
    mappedResidueProduct order r
        (fun i => (e i : ZMod (standardFactorOrder order i))) =
      inverseTruncation.{u} order
        ((standardHallFamily.{u} 3 r).collectedWeightProduct
          (n := 4) e) := by
  unfold mappedResidueProduct
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  change
    inverseTruncation.{u} order
          ((standardHallFamily.{u} 3 r).commutator i
            |>.freeLowerTruncation (n := 4)) ^
        zmodRepresentative
          (e i : ZMod (standardFactorOrder order i)) =
      inverseTruncation.{u} order
        (((standardHallFamily.{u} 3 r).commutator i
          |>.freeLowerTruncation (n := 4)) ^ e i)
  rw [map_zpow]
  apply zpow_mod_pow
  · exact
      (ZMod.intCast_eq_intCast_iff
        (zmodRepresentative
          (e i : ZMod (standardFactorOrder order i)))
        (e i) (standardFactorOrder order i)).mp
        (zmodRepresentative_cast
          (e i : ZMod (standardFactorOrder order i)))
  · exact mapped_standard_order
      order horder i

private theorem standard_four_products
    (e : StandardExponentFamily 3) :
    standardHallProduct 3 4 e =
      (standardHallFamily.{u} 3 1).collectedWeightProduct (n := 4) (e 1) *
        (standardHallFamily.{u} 3 2).collectedWeightProduct (n := 4) (e 2) *
          (standardHallFamily.{u} 3 3).collectedWeightProduct (n := 4)
            (e 3) := by
  norm_num [standardHallProduct, collectedHallProduct,
    collectedPrefixProduct, List.range_succ, mul_assoc]

/-- Reducing every Hall exponent modulo its recursive gcd still gives a
surjective coordinate map onto the cyclic fourth nilpotent product. -/
theorem rank_residue_surjective
    (order : Fin 3 → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Function.Surjective (rankResidueEval.{u} order) := by
  intro x
  obtain ⟨e, he⟩ :=
    mapped_standard_hall.{u} order x
  refine ⟨⟨fun i => (e 1 i : ZMod (standardFactorOrder order i)),
    fun i => (e 2 i : ZMod (standardFactorOrder order i)),
    fun i => (e 3 i : ZMod (standardFactorOrder order i))⟩, ?_⟩
  rw [rankResidueEval,
    mapped_residue_cast order horder 1,
    mapped_residue_cast order horder 2,
    mapped_residue_cast order horder 3,
    ← map_mul, ← map_mul,
    ← standard_four_products]
  exact he

end P1960
end Struik

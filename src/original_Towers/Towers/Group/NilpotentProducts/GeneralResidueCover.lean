import Towers.Group.NilpotentProducts.LowWeightBasis
import Towers.Group.NilpotentProducts.RankResidueCover

/-!
# A Hall-coordinate cover for Struik's Theorem 2

For arbitrary finite rank, the Hall factors of weights one, two, and three
cover the cyclic fourth nilpotent product.  Each exponent may be reduced
modulo the recursive gcd of the orders at its leaves.
-/

namespace Struik
namespace P1960

open Towers
open Towers.TCTex
open Towers.TCTex

universe u

/-- The three residue-valued Hall weight blocks below the class-four cutoff. -/
abbrev ResiduesUpThree
    {t : ℕ} (order : Fin t → ℕ) :=
  (∀ i : (standardHallFamily.{u} t 1).index,
      ZMod (standardFactorOrder order i)) ×
  (∀ i : (standardHallFamily.{u} t 2).index,
      ZMod (standardFactorOrder order i)) ×
  (∀ i : (standardHallFamily.{u} t 3).index,
      ZMod (standardFactorOrder order i))

/-- Evaluate one residue-valued Hall weight block in the cyclic nilpotent
product. -/
noncomputable def mappedGeneralResidue
    {t : ℕ} (order : Fin t → ℕ) (r : ℕ)
    (z : ∀ i : (standardHallFamily.{u} t r).index,
      ZMod (standardFactorOrder order i)) :
    NilpotentCyclicProduct order 4 :=
  ((Finset.univ.sort fun i j :
      (standardHallFamily.{u} t r).index => i ≤ j).map fun i =>
    inverseTruncation.{u} order
        ((standardHallFamily.{u} t r).commutator i
          |>.freeLowerTruncation (n := 4)) ^
      zmodRepresentative (z i)).prod

/-- Evaluate all Hall residue coordinates in increasing weight. -/
noncomputable def generalHallResidue
    {t : ℕ} (order : Fin t → ℕ) :
    ResiduesUpThree.{u} order →
      NilpotentCyclicProduct order 4
  | ⟨z₁, z₂, z₃⟩ =>
      mappedGeneralResidue order 1 z₁ *
        mappedGeneralResidue order 2 z₂ *
          mappedGeneralResidue order 3 z₃

theorem mapped_int_cast
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (r : ℕ)
    (e : (standardHallFamily.{u} t r).index → ℤ) :
    mappedGeneralResidue order r
        (fun i => (e i : ZMod (standardFactorOrder order i))) =
      inverseTruncation.{u} order
        ((standardHallFamily.{u} t r).collectedWeightProduct
          (n := 4) e) := by
  unfold mappedGeneralResidue
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  change
    inverseTruncation.{u} order
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := 4)) ^
        zmodRepresentative
          (e i : ZMod (standardFactorOrder order i)) =
      inverseTruncation.{u} order
        (((standardHallFamily.{u} t r).commutator i
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

@[simp] theorem mapped_general_residue
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (r : ℕ) :
    mappedGeneralResidue order r
        (0 : ∀ i : (standardHallFamily.{u} t r).index,
          ZMod (standardFactorOrder order i)) =
      1 := by
  rw [show
    (0 : ∀ i : (standardHallFamily.{u} t r).index,
      ZMod (standardFactorOrder order i)) =
        fun i => ((0 : ℤ) :
          ZMod (standardFactorOrder order i)) by
      funext i
      simp]
  calc
    mappedGeneralResidue order r
        (fun i => ((0 : ℤ) :
          ZMod (standardFactorOrder order i))) =
        inverseTruncation.{u} order
          ((standardHallFamily.{u} t r).collectedWeightProduct
            (n := 4)
            (0 : (standardHallFamily.{u} t r).index → ℤ)) := by
      simpa using
        mapped_int_cast
          order horder r
          (0 : (standardHallFamily.{u} t r).index → ℤ)
    _ = 1 := by
      rw [BCWta.collected_weight_productzero,
        map_one]

@[simp] theorem general_residue_zero
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    generalHallResidue.{u} order
        (0 : ResiduesUpThree.{u} order) =
      1 := by
  simp [generalHallResidue,
    mapped_general_residue order horder]

private theorem standard_general_products
    {t : ℕ} (e : StandardExponentFamily.{u} t) :
    standardHallProduct t 4 e =
      (standardHallFamily.{u} t 1).collectedWeightProduct (n := 4) (e 1) *
        (standardHallFamily.{u} t 2).collectedWeightProduct (n := 4) (e 2) *
          (standardHallFamily.{u} t 3).collectedWeightProduct (n := 4)
            (e 3) := by
  norm_num [standardHallProduct, collectedHallProduct,
    collectedPrefixProduct, List.range_succ, mul_assoc]

/-- Reducing every Hall exponent modulo its recursive leaf gcd gives a
surjective coordinate map in every finite rank. -/
theorem general_residue_surjective
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Function.Surjective (generalHallResidue.{u} order) := by
  intro x
  obtain ⟨e, he⟩ :=
    mapped_standard_hall.{u} order x
  refine ⟨⟨fun i => (e 1 i : ZMod (standardFactorOrder order i)),
    fun i => (e 2 i : ZMod (standardFactorOrder order i)),
    fun i => (e 3 i : ZMod (standardFactorOrder order i))⟩, ?_⟩
  rw [generalHallResidue,
    mapped_int_cast order horder 1,
    mapped_int_cast order horder 2,
    mapped_int_cast order horder 3,
    ← map_mul, ← map_mul,
    ← standard_general_products]
  exact he

end P1960
end Struik

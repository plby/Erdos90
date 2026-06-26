import Towers.Group.NilpotentProducts.GeneralCollection
import Towers.Group.NilpotentProducts.CyclicProducts
import Mathlib.Data.Int.GCD

/-!
# Odd-order commutators in class-three groups

This is the class-three part of Struik's Lemma 1.  It supplies the
commutator-order bounds used in Theorems 1 and 2.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open Towers.TCTex
open Towers.TCTex.HCThree
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- For an odd natural number `2k+1`, its generalized binomial
coefficient `choose m 2` is `m*k`. -/
lemma ring_choose_two
    (k : ℕ) :
    Ring.choose ((2 * k + 1 : ℕ) : ℤ) 2 =
      ((2 * k + 1 : ℕ) : ℤ) * k := by
  rw [Ring.choose_natCast]
  norm_cast
  rw [Nat.choose_two_right, show 2 * k + 1 - 1 = 2 * k by omega]
  rw [Nat.mul_div_assoc _ (by simp : 2 ∣ 2 * k)]
  simp

/-- In a class-three group, an odd order relation on the left input is
inherited by its commutator with any element. -/
theorem element_order_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {x y : G} {m : ℕ}
    (hm : Odd m) (hx : x ^ m = 1) :
    ⁅x, y⁆ ^ m = 1 := by
  let C := ⁅x, y⁆
  let D := ⁅x, C⁆
  let E := ⁅y, C⁆
  have hx0 : x ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hy0 : y ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hC : C ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa [C] using
      element_lower_series hx0 hy0
  have hD : D ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa [D] using
      element_lower_series hx0 hC
  have hcentralD : ∀ z : G, Commute z D :=
    fun z => commute_series_three hG4 z hD
  have hxz : x ^ (m : ℤ) = 1 := by
    simpa using hx
  have hDm : D ^ (m : ℤ) = 1 := by
    have hscale :
        ⁅x ^ (m : ℤ), C⁆ = D ^ (m : ℤ) := by
      simpa [D] using
        commutator_zpow_commute
          (hcentralD x) (m : ℤ)
    rw [hxz] at hscale
    simpa using hscale.symm
  obtain ⟨km, rfl⟩ := hm
  have hDchoose :
      D ^ Ring.choose (((2 * km + 1 : ℕ) : ℤ)) 2 = 1 := by
    rw [ring_choose_two, zpow_mul, hDm, one_zpow]
  have hchooseOne : Ring.choose (1 : ℤ) 2 = 0 := by
    simpa using (Ring.choose_natCast (R := ℤ) 1 2)
  have hformula :=
    commutator_zpow_three
      hG4 x y (((2 * km + 1 : ℕ) : ℤ)) 1
  change
    _ =
      D ^ (Ring.choose (((2 * km + 1 : ℕ) : ℤ)) 2 * 1) *
        C ^ ((((2 * km + 1 : ℕ) : ℤ)) * 1) *
          E ^ ((((2 * km + 1 : ℕ) : ℤ)) * Ring.choose (1 : ℤ) 2)
    at hformula
  rw [hxz] at hformula
  simp only [mul_one] at hformula
  rw [hDchoose, hchooseOne] at hformula
  simp at hformula
  rw [← zpow_natCast]
  simpa [C] using hformula.symm

/-- In a class-three group, an odd order relation on the right input is
inherited by its commutator with any element. -/
theorem commutator_element_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {x y : G} {n : ℕ}
    (hn : Odd n) (hy : y ^ n = 1) :
    ⁅x, y⁆ ^ n = 1 := by
  let C := ⁅x, y⁆
  let D := ⁅x, C⁆
  let E := ⁅y, C⁆
  have hx0 : x ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hy0 : y ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hC : C ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa [C] using
      element_lower_series hx0 hy0
  have hE : E ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa [E] using
      element_lower_series hy0 hC
  have hcentralE : ∀ z : G, Commute z E :=
    fun z => commute_series_three hG4 z hE
  have hyz : y ^ (n : ℤ) = 1 := by
    simpa using hy
  have hEn : E ^ (n : ℤ) = 1 := by
    have hscale :
        ⁅y ^ (n : ℤ), C⁆ = E ^ (n : ℤ) := by
      simpa [E] using
        commutator_zpow_commute
          (hcentralE y) (n : ℤ)
    rw [hyz] at hscale
    simpa using hscale.symm
  obtain ⟨kn, rfl⟩ := hn
  have hEchoose :
      E ^ Ring.choose (((2 * kn + 1 : ℕ) : ℤ)) 2 = 1 := by
    rw [ring_choose_two, zpow_mul, hEn, one_zpow]
  have hchooseOne : Ring.choose (1 : ℤ) 2 = 0 := by
    simpa using (Ring.choose_natCast (R := ℤ) 1 2)
  have hformula :=
    commutator_zpow_three
      hG4 x y 1 (((2 * kn + 1 : ℕ) : ℤ))
  change
    _ =
      D ^ (Ring.choose (1 : ℤ) 2 * (((2 * kn + 1 : ℕ) : ℤ))) *
        C ^ ((1 : ℤ) * (((2 * kn + 1 : ℕ) : ℤ))) *
          E ^ ((1 : ℤ) * Ring.choose (((2 * kn + 1 : ℕ) : ℤ)) 2)
    at hformula
  rw [hyz] at hformula
  simp only [one_mul] at hformula
  rw [hEchoose, hchooseOne] at hformula
  simp at hformula
  rw [← zpow_natCast]
  simpa [C] using hformula.symm

/-- In a class-three group, the commutator of two odd-order elements has
order dividing the gcd of their specified orders. -/
theorem pow_gcd_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {x y : G} {m n : ℕ}
    (hm : Odd m) (hn : Odd n)
    (hx : x ^ m = 1) (hy : y ^ n = 1) :
    ⁅x, y⁆ ^ Nat.gcd m n = 1 :=
  pow_gcd_eq_one.mpr
    ⟨element_order_odd
        hG4 hm hx,
      commutator_element_odd
        hG4 hn hy⟩

/-- The same gcd bound when order `0` is permitted to denote an infinite
cyclic input, as in Struik's paper. -/
theorem element_gcd_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {x y : G} {m n : ℕ}
    (hm : m = 0 ∨ Odd m) (hn : n = 0 ∨ Odd n)
    (hx : x ^ m = 1) (hy : y ^ n = 1) :
    ⁅x, y⁆ ^ Nat.gcd m n = 1 := by
  rcases hm with rfl | hm
  · rcases hn with rfl | hn
    · simp
    · simpa using
        commutator_element_odd
          hG4 hn hy
  · rcases hn with rfl | hn
    · simpa using
        element_order_odd
          hG4 hm hx
    · exact pow_gcd_odd
        hG4 hm hn hx hy

/-- Hall-convention version of the odd class-three commutator-order
bound. -/
theorem gcd_three_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {m n : ℕ}
    (hm : Odd m) (hn : Odd n)
    (ha : a ^ m = 1) (hb : b ^ n = 1) :
    hallCommutator a b ^ Nat.gcd m n = 1 := by
  rw [hall_element_inv]
  apply pow_gcd_odd
    hG4 hm hn
  · simpa using congrArg Inv.inv ha
  · simpa using congrArg Inv.inv hb

/-- Hall-convention gcd bound with Struik's order-zero convention. -/
theorem commutator_gcd_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {m n : ℕ}
    (hm : m = 0 ∨ Odd m) (hn : n = 0 ∨ Odd n)
    (ha : a ^ m = 1) (hb : b ^ n = 1) :
    hallCommutator a b ^ Nat.gcd m n = 1 := by
  rw [hall_element_inv]
  apply element_gcd_odd
    hG4 hm hn
  · simpa using congrArg Inv.inv ha
  · simpa using congrArg Inv.inv hb

/-- A left-normed Hall triple commutator has order dividing the gcd of
the three specified odd orders. -/
theorem triple_gcd_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {m n q : ℕ}
    (hm : Odd m) (hn : Odd n) (hq : Odd q)
    (ha : a ^ m = 1) (hb : b ^ n = 1) (hc : c ^ q = 1) :
    hallTripleCommutator a b c ^ Nat.gcd (Nat.gcd m n) q = 1 := by
  have hab :
      hallCommutator a b ^ Nat.gcd m n = 1 :=
    gcd_three_odd
      hG4 hm hn ha hb
  have hgcd : Odd (Nat.gcd m n) :=
    hm.of_dvd_nat (Nat.gcd_dvd_left m n)
  exact gcd_three_odd
    hG4 hgcd hq hab hc

/-- The weight-three part of Lemma 1, including infinite cyclic inputs
encoded by order zero. -/
theorem gcd_or_odd
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {m n q : ℕ}
    (hm : m = 0 ∨ Odd m)
    (hn : n = 0 ∨ Odd n)
    (hq : q = 0 ∨ Odd q)
    (ha : a ^ m = 1) (hb : b ^ n = 1) (hc : c ^ q = 1) :
    hallTripleCommutator a b c ^ Nat.gcd (Nat.gcd m n) q = 1 := by
  have hab :
      hallCommutator a b ^ Nat.gcd m n = 1 :=
    commutator_gcd_odd
      hG4 hm hn ha hb
  have hgcd : Nat.gcd m n = 0 ∨ Odd (Nat.gcd m n) := by
    rcases hm with rfl | hm
    · rcases hn with rfl | hn
      · exact Or.inl (by simp)
      · exact Or.inr (by simpa using hn)
    · rcases hn with rfl | hn
      · exact Or.inr (by simpa using hm)
      · exact Or.inr (hm.of_dvd_nat (Nat.gcd_dvd_left m n))
  exact commutator_gcd_odd
    hG4 hgcd hq hab hc

/-- Lemma 1 for a weight-two standard commutator in the fourth
nilpotent product of cyclic groups. -/
theorem weight_nilpotent_four
    {ι : Type*} (order : ι → ℕ) (i j : ι)
    (hi : order i = 0 ∨ Odd (order i))
    (hj : order j = 0 ∨ Odd (order j)) :
    hallCommutator
        (nilpotentCyclicGenerator order 4 i)
        (nilpotentCyclicGenerator order 4 j) ^
      Nat.gcd (order i) (order j) =
        1 := by
  apply commutator_gcd_odd
    (nilpotent_four_bot order)
    hi hj
  · exact nilpotent_cyclic_generator order 4 i
  · exact nilpotent_cyclic_generator order 4 j

/-- Lemma 1 for a weight-three standard commutator in the fourth
nilpotent product of cyclic groups. -/
theorem nilpotent_cyclic_four
    {ι : Type*} (order : ι → ℕ) (i j k : ι)
    (hi : order i = 0 ∨ Odd (order i))
    (hj : order j = 0 ∨ Odd (order j))
    (hk : order k = 0 ∨ Odd (order k)) :
    hallTripleCommutator
        (nilpotentCyclicGenerator order 4 i)
        (nilpotentCyclicGenerator order 4 j)
        (nilpotentCyclicGenerator order 4 k) ^
      Nat.gcd (Nat.gcd (order i) (order j)) (order k) =
        1 := by
  apply gcd_or_odd
    (nilpotent_four_bot order)
    hi hj hk
  · exact nilpotent_cyclic_generator order 4 i
  · exact nilpotent_cyclic_generator order 4 j
  · exact nilpotent_cyclic_generator order 4 k

end P1960
end Struik

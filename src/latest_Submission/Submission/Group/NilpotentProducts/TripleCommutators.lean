import Submission.Group.NilpotentProducts.GeneralCollection
import Submission.Group.NilpotentProducts.CyclicProducts
import Mathlib.Data.Int.GCD

/-!
# Triple-commutator orders in class-three groups

At class three, Hall triple commutators are exactly trilinear.  Unlike the
weight-two part of Lemma 1, these order bounds require no oddness
assumption.  They are the Magnus bounds used in Struik's Theorem 4.
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton
open Submission.TCTex
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- Hall commutators respect the usual lower-central weight sum. -/
lemma commutator_lower_series
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    hallCommutator x y ∈ Subgroup.lowerCentralSeries G (i + j + 1) := by
  rw [hall_element_inv]
  exact element_lower_series
    ((Subgroup.lowerCentralSeries G i).inv_mem hx)
    ((Subgroup.lowerCentralSeries G j).inv_mem hy)

/-- A Hall triple commutator has the sum of the three input weights. -/
lemma triple_commutator_series
    {i j k : ℕ} {x y z : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (hz : z ∈ Subgroup.lowerCentralSeries G k) :
    hallTripleCommutator x y z ∈
      Subgroup.lowerCentralSeries G (i + j + k + 2) := by
  rw [hallTripleCommutator]
  have hxy :=
    commutator_lower_series hx hy
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    commutator_lower_series hxy hz

lemma commute_paper_1960
    (x y : G) :
    hallCommutator x y = 1 ↔ Commute x y := by
  rw [hall_element_inv,
    commutatorElement_eq_one_iff_commute, Commute.inv_inv_iff]

lemma lower_series_class
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {x : G} (hx : x ∈ Subgroup.lowerCentralSeries G 3) :
    x = 1 := by
  rw [hG4] at hx
  exact Subgroup.mem_bot.mp hx

/-- Multiplying the first Hall-commutator input by a central element does
not change the commutator. -/
lemma commutator_left_central
    {x y z : G} (hz : ∀ g : G, Commute g z) :
    hallCommutator (x * z) y = hallCommutator x y := by
  rw [commutatorIdentitiesFirst]
  have hmid :
      hallCommutator (hallCommutator x y) z = 1 :=
    (commute_paper_1960 _ _).2
      (hz (hallCommutator x y))
  have hlast :
      hallCommutator z y = 1 :=
    (commute_paper_1960 _ _).2
      (hz y).symm
  rw [hmid, hlast]
  simp

/-- Once the left input lies in the commutator subgroup, powers pull out
of a Hall commutator exactly in a class-three group. -/
theorem zpow_lower_series
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {x y : G} (hx : x ∈ Subgroup.lowerCentralSeries G 1)
    (r : ℤ) :
    hallCommutator (x ^ r) y = hallCommutator x y ^ r := by
  have hy : y ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have htLeft :
      hallTripleCommutator x y x ∈ Subgroup.lowerCentralSeries G 3 :=
    Subgroup.lowerCentralSeries_antitone (by omega)
      (triple_commutator_series hx hy hx)
  have htRight :
      hallTripleCommutator x y y ∈ Subgroup.lowerCentralSeries G 3 :=
    Subgroup.lowerCentralSeries_antitone (by omega)
      (triple_commutator_series hx hy hy)
  have hleftOne :
      hallTripleCommutator x y x = 1 :=
    lower_series_class hG4 htLeft
  have hrightOne :
      hallTripleCommutator x y y = 1 :=
    lower_series_class hG4 htRight
  simpa [hleftOne, hrightOne] using
    first_class_three hG4 x y r 1

/-- Once the left input lies in the commutator subgroup, powers pull out
of the right Hall-commutator input exactly in a class-three group. -/
theorem commutator_zpow_series
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {x y : G} (hx : x ∈ Subgroup.lowerCentralSeries G 1)
    (r : ℤ) :
    hallCommutator x (y ^ r) = hallCommutator x y ^ r := by
  have hy : y ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have htLeft :
      hallTripleCommutator x y x ∈ Subgroup.lowerCentralSeries G 3 :=
    Subgroup.lowerCentralSeries_antitone (by omega)
      (triple_commutator_series hx hy hx)
  have htRight :
      hallTripleCommutator x y y ∈ Subgroup.lowerCentralSeries G 3 :=
    Subgroup.lowerCentralSeries_antitone (by omega)
      (triple_commutator_series hx hy hy)
  have hleftOne :
      hallTripleCommutator x y x = 1 :=
    lower_series_class hG4 htLeft
  have hrightOne :
      hallTripleCommutator x y y = 1 :=
    lower_series_class hG4 htRight
  simpa [hleftOne, hrightOne] using
    first_class_three hG4 x y 1 r

/-- Exact trilinearity in the first input. -/
theorem triple_zpow_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b c : G) (r : ℤ) :
    hallTripleCommutator (a ^ r) b c =
      hallTripleCommutator a b c ^ r := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  have ha : a ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hb : b ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hC : C ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa [C] using commutator_lower_series ha hb
  have hD : D ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa [D] using
      triple_commutator_series ha hb ha
  have hcentralD : ∀ g : G, Commute g D :=
    fun g => commute_series_three hG4 g hD
  have hinner :
      hallCommutator (a ^ r) b =
        C ^ r * D ^ Ring.choose r 2 := by
    have hchooseOne : Ring.choose (1 : ℤ) 2 = 0 := by
      simpa using (Ring.choose_natCast (R := ℤ) 1 2)
    simpa [C, D, hchooseOne] using
      first_class_three hG4 a b r 1
  rw [hallTripleCommutator, hinner]
  rw [commutator_left_central
    (fun g => (hcentralD g).zpow_right (Ring.choose r 2))]
  exact zpow_lower_series
    hG4 hC r

/-- Exact trilinearity in the second input. -/
theorem triple_zpow_middle
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b c : G) (r : ℤ) :
    hallTripleCommutator a (b ^ r) c =
      hallTripleCommutator a b c ^ r := by
  let C := hallCommutator a b
  let E := hallTripleCommutator a b b
  have ha : a ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hb : b ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hC : C ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa [C] using commutator_lower_series ha hb
  have hE : E ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa [E] using
      triple_commutator_series ha hb hb
  have hcentralE : ∀ g : G, Commute g E :=
    fun g => commute_series_three hG4 g hE
  have hinner :
      hallCommutator a (b ^ r) =
        C ^ r * E ^ Ring.choose r 2 := by
    have hchooseOne : Ring.choose (1 : ℤ) 2 = 0 := by
      simpa using (Ring.choose_natCast (R := ℤ) 1 2)
    simpa [C, E, hchooseOne] using
      first_class_three hG4 a b 1 r
  rw [hallTripleCommutator, hinner]
  rw [commutator_left_central
    (fun g => (hcentralE g).zpow_right (Ring.choose r 2))]
  exact zpow_lower_series
    hG4 hC r

/-- An order relation on the first input kills the same power of a Hall
triple commutator. -/
theorem triple_commutator_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {m : ℕ} (ha : a ^ m = 1) :
    hallTripleCommutator a b c ^ m = 1 := by
  rw [← zpow_natCast,
    ← triple_zpow_three hG4]
  simp [ha, hallTripleCommutator, hallCommutator]

/-- An order relation on the second input kills the same power of a Hall
triple commutator. -/
theorem triple_middle_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {n : ℕ} (hb : b ^ n = 1) :
    hallTripleCommutator a b c ^ n = 1 := by
  rw [← zpow_natCast,
    ← triple_zpow_middle hG4]
  simp [hb, hallTripleCommutator, hallCommutator]

/-- An order relation on the third input kills the same power of a Hall
triple commutator. -/
theorem triple_order_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {q : ℕ} (hc : c ^ q = 1) :
    hallTripleCommutator a b c ^ q = 1 := by
  rw [hallTripleCommutator, hall_element_inv]
  let X := (hallCommutator a b)⁻¹
  let Y := c⁻¹
  have habMem :
      hallCommutator a b ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa using
      (commutator_lower_series
        (i := 0) (j := 0) (x := a) (y := b)
        (by simp) (by simp))
  have hX : X ∈ Subgroup.lowerCentralSeries G 1 :=
    (Subgroup.lowerCentralSeries G 1).inv_mem habMem
  have hY : Y ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hXY : ⁅X, Y⁆ ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa using element_lower_series hX hY
  have hcommute : Commute Y ⁅X, Y⁆ :=
    commute_series_three hG4 Y hXY
  have hYqNat : Y ^ q = 1 := by
    simpa [Y] using congrArg Inv.inv hc
  have hYq : Y ^ (q : ℤ) = 1 := by
    simpa using hYqNat
  have hscale :
      ⁅X, Y ^ (q : ℤ)⁆ = ⁅X, Y⁆ ^ (q : ℤ) :=
    zpow_commute_collection
      hcommute (q : ℤ)
  rw [hYq] at hscale
  change ⁅X, Y⁆ ^ q = 1
  rw [← zpow_natCast]
  simpa using hscale.symm

/-- A Hall triple commutator has order dividing the gcd of any three
specified input orders. -/
theorem triple_gcd_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b c : G} {m n q : ℕ}
    (ha : a ^ m = 1) (hb : b ^ n = 1) (hc : c ^ q = 1) :
    hallTripleCommutator a b c ^ Nat.gcd (Nat.gcd m n) q = 1 :=
  pow_gcd_eq_one.mpr
    ⟨pow_gcd_eq_one.mpr
        ⟨triple_commutator_three
            hG4 ha,
          triple_middle_three
            hG4 hb⟩,
      triple_order_three
        hG4 hc⟩

/-- The unrestricted weight-three order bound for canonical generators
in `F/F₄`. -/
theorem nilpotent_four_unrestricted
    {ι : Type*} (order : ι → ℕ) (i j k : ι) :
    hallTripleCommutator
        (nilpotentCyclicGenerator order 4 i)
        (nilpotentCyclicGenerator order 4 j)
        (nilpotentCyclicGenerator order 4 k) ^
      Nat.gcd (Nat.gcd (order i) (order j)) (order k) =
        1 := by
  apply triple_gcd_three
    (nilpotent_four_bot order)
  · exact nilpotent_cyclic_generator order 4 i
  · exact nilpotent_cyclic_generator order 4 j
  · exact nilpotent_cyclic_generator order 4 k

end P1960
end Struik

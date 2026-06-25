import Submission.Group.NilpotentProducts.CommutatorIdentities
import Submission.Group.Zassenhaus.Polynomial

/-!
# Struik (1960), collection in arbitrary groups of class at most three

Mathlib uses a zero-based lower-central series, so the hypothesis
`Subgroup.lowerCentralSeries G 3 = ⊥` is Struik's condition `G₄ = 1`.
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton
open Submission.TCTex
open Submission.TCTex.HCThree
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- Every member of the third one-based lower-central layer is central when
the fourth layer is trivial. -/
lemma commute_series_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (x : G) {z : G} (hz : z ∈ Subgroup.lowerCentralSeries G 2) :
    Commute x z := by
  have hx : x ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hxz : ⁅x, z⁆ ∈ Subgroup.lowerCentralSeries G 3 := by
    simpa using element_lower_series hx hz
  rw [hG4] at hxz
  rw [← commutatorElement_eq_one_iff_commute]
  exact Subgroup.mem_bot.mp hxz

/-- The signed class-three commutator collection formula in an arbitrary
group whose fourth one-based lower-central term is trivial. -/
lemma commutator_zpow_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ⁅left ^ leftExponent, right ^ rightExponent⁆ =
      ⁅left, ⁅left, right⁆⁆ ^
          (Ring.choose leftExponent 2 * rightExponent) *
        ⁅left, right⁆ ^ (leftExponent * rightExponent) *
          ⁅right, ⁅left, right⁆⁆ ^
            (leftExponent * Ring.choose rightExponent 2) := by
  let C := ⁅left, right⁆
  let D := ⁅left, ⁅left, right⁆⁆
  let E := ⁅right, ⁅left, right⁆⁆
  have hleft : left ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hright : right ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hC : C ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa [C] using
      element_lower_series hleft hright
  have hD : D ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa [D] using
      element_lower_series hleft hC
  have hE : E ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa [E] using
      element_lower_series hright hC
  have hcentralD : ∀ x : G, Commute x D :=
    fun x => commute_series_three hG4 x hD
  have hcentralE : ∀ x : G, Commute x E :=
    fun x => commute_series_three hG4 x hE
  have hleftExpansion :
      ⁅left ^ leftExponent, right⁆ =
        D ^ Ring.choose leftExponent 2 * C ^ leftExponent := by
    simpa [C, D] using
      commutator_element_zpow
        left right (hcentralD left) (hcentralD C) leftExponent
  have hleftPower : left ^ leftExponent ∈ Subgroup.lowerCentralSeries G 0 := by
    simp
  have hpoweredC :
      ⁅left ^ leftExponent, right⁆ ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa using
      element_lower_series hleftPower hright
  have hpoweredE :
      ⁅right, ⁅left ^ leftExponent, right⁆⁆ ∈
        Subgroup.lowerCentralSeries G 2 := by
    simpa using
      element_lower_series hright hpoweredC
  have hrightPoweredE :
      Commute right ⁅right, ⁅left ^ leftExponent, right⁆⁆ :=
    commute_series_three
      hG4 right hpoweredE
  have hpoweredCPoweredE :
      Commute ⁅left ^ leftExponent, right⁆
        ⁅right, ⁅left ^ leftExponent, right⁆⁆ :=
    commute_series_three
      hG4 ⁅left ^ leftExponent, right⁆ hpoweredE
  have hrightExpansion :
      ⁅left ^ leftExponent, right ^ rightExponent⁆ =
        ⁅left ^ leftExponent, right⁆ ^ rightExponent *
          ⁅right, ⁅left ^ leftExponent, right⁆⁆ ^
            Ring.choose rightExponent 2 := by
    exact
      element_zpow_nested
        (left ^ leftExponent) right
        hrightPoweredE hpoweredCPoweredE rightExponent
  have hscaledE :
      ⁅right, ⁅left ^ leftExponent, right⁆⁆ =
        E ^ leftExponent := by
    rw [hleftExpansion, element_mul_right]
    rw [commutatorElement_eq_one_iff_commute.mpr
      ((hcentralD right).zpow_right (Ring.choose leftExponent 2))]
    rw [one_mul]
    rw [zpow_commute_collection
      (hcentralE C)]
    change
      D ^ Ring.choose leftExponent 2 * E ^ leftExponent *
          (D ^ Ring.choose leftExponent 2)⁻¹ =
        E ^ leftExponent
    rw [((hcentralE D).zpow_zpow
      (Ring.choose leftExponent 2) leftExponent).eq]
    group
  rw [hrightExpansion, hscaledE, hleftExpansion]
  rw [((hcentralD C).symm.zpow_zpow
    (Ring.choose leftExponent 2) leftExponent).mul_zpow]
  rw [zpow_mul, zpow_mul, zpow_mul]

/-- A Hall triple commutator belongs to the third one-based lower-central
layer. -/
lemma triple_series_general
    (x y z : G) :
    hallTripleCommutator x y z ∈ Subgroup.lowerCentralSeries G 2 := by
  have hx : x⁻¹ ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hy : y⁻¹ ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hz : z⁻¹ ∈ Subgroup.lowerCentralSeries G 0 := by simp
  have hxy : hallCommutator x y ∈ Subgroup.lowerCentralSeries G 1 := by
    rw [hall_element_inv]
    simpa using element_lower_series hx hy
  rw [hallTripleCommutator, hall_element_inv]
  simpa using
    element_lower_series
      ((Subgroup.lowerCentralSeries G 1).inv_mem hxy) hz

/-- Hall triple commutators are central in a group with `G₄=1`. -/
lemma commute_triple_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (g x y z : G) :
    Commute g (hallTripleCommutator x y z) :=
  commute_series_three hG4 g
    (triple_series_general x y z)

lemma element_triple_general
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) :
    ⁅a⁻¹, hallCommutator a b⁆ = hallTripleCommutator a b a := by
  let C := hallCommutator a b
  let T := hallTripleCommutator a b a
  have hCT : Commute C T :=
    commute_triple_three hG4 C a b a
  have hconj : a⁻¹ * C * a = C * T := by
    simp [C, T, hallTripleCommutator, hallCommutator, mul_assoc]
  rw [commutatorElement_def]
  simp only [inv_inv]
  change a⁻¹ * C * a * C⁻¹ = T
  rw [hconj, hCT.eq]
  group

lemma inv_triple_general
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) :
    ⁅b⁻¹, hallCommutator a b⁆ = hallTripleCommutator a b b := by
  let C := hallCommutator a b
  let T := hallTripleCommutator a b b
  have hCT : Commute C T :=
    commute_triple_three hG4 C a b b
  have hconj : b⁻¹ * C * b = C * T := by
    simp [C, T, hallTripleCommutator, hallCommutator, mul_assoc]
  rw [commutatorElement_def]
  simp only [inv_inv]
  change b⁻¹ * C * b * C⁻¹ = T
  rw [hconj, hCT.eq]
  group

/-- Struik's Lemma 2, equation (16), first formula, in exact class-three
form. -/
theorem first_class_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) (r s : ℤ) :
    hallCommutator (a ^ r) (b ^ s) =
      hallCommutator a b ^ (r * s) *
        hallTripleCommutator a b a ^ (s * Ring.choose r 2) *
          hallTripleCommutator a b b ^ (r * Ring.choose s 2) := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  let E := hallTripleCommutator a b b
  have hDC : Commute D C :=
    (commute_triple_three hG4 C a b a).symm
  have h :=
    commutator_zpow_three hG4 a⁻¹ b⁻¹ r s
  rw [← hall_element_inv] at h
  simp only [inv_zpow] at h
  rw [← hall_element_inv,
    element_triple_general hG4,
    inv_triple_general hG4] at h
  change
    hallCommutator (a ^ r) (b ^ s) =
      D ^ (Ring.choose r 2 * s) * C ^ (r * s) *
        E ^ (r * Ring.choose s 2) at h
  change
    hallCommutator (a ^ r) (b ^ s) =
      C ^ (r * s) * D ^ (s * Ring.choose r 2) *
        E ^ (r * Ring.choose s 2)
  calc
    hallCommutator (a ^ r) (b ^ s) =
        D ^ (Ring.choose r 2 * s) * C ^ (r * s) *
          E ^ (r * Ring.choose s 2) := h
    _ =
        D ^ (s * Ring.choose r 2) * C ^ (r * s) *
          E ^ (r * Ring.choose s 2) := by
            rw [mul_comm (Ring.choose r 2) s]
    _ =
        C ^ (r * s) * D ^ (s * Ring.choose r 2) *
          E ^ (r * Ring.choose s 2) := by
            rw [(hDC.zpow_zpow
              (s * Ring.choose r 2) (r * s)).eq]

/-- Struik's Lemma 2, equation (16), second formula, in exact class-three
form. -/
theorem second_class_three
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) (r s : ℤ) :
    hallCommutator (b ^ r) (a ^ s) =
      hallCommutator a b ^ (-(r * s)) *
        hallTripleCommutator a b a ^ (-(r * Ring.choose s 2)) *
          hallTripleCommutator a b b ^ (-(s * Ring.choose r 2)) := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  let E := hallTripleCommutator a b b
  have hCD : Commute C D :=
    commute_triple_three hG4 C a b a
  have hCE : Commute C E :=
    commute_triple_three hG4 C a b b
  have hDE : Commute D E :=
    commute_triple_three hG4 D a b b
  rw [commutator_swap_inv,
    first_class_three hG4 a b s r]
  change
    (C ^ (s * r) * D ^ (r * Ring.choose s 2) *
      E ^ (s * Ring.choose r 2))⁻¹ =
        C ^ (-(r * s)) * D ^ (-(r * Ring.choose s 2)) *
          E ^ (-(s * Ring.choose r 2))
  rw [mul_inv_rev, mul_inv_rev, ← zpow_neg, ← zpow_neg, ← zpow_neg]
  rw [mul_comm s r]
  calc
    E ^ (-(s * Ring.choose r 2)) *
          (D ^ (-(r * Ring.choose s 2)) * C ^ (-(r * s))) =
        (E ^ (-(s * Ring.choose r 2)) *
          D ^ (-(r * Ring.choose s 2))) * C ^ (-(r * s)) := by
            group
    _ =
        (D ^ (-(r * Ring.choose s 2)) *
          E ^ (-(s * Ring.choose r 2))) * C ^ (-(r * s)) := by
            rw [← (hDE.zpow_zpow
              (-(r * Ring.choose s 2))
              (-(s * Ring.choose r 2))).eq]
    _ =
        D ^ (-(r * Ring.choose s 2)) *
          (E ^ (-(s * Ring.choose r 2)) * C ^ (-(r * s))) := by
            group
    _ =
        D ^ (-(r * Ring.choose s 2)) *
          (C ^ (-(r * s)) * E ^ (-(s * Ring.choose r 2))) := by
            rw [← (hCE.zpow_zpow
              (-(r * s)) (-(s * Ring.choose r 2))).eq]
    _ =
        (D ^ (-(r * Ring.choose s 2)) * C ^ (-(r * s))) *
          E ^ (-(s * Ring.choose r 2)) := by
            group
    _ =
        (C ^ (-(r * s)) * D ^ (-(r * Ring.choose s 2))) *
          E ^ (-(s * Ring.choose r 2)) := by
            rw [← (hCD.zpow_zpow
              (-(r * s)) (-(r * Ring.choose s 2))).eq]

/-- Both formulas of Struik's Lemma 2. -/
theorem of_classThree
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) (r s : ℤ) :
    hallCommutator (a ^ r) (b ^ s) =
        hallCommutator a b ^ (r * s) *
          hallTripleCommutator a b a ^ (s * Ring.choose r 2) *
            hallTripleCommutator a b b ^ (r * Ring.choose s 2) ∧
      hallCommutator (b ^ r) (a ^ s) =
        hallCommutator a b ^ (-(r * s)) *
          hallTripleCommutator a b a ^ (-(r * Ring.choose s 2)) *
            hallTripleCommutator a b b ^ (-(s * Ring.choose r 2)) :=
  ⟨first_class_three hG4 a b r s,
    second_class_three hG4 a b r s⟩

/-- Struik (28), first formula. -/
theorem generalCollectionFirst
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) :
    hallCommutator (a ^ (2 : ℤ)) b =
      hallCommutator a b ^ (2 : ℤ) *
        hallTripleCommutator a b a := by
  have h22 : Ring.choose (2 : ℤ) 2 = 1 := by
    simpa using (Ring.choose_natCast (R := ℤ) 2 2)
  have h12 : Ring.choose (1 : ℤ) 2 = 0 := by
    simpa using (Ring.choose_natCast (R := ℤ) 1 2)
  simpa [h22, h12] using
    first_class_three hG4 a b 2 1

/-- Struik (28), second formula. -/
theorem generalCollectionSecond
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    (a b : G) :
    hallCommutator a (b ^ (2 : ℤ)) =
      hallCommutator a b ^ (2 : ℤ) *
        hallTripleCommutator a b b := by
  have h22 : Ring.choose (2 : ℤ) 2 = 1 := by
    simpa using (Ring.choose_natCast (R := ℤ) 2 2)
  have h12 : Ring.choose (1 : ℤ) 2 = 0 := by
    simpa using (Ring.choose_natCast (R := ℤ) 1 2)
  simpa [h22, h12] using
    first_class_three hG4 a b 1 2

/-- Struik (24): if `b²=1`, then
`1=(a,b)²((a,b),b)` in an arbitrary group. -/
theorem generalCollection
    (a b : G)
    (hb : b ^ (2 : ℤ) = 1) :
    1 =
      hallCommutator a b ^ (2 : ℤ) *
        hallTripleCommutator a b b := by
  have hbmul : b * b = 1 := by
    simpa [zpow_ofNat, pow_two] using hb
  have hbinv : b⁻¹ = b :=
    inv_eq_of_mul_eq_one_right hbmul
  let C := hallCommutator a b
  have hcollect :
      C ^ (2 : ℤ) * hallCommutator C b =
        (C * b) * (C * b) := by
    simp only [hallCommutator, zpow_ofNat, pow_two, hbinv]
    group
  have hCb : C * b = a⁻¹ * b * a := by
    simp [C, hallCommutator, hbinv, hbmul, mul_assoc]
  change 1 = C ^ (2 : ℤ) * hallCommutator C b
  rw [hcollect, hCb]
  symm
  calc
    (a⁻¹ * b * a) * (a⁻¹ * b * a) =
        a⁻¹ * (b * b) * a := by group
    _ = 1 := by rw [hbmul]; simp

end P1960
end Struik

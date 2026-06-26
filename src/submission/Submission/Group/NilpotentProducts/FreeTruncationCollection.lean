import Submission.Group.NilpotentProducts.CommutatorIdentities
import Submission.Group.Zassenhaus.ClassThreeCollection

/-!
# Struik (1960), class-three commutator collection

This file translates the signed class-three collection formulas already
available for mathlib's commutator convention into Hall's convention used
by Struik.
-/

namespace Struik
namespace P1960

open Submission
open Submission.Edmonton
open Submission.TCTex
open Submission.TCTex.HCThree
open scoped commutatorElement

universe u

section FreeLowerCentralTruncation

variable {d n : ℕ}

abbrev FreeTruncation :=
  LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n

/-- A Hall triple commutator belongs to the third one-based lower-central
layer (index `2` in mathlib's zero-based lower-central series). -/
lemma triple_series_two
    (x y z : FreeTruncation (d := d) (n := n)) :
    hallTripleCommutator x y z ∈
      Subgroup.lowerCentralSeries (FreeTruncation (d := d) (n := n)) 2 := by
  have hx :
      x⁻¹ ∈ Subgroup.lowerCentralSeries (FreeTruncation (d := d) (n := n)) 0 := by
    simp
  have hy :
      y⁻¹ ∈ Subgroup.lowerCentralSeries (FreeTruncation (d := d) (n := n)) 0 := by
    simp
  have hz :
      z⁻¹ ∈ Subgroup.lowerCentralSeries (FreeTruncation (d := d) (n := n)) 0 := by
    simp
  have hxy :
      hallCommutator x y ∈
        Subgroup.lowerCentralSeries (FreeTruncation (d := d) (n := n)) 1 := by
    rw [hall_element_inv]
    simpa using element_lower_series hx hy
  rw [hallTripleCommutator, hall_element_inv]
  simpa using
    element_lower_series
      ((Subgroup.lowerCentralSeries (FreeTruncation (d := d) (n := n)) 1).inv_mem hxy)
      hz

/-- At cutoff at most four, every Hall triple commutator is central. -/
lemma commute_commutator_four
    (hn4 : n ≤ 4)
    (g x y z : FreeTruncation (d := d) (n := n)) :
    Commute g (hallTripleCommutator x y z) :=
  commute_series_four
    hn4 g (triple_series_two x y z)

/-- Converting the first nested correction produced by mathlib's
commutator convention into Hall's left-normed triple commutator. -/
lemma commutator_element_triple
    (hn4 : n ≤ 4)
    (a b : FreeTruncation (d := d) (n := n)) :
    ⁅a⁻¹, hallCommutator a b⁆ = hallTripleCommutator a b a := by
  let C := hallCommutator a b
  let T := hallTripleCommutator a b a
  have hCT : Commute C T := by
    exact commute_commutator_four hn4 C a b a
  have hconj : a⁻¹ * C * a = C * T := by
    simp [C, T, hallTripleCommutator, hallCommutator, mul_assoc]
  rw [commutatorElement_def]
  simp only [inv_inv]
  change a⁻¹ * C * a * C⁻¹ = T
  rw [hconj, hCT.eq]
  group

/-- Converting the second nested correction produced by mathlib's
commutator convention into Hall's left-normed triple commutator. -/
lemma element_inv_triple
    (hn4 : n ≤ 4)
    (a b : FreeTruncation (d := d) (n := n)) :
    ⁅b⁻¹, hallCommutator a b⁆ = hallTripleCommutator a b b := by
  let C := hallCommutator a b
  let T := hallTripleCommutator a b b
  have hCT : Commute C T := by
    exact commute_commutator_four hn4 C a b b
  have hconj : b⁻¹ * C * b = C * T := by
    simp [C, T, hallTripleCommutator, hallCommutator, mul_assoc]
  rw [commutatorElement_def]
  simp only [inv_inv]
  change b⁻¹ * C * b * C⁻¹ = T
  rw [hconj, hCT.eq]
  group

/-- Struik's Lemma 2, equation (16), first formula, as an exact equality
in the free lower-central truncation with cutoff at most four. -/
theorem truncationCollectionFirst
    (hn4 : n ≤ 4)
    (a b : FreeTruncation (d := d) (n := n))
    (r s : ℤ) :
    hallCommutator (a ^ r) (b ^ s) =
      hallCommutator a b ^ (r * s) *
        hallTripleCommutator a b a ^ (s * Ring.choose r 2) *
          hallTripleCommutator a b b ^ (r * Ring.choose s 2) := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  let E := hallTripleCommutator a b b
  have hDC : Commute D C := by
    exact
      (commute_commutator_four hn4 C a b a).symm
  have h :=
    element_zpow_class
      hn4 a⁻¹ b⁻¹ r s
  rw [← hall_element_inv] at h
  simp only [inv_zpow] at h
  rw [← hall_element_inv,
    commutator_element_triple hn4,
    element_inv_triple hn4] at h
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

/-- Struik's Lemma 2, equation (16), second formula, as an exact equality
in the free lower-central truncation with cutoff at most four. -/
theorem truncationCollectionSecond
    (hn4 : n ≤ 4)
    (a b : FreeTruncation (d := d) (n := n))
    (r s : ℤ) :
    hallCommutator (b ^ r) (a ^ s) =
      hallCommutator a b ^ (-(r * s)) *
        hallTripleCommutator a b a ^ (-(r * Ring.choose s 2)) *
          hallTripleCommutator a b b ^ (-(s * Ring.choose r 2)) := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  let E := hallTripleCommutator a b b
  have hCD : Commute C D :=
    commute_commutator_four hn4 C a b a
  have hCE : Commute C E :=
    commute_commutator_four hn4 C a b b
  have hDE : Commute D E :=
    commute_commutator_four hn4 D a b b
  rw [commutator_swap_inv, truncationCollectionFirst hn4 a b s r]
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

end FreeLowerCentralTruncation

end P1960
end Struik

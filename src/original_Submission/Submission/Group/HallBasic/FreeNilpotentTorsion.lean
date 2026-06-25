import Submission.Group.HallBasic.NormalForm
import Submission.Group.LowerCentralStrong

/-!
# Unique roots in free nilpotent truncations

The standard Hall coordinates show directly that every natural power map on
`F_d / gamma_n(F_d)` is injective.  The proof advances the difference of two
putative roots through the lower-central series.  At each layer the difference
is central modulo the next layer, so equality of powers makes its leading Hall
coordinates vanish.
-/

namespace Struik

open Submission
open Submission.TCTex
open scoped commutatorElement

universe u

/-- Natural power maps are injective on every free lower-central truncation. -/
theorem free_truncation_injective
    (d n : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Function.Injective
      (fun x : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n =>
        x ^ q) := by
  intro x y hxy
  by_cases hn : 2 ≤ n
  · let N : Type u :=
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
    let xN : N := x
    let yN : N := y
    have hxyN : xN ^ q = yN ^ q := hxy
    let H := standardHallFamily.{u} d
    let hH :
        ∀ r : ℕ,
          1 ≤ r →
            r < n →
              (H r).FormsAssocGradedbasis (n := n) :=
      fun r hr hrn =>
        standard_forms_associated d n r (by omega) hrn
    let z : N := xN⁻¹ * yN
    have hzDepth :
        ∀ k : ℕ,
          k ≤ n - 1 →
            z ∈ Subgroup.lowerCentralSeries N k := by
      intro k hk
      induction k with
      | zero =>
          simp
      | succ k ih =>
          have hkPrev : k ≤ n - 1 := by omega
          have hkMem : z ∈ Subgroup.lowerCentralSeries N k := ih hkPrev
          have hkn : k + 1 < n := by omega
          let K : Subgroup N := Subgroup.lowerCentralSeries N (k + 1)
          letI : K.Normal := inferInstance
          have hcomm : ⁅xN, z⁆ ∈ K := by
            simpa [K] using
              (element_lower_series
                (show xN ∈ Subgroup.lowerCentralSeries N 0 by simp)
                hkMem)
          have hcollection :
              (xN * z) ^ q * (xN ^ q * z ^ q)⁻¹ ∈ K :=
            mul_inv_commutator
              K hcomm q
          have hxz : xN * z = yN := by
            dsimp [z]
            group
          rw [hxz, hxyN, mul_inv_quotient K] at hcollection
          have hzPowQuotient :
              QuotientGroup.mk' K (z ^ q) = 1 := by
            apply mul_left_cancel (a := QuotientGroup.mk' K (yN ^ q))
            simpa only [map_mul, mul_one] using hcollection.symm
          have hzPow : z ^ q ∈ K :=
            (QuotientGroup.eq_one_iff (N := K) (z ^ q)).mp hzPowQuotient
          have hpowCoordinates :=
            form_coordinates_series
              hn H hH (by omega) hkn z (by simpa using hkMem) q
          have hzCoordinates :
              normalFormCoordinates hn H hH z (k + 1) = 0 := by
            funext i
            have hpowZero :
                normalFormCoordinates hn H hH (z ^ q) (k + 1) i = 0 := by
              exact lower_central_series
                (r := k + 2) (s := k + 1)
                hn H hH (z ^ q) (by simpa [K] using hzPow)
                (by omega) (by omega) hkn i
            have hscaled :=
              congrFun hpowCoordinates i
            rw [hpowZero] at hscaled
            have hqInt : (q : ℤ) ≠ 0 := by exact_mod_cast hq
            exact mul_eq_zero.mp hscaled.symm |>.resolve_left hqInt
          have honeCoordinates :
              normalFormCoordinates hn H hH (1 : N) (k + 1) = 0 := by
            funext i
            exact coordinate_one_zero hn H hH (by omega) hkn i
          have hnext :=
            inv_form_coordinates
              hn H hH (by omega) hkn (1 : N) z
              (Subgroup.one_mem (Subgroup.lowerCentralSeries N k))
              (by simpa using hkMem)
              (honeCoordinates.trans hzCoordinates.symm)
          simpa using hnext
    have hzLast : z ∈ Subgroup.lowerCentralSeries N (n - 1) :=
      hzDepth (n - 1) le_rfl
    have hlast : Subgroup.lowerCentralSeries N (n - 1) = ⊥ := by
      simpa [N] using
        (lower_last_bot
          (G := FreeGroup (FreeGenerator.{u} d)) (c := n))
    rw [hlast] at hzLast
    have hzOne : z = 1 := hzLast
    have hxyEq : xN = yN :=
      inv_mul_eq_one.mp (by simpa [z] using hzOne)
    simpa [xN, yN] using hxyEq
  · have hn0 : n - 1 = 0 := by omega
    letI :
        Subsingleton
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
      change Subsingleton
        (FreeGroup (FreeGenerator.{u} d) ⧸
          Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d)) (n - 1))
      rw [hn0, Subgroup.lowerCentralSeries_zero]
      exact QuotientGroup.subsingleton_quotient_top
    exact Subsingleton.elim _ _

/-- Free lower-central truncations have unique roots. -/
instance free_truncation_torsion
    (d n : ℕ) :
    IsMulTorsionFree
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) where
  pow_left_injective q hq :=
    free_truncation_injective d n (q := q) hq

/-- Free lower-central truncations are nilpotent, including the degenerate cutoffs. -/
instance free_truncation_nilpotent
    (d n : ℕ) :
    Group.IsNilpotent
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨n - 1,
      lower_last_bot
        (G := FreeGroup (FreeGenerator.{u} d)) (c := n)⟩

end Struik

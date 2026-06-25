import Submission.Algebra.Magnus.MagnusHomogeneous


/-!
# Finite-alphabet integral converse for weighted Magnus ideals

This file proves the reverse inclusion in Efrat--Chapman, Theorem 4.3 for
a finite free basis, by successively removing the lowest nonzero
lower-central component.
-/

noncomputable section

namespace EChapma
namespace MSeries

open Submission
open Submission.TBluepr

variable {X : Type*} [Fintype X] [DecidableEq X] [Encodable X]

/-- The augmentation difference of a weight-`m` lower-central element,
packaged in `I^m`. -/
def lowerRepWeight
    {m : ℕ} (hm : 0 < m)
    {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)) :
    GroupAlgebra.augmentationPowerSubmodule
      ℤ (FreeGroup X) m := by
  refine ⟨MonoidAlgebra.of ℤ (FreeGroup X) g - 1, ?_⟩
  have hpower :=
    Submission.GShafar.lower_series_succ
      (R := ℤ) (G := FreeGroup X) (m - 1) hg
  simpa [GroupAlgebra.augmentationPower,
    ← GAWt.augmentation_ideal_algebra,
    Nat.sub_add_cancel hm] using hpower

/-- The class of a weight-`m` lower-central element in
`γ_m(F) / γ_(m+1)(F)`. -/
def lowerCentralWeight
    {m : ℕ}
    {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)) :
    Additive
      (LowerGradedLayer
        (FreeGroup X) (m - 1)) :=
  Additive.ofMul
    (QuotientGroup.mk'
      ((Subgroup.lowerCentralSeries (FreeGroup X) ((m - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)))
      ⟨g, hg⟩)

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- The fixed-weight Magnus map sends the class of `g` to the augmentation
layer represented by `g - 1`. -/
theorem free_magnus_class
    {m : ℕ} (hm : 0 < m)
    {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)) :
    Submission.HallTree.freeMagnusInt X hm
        (lowerCentralWeight hg) =
      Submodule.Quotient.mk
        (lowerRepWeight hm hg) := by
  unfold Submission.HallTree.freeMagnusInt
    lowerCentralWeight
  change
    GroupAlgebra.augmentationLayerReindex ℤ (FreeGroup X)
        (Nat.sub_add_cancel hm)
        (associatedGradedMagnus
          (FreeGroup X) (m - 1)
          (Additive.ofMul
            (QuotientGroup.mk'
              ((Subgroup.lowerCentralSeries (FreeGroup X) ((m - 1) + 1)).subgroupOf
                (Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)))
              ⟨g, hg⟩))) =
      Submodule.Quotient.mk
        (lowerRepWeight hm hg)
  rw [associated_graded_mk,
    GroupAlgebra.augmentation_reindex_mk]
  congr 1

omit [Fintype X] [DecidableEq X] in
/-- The fixed-weight integral Magnus map is injective at every positive
weight, in the paper's one-based indexing. -/
theorem free_magnus_injective
    [Finite X]
    {m : ℕ} (hm : 0 < m) :
    Function.Injective
      (Submission.HallTree.freeMagnusInt
        X hm) := by
  classical
  intro left right h
  apply
    IMagnus.associated_graded_injective
      (X := X) (m - 1)
  apply
    (GroupAlgebra.augmentationLayerReindex ℤ (FreeGroup X)
      (Nat.sub_add_cancel hm)).injective
  exact h

omit [Fintype X] [DecidableEq X] [Encodable X] in
/-- The group-algebra Magnus map sends the packaged augmentation difference
back to the actual Magnus difference series. -/
theorem magnus_rep_weight
    {m : ℕ} (hm : 0 < m)
    {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)) :
    GAWt.groupAlgebraMagnus
        (R := ℤ) (X := X)
        (lowerRepWeight hm hg :
          MonoidAlgebra ℤ (FreeGroup X)) =
      magnusDifference (R := ℤ) g := by
  change
    GAWt.groupAlgebraMagnus
        (R := ℤ) (X := X)
        (MonoidAlgebra.of ℤ (FreeGroup X) g - 1) =
      magnusDifference (R := ℤ) g
  rw [map_sub, map_one, GAWt.algebra_magnus]
  rfl

omit [Fintype X] [DecidableEq X] in
/-- One integral correction step in the proof of Theorem 4.3. An element in
`γ_m` with weighted Magnus difference can be multiplied by an allowed
`e(n,m)`th-power correction so that it enters `γ_(m+1)`. -/
theorem weighted_next_central
    [Finite X]
    (e : MDescen)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {g : FreeGroup X}
    (hg : g ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1))
    (hweighted :
      g ∈ magnusWeightedSubgroup (R := ℤ) (X := X) e n) :
    ∃ c : FreeGroup X,
      c ∈ weightedLowerProduct (X := X) e n ∧
        g * c ∈ Subgroup.lowerCentralSeries (FreeGroup X) m := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let a : GroupAlgebra.augmentationPowerSubmodule
      ℤ (FreeGroup X) m :=
    lowerRepWeight hm hg
  let q :
      Additive
        (LowerGradedLayer
          (FreeGroup X) (m - 1)) :=
    lowerCentralWeight hg
  let y : GroupAlgebra.augmentationLayer ℤ (FreeGroup X) m :=
    Submodule.Quotient.mk a
  have hqy :
      Submission.HallTree.freeMagnusInt X hm q =
        y := by
    simpa [a, q, y] using
      free_magnus_class
        (X := X) hm hg
  by_cases hyzero : y = 0
  · have hmkzero :
        (Submodule.Quotient.mk a :
          GroupAlgebra.augmentationLayer ℤ (FreeGroup X) m) =
            0 := by
      simpa [y] using hyzero
    have hadeep :
        (a : MonoidAlgebra ℤ (FreeGroup X)) ∈
          GroupAlgebra.augmentationPower ℤ (FreeGroup X) (m + 1) := by
      have hadeepSub :
          a ∈ GroupAlgebra.augmentationLayerDenom
            ℤ (FreeGroup X) m := by
        rw [← Submodule.Quotient.mk_eq_zero]
        exact hmkzero
      exact hadeepSub
    have haug :
        MonoidAlgebra.of ℤ (FreeGroup X) g - 1 ∈
          GroupAlgebra.augmentationIdeal ℤ (FreeGroup X) ^
            ((m - 1) + 2) := by
      have hexponent : m + 1 = (m - 1) + 2 := by omega
      rw [← hexponent]
      simpa [a, lowerRepWeight,
        GroupAlgebra.augmentationPower] using hadeep
    have hgdeep :
        g ∈ Subgroup.lowerCentralSeries (FreeGroup X) m := by
      simpa [Nat.sub_add_cancel hm] using
        (IMagnus.lower_series_pow
          (X := X) (m - 1) hg haug)
    exact ⟨1, Subgroup.one_mem _, by simpa using hgdeep⟩
  · let p : AssociativeHomogeneousWords ℤ X m :=
      (ICokern.homogeneousRealizationLinear
        (X := X) m).symm y
    have hpdiv :
        ∀ w : AssociativeWordsLength X m,
          (e n m : ℤ) ∣ p.1 w.1 := by
      intro w
      have hcoeff :
          (e n m : ℤ) ∣ magnusDifference (R := ℤ) g w.1 :=
        coefficient_dvd_weighted
          e hm hmn
          ((magnus_weighted_subgroup
            (R := ℤ) (X := X)).mp hweighted)
          w.2
      have hpcoeff :
          p.1 w.1 =
            GAWt.groupAlgebraMagnus
              (R := ℤ) (X := X)
              (a : MonoidAlgebra ℤ (FreeGroup X)) w.1 := by
        simpa [p, y] using
          (homogeneous_realization_magnus
            (X := X) m a w)
      rw [hpcoeff,
        magnus_rep_weight
          (X := X) hm hg]
      exact hcoeff
    obtain ⟨lambda, hpScalar⟩ :=
      homogeneous_smul_dvd
        (X := X) hpdiv
    let z : GroupAlgebra.augmentationLayer ℤ (FreeGroup X) m :=
      ICokern.homogeneousRealizationLinear
        (X := X) m lambda
    have hzScalar : (e n m : ℤ) • z = y := by
      calc
        (e n m : ℤ) • z =
            (e n m : ℤ) •
              ICokern.homogeneousRealizationLinear
                (X := X) m lambda := rfl
        _ =
            ICokern.homogeneousRealizationLinear
              (X := X) m ((e n m : ℤ) • lambda) := by
                rw [map_smul]
        _ =
            ICokern.homogeneousRealizationLinear
              (X := X) m p := by rw [← hpScalar]
        _ = y := by
          exact
            (ICokern.homogeneousRealizationLinear
              (X := X) m).apply_symm_apply y
    have heNonzero : (e n m : ℤ) ≠ 0 := by
      intro he
      apply hyzero
      calc
        y = (e n m : ℤ) • z := hzScalar.symm
        _ = 0 := by rw [he, zero_smul]
    have hzRange :
        (e n m : ℤ) • z ∈
          LinearMap.range
            (Submission.HallTree.freeMagnusInt
              X hm) := by
      rw [hzScalar]
      exact ⟨q, hqy⟩
    obtain ⟨qh, hqh⟩ :=
      ICokern.preimage_magnus_range
        (X := X) hm heNonzero hzRange
    let N :=
      (Subgroup.lowerCentralSeries (FreeGroup X) ((m - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup X) (m - 1))
    obtain ⟨xh, hxh⟩ :=
      QuotientGroup.mk'_surjective N qh.toMul
    let xg : Subgroup.lowerCentralSeries (FreeGroup X) (m - 1) := ⟨g, hg⟩
    have hqImage :
        Submission.HallTree.freeMagnusInt X hm q =
          Submission.HallTree.freeMagnusInt X hm
            ((e n m : ℤ) • qh) := by
      rw [hqy, map_smul, hqh, hzScalar]
    have hqeq : q = (e n m : ℤ) • qh :=
      free_magnus_injective
        (X := X) hm hqImage
    have hqeqNat : q = e n m • qh := by
      simpa only [Nat.cast_smul_eq_nsmul] using hqeq
    have hmul : q.toMul = qh.toMul ^ e n m := by
      simpa only [toMul_nsmul] using
        congrArg Additive.toMul hqeqNat
    have hmk :
        QuotientGroup.mk' N xg =
          (QuotientGroup.mk' N xh) ^ e n m := by
      change q.toMul = (QuotientGroup.mk' N xh) ^ e n m
      rw [hxh]
      exact hmul
    let corrected :
        Subgroup.lowerCentralSeries (FreeGroup X) (m - 1) :=
      xg * (xh ^ e n m)⁻¹
    have hcorrectedQuot :
        QuotientGroup.mk' N corrected = 1 := by
      change
        QuotientGroup.mk' N xg *
            (QuotientGroup.mk' N xh ^ e n m)⁻¹ =
          1
      rw [hmk]
      exact mul_inv_cancel _
    have hcorrectedN : corrected ∈ N :=
      (QuotientGroup.eq_one_iff corrected).mp hcorrectedQuot
    have hdeep :
        g * (((xh : Subgroup.lowerCentralSeries (FreeGroup X) (m - 1)) :
          FreeGroup X) ^ e n m)⁻¹ ∈
            Subgroup.lowerCentralSeries (FreeGroup X) m := by
      simpa [corrected, xg, N, Nat.sub_add_cancel hm] using hcorrectedN
    let h : FreeGroup X := xh
    have hh :
        h ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1) :=
      xh.property
    let c : FreeGroup X := (h ^ e n m)⁻¹
    have hcProduct :
        c ∈ weightedLowerProduct (X := X) e n := by
      apply Subgroup.inv_mem
      exact
        (le_iSup
          (fun i : {i : ℕ // 1 ≤ i ∧ i ≤ n} =>
            subgroupPower
              (Subgroup.lowerCentralSeries (FreeGroup X) (i.1 - 1))
              (e n i.1))
          ⟨m, hm, hmn⟩)
          (pow_subgroup_power
            (Subgroup.lowerCentralSeries (FreeGroup X) (m - 1))
            (e n m) hh)
    refine ⟨c, hcProduct, ?_⟩
    simpa [c, h] using hdeep

omit [Fintype X] [DecidableEq X] in
/-- Iterating the correction step through degree `m` produces a multiplier
from the weighted lower-central product whose product with `g` lies in
`γ_m`. -/
theorem weighted_multiplier_central
    [Finite X]
    (e : MDescen) (he : e.IsBinomial)
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n + 1)
    {g : FreeGroup X}
    (hweighted :
      g ∈ magnusWeightedSubgroup (R := ℤ) (X := X) e n) :
    ∃ k : FreeGroup X,
      k ∈ weightedLowerProduct (X := X) e n ∧
        g * k ∈ Subgroup.lowerCentralSeries (FreeGroup X) (m - 1) := by
  classical
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hmzero : m = 0
      · subst m
        exact ⟨1, Subgroup.one_mem _, by simp⟩
      · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmzero
        have hmle : m ≤ n := by omega
        obtain ⟨k, hkProduct, hgk⟩ :=
          ih hmpos (by omega)
        have hkWeighted :
            k ∈ magnusWeightedSubgroup
              (R := ℤ) (X := X) e n :=
          weighted_magnus_subgroup
            e he n hkProduct
        have hgkWeighted :
            g * k ∈ magnusWeightedSubgroup
              (R := ℤ) (X := X) e n :=
          Subgroup.mul_mem _ hweighted hkWeighted
        obtain ⟨c, hcProduct, hdeep⟩ :=
          weighted_next_central
            (X := X) e hmpos hmle hgk hgkWeighted
        refine
          ⟨k * c,
            Subgroup.mul_mem _ hkProduct hcProduct,
            ?_⟩
        change g * (k * c) ∈ Subgroup.lowerCentralSeries (FreeGroup X) m
        convert hdeep using 1
        exact (_root_.mul_assoc g k c).symm

omit [Fintype X] [DecidableEq X] in
/-- Finite-alphabet integral reverse inclusion in Efrat--Chapman,
Theorem 4.3. -/
theorem magnus_weighted_int
    [Finite X]
    (e : MDescen) (he : e.IsBinomial)
    {n : ℕ} (hn : 1 ≤ n) :
    magnusWeightedSubgroup (R := ℤ) (X := X) e n ≤
      weightedLowerProduct (X := X) e n := by
  classical
  intro g hg
  obtain ⟨k, hkProduct, hgkDeep⟩ :=
    weighted_multiplier_central
      (X := X) e he (m := n + 1) (by omega) le_rfl hg
  have hgkAtWeight :
      g * k ∈ Subgroup.lowerCentralSeries (FreeGroup X) (n - 1) :=
    Subgroup.lowerCentralSeries_antitone (by omega) hgkDeep
  have hfactor :
      subgroupPower
          (Subgroup.lowerCentralSeries (FreeGroup X) (n - 1))
          (e n n) ≤
        weightedLowerProduct (X := X) e n :=
    le_iSup
      (fun i : {i : ℕ // 1 ≤ i ∧ i ≤ n} =>
        subgroupPower
          (Subgroup.lowerCentralSeries (FreeGroup X) (i.1 - 1))
          (e n i.1))
      ⟨n, hn, le_rfl⟩
  rw [e.diagonal n hn, subgroupPower_one] at hfactor
  have hgkProduct :
      g * k ∈ weightedLowerProduct (X := X) e n :=
    hfactor hgkAtWeight
  have hcancel :=
    Subgroup.mul_mem
      (weightedLowerProduct (X := X) e n)
      hgkProduct
      (Subgroup.inv_mem
        (weightedLowerProduct (X := X) e n) hkProduct)
  simpa [mul_assoc] using hcancel

omit [Fintype X] [DecidableEq X] in
/-- Over the integers, the weighted lower-central product and the weighted
dimension subgroup are equal. -/
theorem weighted_dimension_int
    [Finite X]
    (e : MDescen) (he : e.IsBinomial)
    {n : ℕ} (hn : 1 ≤ n) :
    weightedLowerProduct (X := X) e n =
      GAWt.weightedDimensionSubgroup
        (R := ℤ) (X := X) e n := by
  classical
  apply le_antisymm
  · exact
      GAWt.weighted_dimension_subgroup
        e he n
  · exact
      (GAWt.weighted_subgroup_magnus
        (R := ℤ) (X := X) e n).trans
        (magnus_weighted_int
          (X := X) e he hn)

omit [Fintype X] [DecidableEq X] in
/-- Over the integers, the weighted dimension subgroup and the weighted
Magnus subgroup are equal. -/
theorem weighted_dimension_magnus
    [Finite X]
    (e : MDescen) (he : e.IsBinomial)
    {n : ℕ} (hn : 1 ≤ n) :
    GAWt.weightedDimensionSubgroup
        (R := ℤ) (X := X) e n =
      magnusWeightedSubgroup (R := ℤ) (X := X) e n := by
  classical
  apply le_antisymm
  · exact
      GAWt.weighted_subgroup_magnus
        (R := ℤ) (X := X) e n
  · exact
      (magnus_weighted_int
        (X := X) e he hn).trans
        (GAWt.weighted_dimension_subgroup
          e he n)

omit [Fintype X] [DecidableEq X] in
/-- Finite-alphabet form of Efrat--Chapman, Theorem 4.3, integral equality
between the first and third terms. -/
theorem weighted_magnus_int
    [Finite X]
    (e : MDescen) (he : e.IsBinomial)
    {n : ℕ} (hn : 1 ≤ n) :
    weightedLowerProduct (X := X) e n =
      magnusWeightedSubgroup (R := ℤ) (X := X) e n := by
  classical
  apply le_antisymm
  · exact
      weighted_magnus_subgroup
        e he n
  · exact
      magnus_weighted_int
        (X := X) e he hn

end MSeries
end EChapma

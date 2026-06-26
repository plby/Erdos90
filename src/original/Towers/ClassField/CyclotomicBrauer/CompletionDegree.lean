import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Lemma VII.7.3: ideal and completion local degrees

This file joins two existing descriptions of a finite local degree.  The
completion API identifies it with the cardinality of the decomposition
group, while ramification theory identifies that cardinality with `e * f`
for the centered upper prime.
-/

namespace Towers.CField.CBrauer

open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped Pointwise

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance completionDegreeRingOfIntegersGaloisAction :
    MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L)

/-- The degree of a chosen completed factor is the ramification index times
the inertia degree of the height-one prime centered at its absolute value. -/
theorem ramification_idx_deg
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk p).val) :
    let v := (FinitePlace.mk p).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial p⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist p
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion =
      p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
        p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) := by
  dsimp only
  let v := (FinitePlace.mk p).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist p
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  have hw : w.1.IsNontrivial :=
    absolute_extension_nontrivial v w
  have hna : IsNonarchimedean w.1 :=
    absolute_extension_nonarchimedean v w
  let P := nonarchimedeanHeightSpectrum w.1 hw hna
  letI : P.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_lies p w.1 w.2 hw hna
  letI : IsGaloisGroup Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) K L
  letI : p.asIdeal.IsMaximal := inferInstance
  letI : Field ((NumberField.RingOfIntegers K) ⧸ p.asIdeal) :=
    Ideal.Quotient.field p.asIdeal
  letI : P.asIdeal.IsMaximal := inferInstance
  letI : Field ((NumberField.RingOfIntegers L) ⧸ P.asIdeal) :=
    Ideal.Quotient.field P.asIdeal
  letI : Algebra.IsSeparable
      ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)
      ((NumberField.RingOfIntegers L) ⧸ P.asIdeal) := by
    letI : IsGalois
        ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)
        ((NumberField.RingOfIntegers L) ⧸ P.asIdeal) :=
      { __ := Ideal.Quotient.normal
          (A := NumberField.RingOfIntegers K) (G := Gal(L/K))
          p.asIdeal P.asIdeal }
    infer_instance
  calc
    Module.finrank v.Completion w.1.Completion =
        Nat.card (absoluteValueDecomposition v w.1) :=
      finrank_decomposition_card p w
    _ = Nat.card (MulAction.stabilizer Gal(L/K) P.asIdeal) := by
      rw [centered_stabilizer_decomposition v w.1 hw hna]
    _ = p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
        p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) :=
      Ideal.card_stabilizer_eq p.asIdeal p.ne_bot P.asIdeal

set_option synthInstance.maxHeartbeats 500000 in
-- The transitive place action transports dependent completion algebra structures.
/-- In a finite Galois extension, all completions above a fixed finite place
have the same degree.  This lets the compositum construction replace each
block's originally selected place by the restriction of one common upper
place. -/
theorem place_completion_finrank
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w z : CompletionPlacesAbove (L := L) (FinitePlace.mk p).val) :
    let v := (FinitePlace.mk p).val
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : Algebra v.Completion z.1.Completion :=
      (completionLies v z.1 z.2).toAlgebra
    Module.finrank v.Completion w.1.Completion =
      Module.finrank v.Completion z.1.Completion := by
  let v := (FinitePlace.mk p).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist p
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive p
  letI (q : CompletionPlacesAbove (L := L) v) :
      Algebra v.Completion q.1.Completion :=
    (completionLies v q.1 q.2).toAlgebra
  obtain ⟨sigma, hsigma⟩ :=
    MulAction.exists_smul_eq Gal(L/K) z w
  have hz : sigma⁻¹ • w = z := by
    calc
      sigma⁻¹ • w = sigma⁻¹ • (sigma • z) :=
        congrArg (fun y ↦ sigma⁻¹ • y) hsigma.symm
      _ = z := inv_smul_smul sigma z
  subst z
  exact (completionTransportAlg v sigma w).toLinearEquiv.finrank_eq.symm

/-- A completed local degree at any nonarchimedean place divides the global
degree of a finite Galois extension.  This is Lagrange's theorem after
identifying the local degree with the decomposition-group cardinality. -/
theorem finrank_dvd_global
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion ∣ Module.finrank K L := by
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    above_pretr_nonar v hvna
  rw [completion_decomposition_card]
  rw [← IsGalois.card_aut_eq_finrank K L]
  exact Subgroup.card_subgroup_dvd_card _

set_option synthInstance.maxHeartbeats 1000000 in
-- The three completion algebra structures form a large dependent telescope.
set_option maxHeartbeats 3000000 in
-- Elaborating the completion scalar tower requires normalizing all three maps.
omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Compatible places in a global field tower give the expected
factorization of completed local degrees.  The factor order is chosen to
match the numerical fixed-field lemmas: relative degree first, then the
degree of the fixed-field completion over the base completion. -/
theorem completion_finrank_tower
    (D : Type u) [Field D] [NumberField D]
    [Algebra K D] [Algebra D L] [IsScalarTower K D L]
    [FiniteDimensional K D] [IsGalois K D]
    [FiniteDimensional D L] [IsGalois D L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (u : AbsoluteValue D ℝ) (w : AbsoluteValue L ℝ)
    (huv : AbsoluteValue.LiesOver u v)
    (hwu : AbsoluteValue.LiesOver w u)
    (hwv : AbsoluteValue.LiesOver w v) :
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    letI : Algebra u.Completion w.Completion :=
      (completionLies u w hwu).toAlgebra
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    Module.finrank v.Completion w.Completion =
      Module.finrank u.Completion w.Completion *
        Module.finrank v.Completion u.Completion := by
  let uAbove : CompletionPlacesAbove (K := K) (L := D) v := ⟨u, huv⟩
  have hu : u.IsNontrivial :=
    absolute_extension_nontrivial v uAbove
  have huna : IsNonarchimedean u :=
    absolute_extension_nonarchimedean v uAbove
  letI : Fact u.IsNontrivial := ⟨hu⟩
  letI : IsUltrametricDist u.Completion :=
    absoluteUltrametricDist u huna
  let wAboveU : CompletionPlacesAbove (K := D) (L := L) u := ⟨w, hwu⟩
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra u.Completion w.Completion :=
    (completionLies u w hwu).toAlgebra
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : IsScalarTower v.Completion u.Completion w.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    simpa using (completion_lies_trans v u w huv hwu hwv).symm
  letI : FiniteDimensional v.Completion u.Completion :=
    placeCompletionDimensional v uAbove
  letI : FiniteDimensional u.Completion w.Completion :=
    placeCompletionDimensional u wAboveU
  letI : FiniteDimensional v.Completion w.Completion :=
    FiniteDimensional.trans v.Completion u.Completion w.Completion
  simpa only [Nat.mul_comm] using
    (Module.finrank_mul_finrank v.Completion u.Completion w.Completion).symm

set_option synthInstance.maxHeartbeats 1000000 in
-- The restricted place and three induced completion algebras are dependent.
set_option maxHeartbeats 3000000 in
-- Applying the completion-tower factorization normalizes the global tower.
omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Restricting an upper absolute value to the intermediate field produces
the compatible place and the local-degree factorization needed in the
prime-power fixed-field argument. -/
theorem finrank_tower
    (D : Type u) [Field D] [NumberField D]
    [Algebra K D] [Algebra D L] [IsScalarTower K D L]
    [FiniteDimensional K D] [IsGalois K D]
    [FiniteDimensional D L] [IsGalois D L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) :
    ∃ (u : AbsoluteValue D ℝ)
      (huv : AbsoluteValue.LiesOver u v)
      (hwu : AbsoluteValue.LiesOver w.1 u),
      letI : Algebra v.Completion u.Completion :=
        (completionLies v u huv).toAlgebra
      letI : Algebra u.Completion w.1.Completion :=
        (completionLies u w.1 hwu).toAlgebra
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      Module.finrank v.Completion w.1.Completion =
        Module.finrank u.Completion w.1.Completion *
          Module.finrank v.Completion u.Completion := by
  let u : AbsoluteValue D ℝ :=
    w.1.comp (algebraMap D L).injective
  let huv : AbsoluteValue.LiesOver u v := by
    constructor
    ext x
    change w.1 (algebraMap D L (algebraMap K D x)) = v x
    calc
      w.1 (algebraMap D L (algebraMap K D x)) =
          w.1 (algebraMap K L x) := by
        rw [IsScalarTower.algebraMap_apply K D L]
      _ = v x := DFunLike.congr_fun w.2.comp_eq x
  let hwu : AbsoluteValue.LiesOver w.1 u := by
    constructor
    rfl
  refine ⟨u, huv, hwu, ?_⟩
  exact completion_finrank_tower D v u w.1 huv hwu w.2

set_option synthInstance.maxHeartbeats 1000000 in
-- The three induced completion algebras form a dependent scalar tower.
set_option maxHeartbeats 3000000 in
omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- A local degree in an intermediate field divides the local degree at a
compatible upper place.  This is the form used to propagate every
prime-power block's selected local degree into the final compositum. -/
theorem finrank_dvd_tower
    (D : Type u) [Field D] [NumberField D]
    [Algebra K D] [Algebra D L] [IsScalarTower K D L]
    [FiniteDimensional K D] [IsGalois K D]
    [FiniteDimensional D L] [IsGalois D L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (u : AbsoluteValue D ℝ) (w : AbsoluteValue L ℝ)
    (huv : AbsoluteValue.LiesOver u v)
    (hwu : AbsoluteValue.LiesOver w u)
    (hwv : AbsoluteValue.LiesOver w v) :
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    letI : Algebra u.Completion w.Completion :=
      (completionLies u w hwu).toAlgebra
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    Module.finrank v.Completion u.Completion ∣
      Module.finrank v.Completion w.Completion := by
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra u.Completion w.Completion :=
    (completionLies u w hwu).toAlgebra
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  refine ⟨Module.finrank u.Completion w.Completion, ?_⟩
  rw [Nat.mul_comm]
  exact completion_finrank_tower D v u w huv hwu hwv

set_option synthInstance.maxHeartbeats 1000000 in
-- Restricting the upper place elaborates all completion maps simultaneously.
set_option maxHeartbeats 3000000 in
omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Every upper place restricts to an intermediate place whose local degree
divides the upper local degree. -/
theorem completion_finrank_dvd
    (D : Type u) [Field D] [NumberField D]
    [Algebra K D] [Algebra D L] [IsScalarTower K D L]
    [FiniteDimensional K D] [IsGalois K D]
    [FiniteDimensional D L] [IsGalois D L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) :
    ∃ (u : AbsoluteValue D ℝ)
      (huv : AbsoluteValue.LiesOver u v)
      (hwu : AbsoluteValue.LiesOver w.1 u),
      letI : Algebra v.Completion u.Completion :=
        (completionLies v u huv).toAlgebra
      letI : Algebra u.Completion w.1.Completion :=
        (completionLies u w.1 hwu).toAlgebra
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      Module.finrank v.Completion u.Completion ∣
        Module.finrank v.Completion w.1.Completion := by
  obtain ⟨u, huv, hwu, htower⟩ :=
    finrank_tower (L := L) D v w
  refine ⟨u, huv, hwu, ?_⟩
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra u.Completion w.1.Completion :=
    (completionLies u w.1 hwu).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  refine ⟨Module.finrank u.Completion w.1.Completion, ?_⟩
  rw [Nat.mul_comm]
  exact htower

end

end Towers.CField.CBrauer

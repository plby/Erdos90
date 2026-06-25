import Towers.ClassField.LocalBrauer.CanonicalUnramifiedFrobenius
import Towers.ClassField.LocalBrauer.CanonicalCarryInflation
import Towers.ClassField.LocalBrauer.ConcreteInflationComparison
import Towers.ClassField.LocalBrauer.SpectralIntegerTower

/-!
# Restriction of canonical arithmetic Frobenius

Arithmetic Frobenius on a larger canonical unramified level restricts to
arithmetic Frobenius on every smaller canonical level.  The proof compares
the two automorphisms after reduction and uses the inclusion of the spectral
integer rings in the field tower.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open IsLocalRing
open scoped NormedField Valued

attribute [local instance] Ideal.Quotient.field

local instance frobeniusRestrictionLevelDegree_neZero (r : ℕ) :
    NeZero (invariantLevelDegree r) :=
  ⟨(invariant_level_pos r).ne'⟩

private abbrev baseInteger
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] :=
  Valuation.integer (ValuativeRel.valuation K)

private theorem integer_discrete_valuation
    (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [Valuation.Compatible (NormedField.valuation (K := L))] :
    IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := L))) := by
  letI : IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation L)) :=
    discrete_valuation_ring L
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (valuativeIntegerNorm L)

private theorem dvr_local_hom
    (A B : Type u) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] [Algebra.IsIntegral A B] :
    IsLocalHom (algebraMap A B) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 4 0).mp
  exact ((IsLocalRing.maximal_ideal_unique A).unique
    (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal)
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (IsLocalRing.maximalIdeal B))).symm

set_option maxHeartbeats 2000000 in
-- Unfolding the three spectral integer embeddings is expensive.
private theorem spectral_tower_scalar
    (K F E : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field F] [Field E]
    [Algebra K F] [FiniteDimensional K F]
    [Algebra K E] [FiniteDimensional K E]
    [Algebra F E] [IsScalarTower K F E] :
    letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField F :=
      FLExt.nontriviallyNormedField K F
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let A := baseInteger K
    let B := Valuation.integer (NormedField.valuation (K := F))
    let C := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra A B := valuativeSpectralAlgebra K F
    letI : Algebra A C := valuativeSpectralAlgebra K E
    letI : Algebra B C :=
      spectralTowerAlgebra (K := K) (F := F) (E := E)
    IsScalarTower A B C := by
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  let A := baseInteger K
  let B := Valuation.integer (NormedField.valuation (K := F))
  let C := Valuation.integer (NormedField.valuation (K := E))
  letI : Algebra A B := valuativeSpectralAlgebra K F
  letI : Algebra A C := valuativeSpectralAlgebra K E
  letI : Algebra B C :=
    spectralTowerAlgebra (K := K) (F := F) (E := E)
  letI : IsScalarTower A B F :=
    valuativeSpectralTower K F
  letI : IsScalarTower A C E :=
    valuativeSpectralTower K E
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change algebraMap C E (algebraMap A C x) =
    algebraMap C E (algebraMap B C (algebraMap A B x))
  rw [← IsScalarTower.algebraMap_apply A C E]
  rw [show algebraMap B C =
    spectralIntegerTower (K := K) (F := F) (E := E) from rfl]
  change algebraMap A E x =
    ((spectralIntegerTower (K := K) (F := F) (E := E)
      (algebraMap A B x) : C) : E)
  rw [spectral_tower_coe]
  change algebraMap K E (x : K) =
    algebraMap F E (algebraMap K F (x : K))
  exact IsScalarTower.algebraMap_apply K F E (x : K)

/-- Naturality of Frobenius lifts when both Galois actions are obtained by
reduction and the top integral model contains the bottom one. -/
private theorem frobenius_restrict_top
    {A B C GB GC : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
    [IsLocalHom (algebraMap B C)]
    [Fintype (ResidueField A)]
    [Algebra.IsAlgebraic (ResidueField A) (ResidueField B)]
    [Algebra.IsAlgebraic (ResidueField A) (ResidueField C)]
    [Group GB] [Group GC]
    [MulSemiringAction GB B] [MulSemiringAction GC C]
    (res : GC →* GB)
    (eB : GB ≃* Gal(ResidueField B/ResidueField A))
    (eC : GC ≃* Gal(ResidueField C/ResidueField A))
    (hreduceB : ∀ (g : GB) (b : B),
      eB g (residue B b) = residue B (g • b))
    (hreduceC : ∀ (g : GC) (c : C),
      eC g (residue C c) = residue C (g • c))
    (haction : ∀ (g : GC) (b : B),
      algebraMap B C (res g • b) = g • algebraMap B C b) :
    res (eC.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ResidueField A) (ResidueField C))) =
      eB.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ResidueField A) (ResidueField B)) := by
  apply eB.injective
  rw [eB.apply_symm_apply]
  ext x
  obtain ⟨b, rfl⟩ := residue_surjective x
  apply (algebraMap (ResidueField B) (ResidueField C)).injective
  calc
    algebraMap (ResidueField B) (ResidueField C)
        (eB (res (eC.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ResidueField A) (ResidueField C)))) (residue B b)) =
        algebraMap (ResidueField B) (ResidueField C)
          (residue B
            (res (eC.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
              (ResidueField A) (ResidueField C))) • b)) := by
      rw [hreduceB]
    _ = residue C (algebraMap B C
          (res (eC.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
            (ResidueField A) (ResidueField C))) • b)) :=
      ResidueField.algebraMap_residue _
    _ = residue C
          ((eC.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
            (ResidueField A) (ResidueField C))) • algebraMap B C b) := by
      rw [haction]
    _ = eC (eC.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ResidueField A) (ResidueField C)))
          (residue C (algebraMap B C b)) := by
      rw [hreduceC]
    _ = FiniteField.frobeniusAlgEquivOfAlgebraic
          (ResidueField A) (ResidueField C)
          (residue C (algebraMap B C b)) := by
      rw [eC.apply_symm_apply]
    _ = FiniteField.frobeniusAlgEquivOfAlgebraic
          (ResidueField A) (ResidueField C)
          (algebraMap (ResidueField B) (ResidueField C) (residue B b)) := by
      rw [ResidueField.algebraMap_residue]
    _ = algebraMap (ResidueField B) (ResidueField C)
          (FiniteField.frobeniusAlgEquivOfAlgebraic
            (ResidueField A) (ResidueField B) (residue B b)) := by
      change (algebraMap (ResidueField B) (ResidueField C)
          (residue B b)) ^ Fintype.card (ResidueField A) =
        algebraMap (ResidueField B) (ResidueField C)
          ((residue B b) ^ Fintype.card (ResidueField A))
      exact (map_pow _ _ _).symm

set_option maxHeartbeats 6000000 in
-- The proof reinstalls both spectral local-field models and their actions.
set_option synthInstance.maxHeartbeats 100000 in
/-- Arithmetic Frobenius on a larger canonical unramified level restricts
to arithmetic Frobenius on every smaller canonical level. -/
theorem arithmetic_frobenius_restrict
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {n m : ℕ} [NeZero n] [NeZero m] (hnm : n ∣ m) :
    galoisRestrictionHom K
        (unramified_level K (NeZero.pos n) (NeZero.pos m) hnm)
        (canonicalArithmeticFrobenius K m) =
      canonicalArithmeticFrobenius K n := by
  let F := canonicalUnramifiedLevel K n
  let E := canonicalUnramifiedLevel K m
  let hFE : F ≤ E :=
    unramified_level K (NeZero.pos n) (NeZero.pos m) hnm
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  letI : Algebra F E :=
    RingHom.toAlgebra (IntermediateField.inclusion hFE)
  letI : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let A := baseInteger K
  let B := Valuation.integer (NormedField.valuation (K := F))
  let C := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing B :=
    integer_discrete_valuation F
  letI : IsDiscreteValuationRing C :=
    integer_discrete_valuation E
  letI : Algebra A B := valuativeSpectralAlgebra K F
  letI : Algebra A C := valuativeSpectralAlgebra K E
  letI : Algebra B C :=
    spectralTowerAlgebra (K := K) (F := F) (E := E)
  letI : IsScalarTower A B F :=
    (level_spectral_data K n).2.2.1
  letI : IsScalarTower A C E :=
    (level_spectral_data K m).2.2.1
  letI : IsScalarTower B C E :=
    spectralTowerScalar (K := K) (F := F) (E := E)
  letI : IsScalarTower A B C :=
    spectral_tower_scalar K F E
  letI : Module.Finite A B :=
    (level_spectral_data K n).1
  letI : Module.Finite A C :=
    (level_spectral_data K m).1
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  letI : IsLocalHom (algebraMap A B) := dvr_local_hom A B
  letI : IsLocalHom (algebraMap A C) := dvr_local_hom A C
  letI : Module.Finite B C :=
    Module.Finite.of_restrictScalars_finite A B C
  letI : Algebra.IsIntegral B C := Algebra.IsIntegral.of_finite B C
  letI : IsLocalHom (algebraMap B C) := dvr_local_hom B C
  letI : IsIntegralClosure B A F :=
    (level_spectral_data K n).2.2.2
  letI : IsIntegralClosure C A E :=
    (level_spectral_data K m).2.2.2
  letI : MulSemiringAction Gal(F/K) B :=
    IsIntegralClosure.MulSemiringAction A K F B
  letI : MulSemiringAction Gal(E/K) C :=
    IsIntegralClosure.MulSemiringAction A K E C
  letI : Finite (ResidueField A) := local_field_residue K
  letI : Fintype (ResidueField A) := Fintype.ofFinite _
  let res : Gal(E/K) →* Gal(F/K) := galoisRestrictionHom K hFE
  let eF : Gal(F/K) ≃* Gal(ResidueField B / ResidueField A) :=
    canonicalUnramifiedResidue K n
  let eE : Gal(E/K) ≃* Gal(ResidueField C / ResidueField A) :=
    canonicalUnramifiedResidue K m
  have hreduceF (g : Gal(F/K)) (y : B) :
      eF g (residue B y) = residue B (g • y) := by
    rfl
  have hreduceE (g : Gal(E/K)) (y : C) :
      eE g (residue C y) = residue C (g • y) := by
    rfl
  have haction (g : Gal(E/K)) (y : B) :
      algebraMap B C (res g • y) = g • algebraMap B C y := by
    apply Subtype.ext
    simp only [MulAction.compHom_smul_def]
    change algebraMap F E
        (algebraMap B F ((galRestrict A K F B (res g)) y)) =
      algebraMap C E ((galRestrict A K E C g) (algebraMap B C y))
    rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
    change algebraMap F E ((res g) (y : F)) =
      g (algebraMap F E (y : F))
    exact AlgEquiv.restrictNormal_commutes g F (y : F)
  have htop : canonicalArithmeticFrobenius K m =
      eE.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ResidueField A) (ResidueField C)) := by
    apply eE.injective
    rw [eE.apply_symm_apply]
    exact canonical_unramified_frobenius K m
  have hbottom : canonicalArithmeticFrobenius K n =
      eF.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ResidueField A) (ResidueField B)) := by
    apply eF.injective
    rw [eF.apply_symm_apply]
    exact canonical_unramified_frobenius K n
  rw [htop, hbottom]
  exact frobenius_restrict_top res eF eE hreduceF hreduceE haction

/-- Factorial-level form of `arithmetic_frobenius_restrict`. -/
theorem arithmetic_factorial_restriction
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {r s : ℕ} (h : r ≤ s) :
    factorialRestrictionHom K h
        (canonicalArithmeticFrobenius K (invariantLevelDegree s)) =
      canonicalArithmeticFrobenius K (invariantLevelDegree r) := by
  rw [← galois_restriction_factorial K h]
  exact arithmetic_frobenius_restrict K
    (invariant_level_dvd h)

/-- The Frobenius-normalized cyclic coordinate at each level of the
canonical factorial tower. -/
noncomputable def factorialZMod
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (r : ℕ) :
    Multiplicative (ZMod (invariantLevelDegree r)) ≃*
      Gal(unramifiedFactorialLevel K r/K) :=
  levelZMod K
    (invariantLevelDegree r)

@[simp]
theorem factorial_frobenius_z
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (r : ℕ) :
    factorialZMod K r
        (Multiplicative.ofAdd
          (1 : ZMod (invariantLevelDegree r))) =
      canonicalArithmeticFrobenius K (invariantLevelDegree r) :=
  level_frobenius_z K _

/-- Frobenius-normalized coordinates commute with restriction and reduction
throughout the canonical factorial tower. -/
theorem factorial_z_compatible
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    {r s : ℕ} (h : r ≤ s)
    (z : Multiplicative (ZMod (invariantLevelDegree s))) :
    factorialRestrictionHom K h
        (factorialZMod K s z) =
      factorialZMod K r
        (CCarry.indexReduction
          (invariant_level_dvd h) z) := by
  let oneS : Multiplicative (ZMod (invariantLevelDegree s)) :=
    Multiplicative.ofAdd 1
  have hz : z ∈ Subgroup.zpowers oneS := by
    refine ⟨(z.toAdd.val : ℤ), ?_⟩
    change oneS ^ (z.toAdd.val : ℤ) = z
    rw [zpow_natCast]
    apply Multiplicative.toAdd.injective
    simp [oneS]
  obtain ⟨i, hi⟩ := hz
  rw [← hi]
  simp only [map_zpow]
  rw [factorial_frobenius_z,
    arithmetic_factorial_restriction,
    ← factorial_frobenius_z K r]
  apply congrArg (fun x ↦ x ^ i)
  apply congrArg (factorialZMod K r)
  apply Multiplicative.toAdd.injective
  rw [CCarry.reduction_toAdd]
  exact (ZMod.cast_one (invariant_level_dvd h)).symm

end

end Towers.CField.LBrauer

import Submission.ClassField.LocalBrauer.CanonicalUnramifiedData

/-!
# Arithmetic Frobenius on the canonical unramified levels

The Hensel-lifted unramified model constructed in
`UnramifiedExtensionGalois` comes with the lift of residue-field arithmetic
Frobenius.  Its construction uses the equivalence between the Galois group
and the Galois group of the residue extension supplied by unramifiedness.
Here we transport that distinguished element to the canonical splitting
field `canonicalUnramifiedLevel K n`.

Unlike `galZMod`, the cyclic coordinate
defined below is normalized: the class of `1` maps to arithmetic Frobenius.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open Polynomial

open scoped NormedField Valued

attribute [local instance] Ideal.Quotient.field

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev A := Valuation.integer (ValuativeRel.valuation K)

private theorem integer_discrete_valuation
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Valuation.Compatible (NormedField.valuation (K := F))] :
    IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := F))) := by
  letI : IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation F)) :=
    discrete_valuation_ring F
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (valuativeIntegerNorm F)

set_option maxHeartbeats 1000000 in
-- Unpacking the dependent canonical local-data telescope is expensive.
@[implicit_reducible]
private noncomputable def canonical_integer_module
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    Module.Finite (A K) N :=
  (level_spectral_data K n).1

set_option maxHeartbeats 1000000 in
-- Unpacking the dependent canonical local-data telescope is expensive.
@[implicit_reducible]
private noncomputable def integer_formally_unramified
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    Algebra.FormallyUnramified (A K) N :=
  (level_spectral_data K n).2.1

set_option maxHeartbeats 1000000 in
-- Unpacking the dependent canonical local-data telescope is expensive.
@[implicit_reducible]
private noncomputable def canonical_scalar_tower
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    IsScalarTower (A K) N E :=
  (level_spectral_data K n).2.2.1

set_option maxHeartbeats 1000000 in
-- Unpacking the dependent canonical local-data telescope is expensive.
@[implicit_reducible]
private noncomputable def integer_integral_closure
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    IsIntegralClosure N (A K) E :=
  (level_spectral_data K n).2.2.2

set_option maxHeartbeats 1000000 in
-- This local-hom instance depends on the finite integral spectral model.
@[implicit_reducible]
private noncomputable def canonical_integer_hom
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : IsNonarchimedeanLocalField E :=
      FLExt.nonarchimedeanLocalField K E
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : IsDiscreteValuationRing (A K) :=
      discrete_valuation_ring K
    letI : IsDiscreteValuationRing N :=
      integer_discrete_valuation E
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    IsLocalHom (algebraMap (A K) N) := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing N :=
    integer_discrete_valuation E
  letI : Algebra (A K) N := valuativeSpectralAlgebra K E
  letI : Module.Finite (A K) N :=
    canonical_integer_module K n
  letI : Algebra.IsIntegral (A K) N :=
    Algebra.IsIntegral.of_finite (A K) N
  apply ((IsLocalRing.local_hom_TFAE (algebraMap (A K) N)).out 4 0).mp
  exact ((IsLocalRing.maximal_ideal_unique (A K)).unique
    (inferInstance : (IsLocalRing.maximalIdeal (A K)).IsMaximal)
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (IsLocalRing.maximalIdeal N))).symm

set_option maxHeartbeats 3000000 in
-- The spectral local-field and integral-closure instances form a deep tower.
set_option synthInstance.maxHeartbeats 100000 in
/-- Reduction identifies the Galois group of a canonical unramified level
with the Galois group of its spectral residue-field extension. -/
noncomputable def canonicalUnramifiedResidue
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      FLExt.nonarchimedeanLocalField K E
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    letI : IsLocalHom (algebraMap (A K) N) :=
      canonical_integer_hom K n
    Gal(E/K) ≃*
      Gal(IsLocalRing.ResidueField N / IsLocalRing.ResidueField (A K)) := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) := spectralValuationExtension K E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : IsFractionRing (A K) K :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
  letI : IsDiscreteValuationRing N :=
    integer_discrete_valuation E
  letI : IsFractionRing N E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : Algebra (A K) N := valuativeSpectralAlgebra K E
  letI : IsScalarTower (A K) N E :=
    canonical_scalar_tower K n
  letI : Module.Finite (A K) N :=
    canonical_integer_module K n
  letI : Algebra.FormallyUnramified (A K) N :=
    integer_formally_unramified K n
  letI : Algebra.IsIntegral (A K) N :=
    Algebra.IsIntegral.of_finite (A K) N
  letI : IsLocalHom (algebraMap (A K) N) :=
    canonical_integer_hom K n
  letI : (IsLocalRing.maximalIdeal N).LiesOver
      (IsLocalRing.maximalIdeal (A K)) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap (A K) N)).symm
  letI : Algebra.IsUnramifiedAt (A K)
      (IsLocalRing.maximalIdeal N) := by
    change Algebra.FormallyUnramified (A K)
      (Localization.AtPrime (IsLocalRing.maximalIdeal N))
    infer_instance
  letI : IsIntegralClosure N (A K) E :=
    integer_integral_closure K n
  letI : FaithfulSMul (A K) N :=
    (faithfulSMul_iff_algebraMap_injective (A K) N).2 <| by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap K E).injective
      simpa only [IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap N E) hxy
  let G := Gal(E/K)
  letI : MulSemiringAction G N :=
    IsIntegralClosure.MulSemiringAction (A K) K E N
  letI : IsGaloisGroup G (A K) N :=
    IsGaloisGroup.of_isFractionRing G (A K) N K E
  exact
    Submission.NumberTheory.Milne.galois_unramified_local
      (R := A K) (S := N) (G := G)
      (IsLocalRing.maximalIdeal (A K))
      (IsDiscreteValuationRing.not_a_field (A K))
      (IsDiscreteValuationRing.not_a_field N)

set_option maxHeartbeats 1000000 in
-- Constructing the residue extension requires the dependent spectral model.
set_option synthInstance.maxHeartbeats 100000 in
/-- Arithmetic Frobenius on the canonical degree-`n` unramified level.

It is the unique lift, under reduction, of finite-field arithmetic
Frobenius on the residue extension. -/
noncomputable def canonicalArithmeticFrobenius (n : ℕ) [NeZero n] :
    Gal(canonicalUnramifiedLevel K n/K) := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing N :=
    integer_discrete_valuation E
  letI : Algebra (A K) N := valuativeSpectralAlgebra K E
  letI : Module.Finite (A K) N :=
    canonical_integer_module K n
  letI : IsLocalHom (algebraMap (A K) N) :=
    canonical_integer_hom K n
  letI : Finite (IsLocalRing.ResidueField (A K)) :=
    local_field_residue K
  letI : Fintype (IsLocalRing.ResidueField (A K)) :=
    Fintype.ofFinite _
  letI : Module.Finite (IsLocalRing.ResidueField (A K))
      (IsLocalRing.ResidueField N) := inferInstance
  letI : Finite (IsLocalRing.ResidueField N) :=
    Module.finite_of_finite (IsLocalRing.ResidueField (A K))
  letI : Fintype (IsLocalRing.ResidueField N) :=
    Fintype.ofFinite _
  let residueFrobenius :
      Gal(IsLocalRing.ResidueField N / IsLocalRing.ResidueField (A K)) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic
      (IsLocalRing.ResidueField (A K)) (IsLocalRing.ResidueField N)
  exact (canonicalUnramifiedResidue K n).symm residueFrobenius

set_option maxHeartbeats 1000000 in
-- The statement reinstalls the dependent spectral residue-field model.
set_option synthInstance.maxHeartbeats 100000 in
/-- Arithmetic Frobenius is characterized by reducing to finite-field
Frobenius under the unramified Galois-group equivalence. -/
@[simp]
theorem canonical_unramified_frobenius
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : IsNonarchimedeanLocalField E :=
      FLExt.nonarchimedeanLocalField K E
    let N := Valuation.integer (NormedField.valuation (K := E))
    letI : IsDiscreteValuationRing (A K) :=
      discrete_valuation_ring K
    letI : IsDiscreteValuationRing N :=
      integer_discrete_valuation E
    letI : Algebra (A K) N := valuativeSpectralAlgebra K E
    letI : Module.Finite (A K) N :=
      canonical_integer_module K n
    letI : IsLocalHom (algebraMap (A K) N) :=
      canonical_integer_hom K n
    let k := IsLocalRing.ResidueField (A K)
    let l := IsLocalRing.ResidueField N
    letI : Finite k := local_field_residue K
    letI : Fintype k := Fintype.ofFinite k
    letI : Module.Finite k l := inferInstance
    letI : Finite l := Module.finite_of_finite k
    letI : Fintype l := Fintype.ofFinite l
    canonicalUnramifiedResidue K n
        (canonicalArithmeticFrobenius K n) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k l := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing N :=
    integer_discrete_valuation E
  letI : Algebra (A K) N := valuativeSpectralAlgebra K E
  letI : Module.Finite (A K) N :=
    canonical_integer_module K n
  letI : IsLocalHom (algebraMap (A K) N) :=
    canonical_integer_hom K n
  let k := IsLocalRing.ResidueField (A K)
  let l := IsLocalRing.ResidueField N
  letI : Finite k := local_field_residue K
  letI : Fintype k := Fintype.ofFinite k
  letI : Module.Finite k l := inferInstance
  letI : Finite l := Module.finite_of_finite k
  letI : Fintype l := Fintype.ofFinite l
  let e : Gal(E/K) ≃* Gal(l/k) :=
    canonicalUnramifiedResidue K n
  let residueFrobenius : Gal(l/k) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic k l
  change e (e.symm residueFrobenius) = residueFrobenius
  exact e.apply_symm_apply residueFrobenius

set_option maxHeartbeats 2000000 in
-- The proof reinstalls the canonical spectral integral model.
set_option synthInstance.maxHeartbeats 100000 in
/-- Arithmetic Frobenius on the degree-`n` canonical level has order `n`. -/
@[simp]
theorem order_arithmetic_frobenius (n : ℕ) [NeZero n] :
    orderOf (canonicalArithmeticFrobenius K n) = n := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : IsDiscreteValuationRing N :=
    integer_discrete_valuation E
  letI : Algebra (A K) N := valuativeSpectralAlgebra K E
  letI : Module.Finite (A K) N :=
    canonical_integer_module K n
  letI : IsLocalHom (algebraMap (A K) N) :=
    canonical_integer_hom K n
  let k := IsLocalRing.ResidueField (A K)
  let l := IsLocalRing.ResidueField N
  letI : Finite k := local_field_residue K
  letI : Fintype k := Fintype.ofFinite k
  letI : Module.Finite k l := inferInstance
  letI : Finite l := Module.finite_of_finite k
  letI : Fintype l := Fintype.ofFinite l
  let residueFrobenius : Gal(l/k) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic k l
  let e : Gal(E/K) ≃* Gal(l/k) :=
    canonicalUnramifiedResidue K n
  have hresidueGenerates (sigma : Gal(l/k)) :
      sigma ∈ Subgroup.zpowers residueFrobenius := by
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).surjective sigma
    refine ⟨(i.1 : ℤ), ?_⟩
    simpa [residueFrobenius] using hi
  have hresidueOrder : orderOf residueFrobenius = Nat.card Gal(l/k) :=
    orderOf_eq_card_of_forall_mem_zpowers hresidueGenerates
  have hcard : Nat.card Gal(E/K) = n := by
    rw [IsGalois.card_aut_eq_finrank,
      unramified_level_finrank K n]
  change orderOf (e.symm residueFrobenius) = n
  calc
    orderOf (e.symm residueFrobenius) = orderOf residueFrobenius :=
      e.symm.orderOf_eq residueFrobenius
    _ = Nat.card Gal(l/k) := hresidueOrder
    _ = Nat.card Gal(E/K) := Nat.card_congr e.symm.toEquiv
    _ = n := hcard

set_option maxHeartbeats 1000000 in
-- Cardinality elaboration for the canonical Galois group is expensive.
set_option synthInstance.maxHeartbeats 100000 in
/-- Every automorphism of the canonical unramified level is a power of
arithmetic Frobenius, with an exponent strictly smaller than the degree. -/
theorem canonical_arithmetic_frobenius
    (n : ℕ) [NeZero n]
    (sigma : Gal(canonicalUnramifiedLevel K n/K)) :
    ∃ i < n, canonicalArithmeticFrobenius K n ^ i = sigma := by
  let phi := canonicalArithmeticFrobenius K n
  have hcard : Nat.card Gal(canonicalUnramifiedLevel K n/K) = n := by
    rw [IsGalois.card_aut_eq_finrank,
      unramified_level_finrank K n]
  have hphiTop : Subgroup.zpowers phi = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, order_arithmetic_frobenius K n, hcard]
  obtain ⟨i, hi⟩ : sigma ∈ Subgroup.zpowers phi := by
    rw [hphiTop]
    exact Subgroup.mem_top sigma
  refine ⟨i.natMod n, Int.natMod_lt (NeZero.ne n), ?_⟩
  rw [← zpow_natCast, Int.natMod,
    Int.toNat_of_nonneg (Int.emod_nonneg _
      (Nat.cast_ne_zero.mpr (NeZero.ne n)))]
  change phi ^ (i % (n : ℤ)) = sigma
  have hncast : (n : ℤ) = orderOf phi := by
    exact_mod_cast (order_arithmetic_frobenius K n).symm
  rw [hncast]
  exact (zpow_mod_orderOf phi i).trans hi

/-- Arithmetic Frobenius generates the Galois group of the canonical
unramified level. -/
theorem zpowers_arithmetic_frobenius
    (n : ℕ) [NeZero n]
    (sigma : Gal(canonicalUnramifiedLevel K n/K)) :
    sigma ∈ Subgroup.zpowers (canonicalArithmeticFrobenius K n) := by
  obtain ⟨i, _hi, hphi⟩ :=
    canonical_arithmetic_frobenius K n sigma
  refine ⟨(i : ℤ), ?_⟩
  simpa using hphi

/-- The subgroup generated by arithmetic Frobenius is the full Galois
group. -/
@[simp]
theorem zpowers_canonical_arithmetic
    (n : ℕ) [NeZero n] :
    Subgroup.zpowers (canonicalArithmeticFrobenius K n) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  exact zpowers_arithmetic_frobenius K n

/-- The Frobenius-normalized cyclic coordinate on a canonical unramified
Galois group.  In particular, the class of `1` maps to arithmetic
Frobenius. -/
noncomputable def levelZMod
    (n : ℕ) [NeZero n] :
    Multiplicative (ZMod n) ≃*
      Gal(canonicalUnramifiedLevel K n/K) :=
  zmodMulEquivOfGenerator
    (zpowers_arithmetic_frobenius K n)
    (by
      rw [IsGalois.card_aut_eq_finrank,
        unramified_level_finrank K n])

/-- The Frobenius-normalized cyclic coordinate sends `1` to arithmetic
Frobenius. -/
@[simp]
theorem level_frobenius_z
    (n : ℕ) [NeZero n] :
    levelZMod K n
        (Multiplicative.ofAdd (1 : ZMod n)) =
      canonicalArithmeticFrobenius K n := by
  apply zmodMulEquivOfGenerator_apply_ofAdd_one

/-- In Frobenius-normalized coordinates, an integer class acts by the
corresponding power of arithmetic Frobenius. -/
@[simp]
theorem level_z_cast
    (n : ℕ) [NeZero n] (i : ℤ) :
    levelZMod K n
        (Multiplicative.ofAdd (i : ZMod n)) =
      canonicalArithmeticFrobenius K n ^ i := by
  apply zmodMulEquivOfGenerator_apply_ofAdd_intCast

/-- Arithmetic Frobenius has coordinate `1` in the Frobenius-normalized
cyclic presentation. -/
@[simp]
theorem level_z_symm
    (n : ℕ) [NeZero n] :
    (levelZMod K n).symm
        (canonicalArithmeticFrobenius K n) =
      Multiplicative.ofAdd (1 : ZMod n) := by
  apply zmodMulEquivOfGenerator_symm_apply_generator

end

end Submission.CField.LBrauer

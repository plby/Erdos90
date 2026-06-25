import Submission.NumberTheory.Locals.InertiaGaloisEquiv
import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition
import Submission.ClassField.LocalClass.PrincipalSolvability
import Submission.ClassField.LocalBrauer.FiniteLocalExtension
import Submission.ClassField.LocalBrauer.LocalField
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure

/-!
# Solvability of finite local Galois groups

This file supplies the arithmetic group-theoretic input used in Milne's
induction for Lemma III.2.6.  The extension field is given its canonical
spectral local-field structure.  Inertia is treated using the maximal
unramified integral subalgebra and the principal ramification characters;
the quotient is a cyclic finite-field Galois group.
-/

namespace Submission.CField.LClass

open IsLocalRing
open Submission.NumberTheory.Milne
open Submission.CField.LBrauer
open scoped NormedField Valued

noncomputable section

attribute [local instance] NormedField.toValued Ideal.Quotient.field

/-- The unconditional integral-generator form of Proposition 7.55.  This
uses the intrinsic Eisenstein theorem, which does not require the fraction
field of the base DVR to be perfect. -/
private theorem uniformizer_totally_ramified
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L]
    (htr : TotallyRamified A B (maximalIdeal A)) :
    ∃ Pi : B, Pi ≠ 0 ∧
      Algebra.adjoin A ({Pi} : Set B) = ⊤ ∧
      Ideal.span ({Pi} : Set B) = maximalIdeal B := by
  obtain ⟨Pi, hPi⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hPiInt : IsIntegral A Pi := Algebra.IsIntegral.isIntegral Pi
  have heis : (minpoly A Pi).IsEisensteinAt (maximalIdeal A) :=
    minpoly_eisenstein_ramified A B K L htr Pi hPi
  let piL : L := algebraMap B L Pi
  have hgen : IntermediateField.adjoin K ({piL} : Set L) = ⊤ :=
    fraction_weakly_eisenstein
      A B K L htr Pi hPi heis.isWeaklyEisensteinAt
  have hpiLInt : IsIntegral K piL := Algebra.IsIntegral.isIntegral piL
  have hgenAlg : Algebra.adjoin K ({piL} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic piL), hgen]
    rfl
  let powerBasis : PowerBasis K L := PowerBasis.ofAdjoinEqTop hpiLInt hgenAlg
  have hpowerBasisGen : powerBasis.gen = piL :=
    PowerBasis.ofAdjoinEqTop_gen hpiLInt hgenAlg
  have hpiLIntA : IsIntegral A piL :=
    hPiInt.map (IsScalarTower.toAlgHom A B L)
  have hpowerBasisInt : IsIntegral A powerBasis.gen := by
    simpa [hpowerBasisGen] using hpiLIntA
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hpq : maximalIdeal A = Ideal.span ({q} : Set A) :=
    hq.maximalIdeal_eq
  have hmin : minpoly A piL = minpoly A Pi :=
    minpoly.algebraMap_eq (IsFractionRing.injective B L) Pi
  have heisL : (minpoly A powerBasis.gen).IsEisensteinAt
      (Ideal.span ({q} : Set A)) := by
    simpa [hpowerBasisGen, hmin, ← hpq] using heis
  have hclosure : Algebra.adjoin A ({piL} : Set L) =
      integralClosure A L := by
    simpa [hpowerBasisGen] using
      adjoin_minpoly_eisenstein
        A K L powerBasis hpowerBasisInt hq heisL
  have hadjoin : Algebra.adjoin A ({Pi} : Set B) = ⊤ := by
    apply top_unique
    intro x _hx
    let f : B →ₐ[A] L := IsScalarTower.toAlgHom A B L
    have hxInt : IsIntegral A (f x) :=
      (Algebra.IsIntegral.isIntegral x).map f
    have hxClosure : f x ∈ integralClosure A L :=
      (mem_integralClosure_iff A L).2 hxInt
    have hxL : f x ∈ Algebra.adjoin A ({piL} : Set L) := by
      rw [hclosure]
      exact hxClosure
    have hxMap : f x ∈ (Algebra.adjoin A ({Pi} : Set B)).map f := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      exact hxL
    rw [Subalgebra.mem_map] at hxMap
    obtain ⟨y, hy, hxy⟩ := hxMap
    have hyx : y = x := (FaithfulSMul.algebraMap_injective B L) hxy
    simpa [hyx] using hy
  exact ⟨Pi, hPi.ne_zero, hadjoin, hPi.maximalIdeal_eq.symm⟩

section LocalField

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance localGaloisSolvableNormValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance localGaloisSolvableNormValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

set_option maxHeartbeats 1000000 in
-- Resolving the integral-model and intermediate-field scalar towers is expensive.
set_option synthInstance.maxHeartbeats 200000 in
-- The maximal unramified subalgebra creates several equivalent scalar actions.
/-- A finite Galois extension of a nonarchimedean local field has solvable
Galois group.  The topology and valuation on the abstract extension `L` are
the canonical spectral ones. -/
theorem local_galois_solvable
    : IsSolvable Gal(L/K) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) :=
    spectralValuationExtension K L
  let A := Valuation.integer (NormedField.valuation (K := K))
  let B := Valuation.integer (NormedField.valuation (K := L))
  letI : IsDiscreteValuationRing A := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation K)) :=
      discrete_valuation_ring K
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm K)
  letI : IsDiscreteValuationRing B := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation L)) :=
      discrete_valuation_ring L
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm L)
  letI : HenselianLocalRing A :=
    valued_henselian_ring K
  letI : HenselianLocalRing B :=
    valued_henselian_ring L
  letI : Algebra B L := B.subtype.toAlgebra
  letI : IsFractionRing A K :=
    (Valuation.integer.integers
      (NormedField.valuation (K := K))).isFractionRing
  letI : IsFractionRing B L :=
    (Valuation.integer.integers
      (NormedField.valuation (K := L))).isFractionRing
  letI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure B A L :=
    FLExt.spectral_integer_closure K L
  letI : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A L
  have hABinj : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    have hxyL := congrArg (algebraMap B L) hxy
    simpa only [IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A K L] using hxyL
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hABinj
  letI : Module.Finite A B := IsIntegralClosure.finite A K L B
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A B)
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  let G := Gal(L/K)
  letI : MulSemiringAction G B :=
    IsIntegralClosure.MulSemiringAction A K L B
  letI : SMulDistribClass G B L := inferInstance
  letI : IsGaloisGroup G A B :=
    IsGaloisGroup.of_isFractionRing G A B K L
  let p := maximalIdeal A
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  letI : Finite (ResidueField A) := by
    letI : Finite (ResidueField
        (Valuation.integer (ValuativeRel.valuation K))) :=
      local_field_residue K
    exact Finite.of_equiv
      (ResidueField (Valuation.integer (ValuativeRel.valuation K)))
      (ResidueField.mapEquiv (valuativeIntegerNorm K)).toEquiv
  letI : Fintype (ResidueField A) := Fintype.ofFinite _
  letI : Finite (ResidueField B) := by
    letI : Finite (ResidueField
        (Valuation.integer (ValuativeRel.valuation L))) :=
      local_field_residue L
    exact Finite.of_equiv
      (ResidueField (Valuation.integer (ValuativeRel.valuation L)))
      (ResidueField.mapEquiv (valuativeIntegerNorm L)).toEquiv
  letI : Fintype (ResidueField B) := Fintype.ofFinite _
  letI : Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
    infer_instance
  let I := (maximalIdeal B).inertia G
  letI hInormal : I.Normal :=
    maximal_inertia_normal (G := G) p hp
  let eQ : G ⧸ I ≃* Gal((B ⧸ maximalIdeal B)/(A ⧸ p)) :=
    inertiaResidueGalois (G := G) p hp
  have hcyclicQ : IsCyclic (G ⧸ I) := by
    apply eQ.isCyclic.mpr
    change IsCyclic Gal((ResidueField B)/(ResidueField A))
    infer_instance
  letI : IsCyclic (G ⧸ I) := hcyclicQ
  have hsolvableQ : IsSolvable (G ⧸ I) := inferInstance
  let U := maximalUnramifiedSubalgebra A B
  let F := fractionFieldSubalgebra A B K L U
  letI : Module.Finite A U := maximal_subalgebra_finite A B
  letI : Algebra.FormallyUnramified A U :=
    maximal_subalgebra_formally A B
  letI : IsLocalRing U := maximal_subalgebra_ring A B
  letI : IsDiscreteValuationRing U :=
    subalgebra_discrete_valuation A B
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hxy
  letI : Module.IsTorsionFree A U :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A U)
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  let algUF : Algebra U F :=
    fractionIntermediateSubalgebra A B K L U
  letI : SMul U F := algUF.toSMul
  letI : Algebra U F := algUF
  letI : IsFractionRing U F :=
    fraction_intermediate_subalgebra A B K L U
  letI : IsScalarTower A U B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.IsTorsionFree U B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      Subtype.val_injective
  letI : Module.Finite U B :=
    Module.Finite.of_restrictScalars_finite A U B
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.of_finite U B
  letI : IsLocalHom (algebraMap U B) :=
    Algebra.IsIntegral.isLocalHom U B
  let algUL : Algebra U L :=
    ((algebraMap F L).comp (algebraMap U F)).toAlgebra
  letI : SMul U L := algUL.toSMul
  letI : Algebra U L := algUL
  letI : IsScalarTower U F L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower U B L := IsScalarTower.of_algebraMap_eq' <| by
    ext u
    rfl
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' rfl
  have towerUFL : IsScalarTower U F L := by infer_instance
  have towerUBL : IsScalarTower U B L := by infer_instance
  have towerAUL : IsScalarTower A U L := by infer_instance
  letI : IsIntegralClosure B U L :=
    letI := towerAUL
    IsIntegralClosure.tower_top (R := A) (A := U) (B := L) (C := B)
  have htr : TotallyRamified U B (maximalIdeal U) :=
    subalgebra_totally_ramified A B F L
      (hUBL := towerUBL) (hUKUL := towerUFL)
  obtain ⟨Pi, hPi, hgen, hspan⟩ :=
    uniformizer_totally_ramified U B F L htr
  let H := Gal(L/F)
  letI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  letI : MulSemiringAction H B :=
    IsIntegralClosure.MulSemiringAction U F L B
  letI : SMulDistribClass H B L := inferInstance
  letI : IsGaloisGroup H U B :=
    IsGaloisGroup.of_isFractionRing H U B F L
  letI : FaithfulSMul H B := IsGaloisGroup.faithful U
  have hsolvableH : IsSolvable H := by
    apply solvable_ramification_characters
      (R := U) Pi hPi
      (by rw [hspan]; exact (inferInstance : (maximalIdeal B).IsPrime).ne_top)
      hgen (1 : H →* Multiplicative (ZMod 1))
    intro sigma _hsigma
    rw [hspan, ideal_ramification_uniformizer
      (maximalIdeal B) Pi hgen 0 sigma, pow_one]
    have hPiMem : Pi ∈ maximalIdeal B := by
      rw [← hspan]
      exact Ideal.subset_span (Set.mem_singleton Pi)
    have hsPiMem : sigma • Pi ∈ maximalIdeal B := by
      change (MulSemiringAction.toRingEquiv H B sigma) Pi ∈ maximalIdeal B
      rw [IsLocalRing.mem_maximalIdeal,
        map_mem_nonunits_iff (MulSemiringAction.toRingEquiv H B sigma),
        ← IsLocalRing.mem_maximalIdeal]
      exact hPiMem
    exact (maximalIdeal B).sub_mem hsPiMem hPiMem
  have hfixed : inertiaFixedField (K := K) (L := L) (maximalIdeal B) = F :=
    inertia_fraction_subalgebra
      (A := A) (B := B) (K := K) (L := L)
  change IntermediateField.fixedField I = F at hfixed
  let eI : I ≃* H := by
    change I ≃* Gal(L/F)
    exact hfixed ▸ IntermediateField.subgroupEquivAlgEquiv I
  have hsolvableI : IsSolvable I := by
    letI : IsSolvable H := hsolvableH
    exact solvable_of_solvable_injective
      (f := eI.toMonoidHom) eI.injective
  letI : IsSolvable I := hsolvableI
  letI : IsSolvable (G ⧸ I) := hsolvableQ
  apply solvable_of_ker_le_range I.subtype (QuotientGroup.mk' I)
  intro sigma hsigma
  have hsigmaI : sigma ∈ I := by
    simpa only [QuotientGroup.ker_mk'] using hsigma
  exact ⟨⟨sigma, hsigmaI⟩, rfl⟩

end LocalField

end

end Submission.CField.LClass

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Submission.ClassField.NormCorrespondence.SubgroupOpenClosed
import Submission.ClassField.UnramifiedCohom.CohomologicalReduction
import Submission.ClassField.LocalReciprocity.TateZeroQuotient
import Submission.ClassField.CrossedProducts.Multiplicative2Comparison
import Submission.ClassField.LocalBrauer.FiniteExtensionData
import Submission.ClassField.LocalBrauer.SpectralNormData
import Submission.ClassField.LocalBrauer.UnramifiedExtensionGalois
import Submission.ClassField.LocalBrauer.IntegralModelFrobenius
import Submission.ClassField.LocalBrauer.UnitH2
import Submission.NumberTheory.Locals.UnramifiedExtensions


/-!
# Milne, Class Field Theory, Proposition III.1.1

The unit group of a finite unramified extension of nonarchimedean local
fields is Tate-acyclic.  Unramifiedness is expressed by a finite formally
unramified integral-closure model, the same concrete formulation used by the
local-field part of the project.
-/

namespace Submission.CField.UCohom

noncomputable section

open CategoryTheory Representation groupCohomology
open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.LRecip
open Submission.CField.LBrauer
open Submission.CField.CProduca
open Submission.NumberTheory.Milne
open ValuativeRel

attribute [local instance] Ideal.Quotient.field
attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance] IsCyclic.commGroup

private abbrev A (K : Type) [NontriviallyNormedField K]
    [ValuativeRel K] := Valuation.integer (ValuativeRel.valuation K)

namespace FUExt

private abbrev normInteger (F : Type) [NormedField F]
    [IsUltrametricDist F] :=
  Valuation.integer (NormedField.valuation (K := F))

/-- The intrinsic unramifiedness condition for a finite local extension:
its spectral valuation integers are finite and formally unramified over the
base valuation integers. -/
def IsUnramified
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] : Prop :=
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  Module.Finite (normInteger K) (normInteger L) ∧
    Algebra.FormallyUnramified (normInteger K) (normInteger L)

/-- An intrinsically unramified finite extension of a nonarchimedean local
field is Galois.  This is derived from the formally unramified integral
model and the fact that finite residue-field extensions are Galois. -/
@[implicit_reducible]
noncomputable def galoisUnramified
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L]
    (hUnramified : IsUnramified K L) : IsGalois K L := by
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
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  let A0 := normInteger K
  let N := normInteger L
  change Module.Finite A0 N ∧
    Algebra.FormallyUnramified A0 N at hUnramified
  letI : Module.Finite A0 N := hUnramified.1
  letI : Algebra.FormallyUnramified A0 N := hUnramified.2
  let eA := valuativeIntegerNorm K
  letI : Algebra (A K) A0 := eA.toRingHom.toAlgebra
  letI : Algebra (A K) N := valuativeSpectralAlgebra K L
  letI : IsScalarTower (A K) A0 N :=
    ⟨fun x y z ↦ by
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      change _ = algebraMap A0 N (eA x) * _
      rfl⟩
  letI : IsScalarTower (A K) N L :=
    valuativeSpectralTower K L
  let eAAlg : A K ≃ₐ[A K] A0 :=
    AlgEquiv.ofRingEquiv (f := eA) (fun _ ↦ rfl)
  letI : Module.Finite (A K) A0 :=
    Module.Finite.equiv eAAlg.toLinearEquiv
  letI : Module.Finite (A K) N := Module.Finite.trans A0 N
  letI : Algebra.FormallyUnramified (A K) A0 :=
    Algebra.FormallyUnramified.of_equiv eAAlg
  letI : Algebra.FormallyUnramified (A K) N :=
    Algebra.FormallyUnramified.comp (A K) A0 N
  letI : IsIntegralClosure N (A K) L :=
    spectral_integer_valuative K L
  letI : IsDiscreteValuationRing (A K) :=
    discrete_valuation_ring K
  letI : HenselianLocalRing (A K) :=
    Submission.CField.LBrauer.integer_henselian_ring K
  letI : IsDomain N :=
    (IsIntegralClosure.algebraMap_injective N (A K) L).isDomain
      (algebraMap N L)
  letI : FaithfulSMul (A K) N :=
    (faithfulSMul_iff_algebraMap_injective (A K) N).mpr <| by
      intro x y hxy
      have h := congrArg (algebraMap N L) hxy
      simp_rw [← IsScalarTower.algebraMap_apply (A K) N L] at h
      simp_rw [IsScalarTower.algebraMap_apply (A K) K L] at h
      apply Subtype.ext
      exact (algebraMap K L).injective h
  letI : Module.IsTorsionFree (A K) N :=
    IsIntegralClosure.isTorsionFree (A K) L
  letI : Algebra.IsIntegral (A K) N :=
    IsIntegralClosure.isIntegral_algebra (A K) L
  letI : IsLocalHom (algebraMap (A K) N) := inferInstance
  letI : Module.Free (A K) N :=
    Module.free_of_finite_type_torsion_free'
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (A K)) (A K) :=
    Submission.CField.LBrauer.integer_adic_complete K
  letI : HenselianLocalRing N :=
    Submission.CField.LBrauer.henselian_formally_unramified
      (A K) N
  letI : Module.Finite (IsLocalRing.ResidueField (A K))
      (IsLocalRing.ResidueField N) := inferInstance
  letI : Finite (IsLocalRing.ResidueField (A K)) :=
    local_field_residue K
  letI : Finite (IsLocalRing.ResidueField N) :=
    Module.finite_of_finite (IsLocalRing.ResidueField (A K))
  letI : IsGalois (IsLocalRing.ResidueField (A K))
      (IsLocalRing.ResidueField N) := inferInstance
  letI : IsFractionRing N L :=
    IsIntegralClosure.isFractionRing_of_finite_extension (A K) K L N
  exact
    fraction_formally_residue
      (A K) N K L

variable (K L U : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
  [CommRing U] [Algebra (A K) U] [Algebra U L]
  [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
  [Module.Finite (A K) U] [Algebra.FormallyUnramified (A K) U]
  [IsLocalRing U]

include U

set_option maxHeartbeats 1500000 in
-- The residue-field Galois equivalence has a deeply dependent integral-model telescope.
set_option synthInstance.maxHeartbeats 200000 in
omit [IsLocalRing U] in
private theorem galois_cyclic :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    IsCyclic Gal(L/K) := by
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
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) :=
    FLExt.valuativeSpectralExtension K L
  let B := 𝒪[L]
  let G := Gal(L/K)
  let N := Valuation.integer (NormedField.valuation (K := L))
  letI : Algebra (A K) N :=
    valuativeSpectralAlgebra K L
  letI : IsScalarTower (A K) N L :=
    valuativeSpectralTower K L
  have hBL : B = N := valuative_integer_norm L
  let eBL : B ≃+* N := RingEquiv.subringCongr hBL
  let eBLAlg : B ≃ₐ[A K] N :=
    AlgEquiv.ofRingEquiv (f := eBL) (fun _ ↦ Subtype.ext rfl)
  letI : Module.Finite (A K) N :=
    spectral_module_model K L U
  letI : Algebra.FormallyUnramified (A K) N :=
    spectral_formally_model K L U
  letI : Module.Finite (A K) B :=
    Module.Finite.equiv eBLAlg.symm.toLinearEquiv
  letI : Algebra.FormallyUnramified (A K) B :=
    Algebra.FormallyUnramified.of_equiv eBLAlg.symm
  letI : IsIntegralClosure B (A K) L :=
    IsIntegralClosure.of_isIntegrallyClosed B (A K) L
  letI : MulSemiringAction G B :=
    FLExt.integerGaloisAction K L
  letI : Algebra.IsIntegral (A K) B :=
    IsIntegralClosure.isIntegral_algebra (A K) L
  letI : IsGaloisGroup G (A K) B :=
    IsGaloisGroup.of_isFractionRing G (A K) B K L
  letI : (IsLocalRing.maximalIdeal B).LiesOver
      (IsLocalRing.maximalIdeal (A K)) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap (A K) B)).symm
  letI : Algebra.IsUnramifiedAt (A K) (IsLocalRing.maximalIdeal B) := by
    change Algebra.FormallyUnramified (A K)
      (Localization.AtPrime (IsLocalRing.maximalIdeal B))
    infer_instance
  let kB := B ⧸ IsLocalRing.maximalIdeal B
  let kA := (A K) ⧸ IsLocalRing.maximalIdeal (A K)
  let e : G ≃* Gal(kB/kA) :=
    Submission.NumberTheory.Milne.galois_unramified_local
      (R := A K) (S := B) (G := G)
      (IsLocalRing.maximalIdeal (A K))
      (IsDiscreteValuationRing.not_a_field (A K))
      (IsDiscreteValuationRing.not_a_field B)
  haveI : Finite kB := by
    change Finite (IsLocalRing.ResidueField B)
    exact local_field_residue L
  have hcyclicResidue : IsCyclic Gal(kB/kA) := by
    infer_instance
  exact e.isCyclic.mpr hcyclicResidue

set_option maxHeartbeats 1500000 in
-- The unit-part correction unfolds both spectral order and integral Galois actions.
omit [IsGalois K L] in
private theorem integer_1_subsingleton :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : MulSemiringAction Gal(L/K) 𝒪[L] :=
      FLExt.integerGaloisAction K L
    Subsingleton
      (groupCohomology
        (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 1) := by
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
  letI : Algebra.IsIntegral (A K) U :=
    IsIntegralClosure.isIntegral_algebra (A K) L
  letI : FaithfulSMul (A K) U :=
    (faithfulSMul_iff_algebraMap_injective (A K) U).mpr <| by
      intro x y hxy
      have h := congrArg (algebraMap U L) hxy
      simp_rw [← IsScalarTower.algebraMap_apply (A K) U L] at h
      simp_rw [IsScalarTower.algebraMap_apply (A K) K L] at h
      apply Subtype.ext
      exact (algebraMap K L).injective h
  letI : IsLocalHom (algebraMap (A K) U) :=
    Algebra.IsIntegral.isLocalHom (A K) U
  letI : MulSemiringAction Gal(L/K) 𝒪[L] :=
    FLExt.integerGaloisAction K L
  constructor
  intro a b
  suffices hz : ∀ z : H1 (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ), z = 0 by
    exact (hz a).trans (hz b).symm
  intro z
  exact H1_induction_on z fun x ↦ (H1π_eq_zero_iff _).2 <| by
    let fU : Gal(L/K) → 𝒪[L]ˣ := Additive.toMul ∘ x
    have hfU : IsMulCocycle₁ fU :=
      isMulCocycle₁_of_mem_cocycles₁
        (G := Gal(L/K)) (M := 𝒪[L]ˣ) x x.2
    let j : 𝒪[L]ˣ →* Lˣ :=
      Units.map (Valuation.integer (ValuativeRel.valuation L)).subtype.toMonoidHom
    let fL : Gal(L/K) → Lˣ := fun g ↦ j (fU g)
    have hfL : IsMulCocycle₁ fL := by
      intro g h
      dsimp [fL]
      rw [hfU g h, map_mul]
      congr 1
      apply Units.ext
      exact algebraMap.coe_smul' (B := 𝒪[L]) (C := L) g (fU h)
    obtain ⟨beta, hbeta⟩ :=
      isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units fL hfL
    obtain ⟨tAdd, ht⟩ := local_order_surjective K
      (-localUnitOrder L (Additive.ofMul beta))
    let t : Kˣ := tAdd.toMul
    let q : Lˣ := Units.map (algebraMap K L).toMonoidHom t
    let alpha : Lˣ := q * beta
    have halphaOrder :
        localUnitOrder L (Additive.ofMul alpha) = 0 := by
      change localUnitOrder L
          (Additive.ofMul (q * beta)) = 0
      rw [show Additive.ofMul
          (q * beta) =
            Additive.ofMul q +
              Additive.ofMul beta by rfl,
        map_add,
        show localUnitOrder L (Additive.ofMul q) =
            localUnitOrder K (Additive.ofMul t) by
          exact algebra_integral_model K L U t]
      change localUnitOrder K tAdd +
          localUnitOrder L (Additive.ofMul beta) = 0
      rw [ht]
      exact neg_add_cancel _
    have halphaUnit : alpha ∈ localUnitSubgroup L := by
      rw [local_subgroup]
      apply le_antisymm
      · have hle : localUnitOrder L (0 : Additive Lˣ) ≤
            localUnitOrder L (Additive.ofMul alpha) := by
          simp [halphaOrder]
        have := (local_order_valuation L
          (1 : Lˣ) alpha).1 hle
        simpa using this
      · have hle : localUnitOrder L (Additive.ofMul alpha) ≤
            localUnitOrder L (0 : Additive Lˣ) := by
          simp [halphaOrder]
        have := (local_order_valuation L
          alpha (1 : Lˣ)).1 hle
        simpa using this
    let epsilon : 𝒪[L]ˣ :=
      localInteger L ⟨alpha, halphaUnit⟩
    refine (coboundariesOfIsMulCoboundary₁ ?_).2
    refine ⟨epsilon, fun g ↦ ?_⟩
    have hj : Function.Injective j := by
      intro p q hpq
      apply Units.ext
      apply Subtype.ext
      exact congrArg Units.val hpq
    have hj_smul (h : Gal(L/K)) (v : 𝒪[L]ˣ) :
        j (h • v) = h • j v := by
      apply Units.ext
      exact algebraMap.coe_smul' (B := 𝒪[L]) (C := L) h (v : 𝒪[L])
    apply hj
    rw [map_div, hj_smul]
    rw [show j epsilon = alpha by
      apply Units.ext
      rfl]
    have htfix : g • q = q := by
      apply Units.ext
      simp [q]
    have hgbeta : g • beta = fL g * beta := by
      calc
        g • beta = (g • beta / beta) * beta := by simp
        _ = fL g * beta := by rw [hbeta g]
    have halpha_smul : g • alpha = fL g * alpha := by
      calc
        g • alpha = g • (q * beta) := rfl
        _ = (g • q) * (g • beta) := by
          simp only [AlgEquiv.smul_units_def, map_mul]
        _ = q * (fL g * beta) := by rw [htfix, hgbeta]
        _ = fL g * (q * beta) := by ac_rfl
        _ = fL g * alpha := rfl
    rw [halpha_smul]
    simp only [mul_div_cancel_right]
    rfl

set_option maxHeartbeats 2000000 in
-- Combining the norm-data construction with both cohomology presentations is instance-heavy.
set_option synthInstance.maxHeartbeats 300000 in
/-- **Proposition III.1.1.** The unit group of a finite unramified local
extension is acyclic in every Tate degree.  The four clauses are the
project's concrete models for positive degrees, degrees zero and minus one,
and degrees below minus one. -/
theorem unramified_integer_acyclic :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : MulSemiringAction Gal(L/K) 𝒪[L] :=
      FLExt.integerGaloisAction K L
    let C := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    (∀ n : ℕ, 0 < n → Subsingleton (groupCohomology C n)) ∧
      Subsingleton (tateCohomologyZero C) ∧
      Subsingleton (tateCohomologyOne C) ∧
      ∀ n : ℕ, 0 < n → Subsingleton (groupHomology C n) := by
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
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) :=
    FLExt.valuativeSpectralExtension K L
  letI : Algebra.IsIntegral (A K) U :=
    IsIntegralClosure.isIntegral_algebra (A K) L
  letI : FaithfulSMul (A K) U :=
    (faithfulSMul_iff_algebraMap_injective (A K) U).mpr <| by
      intro x y hxy
      have h := congrArg (algebraMap U L) hxy
      simp_rw [← IsScalarTower.algebraMap_apply (A K) U L] at h
      simp_rw [IsScalarTower.algebraMap_apply (A K) K L] at h
      apply Subtype.ext
      exact (algebraMap K L).injective h
  letI : IsLocalHom (algebraMap (A K) U) :=
    Algebra.IsIntegral.isLocalHom (A K) U
  let B := 𝒪[L]
  let G := Gal(L/K)
  letI : MulSemiringAction G B :=
    FLExt.integerGaloisAction K L
  let C := Rep.ofMulDistribMulAction G Bˣ
  letI : IsCyclic G :=
    FUExt.galois_cyclic K L U
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have h1 : Subsingleton (groupCohomology C 1) :=
    FUExt.integer_1_subsingleton K L U
  obtain ⟨hResidueAlgebra, hUnitNorm⟩ :=
    FLExt.residue_unramified_model
      K L U
  letI := hResidueAlgebra
  have hLocalNorm :=
    FLExt.unramified_data_unit
      K L hResidueAlgebra hUnitNorm
  have hNorm : Function.Surjective
      (FLExt.integerUnitNorm K L) :=
    unramified_units_surjective K L
      (FLExt.integerUnitNorm K L) hLocalNorm
  let n := Nat.card G
  letI : NeZero n := ⟨(Nat.card_pos : 0 < Nat.card G).ne'⟩
  let eGal : Multiplicative (ZMod n) ≃* G :=
    zmodCyclicMulEquiv (G := G) (inferInstance : IsCyclic G)
  have hMulH2 : Subsingleton (MHTwo G Bˣ) :=
    integer_subsingleton_surjective
      K L n eGal hNorm
  let eH2 := multiplicativeHCohomology
    (G := G) (M := Bˣ)
  have h2 : Subsingleton (groupCohomology C 2) := by
    letI : Subsingleton (MHTwo G Bˣ) := hMulH2
    exact eH2.symm.injective.subsingleton
  exact tate_subsingleton_cyclic C g hg h1 h2

end FUExt

namespace FUExt

set_option maxHeartbeats 2500000 in
-- Transport from intrinsic spectral integers to the valuative integral model is instance-heavy.
set_option synthInstance.maxHeartbeats 300000 in
/-- Source-level form of Proposition III.1.1, with unramifiedness stated
intrinsically and no auxiliary integral model in the hypotheses. -/
theorem unramified_acyclic_valuative
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L]
    (hUnramified : IsUnramified K L) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : IsGalois K L :=
      galoisUnramified K L hUnramified
    letI : MulSemiringAction Gal(L/K) 𝒪[L] :=
      FLExt.integerGaloisAction K L
    let C := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    (∀ n : ℕ, 0 < n → Subsingleton (groupCohomology C n)) ∧
      Subsingleton (tateCohomologyZero C) ∧
      Subsingleton (tateCohomologyOne C) ∧
      ∀ n : ℕ, 0 < n → Subsingleton (groupHomology C n) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : IsGalois K L :=
    galoisUnramified K L hUnramified
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  let A0 := normInteger K
  let N := normInteger L
  change Module.Finite A0 N ∧
    Algebra.FormallyUnramified A0 N at hUnramified
  letI : Module.Finite A0 N := hUnramified.1
  letI : Algebra.FormallyUnramified A0 N := hUnramified.2
  let eA := valuativeIntegerNorm K
  letI : Algebra (A K) A0 := eA.toRingHom.toAlgebra
  letI : Algebra (A K) N := valuativeSpectralAlgebra K L
  letI : IsScalarTower (A K) A0 N :=
    ⟨fun x y z ↦ by
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      change _ = algebraMap A0 N (eA x) * _
      rfl⟩
  letI : IsScalarTower (A K) N L :=
    valuativeSpectralTower K L
  let eAAlg : A K ≃ₐ[A K] A0 :=
    AlgEquiv.ofRingEquiv (f := eA) (fun _ ↦ rfl)
  letI : Module.Finite (A K) A0 :=
    Module.Finite.equiv eAAlg.toLinearEquiv
  letI : Module.Finite (A K) N :=
    Module.Finite.trans A0 N
  letI : Algebra.FormallyUnramified (A K) A0 :=
    Algebra.FormallyUnramified.of_equiv eAAlg
  letI : Algebra.FormallyUnramified (A K) N :=
    Algebra.FormallyUnramified.comp (A K) A0 N
  letI : IsIntegralClosure N (A K) L :=
    spectral_integer_valuative K L
  exact unramified_integer_acyclic K L N

section CanonicalStatement

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance normIntegerValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance normIntegerValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [Module.Finite K L]

set_option maxHeartbeats 2500000 in
-- The wrapper elaborates the same deeply nested canonical integral models as the proved theorem.
set_option synthInstance.maxHeartbeats 300000 in
/-- **Proposition III.1.1.** The units of a finite unramified extension of
local fields are Tate-acyclic.  The valuation relation and its compatibility
are the canonical ones attached to the norm, so they are not hypotheses of
the source-facing statement. -/
theorem unramified_units_acyclic
    (hUnramified : IsUnramified K L) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : IsGalois K L :=
      galoisUnramified K L hUnramified
    letI : MulSemiringAction Gal(L/K) 𝒪[L] :=
      FLExt.integerGaloisAction K L
    let C := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    (∀ n : ℕ, 0 < n → Subsingleton (groupCohomology C n)) ∧
      Subsingleton (tateCohomologyZero C) ∧
      Subsingleton (tateCohomologyOne C) ∧
      ∀ n : ℕ, 0 < n → Subsingleton (groupHomology C n) :=
  unramified_acyclic_valuative K L hUnramified

end CanonicalStatement

end FUExt

end

end Submission.CField.UCohom

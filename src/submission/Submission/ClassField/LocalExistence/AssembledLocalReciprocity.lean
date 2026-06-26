import Submission.NumberTheory.Locals.ExtensionsFixedDegree
import Submission.ClassField.NormCorrespondence.CanonicalNormalization
import Submission.ClassField.NormCorrespondence.LocalUniqueness
import Submission.ClassField.LocalReciprocity.GlobalBrauer
import Submission.ClassField.LocalReciprocity.UnramifiedNormalization
import Submission.ClassField.LocalExistence.LocalExistence
import Submission.ClassField.LocalBrauer.CofinalityUnconditional

/-!
# The assembled finite Artin maps satisfy local reciprocity

The inverse-limit map assembled in Lemma III.3.3 already induces the finite
norm-residue equivalence at every abelian level.  The only remaining clause
of local reciprocity is its normalization on arbitrary unramified levels.
Every such level is the canonical unramified extension of the same degree,
so Lemma III.3.7 supplies that normalization.
-/

namespace Submission.CField.LExist

open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.NCorr
open Submission.CField.LRecip
open Submission.CField.LBrauer
open scoped NormedField

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance assembledReciprocityValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance assembledReciprocityCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

set_option maxHeartbeats 5000000 in
-- The spectral integer models for both presentations of the unramified
-- extension elaborate simultaneously.
set_option synthInstance.maxHeartbeats 500000 in
/-- Every finite unramified abelian subextension is the canonical unramified
subextension of the same degree. -/
theorem subextension_canonical_unramified
    (L : FASubext K) (hL : L.IsUnramified K) :
    letI : NeZero (Module.finrank K L.1) :=
      ⟨Module.finrank_pos.ne'⟩
    L = canonicalUnramifiedSubextension K (Module.finrank K L.1) := by
  let E := L.1
  let n := Module.finrank K E
  letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
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
  let A := Valuation.integer (ValuativeRel.valuation K)
  let A₀ := Valuation.integer (NormedField.valuation (K := K))
  let U := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing A := discrete_valuation_ring K
  letI : IsDiscreteValuationRing U := by
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm E)
  letI : Algebra A K := A.subtype.toAlgebra
  letI : IsFractionRing A K :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
  letI : Algebra U E := U.subtype.toAlgebra
  letI : IsFractionRing U E :=
    (Valuation.integer.integers (NormedField.valuation (K := E))).isFractionRing
  letI : Algebra A U := valuativeSpectralAlgebra K E
  letI : IsScalarTower A U E := valuativeSpectralTower K E
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  have hL' : Module.Finite A₀ U ∧ Algebra.FormallyUnramified A₀ U := by
    simpa [FASubext.IsUnramified, E, A₀, U] using hL
  letI : Module.Finite A₀ U := hL'.1
  letI : Algebra.FormallyUnramified A₀ U := hL'.2
  let eA : A ≃+* A₀ := valuativeIntegerNorm K
  letI : Algebra A A₀ := eA.toRingHom.toAlgebra
  let eAA₀ : A ≃ₐ[A] A₀ := AlgEquiv.ofRingEquiv (f := eA) (fun _ => rfl)
  letI : Module.Finite A A₀ := Module.Finite.equiv eAA₀.toLinearEquiv
  letI : Algebra.FormallyUnramified A A₀ :=
    Algebra.FormallyUnramified.of_equiv eAA₀
  letI : IsScalarTower A A₀ U := IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro a
    rfl
  letI : Module.Finite A U := Module.Finite.trans A₀ U
  letI : Algebra.FormallyUnramified A U :=
    Algebra.FormallyUnramified.comp A A₀ U
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  have hAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hAU : Function.Injective (algebraMap A U) := by
    intro x y hxy
    apply hAE
    rw [IsScalarTower.algebraMap_eq A U E]
    exact congrArg (algebraMap U E) hxy
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr hAU
  letI : Module.IsTorsionFree A U :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A U)
  letI : Module.Free A U := Module.free_of_finite_type_torsion_free'
  letI : IsLocalHom (algebraMap A U) := inferInstance
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    integer_adic_complete K
  letI : Finite (IsLocalRing.ResidueField A) :=
    local_field_residue K
  have hresidueCard :
      Nat.card (IsLocalRing.ResidueField A) = localResidueCard K := by
    rw [localResidueCard]
    exact Nat.card_congr
      (IsLocalRing.ResidueField.mapEquiv eA).toEquiv
  have hsplit : ((localFrobeniusPolynomial K n).map
      (algebraMap K E)).Splits := by
    simpa [localFrobeniusPolynomial, hresidueCard] using
      (splits_fraction_dvr
        A U K E n rfl)
  obtain ⟨e⟩ := alg_separable_splits
    K E n rfl hsplit
  let F : IntermediateField K (SeparableClosure K) :=
    canonicalUnramifiedLevel K n
  let j : F →ₐ[K] SeparableClosure K :=
    L.1.val.comp e.symm.toAlgHom
  have hjF : j.fieldRange = F := AlgHom.fieldRange_of_normal j
  have hjL : j.fieldRange = L.1 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      exact (e.symm y).property
    · intro x hx
      let xE : E := ⟨x, hx⟩
      refine AlgHom.mem_fieldRange.mpr ⟨e xE, ?_⟩
      change ((e.symm (e xE) : E) : SeparableClosure K) = x
      rw [e.symm_apply_apply]
  have heq :
      (canonicalUnramifiedLevel K n :
        IntermediateField K (SeparableClosure K)) = L.1 :=
    hjF.symm.trans hjL
  have hfinite : L.finiteIntermediateField =
      (canonicalUnramifiedSubextension K n).finiteIntermediateField :=
    FiniteGaloisIntermediateField.val_injective heq.symm
  cases L
  rw [FASubext.mk.injEq]
  exact hfinite

set_option maxHeartbeats 5000000 in
-- Rewriting an arbitrary unramified level through its canonical spectral
-- model unfolds the finite Artin equivalence and its Frobenius coordinate.
set_option synthInstance.maxHeartbeats 500000 in
/-- The inverse-limit assembly of the finite local Artin maps satisfies both
clauses of the local reciprocity law. -/
theorem assembled_artin_reciprocity :
    IsReciprocityMap K (assembledArtinHom K) := by
  constructor
  · intro pi hpi L hL
    let n := Module.finrank K L.1
    letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
    have hEq :=
      subextension_canonical_unramified K L hL
    rw [hEq]
    letI : IsMulCommutative Gal(canonicalUnramifiedLevel K n/K) :=
      (canonicalUnramifiedSubextension K n).isAbelian
    rw [restriction_assembled_all]
    have hmap :
        frobeniusNormalizedArtin K n =
          abelianLocalArtin K
            (canonicalUnramifiedLevel K n) :=
      frobenius_normalized_abelian
        K n
    have hvalue :
        abelianArtinHom K (canonicalUnramifiedLevel K n) pi =
          canonicalArithmeticFrobenius K n := by
      change abelianLocalArtin K
          (canonicalUnramifiedLevel K n)
          (QuotientGroup.mk' (normSubgroup K
            (canonicalUnramifiedLevel K n)) pi) = _
      rw [← hmap]
      exact frobenius_normalized_uniformizer K n pi
        ((Submission.CField.NCorr.local_element_order
          K pi).1 hpi)
    change (canonicalUnramifiedSubextension K n).IsArithmeticFrobenius K
      (abelianArtinHom K (canonicalUnramifiedLevel K n) pi)
    rw [hvalue]
    exact subextension_arithmetic_frobenius K n
  · exact induces_assembled_all K

/-- In characteristic zero, the assembled finite Artin map and Theorem
III.5.1 give the full local existence theorem. -/
theorem existence_theorem_assembled [CharZero K] :
    LocalExistenceTheorem K := by
  intro H
  constructor
  · exact existence_forward_reciprocity K
      (assembledArtinHom K)
      (induces_assembled_all K) H
  · exact localExistenceStatement K H

/-- **Theorem I.1.1 (Local Recip Law), in characteristic zero.** -/
theorem reciprocity_law_assembled [CharZero K] :
    LocalReciprocityLaw K := by
  let phi := assembledArtinHom K
  have hphi : IsReciprocityMap K phi :=
    assembled_artin_reciprocity K
  refine ⟨phi, hphi, ?_⟩
  intro psi hpsi
  exact (reciprocity_unique_existence K
    (existence_theorem_assembled K)
    phi psi hphi hpsi).symm

end

end Submission.CField.LExist

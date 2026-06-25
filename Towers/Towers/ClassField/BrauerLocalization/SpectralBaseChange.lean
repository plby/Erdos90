import Towers.ClassField.HerbrandQuotients.PermutationAssembly
import Towers.ClassField.NormIndex.CanonicalTateFormula
import Towers.ClassField.BrauerLocalization.FiniteCyclicCohomology
import Towers.ClassField.BrauerLocalization.IdeleIdealSupport
import Towers.ClassField.BrauerLocalization.RestrictedNegOne
import Towers.ClassField.Ideles.IdeleNorm

/-!
# Corollary VII.4.4 assembly for Theorem VIII.4.2

The Tate-zero/index comparison, Proposition VII.2.7, and Proposition VII.3.1
are unconditional. This file proves Corollary VII.4.4 and retains compatibility
wrappers for the earlier finite-spectral-base-change boundary.
-/

namespace Towers.CField.BLoc

open Towers.CField.HQuotie
open Towers.CField.LFTheory
open Towers.CField.NIndex
open Towers.CField.Recip
open Towers.CField.CIdeles
open Towers.CField.Ideles
open Towers.CField.CBrauer
open Towers.CField.RExist
open Towers.CField.GClass

universe u

/-- Corollary VII.4.4 now requires only finite spectral local base change and
the arithmetic lattices used in Proposition VII.3.1. -/
theorem spectral_assembly_lattices
    (hbaseChange : FiniteSpectralChange.{u})
    (hlattices : ArithmeticLatticesBridge.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          Module.finrank K L ≤
            (principalIdeles (NumberField.RingOfIntegers K) K ⊔
              ideleNormSubgroup (K := K) (L := L)).index) :=
  natHerbrandStatement
    (assembly_remaining_results
      (restricted_spectral_change hbaseChange)
      (permutation_assembly_lattices hlattices))
    tateIndexBridge

/-- **Corollary VII.4.4 (First Inequality).**  For a finite cyclic
extension, `[I_K : Kˣ Nm(I_L)] ≥ [L : K]`. -/
theorem firstInequality : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic Gal(L/K)],
      Module.finrank K L ≤
        (principalIdeles (NumberField.RingOfIntegers K) K ⊔
          ideleNormSubgroup (K := K) (L := L)).index) :=
  natHerbrandStatement
    ideleHerbrandQuotient tateIndexBridge

/-- After the unconditional proof of Proposition VII.3.1, finite spectral
local base change is the sole remaining input to Corollary VII.4.4. -/
theorem inequality_spectral_change
    (hbaseChange : FiniteSpectralChange.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          Module.finrank K L ≤
            (principalIdeles (NumberField.RingOfIntegers K) K ⊔
              ideleNormSubgroup (K := K) (L := L)).index) :=
  natHerbrandStatement
    (assembly_remaining_results
      (restricted_spectral_change hbaseChange)
      placesHerbrandFormula)
    tateIndexBridge

/-- The sharpest current VIII.4.2 assembly after discharging Lemmas VII.3.2,
VII.3.4, VII.3.5, and the Tate-zero/index comparison. -/
theorem assembly_lattices_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hlattices : ArithmeticLatticesBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  spectral_change_components
    h51 hArtin h81 h73 hbaseChange
      (spectral_assembly_lattices
        hbaseChange hlattices)

/-- The sharp VIII.4.2 boundary after Proposition VII.3.1: the former
arithmetic-lattice parameter has been discharged. -/
theorem spectral_assembly_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u}) :
    GlobalLocalizationSequence.{u} :=
  spectral_change_components
    h51 hArtin h81 h73 hbaseChange
      (inequality_spectral_change hbaseChange)

end Towers.CField.BLoc

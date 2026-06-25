import Submission.ClassField.BrauerLocalization.Injectivity
import Submission.ClassField.BrauerLocalization.SumSurjectivity

/-!
# Componentwise exactness assembly for CFT VIII.4.2

The construction of the canonical Brauer localization data, injectivity of
localization (conditional only on VII.5.1), and surjectivity of the invariant
sum are already available.  This file removes the remaining monolithic
exactness bridge by isolating its two genuine arithmetic obligations:

* global reciprocity: the invariant sum vanishes on localized global classes;
* kernel lifting: every local family with invariant sum zero is global.
-/

namespace Submission.CField.BLoc

open Submission.CField.BGroups
open Submission.CField.LFTheory
open Submission.CField.CProduca
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.CIdeles
open Submission.CField.RExist
open Submission.CField.GClass

noncomputable section

universe u

/-- The global reciprocity component of VIII.4.2, stated for the canonical
normalization carried by any `BData`. -/
def SumInvariantZero : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (x : Additive (BrauerGroup K)),
    BData.sumInvariant K data
        (data.localization.localization x) = 0

/-- The kernel-lifting component of VIII.4.2: a finite-support family of
local Brauer classes whose invariant sum is zero lies in the range of global
localization. -/
def KernelLifting : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v)))),
    BData.sumInvariant K data y = 0 →
      y ∈ Set.range data.localization.localization

/-- Vanishing of the composite and lifting of every kernel element are
exactly the two directions of `Function.Exact`. -/
theorem function_exact_lifting
    (hzero : SumInvariantZero.{u})
    (hlift : KernelLifting.{u})
    (K : Type u) [Field K] [NumberField K]
    (data : BData K) :
    Function.Exact data.localization.localization
      (BData.sumInvariant K data) := by
  intro y
  constructor
  · exact hlift K data y
  · rintro ⟨x, rfl⟩
    exact hzero K data x

/-- Theorem VII.8.1(b) implies the absolute invariant-sum formula.  As with
localization injectivity, choose one finite Galois subextension of the
separable closure splitting the given absolute Brauer class and apply the
relative statement there. -/
theorem global_fundamental_class
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
            InvariantSumReciprocity K data L))) :
    SumInvariantZero.{u} := by
  intro K _ _ data x
  obtain ⟨phi, hphi, _⟩ := hArtin K
  let beta : BrauerGroup K := x.toMul
  have hmem : beta ∈
      ⋃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
        relativeBrauerClasses K E := by
    rw [← brauer_i_classes K]
    trivial
  obtain ⟨E, hbeta⟩ := Set.mem_iUnion.1 hmem
  letI : NumberField E := NumberField.of_module_finite K E
  let z : relativeBrauerGroup K E := ⟨beta, hbeta⟩
  have hrelative := (h81 K phi data hphi).2 E z
  simpa [relativeLocalization, z, beta] using hrelative

/-- The full exactness bridge now follows from VII.5.1, global reciprocity,
and kernel lifting.  Injectivity and surjectivity are supplied by the
previously proved VIII.4.2 assembly modules. -/
theorem exactness_bridge_components
    (h51 : IdeleCohomologyClaims.{u})
    (hzero : SumInvariantZero.{u})
    (hlift : KernelLifting.{u}) :
    ExactnessBridge.{u} := by
  intro K _ _ data
  exact ⟨
    brauer_localization_cohomology h51 K data,
    function_exact_lifting
      hzero hlift K data,
    sumInvariant_surjective K data
  ⟩

/-- Componentwise route to Theorem VIII.4.2.  The Brauer data construction,
localization injectivity, and invariant-sum surjectivity no longer occur as
external bridge assumptions. -/
theorem exactness_assembly_components
    (h51 : IdeleCohomologyClaims.{u})
    (hzero : SumInvariantZero.{u})
    (hlift : KernelLifting.{u}) :
    GlobalLocalizationSequence.{u} :=
  global_localization_bridges
    brauerConstructionBridge
    (exactness_bridge_components h51 hzero hlift)

/-- Final assembly with the reciprocity component supplied directly by
Theorem VII.8.1 and existence of the global Artin map. -/
theorem exactness_assembly_lifting
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
    (hlift : KernelLifting.{u}) :
    GlobalLocalizationSequence.{u} :=
  exactness_assembly_components h51
    (global_fundamental_class hArtin h81) hlift

end

end Submission.CField.BLoc

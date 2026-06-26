import Towers.ClassField.ReciprocityExistence.CanonicalProduct
import Towers.ClassField.ReciprocityExistence.CupProductData
import Towers.ClassField.ReciprocityExistence.FinitePlaceFormula
import Towers.ClassField.ReciprocityExistence.InfinitePlaceFormula
import Towers.ClassField.Reciprocity.CompletionArtinHom
import Towers.ClassField.Reciprocity.RestrictedFactorFamily

/-!
# The canonical placewise Proposition III.3.6 package

The continuous global Artin map at a finite abelian layer is reconstructed
as the product of its one-place restrictions.  Its finite restrictions are
the normalized maps used in Proposition III.3.6, and its archimedean
restrictions are the unique completed Artin maps.  The finite and infinite
cup-coordinate theorems therefore supply the honest placewise package needed
for the right square of Lemma VII.8.5.
-/

namespace Towers.CField.RExist

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo
open Towers.CField.HNorm
open scoped IsMulCommutative

noncomputable section

universe u

noncomputable local instance placewiseNumberField
    {K : Type u} [Field K] [NumberField K]
    (E : FASubext K) : NumberField E.1 :=
  NumberField.of_module_finite K E.1

set_option maxHeartbeats 3000000 in
-- The reconstructed restricted product and both kinds of dependent local
-- coordinates elaborate in one structure literal.
set_option synthInstance.maxHeartbeats 1000000 in
-- The chosen finite completion is normalized against the literal prime factor.
set_option maxRecDepth 100000 in
/-- The continuous global Artin map supplies the canonically normalized
placewise Proposition III.3.6 data required by Theorem VII.8.1. -/
theorem placewiseCupBridge :
    PlacewiseCupBridge.{u} := by
  intro K _ _ E phi data hphi
  letI : NumberField E.1 := NumberField.of_module_finite K E.1
  let layerArtin :
      IdeleGroup (NumberField.RingOfIntegers K) K →* Gal(E.1/K) :=
    (localAbelianRestriction E).comp phi
  have hlayerContinuous : Continuous layerArtin :=
    (continuous_abelian_restriction E).comp hphi.1
  obtain ⟨D, hDartin, hDfinite, hDinfinite⟩ :=
    artin_product_continuous
      (K := K) (A := Gal(E.1/K)) layerArtin hlayerContinuous
  refine ⟨{
    artinProduct := D
    artin_eq := hDartin.symm
    finite_artin_eq := ?_
    finite_cup_eq := ?_
    infinite_formula := ?_ }⟩
  · intro P
    let completion := completionChoice K E.1
    let w := hasseChosenPlace completion (.inl P)
    let Q := placeUpperFactor
      (K := K) (L := E.1) P w
    obtain ⟨phiP, hphiP, hcoordinate⟩ := hphi.2.1 E P Q
    rcases hphiP with
      ⟨w', hw'v, hw'Q, localEquiv, hlocalFormula, hnormalized⟩
    have hphiPnormalized :
        phiP = (chosenCharacterFormulaData K E P).artin := by
      simpa [chosenCharacterFormulaData,
        characterFormulaData,
        adicArtinUniverse] using hnormalized w
    apply MonoidHom.ext
    intro x
    calc
      D.finite.localHom P x =
          layerArtin
            (finitePlaceEmbedding
              (NumberField.RingOfIntegers K) K P x) := hDfinite P x
      _ = phiP x := hcoordinate x
      _ = (chosenCharacterFormulaData K E P).artin x :=
        DFunLike.congr_fun hphiPnormalized x
  · intro chi a P
    exact finite_cup_invariant K E.1 data P a chi
  · intro chi a v
    let completion := completionChoice K E.1
    let w := completion.infiniteUpper v
    obtain ⟨phiV, hphiV, hcoordinate⟩ := hphi.2.2 E v w
    have hphiVcanonical :
        phiV = infiniteGlobalArtin v w :=
      infinite_global_artin
        E v w phiV hphiV
    have hDinfiniteCanonical :
        D.infinite v = infiniteGlobalArtin v w := by
      apply MonoidHom.ext
      intro x
      calc
        D.infinite v x =
            layerArtin
              (infinitePlaceEmbedding
                (NumberField.RingOfIntegers K) K v x) := hDinfinite v x
        _ = phiV x := hcoordinate x
        _ = infiniteGlobalArtin v w x :=
          DFunLike.congr_fun hphiVcanonical x
    calc
      data.placeInvariant.invariant (.inr v)
          (multiplicativeIdeleCup K E.1 chi
            (Additive.ofMul a) (.inr v)) =
        chi (Additive.ofMul
          (infiniteGlobalArtin v w
            (MulEquiv.piUnits a.1 v))) :=
              infinite_cup_invariant K E.1 data v a chi
      _ = chi (Additive.ofMul
          (D.infinite v (MulEquiv.piUnits a.1 v))) := by
        rw [hDinfiniteCanonical]

/-- With the canonical placewise Proposition III.3.6 package constructed,
the cyclotomic base case is the sole remaining input to Theorem VII.8.1. -/
theorem placewise_package_case
    (hbase : CyclotomicCaseBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)) :=
  cup_base_placewise
    hbase placewiseCupBridge

end

end Towers.CField.RExist

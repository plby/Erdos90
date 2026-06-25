import Towers.ClassField.ReciprocityExistence.CupNaturality
import Towers.ClassField.ReciprocityExistence.FieldSurjectivity
import Towers.ClassField.ReciprocityExistence.ArtinInvariantSum
import Towers.ClassField.ReciprocityExistence.PlaceFormula
import Towers.ClassField.ReciprocityExistence.Realization

/-!
# The canonical cup-product package for Theorem VII.8.1

The field cup, idèle cup, left-hand naturality square, and cyclic
surjectivity are now constructed unconditionally.  Thus construction of
`CupProductData` reduces exactly to the right-hand square, which is
the placewise character formula of Proposition III.3.6.
-/

namespace Towers.CField.RExist

open scoped IsMulCommutative
open IsDedekindDomain NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.HNorm

noncomputable section

universe u

noncomputable local instance cupProductDataNumberField
    {K : Type u} [Field K] [NumberField K]
    (E : FASubext K) : NumberField E.1 :=
  NumberField.of_module_finite K E.1

/-- The transported Proposition III.3.6 data at the same chosen upper
completion used by the idèle `H²` decomposition. -/
noncomputable def chosenCharacterFormulaData
    (K : Type u) [Field K] [NumberField K]
    (E : FASubext K)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharacterFormulaData K E.1 P :=
  characterFormulaData K E.1 P
    (hasseChosenPlace
      (completionChoice K E.1) (.inl P))

/-- The genuinely placewise input to the right square in Lemma VII.8.5.

The old bridge tried to obtain the conclusion below from
`ContinuousGlobalArtin` alone.  That predicate only says that each
finite coordinate is induced by *some* norm-quotient equivalence; it neither
identifies that equivalence with the cohomologically normalized Artin map of
Proposition III.3.6 nor says that the global map is the product of the chosen
coordinate maps.  Both facts are mathematically essential, so they are
recorded here, together with the finite- and infinite-place cup formulas. -/
structure PlacewiseCupData
    (K : Type u) [Field K] [NumberField K]
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K) where
  artinProduct : FAProduc K Gal(E.1/K)
  artin_eq :
    (localAbelianRestriction E).comp phi = artinProduct.artin
  finite_artin_eq : ∀ P,
    artinProduct.finite.localHom P =
      (chosenCharacterFormulaData K E P).artin
  finite_cup_eq : ∀ chi a P,
    data.placeInvariant.invariant (.inl P)
        (multiplicativeIdeleCup K E.1 chi
          (Additive.ofMul a) (.inl P)) =
      (chosenCharacterFormulaData K E P).cupInvariant
        (a.2.1 P) chi
  infinite_formula : ∀ chi a v,
    data.placeInvariant.invariant (.inr v)
        (multiplicativeIdeleCup K E.1 chi
          (Additive.ofMul a) (.inr v)) =
      chi (Additive.ofMul
        (artinProduct.infinite v (MulEquiv.piUnits a.1 v)))

/-- The remaining honest construction obligation for Theorem VII.8.1:
produce the canonically normalized placewise data.  Unlike the former local
comparison bridge, this does not conceal a false implication from an
arbitrary norm-quotient equivalence. -/
def PlacewiseCupBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K),
    ContinuousGlobalArtin phi →
      Nonempty (PlacewiseCupData K E phi data)

set_option maxHeartbeats 2000000 in
-- Elaborating the dependent direct-sum family and both place branches is expensive.
/-- The global right square follows from the canonical placewise formulas
and the finite-product calculation. -/
theorem multiplicative_cup_placewise
    {K : Type u} [Field K] [NumberField K]
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K)
    (hplace : PlacewiseCupData K E phi data) :
    CupInvariantComparison
      ((localAbelianRestriction E).comp phi)
      (multiplicativeIdeleCup K E.1)
      (BData.sumInvariant K data) := by
  classical
  letI : NumberField E.1 := NumberField.of_module_finite K E.1
  change CupInvariantComparison
    ((localAbelianRestriction E).comp phi)
    (multiplicativeIdeleCup K E.1)
    (DirectSum.toAddMonoid data.placeInvariant.invariant)
  intro chi a
  rw [hplace.artin_eq]
  exact direct_character_artin
    hplace.artinProduct chi a data.placeInvariant.invariant
    (multiplicativeIdeleCup K E.1 chi (Additive.ofMul a))
    (by
      intro P
      let localData := chosenCharacterFormulaData K E P
      calc
        data.placeInvariant.invariant (.inl P)
            (multiplicativeIdeleCup K E.1 chi
              (Additive.ofMul a) (.inl P)) =
            localData.cupInvariant (a.2.1 P) chi :=
          hplace.finite_cup_eq chi a P
        _ = chi (Additive.ofMul (localData.artin (a.2.1 P))) :=
          (localData.formula (a.2.1 P) chi).symm
        _ = chi (Additive.ofMul
            (hplace.artinProduct.finite.localHom P (a.2.1 P))) := by
          rw [hplace.finite_artin_eq P])
    (hplace.infinite_formula chi a)

/-- All other fields of the canonical cup-product package are discharged
by the literal multiplicative cup construction. -/
theorem cup_bridge_placewise
    (hplacewise : PlacewiseCupBridge.{u}) :
    CupDataBridge.{u} := by
  intro K _ _ E phi data hphi
  letI : NumberField E.1 := NumberField.of_module_finite K E.1
  obtain ⟨hplace⟩ := hplacewise K E phi data hphi
  refine ⟨
    { fieldCup := multiplicativeFieldCup K E.1
      ideleCup := multiplicativeIdeleCup K E.1
      naturality := global_multiplicative_naturality K E.1 data
      localInvariantComparison :=
        multiplicative_cup_placewise
          E phi data hplace
      cyclic_surjective := ?_ }⟩
  intro hcyclic
  letI : IsCyclic Gal(E.1/K) := hcyclic
  obtain ⟨chi, _, hsurjective⟩ :=
    multiplicative_cup_surjective K E.1
  exact ⟨chi, hsurjective⟩

/-- Theorem VII.8.1 now needs only its cyclotomic base case and the honestly
stated, canonically normalized placewise Proposition III.3.6 data. -/
theorem cup_base_placewise
    (hbase : CyclotomicCaseBridge.{u})
    (hplacewise : PlacewiseCupBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)) :=
  realization_remaining_bridges hbase
    (cup_bridge_placewise hplacewise)

end

end Towers.CField.RExist

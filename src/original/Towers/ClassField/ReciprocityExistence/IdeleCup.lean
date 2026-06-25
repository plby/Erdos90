import Towers.ClassField.ReciprocityExistence.MultiplicativeCup
import Towers.ClassField.NormIndex.IdeleExtensionMap
import Towers.ClassField.HasseNorm.LiftedH2
import Towers.ClassField.HasseNorm.HCompletionProduct
import Towers.ClassField.BrauerLocalization.H2Comparison
import Towers.ClassField.BrauerLocalization.BrauerKernelLifting

/-!
# The universe-polymorphic idèle cup map

The middle vertical arrow in Lemma VII.8.5 is constructed from the literal
multiplicative cocycle on `I_L`, then passed through the unconditional
idèle `H²` decomposition, the local crossed-product equivalences, and the
inclusions from local relative to local absolute Brauer groups.
-/

namespace Towers.CField.RExist

open CategoryTheory
open IsDedekindDomain NumberField
open Towers.CField.CProduca
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex
open Towers.CField.HNorm
open Towers.CField.BLoc
open groupCohomology
open scoped IsMulCommutative

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

private noncomputable abbrev ideleAction :
    IAData (K := K) (L := L) :=
  concreteActionData

local instance concreteIdeleMulAction :
    MulDistribMulAction Gal(L/K)
      (IdeleGroup (NumberField.RingOfIntegers L) L) :=
  (ideleAction K L).action

omit [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] in
/-- The extended base idèle is fixed by the concrete Galois action. -/
theorem global_multiplicative_fixed
    (a : IdeleGroup (NumberField.RingOfIntegers K) K) (g : Gal(L/K)) :
    g • ideleExtensionMonoid (K := K) (L := L) a =
      ideleExtensionMonoid (K := K) (L := L) a :=
  idele_monoid_fixed (K := K) (L := L) g a

/-- The multiplicative class of the literal idèle cup cocycle. -/
noncomputable def globalMultiplicativeClass
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    MHTwo Gal(L/K)
      (IdeleGroup (NumberField.RingOfIntegers L) L) :=
  invariantCharacterCup
    (ideleExtensionMonoid (K := K) (L := L) a)
    (global_multiplicative_fixed K L a) chi

omit [FiniteDimensional K L] in
@[simp]
theorem multiplicative_idele_cup
    (a b : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    globalMultiplicativeClass K L (a * b) chi =
      globalMultiplicativeClass K L a chi *
        globalMultiplicativeClass K L b chi := by
  rw [globalMultiplicativeClass,
    globalMultiplicativeClass,
    globalMultiplicativeClass,
    invariantCharacterCup, invariantCharacterCup,
    invariantCharacterCup, ← MHTwo.mk_mul]
  congr 1
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change (ideleExtensionMonoid (K := K) (L := L) (a * b)) ^
      rationalBoundaryExponent chi g h =
    (ideleExtensionMonoid (K := K) (L := L) a) ^
        rationalBoundaryExponent chi g h *
      (ideleExtensionMonoid (K := K) (L := L) b) ^
        rationalBoundaryExponent chi g h
  rw [map_mul, mul_zpow]

omit [FiniteDimensional K L] in
@[simp]
theorem global_idele_cup
    (chi : CharacterModule (Additive Gal(L/K))) :
    globalMultiplicativeClass K L 1 chi = 1 := by
  rw [globalMultiplicativeClass, invariantCharacterCup]
  change MHTwo.mk _ = MHTwo.mk 1
  congr 1
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change (ideleExtensionMonoid (K := K) (L := L) 1) ^
      rationalBoundaryExponent chi g h = 1
  rw [map_one, one_zpow]

/-- The direct multiplicative presentation and the resized concrete idèle
representation have identical carriers and actions. -/
noncomputable def multiplicativeIsoConcrete :
    uliftMulRepresentation
        (G := Gal(L/K))
        (M := IdeleGroup (NumberField.RingOfIntegers L) L) ≅
      resizedConcreteRepresentation K L := by
  apply Rep.mkIso
  refine
    { toLinearEquiv := LinearEquiv.refl (ULift.{u} ℤ)
        (Additive (IdeleGroup (NumberField.RingOfIntegers L) L))
      isIntertwining' := ?_ }
  intro g
  rfl

/-- The literal idèle cup class in the resized `H²` group used by the
unconditional completion-product decomposition. -/
noncomputable def globalMultiplicative2
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    H2 (resizedConcreteRepresentation K L) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
      (multiplicativeIsoConcrete K L)).hom
    ((multiplicativeUCohomology
      (G := Gal(L/K))
      (M := IdeleGroup (NumberField.RingOfIntegers L) L)
      (globalMultiplicativeClass K L a chi)).toAdd)

@[simp]
theorem global_multiplicative_idele
    (a b : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    globalMultiplicative2 K L (a * b) chi =
      globalMultiplicative2 K L a chi +
        globalMultiplicative2 K L b chi := by
  simp only [globalMultiplicative2,
    multiplicative_idele_cup, map_mul,
    toAdd_mul]
  exact map_add _ _ _

@[simp]
theorem global_multiplicative_h
    (chi : CharacterModule (Additive Gal(L/K))) :
    globalMultiplicative2 K L 1 chi = 0 := by
  simp only [globalMultiplicative2,
    global_idele_cup, map_one,
    toAdd_one]
  exact map_zero _

/-- The idèle cup as an additive map into resized idèle cohomology. -/
noncomputable def globalMultiplicativeCup
    (chi : CharacterModule (Additive Gal(L/K))) :
    Additive (IdeleGroup (NumberField.RingOfIntegers K) K) →+
      H2 (resizedConcreteRepresentation K L) where
  toFun a := globalMultiplicative2 K L a.toMul chi
  map_zero' := global_multiplicative_h K L chi
  map_add' a b := global_multiplicative_idele
    K L a.toMul b.toMul chi

/-- A fixed simultaneous choice of one upper completion at every place. -/
noncomputable def completionChoice :
    HasseCompletionData K L :=
  Classical.choice
    (hasseExistenceBridge K L)

set_option synthInstance.maxHeartbeats 300000 in
-- The direct sum of local Brauer groups carries a deeply nested coefficient action.
/-- The middle vertical arrow of Lemma VII.8.5, with the local relative
classes included into the absolute local Brauer groups. -/
noncomputable def multiplicativeIdeleCup
    (chi : CharacterModule (Additive Gal(L/K))) :
    Additive (IdeleGroup (NumberField.RingOfIntegers K) K) →+
      DirectSum (NumberFieldPlace K)
        (fun v => Additive
          (BrauerGroup (placeCompletion K v))) :=
  (brauerDirectInclusion K L
      (completionChoice K L)).comp
    ((directRelativeBrauer
        K L (completionChoice K L)).toAddMonoidHom.comp
      ((resizedHDecomposition
          (K := K) (L := L)).toAddMonoidHom.comp
        (globalMultiplicativeCup K L chi)))

end

end Towers.CField.RExist

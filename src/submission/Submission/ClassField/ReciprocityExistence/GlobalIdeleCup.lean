import Submission.ClassField.LocalReciprocity.CharacterBoundary
import Submission.ClassField.NormIndex.IdeleExtensionMap
import Submission.ClassField.CohomologyOps.Naturality

/-!
# The idèle-side cup product in Lemma VII.8.5

For a finite Galois extension `L/K`, a base idèle extends to a
Galois-invariant idèle of `L`.  Cupping that invariant with `δχ` constructs
the middle vertical map in Milne's diagram before the local `H²`
decomposition is applied.
-/

namespace Submission.CField.RExist

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory
open IsDedekindDomain NumberField
open Submission.CField.COps.CPBuild
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex

noncomputable section

variable (K L : Type) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private noncomputable abbrev ideleAction :
    IAData (K := K) (L := L) :=
  concreteActionData

private abbrev ideleRep := (ideleAction K L).representation

/-- A base idèle extended to a Galois-invariant idèle of `L`. -/
noncomputable def globalBaseInvariant
    (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    (ideleRep K L).ρ.invariants :=
  ⟨Additive.ofMul (ideleExtensionMonoid (K := K) (L := L) a), by
    intro sigma
    apply Additive.toMul.injective
    exact idele_monoid_fixed (K := K) (L := L) sigma a⟩

omit [FiniteDimensional K L] in
@[simp]
theorem global_base_invariant
    (a b : IdeleGroup (NumberField.RingOfIntegers K) K) :
    globalBaseInvariant K L (a * b) =
      globalBaseInvariant K L a + globalBaseInvariant K L b := by
  apply Subtype.ext
  change Additive.ofMul
      (ideleExtensionMonoid (K := K) (L := L) (a * b)) =
    Additive.ofMul
      (ideleExtensionMonoid (K := K) (L := L) a *
        ideleExtensionMonoid (K := K) (L := L) b)
  congr 1
  exact map_mul (ideleExtensionMonoid (K := K) (L := L)) a b

omit [FiniteDimensional K L] in
@[simp]
theorem global_base_idele :
    globalBaseInvariant K L 1 = 0 := by
  apply Subtype.ext
  change Additive.ofMul
      (ideleExtensionMonoid (K := K) (L := L) 1) = Additive.ofMul 1
  congr 1
  exact map_one (ideleExtensionMonoid (K := K) (L := L))

/-- A base idèle as a degree-zero cohomology class of the idèle
representation of `L`. -/
noncomputable def globalBase0
    (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    groupCohomology (ideleRep K L) 0 :=
  groupCohomology.π _ 0
    ((groupCohomology.cocyclesIso₀ (ideleRep K L)).inv
      (globalBaseInvariant K L a))

omit [FiniteDimensional K L] in
@[simp]
theorem global_base_0
    (a b : IdeleGroup (NumberField.RingOfIntegers K) K) :
    globalBase0 K L (a * b) =
      globalBase0 K L a + globalBase0 K L b := by
  simp only [globalBase0, global_base_invariant, map_add]

omit [FiniteDimensional K L] in
@[simp]
theorem global_h_0 : globalBase0 K L 1 = 0 := by
  simp only [globalBase0, global_base_idele, map_zero]

/-- The literal class `a ∪ δχ` in the degree-two cohomology of the idèle
representation. -/
noncomputable def globalCupBoundary
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : RationalCharacter Gal(L/K)) :
    groupCohomology.H2 (ideleRep K L) :=
  groupCohomology.map (MonoidHom.id Gal(L/K))
    (ρ_ (ideleRep K L)).hom 2
    (cupCohomology (ideleRep K L)
      (Rep.trivial ℤ Gal(L/K) ℤ) 0 2
      (globalBase0 K L a) (characterBoundary Gal(L/K) chi))

@[simp]
theorem global_cup_boundary
    (a b : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : RationalCharacter Gal(L/K)) :
    globalCupBoundary K L (a * b) chi =
      globalCupBoundary K L a chi +
        globalCupBoundary K L b chi := by
  simp only [globalCupBoundary, global_base_0,
    map_add, LinearMap.add_apply]

@[simp]
theorem global_character_boundary
    (chi : RationalCharacter Gal(L/K)) :
    globalCupBoundary K L 1 chi = 0 := by
  simp only [globalCupBoundary, global_h_0,
    map_zero, LinearMap.zero_apply]

/-- The idèle-side vertical arrow before decomposing idèle cohomology into
its local summands. -/
noncomputable def globalIdeleCup
    (chi : RationalCharacter Gal(L/K)) :
    Additive (IdeleGroup (NumberField.RingOfIntegers K) K) →+
      groupCohomology.H2 (ideleRep K L) where
  toFun a := globalCupBoundary K L a.toMul chi
  map_zero' := by
    rw [show (0 : Additive
      (IdeleGroup (NumberField.RingOfIntegers K) K)).toMul = 1 by rfl,
      global_character_boundary]
  map_add' a b := by
    rw [show (a + b).toMul = a.toMul * b.toMul by rfl,
      global_cup_boundary]

end

end Submission.CField.RExist

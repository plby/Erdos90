import Submission.ClassField.CohomologyOps.CastCompSymm
import Submission.ClassField.LocalReciprocity.CharacterBoundary
import Submission.ClassField.BrauerLocalization.Relative2Comparison

/-!
# The field-side cup product in Lemma VII.8.5

For a finite abelian Galois extension `L/K`, this file constructs the
vertical map on the left of Milne's cup-product diagram:

`a ↦ a ∪ δχ : Kˣ → H²(Gal(L/K), Lˣ) = Br(L/K)`.

Unlike the abstract diagram interface, the map here is the literal
categorical cup product followed by the already-proved relative
Brauer/`H²` equivalence.
-/

namespace Submission.CField.RExist

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory
open Submission.CField.COps.CPBuild
open Submission.CField.LRecip
open Submission.CField.BGroups
open Submission.CField.BLoc

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev globalUnitsRep := Rep.ofAlgebraAutOnUnits K L

/-- A base-field unit as a Galois-invariant unit of `L`. -/
noncomputable def globalUnitInvariant (a : Kˣ) :
    (globalUnitsRep K L).ρ.invariants :=
  ⟨Units.map (algebraMap K L) a, by
    intro sigma
    apply Units.ext
    exact sigma.commutes a⟩

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_base_mul (a b : Kˣ) :
    globalUnitInvariant K L (a * b) =
      globalUnitInvariant K L a + globalUnitInvariant K L b := by
  apply Subtype.ext
  let f : Kˣ →* Lˣ := Units.map (algebraMap K L)
  change Additive.ofMul (f (a * b)) = Additive.ofMul (f a * f b)
  congr 1
  exact f.map_mul a b

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_base_unit :
    globalUnitInvariant K L 1 = 0 := by
  apply Subtype.ext
  let f : Kˣ →* Lˣ := Units.map (algebraMap K L)
  change Additive.ofMul (f 1) = Additive.ofMul 1
  congr 1
  exact f.map_one

/-- A base-field unit as a degree-zero class with coefficients in `Lˣ`. -/
noncomputable def globalH0 (a : Kˣ) :
    groupCohomology (globalUnitsRep K L) 0 :=
  groupCohomology.π _ 0
    ((groupCohomology.cocyclesIso₀ (globalUnitsRep K L)).inv
      (globalUnitInvariant K L a))

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_0_mul (a b : Kˣ) :
    globalH0 K L (a * b) =
      globalH0 K L a + globalH0 K L b := by
  simp only [globalH0, global_base_mul, map_add]

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_0_one : globalH0 K L 1 = 0 := by
  simp only [globalH0, global_base_unit, map_zero]

/-- The literal class `a ∪ δχ` in `H²(Gal(L/K), Lˣ)`. -/
noncomputable def globalCharacterBoundary
    (a : Kˣ) (chi : RationalCharacter Gal(L/K)) :
    groupCohomology.H2 (globalUnitsRep K L) :=
  groupCohomology.map (MonoidHom.id Gal(L/K))
    (ρ_ (globalUnitsRep K L)).hom 2
    (cupCohomology (globalUnitsRep K L)
      (Rep.trivial ℤ Gal(L/K) ℤ) 0 2
      (globalH0 K L a) (characterBoundary Gal(L/K) chi))

omit [IsGalois K L] in
@[simp]
theorem global_cup_character
    (a b : Kˣ) (chi : RationalCharacter Gal(L/K)) :
    globalCharacterBoundary K L (a * b) chi =
      globalCharacterBoundary K L a chi +
        globalCharacterBoundary K L b chi := by
  simp only [globalCharacterBoundary, global_0_mul,
    map_add, LinearMap.add_apply]

omit [IsGalois K L] in
@[simp]
theorem cup_character_boundary
    (a : Kˣ) (chi psi : RationalCharacter Gal(L/K)) :
    globalCharacterBoundary K L a (chi + psi) =
      globalCharacterBoundary K L a chi +
        globalCharacterBoundary K L a psi := by
  simp only [globalCharacterBoundary, characterBoundary_add,
    map_add]

omit [IsGalois K L] in
@[simp]
theorem global_boundary_one
    (chi : RationalCharacter Gal(L/K)) :
    globalCharacterBoundary K L 1 chi = 0 := by
  simp only [globalCharacterBoundary, global_0_one,
    map_zero, LinearMap.zero_apply]

/-- The actual field-side vertical arrow in Lemma VII.8.5, with its target
identified with the relative Brauer group. -/
noncomputable def globalFieldCup
    (chi : RationalCharacter Gal(L/K)) :
    Additive Kˣ →+ Additive (relativeBrauerGroup K L) where
  toFun a := (relativeBrauerCohomology K L).symm
    (globalCharacterBoundary K L a.toMul chi)
  map_zero' := by
    rw [show (0 : Additive Kˣ).toMul = 1 by rfl,
      global_boundary_one, map_zero]
  map_add' a b := by
    rw [show (a + b).toMul = a.toMul * b.toMul by rfl,
      global_cup_character, map_add]

@[simp]
theorem global_field_cup
    (chi : RationalCharacter Gal(L/K)) (a : Additive Kˣ) :
    relativeBrauerCohomology K L
        (globalFieldCup K L chi a) =
      globalCharacterBoundary K L a.toMul chi := by
  exact (relativeBrauerCohomology K L).apply_symm_apply _

@[simp]
theorem global_cup_add
    (chi psi : RationalCharacter Gal(L/K)) :
    globalFieldCup K L (chi + psi) =
      globalFieldCup K L chi + globalFieldCup K L psi := by
  apply AddMonoidHom.ext
  intro a
  apply (relativeBrauerCohomology K L).injective
  simp only [AddMonoidHom.add_apply, global_field_cup,
    cup_character_boundary, map_add]

end

end Submission.CField.RExist

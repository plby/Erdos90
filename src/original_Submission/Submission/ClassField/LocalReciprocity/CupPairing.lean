import Submission.ClassField.CohomologyOps.CastCompSymm
import Submission.ClassField.LocalClass.Absolute2Restriction
import Submission.ClassField.LocalReciprocity.CharacterBoundary
import Submission.ClassField.LocalReciprocity.LocalUnitsRep

/-!
# The cohomological pairing in Proposition III.3.6

This file constructs, with the literal coefficient modules appearing in
Milne, the class

`a ∪ δχ ∈ H²(Gal(L/K), Lˣ)`

and applies the canonical finite local invariant to it.  No compatibility
with the negative-degree Tate construction of the Artin map is asserted
here; that is the remaining character-pairing theorem.
-/

namespace Submission.CField.LRecip

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory
open Submission.CField.COps.CPBuild
open Submission.CField.LFTheory
open Submission.CField.LClass
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance cupPairingValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance cupPairingValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev localUnitsRep :=
  Rep.ofMulDistribMulAction Gal(L/K) Lˣ

/-- A base-field unit, regarded as a Galois-invariant unit of the extension. -/
noncomputable def baseUnitInvariant (a : Kˣ) :
    (localUnitsRep K L).ρ.invariants :=
  ⟨Units.map (algebraMap K L) a, by
    intro σ
    apply Units.ext
    exact σ.commutes a⟩

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem base_invariant_mul (a b : Kˣ) :
    baseUnitInvariant K L (a * b) =
      baseUnitInvariant K L a + baseUnitInvariant K L b := by
  apply Subtype.ext
  let f : Kˣ →* Lˣ := Units.map (algebraMap K L)
  change Additive.ofMul (f (a * b)) = Additive.ofMul (f a * f b)
  congr 1
  exact f.map_mul a b

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem base_unit_invariant :
    baseUnitInvariant K L 1 = 0 := by
  apply Subtype.ext
  let f : Kˣ →* Lˣ := Units.map (algebraMap K L)
  change Additive.ofMul (f 1) = Additive.ofMul 1
  congr 1
  exact f.map_one

/-- A base-field unit as a degree-zero cohomology class of `Lˣ`. -/
noncomputable def baseH0 (a : Kˣ) :
    groupCohomology (localUnitsRep K L) 0 :=
  groupCohomology.π _ 0
    ((groupCohomology.cocyclesIso₀ (localUnitsRep K L)).inv
      (baseUnitInvariant K L a))

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem base_h_0 (a b : Kˣ) :
    baseH0 K L (a * b) =
      baseH0 K L a + baseH0 K L b := by
  simp only [baseH0, base_invariant_mul, map_add]

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem base_0_one :
    baseH0 K L 1 = 0 := by
  simp only [baseH0, base_unit_invariant, map_zero]

/-- The ordinary-cohomology cup product `a ∪ δχ`, with the output
`Lˣ ⊗ Z` transported back to `Lˣ` by the right unitor. -/
noncomputable def cupCharacterBoundary
    (a : Kˣ) (χ : RationalCharacter Gal(L/K)) :
    groupCohomology.H2 (localUnitsRep K L) :=
  groupCohomology.map (MonoidHom.id Gal(L/K))
    (ρ_ (localUnitsRep K L)).hom 2
    (cupCohomology (localUnitsRep K L)
      (Rep.trivial ℤ Gal(L/K) ℤ) 0 2
      (baseH0 K L a) (characterBoundary Gal(L/K) χ))

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] [IsGalois K L] in
@[simp]
theorem unit_cup_boundary
    (a b : Kˣ) (χ : RationalCharacter Gal(L/K)) :
    cupCharacterBoundary K L (a * b) χ =
      cupCharacterBoundary K L a χ +
        cupCharacterBoundary K L b χ := by
  simp only [cupCharacterBoundary, base_h_0, map_add,
    LinearMap.add_apply]

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] [IsGalois K L] in
@[simp]
theorem cup_boundary_add
    (a : Kˣ) (χ ψ : RationalCharacter Gal(L/K)) :
    cupCharacterBoundary K L a (χ + ψ) =
      cupCharacterBoundary K L a χ +
        cupCharacterBoundary K L a ψ := by
  simp only [cupCharacterBoundary, characterBoundary_add, map_add]

/-- Apply the canonical finite local invariant to a categorical `H²` class. -/
noncomputable def invariantH2
    (x : groupCohomology.H2 (localUnitsRep K L)) : LocalInvariant :=
  (relativeHTorsion K L
    ((multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ)).symm
        (Multiplicative.ofAdd x)) : Multiplicative LocalInvariant).toAdd

@[simp]
theorem invariant_h_add
    (x y : groupCohomology.H2 (localUnitsRep K L)) :
    invariantH2 K L (x + y) =
      invariantH2 K L x + invariantH2 K L y := by
  change
    ((relativeHTorsion K L
      ((multiplicativeHCohomology
        (G := Gal(L/K)) (M := Lˣ)).symm
          (Multiplicative.ofAdd (x + y))) :
        Multiplicative LocalInvariant).toAdd = _)
  rw [ofAdd_add, map_mul, map_mul]
  rfl

/-- The right-hand side of Proposition III.3.6, constructed without any
extra hypotheses: `inv_K (a ∪ δχ)`. -/
noncomputable def characterCupInvariant
    (a : Kˣ) (χ : RationalCharacter Gal(L/K)) :
    LocalInvariant :=
  invariantH2 K L (cupCharacterBoundary K L a χ)

@[simp]
theorem character_cup_mul
    (a b : Kˣ) (χ : RationalCharacter Gal(L/K)) :
    characterCupInvariant K L (a * b) χ =
      characterCupInvariant K L a χ +
        characterCupInvariant K L b χ := by
  simp only [characterCupInvariant, unit_cup_boundary,
    invariant_h_add]

@[simp]
theorem character_cup_add
    (a : Kˣ) (χ ψ : RationalCharacter Gal(L/K)) :
    characterCupInvariant K L a (χ + ψ) =
      characterCupInvariant K L a χ +
        characterCupInvariant K L a ψ := by
  simp only [characterCupInvariant, cup_boundary_add,
    invariant_h_add]

/-- For each Galois character, the cup-product invariant is an additive
character on the additive notation for `Kˣ` (equivalently, a multiplicative
character of `Kˣ`). -/
noncomputable def characterCup
    (χ : RationalCharacter Gal(L/K)) :
    Additive Kˣ →+ LocalInvariant where
  toFun a := characterCupInvariant K L a.toMul χ
  map_zero' := by
    change characterCupInvariant K L 1 χ = 0
    have h := character_cup_mul K L (1 : Kˣ) 1 χ
    apply add_left_cancel (a := characterCupInvariant K L 1 χ)
    rw [add_zero, ← h, one_mul]
  map_add' a b := character_cup_mul K L a.toMul b.toMul χ

/-- The unconditional finite local Artin homomorphism before quotienting
its source by the norm subgroup. -/
noncomputable def abelianArtinHom
    [IsMulCommutative Gal(L/K)]
    : Kˣ →* Gal(L/K) :=
  (abelianLocalArtin K L).toMonoidHom.comp
    (QuotientGroup.mk' (normSubgroup K L))

/-- The literal equality asserted by Proposition III.3.6, packaged as a
proposition using the unconditional Artin map, character boundary, cup
product, and local invariant constructed above. -/
def CharacterFormula
    [IsMulCommutative Gal(L/K)]
    (a : Kˣ) (χ : RationalCharacter Gal(L/K)) : Prop :=
  χ (Additive.ofMul (abelianArtinHom K L a)) =
    characterCupInvariant K L a χ

end

end Submission.CField.LRecip

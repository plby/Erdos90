import Submission.ClassField.LocalReciprocity.CupPairing
import Submission.ClassField.LocalReciprocity.TatePairing

/-!
# Norm compatibility in Proposition III.3.6

The cup class `a ∪ δχ` vanishes when `a` is a field norm.  Thus the
right-hand side of the character formula factors through the same norm
quotient as the local Artin map.
-/

namespace Submission.CField.LRecip

open CategoryTheory MonoidalCategory Rep
open scoped MonoidalCategory
open Submission.CField.LFTheory
open Submission.CField.COps.CPBuild
open Submission.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance normCompatibilityNormValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance normCompatibilityNormValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

private abbrev localUnitsRep :=
  Rep.ofMulDistribMulAction Gal(L/K) Lˣ

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- The invariant attached to a field norm is the representation-theoretic
group norm of the same extension-field unit. -/
private theorem base_invariant_units (x : Lˣ) :
    baseUnitInvariant K L (normOnUnits K L x) =
      ⟨(localUnitsRep K L).ρ.norm (Additive.ofMul x),
        fun g ↦ (localUnitsRep K L).ρ.self_norm_apply g (Additive.ofMul x)⟩ := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap K L) (normOnUnits K L x)) =
    (localUnitsRep K L).ρ.norm (Additive.ofMul x)
  apply Additive.toMul.injective
  change Additive.toMul
      (Additive.ofMul (Units.map (algebraMap K L) (normOnUnits K L x))) =
    Additive.toMul
      ((Representation.ofMulDistribMulAction Gal(L/K) Lˣ).norm
        (Additive.ofMul x))
  rw [toMul_ofMul, Representation.norm_ofMulDistribMulAction_eq]
  apply Units.ext
  simpa [baseUnitInvariant, localUnitsRep, normOnUnits] using
    (Algebra.norm_eq_prod_automorphisms K (x : L))

set_option maxHeartbeats 5000000 in
-- The unrestricted ambient Galois action makes the projection-formula elaboration deeper.
omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- Cupping a field norm with any character boundary gives the zero
categorical `H²` class. -/
theorem cup_boundary_units
    (x : Lˣ) (chi : RationalCharacter Gal(L/K)) :
    cupCharacterBoundary K L (normOnUnits K L x) chi = 0 := by
  let C := localUnitsRep K L
  have hcup := cup_cohomology_invariant C (Additive.ofMul x)
    (characterBoundary Gal(L/K) chi)
  have hzero :
      cupCohomology C (Rep.trivial ℤ Gal(L/K) ℤ) 0 2
        (baseH0 K L (normOnUnits K L x))
        (characterBoundary Gal(L/K) chi) = 0 := by
    rw [baseH0, base_invariant_units K L x]
    simpa [C] using hcup
  rw [cupCharacterBoundary, hzero, map_zero]

/-- Consequently the local cup invariant vanishes on every field norm. -/
theorem character_cup_units
    (x : Lˣ) (chi : RationalCharacter Gal(L/K)) :
    characterCupInvariant K L (normOnUnits K L x) chi = 0 := by
  rw [characterCupInvariant, cup_boundary_units]
  have h := invariant_h_add K L
    (0 : groupCohomology.H2 (localUnitsRep K L)) 0
  apply add_left_cancel (a := invariantH2 K L 0)
  rw [add_zero, ← h, zero_add]

/-- The cup-product invariant therefore descends canonically to the local
norm quotient `Kˣ / N(Lˣ)`. -/
noncomputable def characterCupQuotient
    (chi : RationalCharacter Gal(L/K)) :
    (Kˣ ⧸ normSubgroup K L) →* Multiplicative LocalInvariant :=
  QuotientGroup.lift (normSubgroup K L)
    (characterCup K L chi).toMultiplicative
    (by
      intro a ha
      obtain ⟨x, rfl⟩ := ha
      change Multiplicative.ofAdd
        (characterCupInvariant K L (normOnUnits K L x) chi) = 1
      rw [character_cup_units]
      rfl)

@[simp]
theorem character_cup_mk
    (chi : RationalCharacter Gal(L/K)) (a : Kˣ) :
    characterCupQuotient K L chi
        (QuotientGroup.mk' (normSubgroup K L) a) =
      Multiplicative.ofAdd (characterCupInvariant K L a chi) := by
  exact QuotientGroup.lift_mk' _ _ _

/-- Character evaluation after the finite local Artin equivalence, as a
character of the same norm quotient. -/
noncomputable def localArtinCharacter
    [IsMulCommutative Gal(L/K)]
    (chi : RationalCharacter Gal(L/K)) :
    (Kˣ ⧸ normSubgroup K L) →* Multiplicative LocalInvariant :=
  chi.toMultiplicative.comp
    (abelianLocalArtin K L).toMonoidHom

@[simp]
theorem artin_character_mk
    [IsMulCommutative Gal(L/K)]
    (chi : RationalCharacter Gal(L/K)) (a : Kˣ) :
    localArtinCharacter K L chi
        (QuotientGroup.mk' (normSubgroup K L) a) =
      Multiplicative.ofAdd
        (chi (Additive.ofMul (abelianArtinHom K L a))) :=
  rfl

/-- Proposition III.3.6 is exactly equality of the two characters of the
finite local norm quotient constructed above. -/
theorem character_all_characters
    [IsMulCommutative Gal(L/K)]
    (chi : RationalCharacter Gal(L/K)) :
    (∀ a : Kˣ, CharacterFormula K L a chi) ↔
      localArtinCharacter K L chi =
        characterCupQuotient K L chi := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (normSubgroup K L) q
    rw [artin_character_mk,
      character_cup_mk]
    exact congrArg Multiplicative.ofAdd (h a)
  · intro h a
    have ha := DFunLike.congr_fun h
      (QuotientGroup.mk' (normSubgroup K L) a)
    rw [artin_character_mk,
      character_cup_mk] at ha
    exact Multiplicative.ofAdd.injective ha

end

end Submission.CField.LRecip

import Towers.ClassField.LocalReciprocity.AmbientPairing

/-!
# Universe-polymorphic form of Proposition III.3.6

The categorical `Rep ℤ` proof of Proposition III.3.6 lives in `Type 0`.
The literal multiplicative cup cocycle and the canonical local Brauer
invariant are universe-polymorphic, however.  Finite rational-character
double duality therefore gives the local Artin homomorphism directly in the
ambient universe, with no `Small` or characteristic-zero hypothesis.
-/

namespace Towers.CField.LRecip

open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.RExist
open scoped IsMulCommutative

noncomputable section

universe u v

/-- The universe-polymorphic canonical local Artin homomorphism. -/
noncomputable def abelianArtinUniverse
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative Gal(L/K)] :
    Kˣ →* Gal(L/K) :=
  multiplicativeCupArtin K L

/-- The universe-polymorphic local cup invariant paired with a character. -/
noncomputable def characterCupUniverse
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (a : Kˣ) (χ : CharacterModule (Additive Gal(L/K))) : LocalInvariant :=
  ambientCupInvariant K L a χ

/-- The universe-polymorphic cup invariant is definitionally the canonical
local invariant of the literal multiplicative crossed product. -/
theorem character_universe_multiplicative
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (a : Kˣ) (χ : CharacterModule (Additive Gal(L/K))) :
    characterCupUniverse K L a χ =
      (carryBrauerInvariant K
        (((CProduc.hRelativeBrauer K L
          (multiplicativeCupClass K L a χ) :
            relativeBrauerGroup K L) : BrauerGroup K))).toAdd := by
  rfl

/-- **Proposition III.3.6, universe-polymorphic form.** -/
theorem abelian_universe_character
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (a : Kˣ) (χ : CharacterModule (Additive Gal(L/K))) :
    χ (Additive.ofMul (abelianArtinUniverse K L a)) =
      characterCupUniverse K L a χ :=
  multiplicative_cup_character K L a χ

/-- Proposition III.3.6 after postcomposing the ambient local Artin
homomorphism with a homomorphism to an ambient abelian group. -/
theorem abelian_universe_comp
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative Gal(L/K)]
    {G : Type v} [CommGroup G]
    (j : Gal(L/K) →* G) (a : Kˣ)
    (χ : CharacterModule (Additive G)) :
    characterCupUniverse K L a (χ.comp j.toAdditive) =
      χ (Additive.ofMul (j (abelianArtinUniverse K L a))) := by
  simpa only [AddMonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_toAdditive, toMul_ofMul] using
      (abelian_universe_character
        K L a (χ.comp j.toAdditive)).symm

end

end Towers.CField.LRecip

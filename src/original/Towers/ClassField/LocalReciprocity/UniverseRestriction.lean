import Towers.ClassField.LocalReciprocity.GlobalBrauer
import Towers.ClassField.LocalReciprocity.UniversePolymorphicArtin

/-!
# Universe-polymorphic restriction of the local Artin map

The Type-0 form of Lemma III.3.3 uses the categorical norm-residue map.
For the ambient cup-defined map, the same proof only needs the already
universe-polymorphic crossed-product inflation calculation and rational
character separation.
-/

namespace Towers.CField.LRecip

open Towers.CField.BGroups
open Towers.CField.LBrauer
open Towers.CField.RExist
open scoped IsMulCommutative

noncomputable section

universe u

variable (K Omega : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsNonarchimedeanLocalField K]
  [Field Omega] [Algebra K Omega]
  {F E : FiniteGaloisIntermediateField K Omega}
  [IsMulCommutative Gal(F/K)]

/-- The ambient cup invariant is unchanged when a character from a smaller
finite Galois level is inflated along restriction from a larger level. -/
theorem character_universe_restriction
    [IsMulCommutative Gal(E/K)]
    (hFE : F ≤ E) (a : Kˣ) (chi : RationalCharacter Gal(F/K)) :
    characterCupUniverse K E a
        (chi.comp (galoisRestrictionHom K hFE).toAdditive) =
      characterCupUniverse K F a chi := by
  rw [character_universe_multiplicative,
    character_universe_multiplicative]
  exact congrArg
    (fun x : BrauerGroup K =>
      (carryBrauerInvariant K x).toAdd)
    (global_multiplicative_brauer
      K Omega hFE a chi).symm

set_option maxHeartbeats 5000000 in
-- Character separation expands both ambient Artin maps and the restriction map.
/-- **Lemma III.3.3, universe-polymorphic ambient form.**  Galois restriction
carries the upper cup-defined local Artin homomorphism to the lower one. -/
theorem abelian_universe_restriction
    [IsMulCommutative Gal(E/K)]
    (hFE : F ≤ E) :
    (galoisRestrictionHom K hFE).comp
        (abelianArtinUniverse K E) =
      abelianArtinUniverse K F := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  calc
    chi (Additive.ofMul
        (galoisRestrictionHom K hFE
          (abelianArtinUniverse K E a))) =
        characterCupUniverse K E a
          (chi.comp (galoisRestrictionHom K hFE).toAdditive) :=
      (abelian_universe_comp K E
        (galoisRestrictionHom K hFE) a chi).symm
    _ = characterCupUniverse K F a chi :=
      character_universe_restriction
        K Omega hFE a chi
    _ = chi (Additive.ofMul
        (abelianArtinUniverse K F a)) :=
      (abelian_universe_character K F a chi).symm

end


end Towers.CField.LRecip

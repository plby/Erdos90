import Towers.ClassField.LocalReciprocity.TransportedProduct
import Towers.ClassField.LocalReciprocity.AmbientPairing
import Towers.ClassField.LocalReciprocity.UniversePolymorphicArtin
import Towers.ClassField.ReciprocityExistence.CupComparison

/-!
# Compatibility of the ambient and norm-residue Artin maps

In `Type 0`, the original categorical proof of Proposition III.3.6 is
available.  The comparison with the literal multiplicative cup cocycle and
character duality then identify the ambient-universe construction with the
previously constructed norm-residue Artin map.
-/

namespace Towers.CField.LRecip

open Towers.CField.LBrauer
open Towers.CField.RExist

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance ambientCompatibilityValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance ambientCompatibilityCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [IsMulCommutative Gal(L/K)]

/-- In the categorical universe, the cup-defined Artin homomorphism is the
original norm-residue Artin homomorphism. -/
theorem abelian_multiplicative_cup :
    abelianArtinHom K L =
      multiplicativeCupArtin K L := by
  apply multiplicative_cup_unique K L
  intro a χ
  have hcat := transportedCupBoundary K L a χ
  change χ (Additive.ofMul (abelianArtinHom K L a)) =
    characterCupInvariant K L a χ at hcat
  rw [hcat]
  simpa [ambientCupInvariant, ambientMultiplicativeInvariant]
    using character_cup_multiplicative K L a χ

/-- In the categorical universe, the original norm-residue Artin map is the
universe-polymorphic ambient cup-defined Artin map. -/
theorem abelian_local_universe :
    abelianArtinHom K L =
      abelianArtinUniverse K L := by
  rw [abelian_multiplicative_cup]
  rfl

end

end Towers.CField.LRecip

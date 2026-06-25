import Towers.ClassField.LocalReciprocity.TransportedProduct

/-!
# Functorial form of Proposition III.3.6

At a completion of a global extension, the relevant local character is the
restriction of a global character to the decomposition group.  This file
records Proposition III.3.6 in exactly that form.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance functorialityValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance functorialityValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

/-- Proposition III.3.6 after restricting a character along a homomorphism
out of the local Galois group.  In global applications this homomorphism is
the inclusion of a decomposition group. -/
theorem comp
    {G : Type} [CommGroup G]
    (j : Gal(L/K) →* G) (a : Kˣ) (chi : RationalCharacter G) :
    characterCupInvariant K L a (chi.comp j.toAdditive) =
      chi (Additive.ofMul (j (abelianArtinHom K L a))) := by
  simpa only [CharacterFormula, AddMonoidHom.coe_comp,
    Function.comp_apply, MonoidHom.coe_toAdditive,
    toMul_ofMul]
    using (transportedCupBoundary K L a (chi.comp j.toAdditive)).symm

end

end Towers.CField.LRecip

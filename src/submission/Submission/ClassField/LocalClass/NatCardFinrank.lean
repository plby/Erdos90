import Submission.ClassField.LocalClass.CardinalityCanonicalSplitting
import Submission.ClassField.LocalClass.FiniteGaloisExtensions

/-!
# Milne, Class Field Theory, Lemma III.2.6

The degree-two cohomology group of a finite Galois extension of local
fields has cardinality equal to the extension degree.
-/

namespace Submission.CField.LClass

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteLocalH2NatCardEqFinrankSourceValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteLocalH2NatCardEqFinrankSourceValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- **Lemma III.2.6.** `H²(L/K)` has order `[L : K]`. -/
theorem h_card_finrank :
    Nat.card
        (groupCohomology.H2
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) =
      Module.finrank K L :=
  cohomology_h_units
    K L (brauer_relative_galois K L)

end

end Submission.CField.LClass

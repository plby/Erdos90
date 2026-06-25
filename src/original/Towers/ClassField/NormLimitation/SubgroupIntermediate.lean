import Towers.ClassField.KummerNormIndex.LocalCriterionIdeles
import Towers.ClassField.NormLimitation.IsUnitOutside

/-!
# Chapter VII, Section 9, Proposition 9.2

The local-to-global power criterion is Proposition VII.6.10 with no
auxiliary places.  Proposition 6.10 has already been proved unconditionally,
so this file closes the printed statement without any bridge hypothesis.
-/

namespace Towers.CField.NLimita

open Towers.CField.KNIndex
open Towers.CField.Ideles
open Towers.CField.NIndex

noncomputable section

universe u

/-- **Proposition VII.9.2.** -/
theorem intermediateReductionStatement : (∀ (n : ℕ) (K : Type u) [Field K] [NumberField K],
      (primitiveRoots n K).Nonempty →
      ∀ S : Finset (NumberFieldPlace K),
        ContainsAllPlaces K S →
        (∀ v : NumberFieldPlace K,
          normalizedPlaceValue K v (n : K) ≠ 1 → v ∈ S) →
        CIGenera K S →
        ∀ a : Kˣ,
          (∀ v : NumberFieldPlace K, v ∈ S →
            nthPowerPlace K n a v) →
          isUnitOutside K a S →
          a ∈ (powMonoidHom n : Kˣ →* Kˣ).range) :=
  isUnitOutside_implies_nthPower criterionIdelesStatement

end

end Towers.CField.NLimita

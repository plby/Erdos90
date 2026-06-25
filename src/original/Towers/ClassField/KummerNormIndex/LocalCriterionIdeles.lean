import Towers.ClassField.KummerNormIndex.KummerExtension
import Towers.ClassField.KummerNormIndex.OutsideUnramified
import Towers.ClassField.BrauerLocalization.CokernelAssembly

/-!
# Proposition VII.6.10

The Kummer extension, its local norm calculations, and the earlier idèle
results are now all unconditional.  This file assembles them into the source
statement of Proposition 6.10.
-/

namespace Towers.CField.KNIndex

open Towers.CField.BLoc
open Towers.CField.Ideles
open Towers.CField.NIndex
open Towers.NumberTheory.Milne

noncomputable section

universe u

/-- **Proposition VII.6.10.** -/
theorem criterionIdelesStatement : (∀ (n : ℕ) (K : Type u) [Field K] [NumberField K],
      (primitiveRoots n K).Nonempty →
      ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
        ContainsAllPlaces K S →
        (∀ v : NumberFieldPlace K,
          normalizedPlaceValue K v (n : K) ≠ 1 → v ∈ S) →
        CIGenera K S →
        ∀ (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
          (Sum.inl P : NumberFieldPlace K) ∉ S),
        Function.Surjective (obviousMap K n S T hDisjoint) →
        ∀ b : Kˣ,
          (∀ v : NumberFieldPlace K, v ∈ S →
            nthPowerPlace K n b v) →
          nthPlaceOutside K b S T →
          b ∈ (powMonoidHom n : Kˣ →* Kˣ).range) :=
  nth_statement_bridges
    kummerExtensionBridge
    localNormBridge
    fractionalIdealPrime
    cyclicSubextensionDegree

end

end Towers.CField.KNIndex

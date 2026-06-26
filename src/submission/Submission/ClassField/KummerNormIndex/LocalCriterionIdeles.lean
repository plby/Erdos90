import Submission.ClassField.KummerNormIndex.KummerExtension
import Submission.ClassField.KummerNormIndex.OutsideUnramified
import Submission.ClassField.BrauerLocalization.CokernelAssembly

/-!
# Proposition VII.6.10

The Kummer extension, its local norm calculations, and the earlier idèle
results are now all unconditional.  This file assembles them into the source
statement of Proposition 6.10.
-/

namespace Submission.CField.KNIndex

open Submission.CField.BLoc
open Submission.CField.Ideles
open Submission.CField.NIndex
open Submission.NumberTheory.Milne

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

end Submission.CField.KNIndex

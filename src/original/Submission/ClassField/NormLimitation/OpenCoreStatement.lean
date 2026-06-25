import Submission.ClassField.NormIndex.FractionalIdealPrime
import Submission.ClassField.KummerNormIndex.PlaceValue
import Submission.ClassField.NormLimitation.CoreDefinitions

/-! # The open-neighborhood interface in Lemma VII.9.3 -/

namespace Submission.CField.NLimita

open NumberField
open Submission.CField.Ideles
open Submission.CField.NIndex
open Submission.CField.KNIndex

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- The idèle-topology input: an open subgroup contains an outside-unit
neighborhood, and `S` may be enlarged to contain the infinite places, the
places dividing `p`, and ideal-class generators. -/
def OpenCoreBridge : Prop :=
  ∀ (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (_hp : p.Prime)
    (V : Subgroup (CK K)),
    IsOpen (V : Set (CK K)) →
      ∃ S : Finset (NumberFieldPlace K),
        ContainsAllPlaces K S ∧
        (∀ v : NumberFieldPlace K,
          normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) ∧
        CIGenera K S ∧
        outsideUnitClasses K S ≤ V

end

end Submission.CField.NLimita

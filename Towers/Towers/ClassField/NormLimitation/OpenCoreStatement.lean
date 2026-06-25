import Towers.ClassField.NormIndex.FractionalIdealPrime
import Towers.ClassField.KummerNormIndex.PlaceValue
import Towers.ClassField.NormLimitation.CoreDefinitions

/-! # The open-neighborhood interface in Lemma VII.9.3 -/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.Ideles
open Towers.CField.NIndex
open Towers.CField.KNIndex

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

end Towers.CField.NLimita

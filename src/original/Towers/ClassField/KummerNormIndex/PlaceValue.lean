import Towers.ClassField.Ideles.GlobalPlace

/-! # The normalized absolute value used in Lemma VII.6.6 -/

namespace Towers.CField.KNIndex

open NumberField
open Towers.CField.Ideles

noncomputable section

universe u

/-- The normalized absolute value used in the number-field product formula.
At a complex infinite place this includes the multiplicity two. -/
def normalizedPlaceValue
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (x : K) : ℝ :=
  match v with
  | .inl P => (FinitePlace.equivHeightOneSpectrum.symm P) x
  | .inr v => v.1 x ^ v.mult

end


end Towers.CField.KNIndex

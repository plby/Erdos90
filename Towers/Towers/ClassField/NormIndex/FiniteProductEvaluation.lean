import Towers.ClassField.NormIndex.FiniteExtensionCoordinate

/-!
# Evaluation of finite-idèle products
-/

namespace Towers.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open scoped BigOperators

noncomputable section

universe u

variable {L : Type u} [Field L] [NumberField L]

noncomputable def finiteMonoidHom
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    FiniteIdeles (NumberField.RingOfIntegers L) L →* (Q.adicCompletion L)ˣ where
  toFun y := y.1 Q
  map_one' := rfl
  map_mul' _ _ := rfl

theorem finite_idele_prod
    {A : Type*} [Fintype A]
    (f : A → FiniteIdeles (NumberField.RingOfIntegers L) L)
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    (∏ a, f a).1 Q = ∏ a, (f a).1 Q := by
  exact map_prod (finiteMonoidHom (L := L) Q) f Finset.univ

end

end Towers.CField.NIndex

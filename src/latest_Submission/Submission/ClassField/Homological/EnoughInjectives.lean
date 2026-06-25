import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.RepresentationTheory.Rep.Iso

open CategoryTheory

universe u w

variable {k G : Type u} [CommRing k] [Monoid G]

instance : EnoughInjectives (Rep.{max w u} k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughInjectives_iff.mpr
    (ModuleCat.enoughInjectives (MonoidAlgebra k G))

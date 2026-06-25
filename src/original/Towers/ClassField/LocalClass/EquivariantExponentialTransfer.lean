import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Milne, Class Field Theory, Lemma III.2.4: equivariant exponential transfer

In characteristic zero, Milne applies the local exponential to a sufficiently
small additive lattice from Lemma III.2.3.  Once exponential and logarithm
give a Galois-equivariant isomorphism onto a subgroup of principal units,
cohomology vanishing transports formally across that isomorphism.  This file
proves that unconditional categorical step.
-/

namespace Towers.CField.LClass

open CategoryTheory

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- A Galois-equivariant additive-to-multiplicative local exponential
isomorphism transports vanishing in each cohomological degree. -/
theorem cohomology_equivariant_exp
    (A V : Rep R G) (expIso : A ≅ V) (r : ℕ)
    (hA : Limits.IsZero (groupCohomology A r)) :
    Limits.IsZero (groupCohomology V r) :=
  hA.of_iso ((groupCohomology.functor R G r).mapIso expIso.symm)

/-- The all-positive-degree form used in Lemma III.2.4. -/
theorem vanishes_equivariant_exp
    (A V : Rep R G) (expIso : A ≅ V)
    (hA : ∀ r : ℕ, 0 < r → Limits.IsZero (groupCohomology A r)) :
    ∀ r : ℕ, 0 < r → Limits.IsZero (groupCohomology V r) :=
  fun r hr ↦ cohomology_equivariant_exp A V expIso r (hA r hr)

end Towers.CField.LClass

import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Milne, Class Field Theory, Proposition II.1.25

The categorical group-cohomology functor immediately gives the finite-product
part once its additivity is made explicit.  The full arbitrary-product result,
using exactness of products of modules, is proved in
`Proposition125Arbitrary`.
-/

namespace Towers.CField.COps

open CategoryTheory CategoryTheory.Limits

universe u

variable (k G : Type u) [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- The group-cohomology functor is additive. -/
noncomputable instance cohomology_functor_additive (n : ℕ) :
    (groupCohomology.functor k G n).Additive where
  map_add {X Y} f g := by
    change HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n + HomologicalComplex.homologyMap _ n
    rw [← HomologicalComplex.homologyMap_add]
    congr 1

noncomputable instance functor_binary_biproducts (n : ℕ) :
    PreservesBinaryBiproducts (groupCohomology.functor k G n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The finite-family specialization of Proposition II.1.25. -/
noncomputable def cohomologyProductIso
    {ι : Type u} [Finite ι] (A : ι → Rep k G) (n : ℕ) :
    groupCohomology (∏ᶜ A) n ≅ ∏ᶜ fun i ↦ groupCohomology (A i) n :=
  preservesLimitIso (groupCohomology.functor k G n) (Discrete.functor A) ≪≫
    HasLimit.isoOfNatIso
      (Discrete.compNatIsoDiscrete A (groupCohomology.functor k G n))

/-- The binary direct-sum formula singled out after Proposition II.1.25. -/
noncomputable def cohomologyBiprodIso (A B : Rep k G) (n : ℕ) :
    groupCohomology (A ⊞ B) n ≅
      groupCohomology A n ⊞ groupCohomology B n :=
  (groupCohomology.functor k G n).mapBiprod A B

end Towers.CField.COps

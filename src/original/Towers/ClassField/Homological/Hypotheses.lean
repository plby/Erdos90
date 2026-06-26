import Towers.ClassField.Homological.ProjectiveExtComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Milne, Class Field Theory, Proposition II.A.13 (source hypotheses)

Milne assumes that the abelian category has enough injectives and enough
projectives.  Mathlib's comparison with derived-category `Ext` is phrased
using `HasExt`; enough injectives supply that smallness condition in the safe
universe `max u v`.  This wrapper therefore exposes exactly Milne's
categorical hypotheses (apart from that universe bookkeeping).
-/

open CategoryTheory CochainComplex HomComplex Abelian

universe v u

namespace Towers.CField.Homological

variable {C : Type u} [Category.{v} C] [Abelian C]
  [EnoughInjectives C] [EnoughProjectives C]

/-- Proposition II.A.13 under the hypotheses in the source: computing
`Ext` from a projective resolution of the first variable or from an injective
resolution of the second variable gives canonically isomorphic groups. -/
noncomputable def projective_ext_enough
    {X Y : C} (P : ProjectiveResolution X) (I : InjectiveResolution Y) (n : ℕ) :
    CohomologyClass P.cochainComplex ((singleFunctor C 0).obj Y) n ≃+
      CohomologyClass ((singleFunctor C 0).obj X) I.cochainComplex n := by
  letI : HasExt.{max u v} C := hasExt_of_enoughInjectives C
  exact projectiveExtComparison.{max u v} P I n

end Towers.CField.Homological

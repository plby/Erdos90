import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Milne, Class Field Theory, Proposition II.A.13

Computing Ext with a projective resolution in the first variable or an
injective resolution in the second variable gives canonically equivalent
cohomology groups.
-/

open CategoryTheory CochainComplex HomComplex Abelian

universe w v u

namespace Towers.CField.Homological

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Proposition A.13.  Both resolution constructions are identified with
the same derived-category Ext group, giving this canonical comparison. -/
noncomputable def projectiveExtComparison {X Y : C}
    (P : ProjectiveResolution X) (I : InjectiveResolution Y) (n : ℕ) :
    CohomologyClass P.cochainComplex ((singleFunctor C 0).obj Y) n ≃+
      CohomologyClass ((singleFunctor C 0).obj X) I.cochainComplex n :=
  P.extAddEquivCohomologyClass.symm.trans I.extAddEquivCohomologyClass

end Towers.CField.Homological

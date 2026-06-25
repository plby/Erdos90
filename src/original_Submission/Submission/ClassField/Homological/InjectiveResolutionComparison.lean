import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Chapter II, Appendix, Lemma A.6

Injective resolutions exist in an abelian category with enough injectives, and
two injective resolutions of the same object have a comparison map over that
object.
-/

open CategoryTheory

universe v u

namespace Submission.CField.Homological

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The existence assertion in Lemma A.6. -/
theorem exists_injectiveResolution [EnoughInjectives C] (X : C) :
    Nonempty (InjectiveResolution X) :=
  HasInjectiveResolution.out

/-- The comparison map in Lemma A.6, extending the identity of the resolved
object. -/
noncomputable def injectiveResolutionComparison {X : C}
    (I J : InjectiveResolution X) : I.cocomplex ⟶ J.cocomplex :=
  InjectiveResolution.desc (𝟙 X) J I

@[reassoc]
theorem resolution_comparison_commutes {X : C}
    (I J : InjectiveResolution X) :
    I.ι ≫ injectiveResolutionComparison I J = J.ι := by
  simp [injectiveResolutionComparison]

end Submission.CField.Homological

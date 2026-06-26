import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Milne, Class Field Theory, Remark II.A.12

The normalization and injective-vanishing properties of right-derived
functors.
-/

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace Towers.CField.Homological

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Remark A.12(a): degree zero is the original left exact functor. -/
noncomputable def derived_iso_self (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] : F.rightDerived 0 ≅ F :=
  F.rightDerivedZeroIsoSelf

/-- Remark A.12(b): positive right-derived functors vanish on injective
objects. -/
theorem right_derived_injective
    (F : C ⥤ D) [F.Additive] (n : ℕ) (I : C) [Injective I] :
    IsZero ((F.rightDerived (n + 1)).obj I) :=
  F.isZero_rightDerived_obj_injective_succ n I

end Towers.CField.Homological

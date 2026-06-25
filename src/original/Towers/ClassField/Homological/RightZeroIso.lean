import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Chapter II, Appendix, Remark A.7

The zeroth right-derived functor of a left exact functor is the original
functor.
-/

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace Towers.CField.Homological

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Remark A.7, naturally in the resolved object. -/
noncomputable def rightDerivedIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] : F.rightDerived 0 ≅ F :=
  F.rightDerivedZeroIsoSelf

end Towers.CField.Homological

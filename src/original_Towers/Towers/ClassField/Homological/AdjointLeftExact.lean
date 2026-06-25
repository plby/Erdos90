import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Chapter II, Appendix, Proposition A.5

A functor admitting an exact left adjoint preserves injective objects.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Towers.CField.Homological

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Proposition A.5.  Here exactness is stated directly as preservation of
exact short complexes. -/
theorem adjoint_preserves_exact
    (L : D ⥤ C) (F : C ⥤ D) (adj : L ⊣ F) [L.PreservesZeroMorphisms]
    (hL : ∀ (S : ShortComplex D), S.Exact → (S.map L).Exact)
    (I : C) (hI : Injective I) : Injective (F.obj I) := by
  letI : L.PreservesMonomorphisms := L.preservesMonomorphisms_of_map_exact hL
  exact adj.map_injective I hI

end Towers.CField.Homological

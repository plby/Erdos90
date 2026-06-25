import Towers.ClassField.ReciprocityExistence.MultiplicativeCup
import Towers.ClassField.CrossedProducts.CohomologyRestriction

/-!
# Restriction of the multiplicative character cup

Milne's literal cocycle `(g, h) \mapsto x ^ n(g, h)` is natural when the
acting group is restricted along a homomorphism.  This is the representative
calculation needed before applying Shapiro at a chosen place.
-/

namespace Towers.CField.RExist

open Towers.CField.CProduca

noncomputable section

universe uG uH uM

variable {G : Type uG} {H : Type uH} {M : Type uM}
  [Group G] [Group H] [CommGroup M]
  [MulDistribMulAction G M] [MulDistribMulAction H M]

/-- The canonical rational lift of a character is unchanged after
restriction, apart from evaluating the original character on the image. -/
theorem rational_character_comp
    (f : H →* G) (chi : Additive G →+ AddCircle (1 : ℚ)) (h : H) :
    rationalCharacterLift (chi.comp f.toAdditive) h =
      rationalCharacterLift chi (f h) := by
  rfl

/-- The integral boundary exponent used in the multiplicative cup is
natural under restriction of the acting group. -/
theorem rational_boundary_comp
    (f : H →* G) (chi : Additive G →+ AddCircle (1 : ℚ)) (g h : H) :
    rationalBoundaryExponent (chi.comp f.toAdditive) g h =
      rationalBoundaryExponent chi (f g) (f h) := by
  have hq :
      ((rationalBoundaryExponent
        (chi.comp f.toAdditive) g h : ℤ) : ℚ) =
        ((rationalBoundaryExponent chi (f g) (f h) : ℤ) : ℚ) := by
    rw [rational_boundary_spec,
      rational_boundary_spec]
    simp only [rational_character_comp, map_mul]
  exact_mod_cast hq

/-- Restricting Milne's literal cup cocycle gives the literal cup cocycle
for the restricted character. -/
theorem cup_cocycle_restrict
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (x : M) (hx : ∀ g : G, g • x = x)
    (chi : Additive G →+ AddCircle (1 : ℚ)) :
    NMCocycl₂.restrict f hsmul
        (invariantCupCocycle x hx chi) =
      invariantCupCocycle x
        (fun h => (hsmul h x).trans (hx (f h)))
        (chi.comp f.toAdditive) := by
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change x ^ rationalBoundaryExponent chi (f g) (f h) =
    x ^ rationalBoundaryExponent (chi.comp f.toAdditive) g h
  rw [rational_boundary_comp]

/-- Restriction in multiplicative `H²` carries the invariant-character cup
class to the cup class of the restricted character. -/
theorem invariant_cup_restriction
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (x : M) (hx : ∀ g : G, g • x = x)
    (chi : Additive G →+ AddCircle (1 : ℚ)) :
    MHTwo.restrictionHom f hsmul
        (invariantCharacterCup x hx chi) =
      invariantCharacterCup x
        (fun h => (hsmul h x).trans (hx (f h)))
        (chi.comp f.toAdditive) := by
  rw [invariantCharacterCup, invariantCharacterCup,
    MHTwo.restrictionHom_mk,
    cup_cocycle_restrict]

end

end Towers.CField.RExist

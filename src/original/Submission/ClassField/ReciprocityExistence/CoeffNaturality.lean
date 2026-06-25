import Submission.ClassField.ReciprocityExistence.MultiplicativeCup
import Submission.FieldTheory.CentralFactorSet

/-!
# Coefficient naturality of the multiplicative character cup

Milne's literal cocycle `(g, h) \mapsto x ^ n(g, h)` commutes with every
equivariant homomorphism of multiplicative coefficient groups.  Together
with `MultiplicativeCupRestriction`, this is the representative calculation
needed to evaluate the finite completion-product cup at a chosen place.
-/

namespace Submission.CField.RExist

open Submission.CField.CProduca

noncomputable section

universe uG uM uN

variable {G : Type uG} {M : Type uM} {N : Type uN}
  [CommGroup G] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]

/-- Applying an equivariant coefficient homomorphism to the literal cup
cocycle replaces its invariant coefficient by its image. -/
theorem cup_cocycle_coefficients
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (x : M) (hx : ∀ g : G, g • x = x)
    (chi : CharacterModule (Additive G)) :
    NMCocycl₂.mapCoefficients f hf
        (invariantCupCocycle x hx chi) =
      invariantCupCocycle (f x)
        (fun g => by rw [← hf g x, hx g]) chi := by
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change f (x ^ rationalBoundaryExponent chi g h) =
    f x ^ rationalBoundaryExponent chi g h
  exact map_zpow f x _

/-- Change of coefficients in multiplicative `H²` carries the
invariant-character cup class to the cup class of the image coefficient. -/
theorem invariant_cup_coefficients
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (x : M) (hx : ∀ g : G, g • x = x)
    (chi : CharacterModule (Additive G)) :
    MHTwo.mapCoefficientsHom f hf
        (invariantCharacterCup x hx chi) =
      invariantCharacterCup (f x)
        (fun g => by rw [← hf g x, hx g]) chi := by
  rw [invariantCharacterCup, invariantCharacterCup,
    MHTwo.coefficients_hom_mk,
    cup_cocycle_coefficients]

/-- The literal cup class is independent of the chosen proof that its
coefficient is invariant, and transports along equality of coefficients. -/
theorem invariant_cup_congr
    (x y : M) (hxy : x = y)
    (hx : ∀ g : G, g • x = x) (hy : ∀ g : G, g • y = y)
    (chi : CharacterModule (Additive G)) :
    invariantCharacterCup x hx chi =
      invariantCharacterCup y hy chi := by
  subst y
  rfl

end

end Submission.CField.RExist

import Mathlib.Algebra.Module.CharacterModule

/-!
# Milne, Class Field Theory, Lemma III.3.7: character-duality conclusion

The last step of Milne's proof uses that homomorphisms to `ℚ / ℤ` separate
the elements of an abelian group.  Consequently, once Proposition III.3.6
and the invariant calculation show that the local Artin image and the
appropriate power of Frobenius have the same value under every character,
the two group elements are equal.

The preceding invariant and cup-product calculation is not included here;
it requires cohomological infrastructure not currently available in the
project.
-/

namespace Submission.CField.LRecip

universe u v

variable {G : Type u} [CommGroup G]

/-- Additive `ℚ / ℤ`-valued characters separate elements of a commutative
group, written multiplicatively via `Additive G`. -/
theorem forall_rational_character {x y : G}
    (h : ∀ χ : CharacterModule (Additive G),
      χ (Additive.ofMul x) = χ (Additive.ofMul y)) :
    x = y := by
  apply Additive.ofMul.injective
  apply sub_eq_zero.mp
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  rw [map_sub, h χ, sub_self]

/-- **Lemma III.3.7, final duality step.** If every `ℚ / ℤ`-valued
character takes the Artin image of `a` to its value on
`Frob ^ ord(a)`, then the Artin image itself is that Frobenius power. -/
theorem artin_zpow_values
    {A : Type v} [Monoid A] (artin : A →* G) (frobenius : G)
    (ord : A → ℤ) (a : A)
    (h : ∀ χ : CharacterModule (Additive G),
      χ (Additive.ofMul (artin a)) =
        χ (Additive.ofMul (frobenius ^ ord a))) :
    artin a = frobenius ^ ord a :=
  forall_rational_character h

end Submission.CField.LRecip

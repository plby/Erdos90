import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Milne, Class Field Theory, Lemma II.A.1

The extended snake lemma in an arbitrary abelian category.
-/

namespace Towers.CField.Homological

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Lemma II.A.1 (extended snake lemma).** The six morphisms formed by the
kernels, the connecting morphism, and the cokernels of a morphism of exact
short complexes form an exact sequence. -/
theorem extendedSnakeLemma (S : ShortComplex.SnakeInput C) :
    S.composableArrows.Exact :=
  S.snake_lemma

/-- If the upper row also starts with zero, the first map in the snake
sequence is a monomorphism, giving the initial zero in Milne's display. -/
theorem extended_snake_lemma (S : ShortComplex.SnakeInput C)
    [Mono S.L₁.f] : Mono S.L₀.f :=
  inferInstance

/-- If the lower row also ends with zero, the last map in the snake sequence
is an epimorphism, giving the terminal zero in Milne's display. -/
theorem snake_lemma_epi (S : ShortComplex.SnakeInput C)
    [Epi S.L₂.g] : Epi S.L₃.g :=
  inferInstance

end Towers.CField.Homological

import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# Milne, Class Field Theory, Lemma II.A.2

The kernel-cokernel exact sequence associated to two composable morphisms.
-/

namespace Submission.CField.Homological

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C}

/-- **Lemma II.A.2 (kernel-cokernel lemma).** For `X ⟶ Y ⟶ Z`, the sequence
`ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g`
is exact.  Mathlib's endpoint instances say that its first map is mono and
its last map is epi, supplying the displayed zeros. -/
theorem kernelCokernel_exact (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CategoryTheory.kernelCokernelCompSequence f g).Exact :=
  CategoryTheory.kernelCokernelCompSequence_exact f g

end Submission.CField.Homological

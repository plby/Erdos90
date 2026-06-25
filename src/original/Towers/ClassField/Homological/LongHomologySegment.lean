import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Milne, Class Field Theory, Proposition II.A.11

The functorial long exact homology sequence underlying the long exact sequence
of right-derived functors.
-/

open CategoryTheory ComposableArrows

universe v u w

namespace Towers.CField.Homological

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- A six-object window in the long exact homology sequence attached to a
short exact sequence of complexes. -/
noncomputable def longExactSegment
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (i j : ι) (hij : c.Rel i j) : ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅ hS i j hij

/-- Exactness of every six-object window in the long exact homology sequence,
which is the exactness assertion used in Proposition A.11 after applying a
left exact functor to injective resolutions. -/
theorem long_homology_segment
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    (longExactSegment hS i j hij).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact hS i j hij

/-- A morphism of short exact sequences induces a morphism of their long
exact homology sequences. -/
noncomputable def longHomologySegment
    {S T : ShortComplex (HomologicalComplex C c)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    longExactSegment hS i j hij ⟶
      longExactSegment hT i j hij :=
  HomologicalComplex.HomologySequence.mapComposableArrows₅ f hS hT i j hij

/-- Naturality of the connecting morphism in the long exact homology
sequence. -/
theorem long_connecting_naturality
    {S T : ShortComplex (HomologicalComplex C c)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    hS.δ i j hij ≫ HomologicalComplex.homologyMap f.τ₁ j =
      HomologicalComplex.homologyMap f.τ₃ i ≫ hT.δ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality f hS hT i j hij

end Towers.CField.Homological

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Milne, Class Field Theory, Lemma II.4.1

Filtered colimits of modules preserve exact sequences.  Consequently, they
commute with the homology (and hence the cohomology) of complexes.
-/

namespace Submission.CField.PCohom

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {R : Type u} [Ring R]
  {J : Type u} [SmallCategory J] [IsFiltered J]

/-- **Lemma II.4.1, exactness.** A compatible filtered system of exact
sequences of `R`-modules remains exact after taking its colimit. -/
theorem filteredColimit_exact
    (S : ShortComplex (J ⥤ ModuleCat.{u} R)) (hS : S.Exact) :
    (S.map (colim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)).Exact :=
  hS.map _

/-- **Lemma II.4.1, cohomology consequence.** At every degree, the homology
of the filtered colimit is canonically the filtered colimit of the homology.

The same statement applies to cochain complexes by choosing the appropriate
`ComplexShape`. -/
noncomputable def filteredColimitHomology
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (J ⥤ ModuleCat.{u} R) c) (n : ι) :
    ((K.sc n).map
      (colim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)).homology ≅
      (colim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).obj
        ((K.sc n).homology) :=
  (K.sc n).mapHomologyIso _

end

end Submission.CField.PCohom

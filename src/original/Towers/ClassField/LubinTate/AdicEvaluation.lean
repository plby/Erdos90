import Towers.ClassField.FormalGroups.FormalGroupEvaluation
import Towers.ClassField.FormalGroups.LubinTateHomomorphism

/-!
# Class Field Theory, Chapter I, Section 3: convergent Lubin-Tate evaluation

At the start of Section 3, Milne evaluates the Lubin-Tate formal group law
`F_f` and its scalar endomorphisms `[a]_f` on elements of a maximal ideal.
This file gives the corresponding constructions for any complete adic local
domain.  The values are elements of the defining ideal by the convergence
results proved after Remark 2.4.
-/

namespace Towers.CField.LTate

open Towers.CField.FGroups

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [T2Space R] [CompleteSpace R]

/-- The convergent value `F_f(alpha,beta)` in the adic ideal. -/
noncomputable def lubinLawValue
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (alpha beta : I) : I :=
  FGLaw.adicValue hI
    (lubinFormalLaw pi hpi0 hpi hfield f hf) alpha beta

/-- The convergent value `[a]_f(alpha)` in the adic ideal. -/
noncomputable def lubinScalarValue
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (a : R) (alpha : I) : I :=
  (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).adicValue hI alpha

end

end Towers.CField.LTate

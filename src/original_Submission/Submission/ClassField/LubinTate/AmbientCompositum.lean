import Submission.ClassField.LubinTate.RootFieldTower
import Submission.NumberTheory.Locals.MaximalUnramifiedExtension

/-!
# Class Field Theory, Chapter I, Theorem 3.9: the ambient compositum

Milne's Theorem 3.9 says that both `K_pi * K^un` and the local Artin map are
independent of the uniformizer.  This file defines the field appearing in
that statement inside a fixed algebraic closure and records the exact `Prop`
for its independence.  The map clause will be added only after the coherent
infinite unit action and arithmetic Frobenius on `K^un` have been constructed.
-/

namespace Submission.CField.LTate

noncomputable section

open Submission.NumberTheory.Milne

universe u v w

namespace LTDatum

variable (A : Type u) (K : Type v) (Omega : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field Omega] [Algebra K Omega] [Algebra A Omega]
  [IsScalarTower A K Omega] [IsAlgClosure K Omega]

/-- The field `K_pi * K^un` in Theorem I.3.9, realized as the compositum of
the infinite Lubin--Tate torsion field and the maximal unramified intermediate
field inside the same algebraic closure. -/
def lubinUnramifiedComposite (D : LTDatum A) :
    IntermediateField K Omega :=
  D.infiniteTorsionField K Omega ⊔
    maximalAlgebraicClosure A K Omega

omit [IsAlgClosure K Omega] in
/-- The compositum is the directed supremum of the finite Lubin--Tate levels
after adjoining the fixed maximal unramified field. -/
theorem composite_i_sup
    (D : LTDatum A) :
    D.lubinUnramifiedComposite A K Omega =
      ⨆ n, D.torsionLevelField K Omega n ⊔
        maximalAlgebraicClosure A K Omega := by
  rw [lubinUnramifiedComposite, infiniteTorsionField, iSup_sup]

omit [IsAlgClosure K Omega] in
/-- Every finite Lubin--Tate level lies in the compositum of Theorem I.3.9. -/
theorem torsion_lubin_composite
    (D : LTDatum A) (n : ℕ) :
    D.torsionLevelField K Omega n ≤
      D.lubinUnramifiedComposite A K Omega := by
  exact le_trans (le_iSup (D.torsionLevelField K Omega) n) le_sup_left

omit [IsAlgClosure K Omega] in
/-- The maximal unramified extension lies in the compositum of
Theorem I.3.9. -/
theorem maximal_lubin_composite
    (D : LTDatum A) :
    maximalAlgebraicClosure A K Omega ≤
      D.lubinUnramifiedComposite A K Omega :=
  le_sup_right

/-- The field-independence clause of Theorem I.3.9.  Quantifying over all
polynomial Lubin--Tate data makes explicit that the field is independent of
both the chosen prime element and the auxiliary Lubin--Tate series. -/
def LubinCompositeIndependence : Prop :=
  ∀ D D' : LTDatum A,
    D.lubinUnramifiedComposite A K Omega =
      D'.lubinUnramifiedComposite A K Omega

end LTDatum

end

end Submission.CField.LTate

import Submission.ClassField.HasseNorm.QuadraticForms
import Submission.ClassField.Ideles.GlobalPlace
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-! # Chapter VIII, Section 3, Theorem 3.5 (Hasse--Minkowski) -/

namespace Submission.CField.HNorm

open scoped TensorProduct
open NumberField
open Submission.CField.Ideles

noncomputable section
universe u

/-- Scalar extension of a quadratic form to one completion. -/
noncomputable def quadraticFormPlace
    (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (v : NumberFieldPlace K) :
    QuadraticForm (placeCompletion K v)
      (placeCompletion K v ⊗[K] V) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  exact Q.baseChange (placeCompletion K v)

/-- **Theorem VIII.3.5(a).** -/
def MinkowskiAlmostEverywhere : Prop :=
  ∀ (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    Q.Nondegenerate → 3 ≤ Module.finrank K V →
      ∃ S : Finset (NumberFieldPlace K),
        ∀ v, v ∉ S → Represents (quadraticFormPlace K V Q v) 0

/-- **Theorem VIII.3.5(b).** -/
def HasseMinkowskiGlobal : Prop :=
  ∀ (K V : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    Q.Nondegenerate →
      (∀ v, Represents (quadraticFormPlace K V Q v) 0) →
      Represents Q 0

theorem of_two_clauses
    (ha : MinkowskiAlmostEverywhere.{u})
    (hb : HasseMinkowskiGlobal.{u}) :
    (MinkowskiAlmostEverywhere.{u} ∧ HasseMinkowskiGlobal.{u}) :=
  ⟨ha, hb⟩

end
end Submission.CField.HNorm

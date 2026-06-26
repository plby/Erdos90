import Submission.ClassField.QuadraticForms.QOrthogonal
import Submission.ClassField.HasseNorm.QuadraticFormPlace

/-! # Chapter VIII, Section 6, Theorem 6.3 -/

namespace Submission.CField.QForms

open NumberField
open Submission.CField.Ideles
open Submission.CField.HNorm

noncomputable section
universe u

/-- Two quadratic forms become equivalent at a place after scalar extension
to the corresponding completion. -/
def QuadraticFormsEquivalent
    (K V W : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (v : NumberFieldPlace K) : Prop :=
  Nonempty
    ((quadraticFormPlace K V Q v).IsometryEquiv
      (quadraticFormPlace K W Q' v))

/-- Proposition 6.2 packaged at the universe used by this section. -/
def FormsEquivalent : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V],
    (∀ (Q : QuadraticForm k V) (U W : Submodule k V),
          (Q.restrict U).Nondegenerate →
          Nonempty ((Q.restrict U).IsometryEquiv (Q.restrict W)) →
          Nonempty
            ((Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin U)).IsometryEquiv
              (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W))))

/-- The rank induction in Milne's proof, isolated from its two mathematical
inputs: the local-global isotropy theorem 3.5 and cancellation 6.2.  It only
handles the nondegenerate case, exactly as the body of the source proof does. -/
def NondegenerateInductionBridge : Prop :=
  (MinkowskiAlmostEverywhere.{u} ∧ HasseMinkowskiGlobal.{u}) →
  FormsEquivalent.{u} →
  ∀ (K V W : Type u) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K V) (Q' : QuadraticForm K W),
    Q.Nondegenerate → Q'.Nondegenerate →
    (∀ v, QuadraticFormsEquivalent K V W Q Q' v) →
    Nonempty (Q.IsometryEquiv Q')

/-- The preliminary “we may suppose the forms are nondegenerate” reduction.
It is stated as a reusable lifting principle and does not assume the desired
theorem outright. -/
def NonsingularReductionBridge : Prop :=
  (∀ (K V W : Type u) [Field K] [NumberField K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (Q : QuadraticForm K V) (Q' : QuadraticForm K W),
      Q.Nondegenerate → Q'.Nondegenerate →
      (∀ v, QuadraticFormsEquivalent K V W Q Q' v) →
      Nonempty (Q.IsometryEquiv Q')) →
    (∀ (K V W : Type u) [Field K] [NumberField K]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          [AddCommGroup W] [Module K W] [FiniteDimensional K W]
          (Q : QuadraticForm K V) (Q' : QuadraticForm K W),
          (∀ v, QuadraticFormsEquivalent K V W Q Q' v) →
          Nonempty (Q.IsometryEquiv Q'))

/-- The exact source theorem follows once the two explicitly identified
linear-algebra orchestration steps and the earlier numbered inputs are
available. -/
theorem of_induction
    (h35 : (MinkowskiAlmostEverywhere.{u} ∧ HasseMinkowskiGlobal.{u}))
    (h62 : FormsEquivalent.{u})
    (hInduction : NondegenerateInductionBridge.{u})
    (hReduction : NonsingularReductionBridge.{u}) :
    (∀ (K V W : Type u) [Field K] [NumberField K]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          [AddCommGroup W] [Module K W] [FiniteDimensional K W]
          (Q : QuadraticForm K V) (Q' : QuadraticForm K W),
          (∀ v, QuadraticFormsEquivalent K V W Q Q' v) →
          Nonempty (Q.IsometryEquiv Q')) :=
  hReduction (hInduction h35 h62)

end
end Submission.CField.QForms

import Submission.ClassField.QuadraticForms.Cancellation
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-! # Chapter VIII, Section 6, Proposition 6.2 -/

namespace Submission.CField.QForms

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

private abbrev QOrthogonal (Q : QuadraticForm k V) (U : Submodule k V) :
    Submodule k V :=
  LinearMap.BilinForm.orthogonal Q.polarBilin U

/-- Universe-polymorphic packaging of Proposition 6.2 for use as an input to
later theorems. -/
def UniversalOrthogonalDecomposition : Prop :=
  ∀ (k V : Type*) [Field k] [AddCommGroup V] [Module k V],
    (∀ (Q : QuadraticForm k V) (U W : Submodule k V),
          (Q.restrict U).Nondegenerate →
          Nonempty ((Q.restrict U).IsometryEquiv (Q.restrict W)) →
          Nonempty
            ((Q.restrict (QOrthogonal Q U)).IsometryEquiv
              (Q.restrict (QOrthogonal Q W))))

/-- The missing Witt-extension step, stated independently of the desired
complement conclusion.  It says that the given subspace isometry extends far
enough to an ambient isometry carrying `U` onto `W`. -/
def WittExtensionBridge : Prop :=
  ∀ (Q : QuadraticForm k V) (U W : Submodule k V)
    (_ : (Q.restrict U).IsometryEquiv (Q.restrict W)),
    (Q.restrict U).Nondegenerate →
    ∃ F : Q.IsometryEquiv Q,
      U.map F.toLinearEquiv.toLinearMap = W

/-- Proposition 6.2 follows from the Witt-extension step and the already
proved restriction of an ambient isometry to orthogonal complements. -/
theorem of_wittExtension
    (hWitt : WittExtensionBridge (k := k) (V := V)) :
    (∀ (Q : QuadraticForm k V) (U W : Submodule k V),
          (Q.restrict U).Nondegenerate →
          Nonempty ((Q.restrict U).IsometryEquiv (Q.restrict W)) →
          Nonempty
            ((Q.restrict (QOrthogonal Q U)).IsometryEquiv
              (Q.restrict (QOrthogonal Q W)))) := by
  intro Q U W hnondegenerate hisometric
  obtain ⟨f⟩ := hisometric
  obtain ⟨F, hF⟩ := hWitt Q U W f hnondegenerate
  exact ⟨of_ambient_isometry Q F U W hF⟩

end Submission.CField.QForms

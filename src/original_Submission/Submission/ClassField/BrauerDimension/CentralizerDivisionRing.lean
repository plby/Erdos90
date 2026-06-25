import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Submission.ClassField.BrauerDimension.CentralizerAlgRing

/-!
# Chapter IV, Section 5, Theorem 5.3: source-facing statement

Milne assumes that `V` is finite-dimensional over the base field, rather
than merely finitely generated over the acting algebra.  This file exposes
that interface and records that the division rings in the Wedderburn
decomposition are themselves finite-dimensional over the base field.
-/

namespace Submission.CField.BDim

universe u

variable (k A V : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSemisimpleModule A V] [Module.Finite k V]

/-- The source-facing form of Milne's Theorem IV.5.3.  The hypotheses encode
the `k`-algebra action of `A` on the finite-dimensional `k`-space `V`.
The centralizer `Module.End A V` is a finite product of matrix algebras over
division `k`-algebras which are finite-dimensional over `k`. -/
theorem centralizer_matrix_division :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ)
      (_ : ∀ i, DivisionRing (D i)) (_ : ∀ i, Algebra k (D i))
      (_ : ∀ i, Module.Finite k (D i)),
      (∀ i, NeZero (d i)) ∧
        Nonempty
          (Module.End A V ≃ₐ[k]
            ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  classical
  letI : Module.Finite A V :=
    Module.Finite.of_restrictScalars_finite k A V
  obtain ⟨n, S, d, hS, hd, ⟨e⟩⟩ :=
    IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end k A V
  letI (i : Fin n) : IsSimpleModule A (S i) := hS i
  letI (i : Fin n) : Module.Finite k (S i) :=
    Module.Finite.of_injective ((S i).subtype.restrictScalars k)
      (S i).subtype_injective
  have hfinite (i : Fin n) : Module.Finite k (Module.End A (S i)) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ k A (S i) (S i) k)
      (LinearMap.restrictScalars_injective k)
  exact ⟨n, fun i ↦ Module.End A (S i), d,
    (fun _ ↦ inferInstance), (fun _ ↦ inferInstance), hfinite, hd, ⟨e⟩⟩

/-- In particular, the factors in the preceding decomposition really are
finite-dimensional simple `k`-algebras, as in Milne's wording. -/
theorem centralizer_pi_simple :
    ∃ (n : ℕ) (B : Fin n → Type u)
      (_ : ∀ i, Ring (B i)) (_ : ∀ i, Algebra k (B i))
      (_ : ∀ i, IsSimpleRing (B i)) (_ : ∀ i, Module.Finite k (B i)),
      Nonempty (Module.End A V ≃ₐ[k] ∀ i, B i) := by
  classical
  obtain ⟨n, D, d, hDdiv, hDalg, hDfinite, hd, ⟨e⟩⟩ :=
    centralizer_matrix_division k A V
  letI (i : Fin n) : DivisionRing (D i) := hDdiv i
  letI (i : Fin n) : Algebra k (D i) := hDalg i
  letI (i : Fin n) : Module.Finite k (D i) := hDfinite i
  letI (i : Fin n) : NeZero (d i) := hd i
  exact ⟨n, fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i),
    (fun _ ↦ inferInstance), (fun _ ↦ inferInstance),
    (fun _ ↦ inferInstance), (fun _ ↦ inferInstance), ⟨e⟩⟩

end Submission.CField.BDim

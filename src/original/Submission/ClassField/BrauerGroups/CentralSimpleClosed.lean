import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Submission.ClassField.BrauerGroups.BrauerGroup
import Submission.ClassField.BrauerGroups.CentralMatrix


/-!
# Chapter IV, Example 2.14

We record the two vanishing examples that follow directly from
Wedderburn--Artin and results already available in Mathlib: algebraically
closed fields and finite fields.  The real, local-field, and number-field
computations are deferred to the later sections cited by Milne.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

omit [Algebra.IsCentral k A] in
/-- Example IV.2.14(a): over an algebraically closed field, every central
simple algebra is a matrix algebra over the base field. -/
theorem simple_matrix_closed [IsAlgClosed k] :
    ∃ (n : ℕ) (_ : NeZero n),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k) :=
  IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k A

/-- Example IV.2.14(c): over a finite field, every central simple algebra is a
matrix algebra over the base field. -/
theorem simple_alg_matrix [Finite k] :
    ∃ (n : ℕ) (_ : NeZero n),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, D, hDdiv, hDalg, hDfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero n := hn
  letI : DivisionRing D := hDdiv
  letI : Algebra k D := hDalg
  letI : Module.Finite k D := hDfin
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv k A _ e
  letI : Algebra.IsCentral k (D ⊗[k] Matrix (Fin n) (Fin n) k) :=
    Algebra.IsCentral.of_algEquiv k _ _ (matrixEquivTensor (Fin n) k D)
  letI : Algebra.IsCentral k D :=
    Algebra.IsCentral.left_of_tensor_of_field k D (Matrix (Fin n) (Fin n) k)
  letI : Finite D := Module.finite_of_finite k
  letI : Field D := littleWedderburn D
  have hbij : Function.Bijective (algebraMap k D) :=
    Algebra.IsCentral.baseField_essentially_unique k D D
  let ekD : k ≃ₐ[k] D := AlgEquiv.ofBijective (Algebra.ofId k D) hbij
  exact ⟨n, hn, ⟨e.trans ekD.symm.mapMatrix⟩⟩

/-- Example IV.2.14(a): the Brauer quotient of an algebraically closed field
is trivial. -/
theorem brauer_subsingleton_closed [IsAlgClosed k] :
    Subsingleton (BrauerGroup.{u, u} k) :=
  subsingleton_matrix_classification k fun A => by
    obtain ⟨n, hn, e⟩ := simple_matrix_closed k A
    exact ⟨n, hn.out, e⟩

/-- Example IV.2.14(c): the Brauer quotient of a finite field is trivial. -/
theorem brauer_subsingleton_field [Finite k] :
    Subsingleton (BrauerGroup.{u, u} k) :=
  subsingleton_matrix_classification k fun A => by
    obtain ⟨n, hn, e⟩ := simple_alg_matrix k A
    exact ⟨n, hn.out, e⟩

end Submission.CField.BGroups

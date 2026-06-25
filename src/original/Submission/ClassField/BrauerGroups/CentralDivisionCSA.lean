import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Submission.ClassField.SimpleAlgebras.NaturalRightMul
import Submission.ClassField.BrauerGroups.BrauerGroup
import Submission.ClassField.BrauerGroups.TensorMatrixEquiv

/-!
# Chapter IV, Remark 2.13

The division-algebra representative of a Brauer class is unique.  More
precisely, two finite-dimensional central division algebras are Brauer
equivalent if and only if they are isomorphic as algebras over the base field.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

universe u v

variable (k : Type u) [Field k]

private theorem central_matrix
    {D : Type v} [DivisionRing D] [Algebra k D]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (h : Algebra.IsCentral k (Matrix n n D)) : Algebra.IsCentral k D := by
  letI : Algebra.IsCentral k (Matrix n n D) := h
  constructor
  intro z hz
  have hz' : Matrix.scalar n z ∈ Subalgebra.center k (Matrix n n D) := by
    rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
    exact ⟨z, hz, rfl⟩
  have hzbot := Algebra.IsCentral.out hz'
  rw [Algebra.mem_bot] at hzbot ⊢
  obtain ⟨c, hc⟩ := hzbot
  refine ⟨c, ?_⟩
  let i : n := Classical.arbitrary n
  have hii := congrFun (congrFun hc i) i
  change (if i = i then algebraMap k D c else 0) =
    (if i = i then z else 0) at hii
  simpa using hii

/-- Package a finite-dimensional central division algebra as a member of
Mathlib's type of central simple algebras. -/
def centralDivisionCSA (D : Type v) [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k D] [Module.Finite k D] : CSA.{u, v} k where
  toAlgCat := AlgCat.of k D
  isCentral := inferInstance
  isSimple := inferInstance
  fin_dim := inferInstance

/-- **Remark IV.2.13(a), existence.** Every finite-dimensional central simple
algebra is a matrix algebra over a finite-dimensional central division
algebra. -/
theorem matrix_division_algebra
    (A : Type v) [Ring A] [Algebra k A]
    [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type v)
      (_ : DivisionRing D) (_ : Algebra k D)
      (_ : Algebra.IsCentral k D) (_ : Module.Finite k D),
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, D, hDdiv, hDalg, hDfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero n := hn
  letI : DivisionRing D := hDdiv
  letI : Algebra k D := hDalg
  letI : Module.Finite k D := hDfin
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv k A _ e
  letI : Algebra.IsCentral k D :=
    central_matrix k
      (inferInstance : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D))
  exact ⟨n, hn, D, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨e⟩⟩

/-- Every Brauer class has a representative which is a finite-dimensional
central division algebra. -/
theorem division_brauer_representative
    (A : CSA.{u, v} k) :
    ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D)
      (_ : Algebra.IsCentral k D) (_ : Module.Finite k D),
      IsBrauerEquivalent A (centralDivisionCSA k D) := by
  obtain ⟨n, hn, D, hDdiv, hDalg, hDcentral, hDfin, ⟨e⟩⟩ :=
    matrix_division_algebra k A
  letI : NeZero n := hn
  letI : DivisionRing D := hDdiv
  letI : Algebra k D := hDalg
  letI : Algebra.IsCentral k D := hDcentral
  letI : Module.Finite k D := hDfin
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    1, n, one_ne_zero, NeZero.ne n, ?_⟩
  exact ⟨(matrixFinAlg k A).trans e⟩

/-- Milne, Remark IV.2.13(a), uniqueness of the central division-algebra
representative of a Brauer class. -/
theorem division_brauer_equivalent
    (D E : Type v) [DivisionRing D] [DivisionRing E]
    [Algebra k D] [Algebra k E]
    [Algebra.IsCentral k D] [Algebra.IsCentral k E]
    [Module.Finite k D] [Module.Finite k E] :
    IsBrauerEquivalent (centralDivisionCSA k D) (centralDivisionCSA k E) ↔
      Nonempty (D ≃ₐ[k] E) := by
  constructor
  · rintro ⟨n, m, hn, hm, ⟨e⟩⟩
    letI : NeZero n := ⟨hn⟩
    letI : NeZero m := ⟨hm⟩
    letI : IsArtinianRing (Matrix (Fin n) (Fin n) D) :=
      IsArtinianRing.of_finite k (Matrix (Fin n) (Fin n) D)
    exact (SAlgebr.wedderburn_presentation_unique
      k (Matrix (Fin n) (Fin n) D) D E n m (AlgEquiv.refl) e).2
  · rintro ⟨e⟩
    exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

end Submission.CField.BGroups

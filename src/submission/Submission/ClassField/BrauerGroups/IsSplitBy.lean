import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import Submission.ClassField.BrauerGroups.FinrankSimpleSquare
import Submission.ClassField.BrauerGroups.CentralSimpleClosed

/-!
# Chapter IV, Proposition 2.17

Every finite-dimensional central simple algebra is split by a finite extension
contained in a fixed algebraic closure of the base field.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

noncomputable section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A field extension splits an algebra when its scalar extension is a full
matrix algebra. -/
def ISBy (k K A : Type u) [Field k] [Field K] [Ring A]
    [Algebra k K] [Algebra k A] : Prop :=
  ∃ (n : ℕ) (_ : NeZero n),
    Nonempty (A ⊗[k] K ≃ₐ[K] Matrix (Fin n) (Fin n) K)

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

set_option maxHeartbeats 400000 in
-- The proof elaborates a finite family of matrix coefficients and its descended algebra map.
/-- Milne, Proposition IV.2.17: every central simple algebra over `k` is split
by a finite extension of `k` inside `AlgebraicClosure k`. -/
theorem finite_splitting_field :
    ∃ K : IntermediateField k (AlgebraicClosure k),
      FiniteDimensional k K ∧ ISBy k K A := by
  let C := AlgebraicClosure k
  have hCSA := scalar_extension_simple k C A
  letI : IsSimpleRing (A ⊗[k] C) := hCSA.1
  letI : Algebra.IsCentral C (A ⊗[k] C) := hCSA.2
  letI : Module.Finite C (C ⊗[k] A) := Module.Finite.base_change k C A
  letI : Module.Finite C (A ⊗[k] C) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight k C A).toLinearEquiv
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    simple_matrix_closed C (A ⊗[k] C)
  let b := Module.finBasis k A
  let g : A →ₐ[k] Matrix (Fin n) (Fin n) C :=
    (e.restrictScalars k).toAlgHom.comp Algebra.TensorProduct.includeLeft
  let coeffs : Set C := Set.range fun x : Fin (Module.finrank k A) × Fin n × Fin n =>
    g (b x.1) x.2.1 x.2.2
  have hcoeffs : coeffs.Finite := Set.finite_range _
  letI : Fintype coeffs := hcoeffs.fintype
  let K := IntermediateField.adjoin k coeffs
  have hKfinite : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  letI : FiniteDimensional k K := hKfinite
  let gb : Fin (Module.finrank k A) → Matrix (Fin n) (Fin n) K := fun i p q =>
    ⟨g (b i) p q, IntermediateField.subset_adjoin k coeffs ⟨(i, p, q), rfl⟩⟩
  let gLin : A →ₗ[k] Matrix (Fin n) (Fin n) K := b.constr k gb
  have gLin_map_linear :
      K.val.mapMatrix.toLinearMap.comp gLin = g.toLinearMap := by
    apply b.ext
    intro i
    ext p q
    simp [gLin, gb]
  have gLin_map (a : A) : K.val.mapMatrix (gLin a) = g a :=
    DFunLike.congr_fun gLin_map_linear a
  let gK : A →ₐ[k] Matrix (Fin n) (Fin n) K :=
    { toFun := gLin
      map_zero' := gLin.map_zero
      map_add' := gLin.map_add
      map_one' := by
        apply K.val.mapMatrix.injective
        exact
          (gLin_map 1).trans <| g.map_one.trans K.val.mapMatrix.map_one.symm
      map_mul' := by
        intro x y
        apply K.val.mapMatrix.injective
        exact (gLin_map (x * y)).trans <| (g.map_mul x y).trans <|
          congrArg₂ (fun X Y => X * Y) (gLin_map x).symm (gLin_map y).symm |>.trans
            (K.val.mapMatrix.map_mul (gLin x) (gLin y)).symm
      commutes' := by
        intro r
        apply K.val.mapMatrix.injective
        exact (gLin_map (algebraMap k A r)).trans <| (g.commutes r).trans <|
          (K.val.mapMatrix.commutes r).symm }
  let f : K ⊗[k] A →ₐ[K] Matrix (Fin n) (Fin n) K :=
    (AlgHom.liftEquiv k K A (Matrix (Fin n) (Fin n) K)) gK
  letI : IsSimpleRing (K ⊗[k] A) :=
    tensor_simple_right (k := k) (A := K) (B := A)
  letI : Module.Finite K (K ⊗[k] A) := Module.Finite.base_change k K A
  have hinj : Function.Injective f := f.toRingHom.injective
  have hdimC : Module.finrank k A = n ^ 2 := by
    calc
      Module.finrank k A = Module.finrank C (C ⊗[k] A) :=
        Module.finrank_baseChange.symm
      _ = Module.finrank C (A ⊗[k] C) :=
        (Algebra.TensorProduct.commRight k C A).toLinearEquiv.finrank_eq
      _ = Module.finrank C (Matrix (Fin n) (Fin n) C) :=
        e.toLinearEquiv.finrank_eq
      _ = n ^ 2 := by simp [Module.finrank_matrix, pow_two]
  have hdim :
      Module.finrank K (K ⊗[k] A) =
        Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    calc
      Module.finrank K (K ⊗[k] A) = Module.finrank k A :=
        Module.finrank_baseChange
      _ = n ^ 2 := hdimC
      _ = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
        simp [Module.finrank_matrix, pow_two]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨K, hKfinite, n, hn, ?_⟩
  let eK : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
    AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  exact ⟨(Algebra.TensorProduct.commRight k K A).symm.trans eK⟩

end

end Submission.CField.BGroups

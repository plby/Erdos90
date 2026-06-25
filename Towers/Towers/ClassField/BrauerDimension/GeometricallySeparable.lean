import Mathlib
import Towers.NumberTheory.FieldExtensions.SeparableTensorProduct
import Towers.ClassField.BrauerGroups.ScalarExtensionCentral

/-!
# Chapter IV, Section 5, Proposition 5.6 (source statement)

Milne's proposition says that scalar extension along an arbitrary separable
field extension preserves finite-dimensional semisimple algebras.
-/

namespace Towers.CField.BDim

open scoped TensorProduct

noncomputable section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Algebra.TensorProduct.leftAlgebra

/-- The central-simple case of Proposition IV.5.6 does not require either
separability or finite-dimensionality of the scalar field extension. -/
theorem scalar_semisimple_simple
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A] :
    IsSemisimpleRing (A ⊗[k] K) := by
  letI : IsSimpleRing (A ⊗[k] K) :=
    BGroups.tensor_simple_ring k A K
  letI : Module.Finite K (A ⊗[k] K) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight k K A).toLinearEquiv
  letI : IsArtinianRing (A ⊗[k] K) :=
    IsArtinianRing.of_finite K (A ⊗[k] K)
  exact IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance

private theorem geometrically_reduced_separable
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] :
    Algebra.IsGeometricallyReduced k K := by
  apply Algebra.IsGeometricallyReduced.of_forall_fg
  intro B hB
  letI : Field B := (Subalgebra.isField_of_algebraic (A := B)).toField
  letI : Algebra.FiniteType k B :=
    { out := (Subalgebra.fg_top B).mpr hB }
  letI : Algebra.IsAlgebraic k B := Algebra.IsAlgebraic.tower_bot k B K
  letI : Module.Finite k B :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : Algebra.IsSeparable k B :=
    Algebra.IsSeparable.of_algHom (F := k) K B.val
  rcases
      Towers.NumberTheory.Milne.tensor_pi_separable
        k B (AlgebraicClosure k) with
    ⟨ι, hι, L, hL, hAlg, e, hfin⟩
  letI : Finite ι := hι
  letI : ∀ i, Field (L i) := hL
  letI : ∀ i, Algebra (AlgebraicClosure k) (L i) := hAlg
  let e' : (AlgebraicClosure k ⊗[k] B) ≃ₐ[AlgebraicClosure k]
      ((i : ι) → L i) :=
    (Algebra.TensorProduct.commRight k (AlgebraicClosure k) B).trans e
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_of_injective e'.toRingEquiv e'.toRingEquiv.injective

private theorem simple_semisimple_reduced
    (F R A : Type u) [Field F] [CommRing R] [Algebra F R]
    [IsArtinianRing R] [IsReduced R]
    [Ring A] [Algebra F A] [IsSimpleRing A] [Algebra.IsCentral F A]
    [Module.Finite F A] :
    IsSemisimpleRing (A ⊗[F] R) := by
  classical
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  letI (I : MaximalSpectrum R) : Field (R ⧸ I.asIdeal) :=
    Ideal.Quotient.field I.asIdeal
  let quotientAlgebra (I : MaximalSpectrum R) : Algebra F (R ⧸ I.asIdeal) :=
    (Ideal.Quotient.mk I.asIdeal).comp (algebraMap F R) |>.toAlgebra
  letI (I : MaximalSpectrum R) : Algebra F (R ⧸ I.asIdeal) :=
    quotientAlgebra I
  letI (I : MaximalSpectrum R) : SMul F (R ⧸ I.asIdeal) :=
    (quotientAlgebra I).toSMul
  letI (I : MaximalSpectrum R) : Module F (R ⧸ I.asIdeal) :=
    (quotientAlgebra I).toModule
  letI : Algebra F ((I : MaximalSpectrum R) → R ⧸ I.asIdeal) :=
    Pi.algebra (MaximalSpectrum R) (fun I ↦ R ⧸ I.asIdeal)
  let eR : R ≃ₐ[F] ((I : MaximalSpectrum R) → R ⧸ I.asIdeal) :=
    { __ := (IsArtinianRing.equivPi R).toRingEquiv
      commutes' := fun _ ↦ rfl }
  let e : (A ⊗[F] R) ≃ₐ[F]
      ((I : MaximalSpectrum R) → A ⊗[F] (R ⧸ I.asIdeal)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A) eR).trans
      (Algebra.TensorProduct.piRight F F A
        (fun I : MaximalSpectrum R ↦ R ⧸ I.asIdeal))
  letI (I : MaximalSpectrum R) :
      IsSemisimpleRing (A ⊗[F] (R ⧸ I.asIdeal)) :=
    scalar_semisimple_simple F (R ⧸ I.asIdeal) A
  exact e.symm.toRingEquiv.isSemisimpleRing

private def cancelChangeNoncomm
    (k F A K : Type u) [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K]
    [Ring A] [Algebra k A] [Algebra F A] [IsScalarTower k F A] :
    (A ⊗[F] (F ⊗[k] K)) ≃ₐ[F] (A ⊗[k] K) :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k F F A K).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

private theorem semisimple_ring_simple
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Module.Finite k A] :
    IsSemisimpleRing (A ⊗[k] K) := by
  let F := Subring.center A
  let centerField : Field F := (IsSimpleRing.isField_center A).toField
  letI : Field F := centerField
  letI : CommRing F := centerField.toCommRing
  letI : Ring F := centerField.toRing
  letI : Semiring F := centerField.toSemiring
  let kToCenter : k →+* F :=
    { toFun := fun x ↦ ⟨algebraMap k A x, Set.algebraMap_mem_center x⟩
      map_one' := by
        apply Subtype.ext
        change algebraMap k A 1 = 1
        simp
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        change algebraMap k A (x * y) = algebraMap k A x * algebraMap k A y
        simp
      map_zero' := by
        apply Subtype.ext
        change algebraMap k A 0 = 0
        simp
      map_add' := fun x y ↦ by
        apply Subtype.ext
        change algebraMap k A (x + y) = algebraMap k A x + algebraMap k A y
        simp }
  let centerBaseAlgebra : Algebra k F := kToCenter.toAlgebra
  let centerAlgebra : Algebra F A :=
    F.subtype.toAlgebra' fun c x ↦ by
      have hc : (c : A) ∈ Subring.center A := c.property
      rw [Subring.mem_center_iff] at hc
      exact (hc x).symm
  letI : Algebra k F := centerBaseAlgebra
  letI : SMul k F := centerBaseAlgebra.toSMul
  letI : Module k F := centerBaseAlgebra.toModule
  letI : Algebra F A := centerAlgebra
  letI : SMul F A := centerAlgebra.toSMul
  letI : Module F A := centerAlgebra.toModule
  letI : IsScalarTower k F A := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rfl
  let centerInclusion : F →ₐ[k] A :=
    { F.subtype with commutes' := fun _ ↦ rfl }
  letI : Module.Finite k F :=
    Module.Finite.of_injective centerInclusion.toLinearMap Subtype.val_injective
  letI : Module.Finite F A :=
    Module.Finite.of_restrictScalars_finite k F A
  letI : Algebra.IsCentral F A := by
    constructor
    intro z hz
    rw [Subalgebra.mem_center_iff] at hz
    rw [Algebra.mem_bot]
    refine ⟨⟨z, ?_⟩, ?_⟩
    · rw [Subring.mem_center_iff]
      exact hz
    · rfl
  letI : Algebra.IsGeometricallyReduced k K :=
    geometrically_reduced_separable k K
  let R := F ⊗[k] K
  let baseScalarAlgebra : Algebra k K := inferInstance
  let tensorCommRing : CommRing R :=
    @Algebra.TensorProduct.instCommRing k F K _ _ centerBaseAlgebra _ baseScalarAlgebra
  letI : CommRing R := tensorCommRing
  let scalarAlgebra : Algebra K R :=
    @Algebra.TensorProduct.rightAlgebra k F K _ _ centerBaseAlgebra _ baseScalarAlgebra
  letI : Algebra K R := scalarAlgebra
  letI : SMul K R := scalarAlgebra.toSMul
  letI : Module K R := scalarAlgebra.toModule
  let centerTensorAlgebra : Algebra F R :=
    @Algebra.TensorProduct.leftAlgebra k F F K _ _ centerBaseAlgebra _
      baseScalarAlgebra _ (Algebra.id F) _
  letI : Algebra F R := centerTensorAlgebra
  letI : SMul F R := centerTensorAlgebra.toSMul
  letI : Module F R := centerTensorAlgebra.toModule
  letI : Algebra.IsAlgebraic k F := Algebra.IsAlgebraic.of_finite k F
  letI : IsReduced R :=
    isReduced_of_injective
      (Algebra.TensorProduct.map
        ((IsAlgClosed.lift : F →ₐ[k] AlgebraicClosure k)) 1)
      (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))
  letI : Module.Finite K (K ⊗[k] F) := Module.Finite.base_change k K F
  letI : Module.Finite K R :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight k K F).toLinearEquiv
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  let tensorARing : Ring (A ⊗[F] R) :=
    @Algebra.TensorProduct.instRing F A R _ _ centerAlgebra _ centerTensorAlgebra
  letI : Ring (A ⊗[F] R) := tensorARing
  letI : IsSemisimpleRing (A ⊗[F] R) :=
    simple_semisimple_reduced F R A
  exact (cancelChangeNoncomm k F A K).toRingEquiv.isSemisimpleRing

/-- Milne, Proposition IV.5.6: scalar extension by an arbitrary separable
field extension preserves every finite-dimensional semisimple algebra. -/
theorem scalar_semisimple_separable
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K]
    [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A] :
    IsSemisimpleRing (A ⊗[k] K) := by
  classical
  obtain ⟨n, D, d, hDiv, hAlg, hFin, hd, ⟨eA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite k A
  letI (i : Fin n) : DivisionRing (D i) := hDiv i
  letI (i : Fin n) : Algebra k (D i) := hAlg i
  letI (i : Fin n) : Module.Finite k (D i) := hFin i
  letI (i : Fin n) : NeZero (d i) := hd i
  let M : Fin n → Type u := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)
  let e : (A ⊗[k] K) ≃ₐ[k] ((i : Fin n) → M i ⊗[k] K) :=
    (Algebra.TensorProduct.congr eA (AlgEquiv.refl : K ≃ₐ[k] K)).trans <|
      (Algebra.TensorProduct.comm k ((i : Fin n) → M i) K).trans <|
        (Algebra.TensorProduct.piRight k k K M).trans <|
          AlgEquiv.piCongrRight fun i ↦ Algebra.TensorProduct.comm k K (M i)
  letI (i : Fin n) : IsSemisimpleRing (M i ⊗[k] K) :=
    semisimple_ring_simple k K (M i)
  exact e.symm.toRingEquiv.isSemisimpleRing

end

end Towers.CField.BDim

import Towers.NumberTheory.Completions.DifferentCompletionBasis
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# Comparing scalar extension with completed total quotient rings

The trace-dual basis calculation is naturally stated in `F ⊗[K] L`, while
the semilocal completion is first constructed as `C ⊗[R] S` and then
passed to a total quotient ring.  This file isolates the standard
localization and tensor-product equivalences connecting those presentations.
-/

namespace Towers.NumberTheory.Milne

open nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

section FractionFieldBaseChange

variable {R S K L : Type u}
  [CommRing R] [CommRing S] [Field K] [Field L]
  [Algebra R S] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [Algebra R L] [Algebra K L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]

/-- Localizing the right tensor factor identifies `K ⊗[R] S` with the
fraction field `L`.  Unlike the standard localization equivalence, this is
packaged as a `K`-algebra equivalence. -/
noncomputable def fractionTensorAlg : K ⊗[R] S ≃ₐ[K] L := by
  letI : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let eS : K ⊗[R] S ≃ₐ[S] L :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S R⁰) _ _
  refine AlgEquiv.ofRingEquiv (f := eS.toRingEquiv) ?_
  intro x
  have hhom : eS.toRingEquiv.toRingHom.comp (algebraMap K (K ⊗[R] S)) =
      algebraMap K L := by
    apply IsLocalization.ringHom_ext R⁰
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R K (K ⊗[R] S)]
    rw [IsScalarTower.algebraMap_apply R S (K ⊗[R] S)]
    change eS (algebraMap S (K ⊗[R] S) (algebraMap R S r)) = _
    rw [eS.commutes]
    rw [← IsScalarTower.algebraMap_apply R S L,
      ← IsScalarTower.algebraMap_apply R K L]
  exact DFunLike.congr_fun hhom x

@[simp]
theorem fraction_tmul_algebra
    (s : S) :
    fractionTensorAlg ((1 : K) ⊗ₜ[R] s) =
      algebraMap S L s := by
  letI : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  change (IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid S R⁰) (K ⊗[R] S) L)
        ((1 : K) ⊗ₜ[R] s) = algebraMap S L s
  rw [show (1 : K) ⊗ₜ[R] s = algebraMap S (K ⊗[R] S) s by rfl]
  exact (IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid S R⁰) (K ⊗[R] S) L).commutes s

@[simp]
theorem fraction_tensor_algebra
    (s : S) :
    (fractionTensorAlg (R := R) (S := S) (K := K) (L := L)).symm
        (algebraMap S L s) = (1 : K) ⊗ₜ[R] s := by
  apply (fractionTensorAlg
    (R := R) (S := S) (K := K) (L := L)).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (fraction_tmul_algebra
    (R := R) (S := S) (K := K) (L := L) s).symm

variable {F : Type u} [Field F] [Algebra R F] [Algebra K F]
  [IsScalarTower R K F]

/-- Extending `L/K` to an overfield `F` is the same algebra as extending
the integral model `S/R` directly to `F`. -/
noncomputable def scalarExtensionFraction :
    F ⊗[K] L ≃ₐ[F] F ⊗[R] S :=
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl : F ≃ₐ[F] F)
      (fractionTensorAlg (R := R) (S := S) (K := K) (L := L)).symm).trans
    (Algebra.TensorProduct.cancelBaseChange R K F F S)

@[simp]
theorem scalar_tmul_algebra
    (f : F) (s : S) :
    scalarExtensionFraction
        (f ⊗ₜ[K] algebraMap S L s) = f ⊗ₜ[R] s := by
  simp [scalarExtensionFraction,
    fraction_tensor_algebra]

end FractionFieldBaseChange

section LocalizationTarget

variable {C F B Q : Type u}
  [CommRing C] [IsDomain C] [Field F] [Algebra C F] [IsFractionRing C F]
  [CommRing B] [Algebra C B]
  [CommRing Q] [Algebra B Q] [Algebra C Q] [IsScalarTower C B Q]
  [Algebra F Q] [IsScalarTower C F Q]
  [IsLocalization (Algebra.algebraMapSubmonoid B C⁰) Q]

/-- If `Q` is obtained from `B` by inverting the image of the nonzero
elements of `C`, then `Q` is the scalar extension `F ⊗[C] B` as an
`F`-algebra. -/
noncomputable def fractionTensorLocalization :
    F ⊗[C] B ≃ₐ[F] Q := by
  letI : Algebra B (F ⊗[C] B) := Algebra.TensorProduct.rightAlgebra
  let eB : F ⊗[C] B ≃ₐ[B] Q :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B C⁰) _ _
  refine AlgEquiv.ofRingEquiv (f := eB.toRingEquiv) ?_
  intro x
  have hhom : eB.toRingEquiv.toRingHom.comp (algebraMap F (F ⊗[C] B)) =
      algebraMap F Q := by
    apply IsLocalization.ringHom_ext C⁰
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply C F (F ⊗[C] B)]
    rw [IsScalarTower.algebraMap_apply C B (F ⊗[C] B)]
    change eB (algebraMap B (F ⊗[C] B) (algebraMap C B c)) = _
    rw [eB.commutes]
    rw [← IsScalarTower.algebraMap_apply C F Q,
      ← IsScalarTower.algebraMap_apply C B Q]
  exact DFunLike.congr_fun hhom x

omit [IsDomain C] in
@[simp]
theorem fraction_localization_tmul
    (f : F) (b : B) :
    fractionTensorLocalization (f ⊗ₜ[C] b) =
      algebraMap F Q f * algebraMap B Q b := by
  letI : Algebra B (F ⊗[C] B) := Algebra.TensorProduct.rightAlgebra
  rw [show f ⊗ₜ[C] b =
      algebraMap F (F ⊗[C] B) f * algebraMap B (F ⊗[C] B) b by
    rw [Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.right_algebraMap_apply]
    simp]
  rw [map_mul]
  rw [(fractionTensorLocalization (C := C)
    (F := F) (B := B) (Q := Q)).commutes]
  congr 1
  change (IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid B C⁰) (F ⊗[C] B) Q)
      (algebraMap B (F ⊗[C] B) b) = algebraMap B Q b
  exact (IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid B C⁰) (F ⊗[C] B) Q).commutes b

end LocalizationTarget

section CompletedTensor

variable {R S K L C F Q : Type u}
  [CommRing R] [CommRing S] [Field K] [Field L]
  [Algebra R S] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [Algebra R L] [Algebra K L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
  [CommRing C] [IsDomain C] [Algebra R C]
  [Field F] [Algebra C F] [IsFractionRing C F]
  [Algebra R F] [IsScalarTower R C F]
  [Algebra K F] [IsScalarTower R K F]

/-- Before taking a total quotient ring, the scalar-extension algebra is
canonically the localization of the completed tensor algebra at `C⁰`. -/
noncomputable def scalarLocalizationTensor :
    F ⊗[K] L ≃ₐ[F] F ⊗[C] (C ⊗[R] S) :=
  (scalarExtensionFraction
      (R := R) (S := S) (K := K) (L := L) (F := F)).trans
    (Algebra.TensorProduct.cancelBaseChange R C F F S).symm

omit [IsDomain C] [IsFractionRing C F] in
@[simp]
theorem scalar_localization_tmul
    (f : F) (s : S) :
    scalarLocalizationTensor
        (f ⊗ₜ[K] algebraMap S L s) =
      f ⊗ₜ[C] ((1 : C) ⊗ₜ[R] s) := by
  simp [scalarLocalizationTensor,
    scalar_tmul_algebra]

variable [CommRing Q] [Algebra (C ⊗[R] S) Q]
  [Algebra C Q] [IsScalarTower C (C ⊗[R] S) Q]
  [Algebra F Q] [IsScalarTower C F Q]
  [IsLocalization
    (Algebra.algebraMapSubmonoid (C ⊗[R] S) C⁰) Q]

/-- If the target total quotient ring is the localization of the completed
tensor algebra at the nonzero elements of the completed base, the two
fraction-field presentations are equivalent as `F`-algebras. -/
noncomputable def scalarFractionTensor :
    F ⊗[K] L ≃ₐ[F] Q :=
  (scalarLocalizationTensor
      (R := R) (S := S) (K := K) (L := L) (C := C) (F := F)).trans
    (fractionTensorLocalization
      (C := C) (F := F) (B := C ⊗[R] S) (Q := Q))

omit [IsDomain C] in
@[simp]
theorem scalar_fraction_tmul
    (f : F) (s : S) :
    scalarFractionTensor
        (R := R) (S := S) (K := K) (L := L)
        (C := C) (F := F) (Q := Q)
        (f ⊗ₜ[K] algebraMap S L s) =
      algebraMap F Q f *
        algebraMap (C ⊗[R] S) Q ((1 : C) ⊗ₜ[R] s) := by
  rw [scalarFractionTensor, AlgEquiv.trans_apply,
    scalar_localization_tmul]
  exact fraction_localization_tmul
    (C := C) (F := F) (B := C ⊗[R] S) (Q := Q)
    f ((1 : C) ⊗ₜ[R] s)

end CompletedTensor

end

end Towers.NumberTheory.Milne

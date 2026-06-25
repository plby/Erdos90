import Towers.ClassField.NormCorrespondence.CanonicalNormalization
import Towers.ClassField.LocalBrauer.TotallyCanonicalTransport

/-!
# Arithmetic Frobenius across a totally ramified base change

For a totally ramified extension `F / K`, scalar extension of the canonical
unramified degree-`n` extension of `K` is the canonical unramified degree-`n`
extension of `F`.  The induced Galois equivalence carries arithmetic
Frobenius to arithmetic Frobenius.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (K F : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]
  [NormedAlgebra K F] [FiniteDimensional K F]
  [Algebra 𝒪[K] 𝒪[F]] [Module.Finite 𝒪[K] 𝒪[F]]
  [Module.IsTorsionFree 𝒪[K] 𝒪[F]]
  [IsScalarTower 𝒪[K] K F] [IsScalarTower 𝒪[K] 𝒪[F] F]

private abbrev U (n : ℕ) := canonicalUnramifiedLevel K n
private abbrev E (n : ℕ) := canonicalUnramifiedLevel F n
private abbrev T (n : ℕ) := U K n ⊗[K] F

set_option maxHeartbeats 5000000 in
-- Transporting arithmetic Frobenius through the tensor compositum requires
-- extensive normalization of algebra and Galois instances.
set_option synthInstance.maxHeartbeats 500000 in
/-- The Galois equivalence on canonical unramified levels induced by a
field-valued tensor compositum preserves arithmetic Frobenius. -/
theorem tensor_arithmetic_frobenius
    (n : ℕ) [NeZero n]
    (htotal : TotallyRamified 𝒪[K] 𝒪[F]
      (IsLocalRing.maximalIdeal 𝒪[K]))
    (hT : IsField (T K F n))
    (e : T K F n ≃ₐ[F] E F n) :
    (tensorCompositumGalois K (U K n) F hT).trans e.autCongr
        (canonicalArithmeticFrobenius K n) =
      canonicalArithmeticFrobenius F n := by
  let UK := U K n
  let EF := E F n
  let TF := T K F n
  letI : Algebra.IsAlgebraic K UK := Algebra.IsAlgebraic.of_finite K UK
  letI : NontriviallyNormedField UK :=
    FLExt.nontriviallyNormedField K UK
  letI : NormedAlgebra K UK := spectralNorm.normedAlgebra K UK
  letI : IsUltrametricDist UK := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel UK := FLExt.valuativeRel K UK
  letI : Valuation.Compatible (NormedField.valuation (K := UK)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := UK))
  letI : IsNonarchimedeanLocalField UK :=
    FLExt.nonarchimedeanLocalField K UK
  letI : Algebra.IsAlgebraic F EF := Algebra.IsAlgebraic.of_finite F EF
  letI : NontriviallyNormedField EF :=
    FLExt.nontriviallyNormedField F EF
  letI : NormedAlgebra F EF := spectralNorm.normedAlgebra F EF
  letI : IsUltrametricDist EF := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel EF := FLExt.valuativeRel F EF
  letI : Valuation.Compatible (NormedField.valuation (K := EF)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := EF))
  letI : IsNonarchimedeanLocalField EF :=
    FLExt.nonarchimedeanLocalField F EF
  letI : Field TF := hT.toField
  letI : Module.Finite F TF := by
    letI : Module.Finite F (F ⊗[K] UK) := Module.Finite.base_change K F UK
    exact Module.Finite.equiv
      (Algebra.TensorProduct.commRight K F UK).toLinearEquiv
  letI : IsGalois F TF := tensor_compositum K UK F hT
  let algKE : Algebra K EF :=
    ((algebraMap F EF).comp (algebraMap K F)).toAlgebra
  letI : Algebra K EF := algKE
  letI : IsScalarTower K F EF := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsAlgebraic K EF := Algebra.IsAlgebraic.trans K F EF
  let iUE : UK →+* EF :=
    e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom
        (R := K) (A := UK) (B := F))
  let algUE : Algebra UK EF := iUE.toAlgebra
  letI : Algebra UK EF := algUE
  have hiK (x : K) :
      iUE (algebraMap K UK x) = algebraMap K EF x := by
    change e (algebraMap K UK x ⊗ₜ[K] (1 : F)) =
      algebraMap F EF (algebraMap K F x)
    rw [← e.commutes]
    apply congrArg e
    change algebraMap K UK x ⊗ₜ[K] (1 : F) =
      (1 : UK) ⊗ₜ[K] algebraMap K F x
    rw [← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply']
  have he_tmul (x : UK) (y : F) :
      e (x ⊗ₜ[K] y) = iUE x * algebraMap F EF y := by
    change e (x ⊗ₜ[K] y) =
      e (x ⊗ₜ[K] (1 : F)) * algebraMap F EF y
    rw [← e.commutes, ← map_mul]
    congr 1
    rw [show algebraMap F TF y = (1 : UK) ⊗ₜ[K] y by rfl]
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  letI : IsScalarTower K UK EF := IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro x
    exact (hiK x).symm
  letI : NormedAlgebra K EF :=
    { (inferInstance : Algebra K EF) with
      norm_smul_le := by
        intro x y
        rw [Algebra.smul_def, norm_mul]
        change ‖algebraMap K EF x‖ * ‖y‖ ≤ ‖x‖ * ‖y‖
        rw [show algebraMap K EF x =
          algebraMap F EF (algebraMap K F x) by
            exact IsScalarTower.algebraMap_apply K F EF x]
        rw [norm_algebraMap' EF]
        have hx : ‖algebraMap K F x‖ = ‖x‖ := norm_algebraMap' F x
        rw [hx] }
  have hiNorm (x : UK) : ‖iUE x‖ = ‖x‖ := by
    change ‖algebraMap UK EF x‖ = ‖x‖
    rw [NormedAlgebra.norm_eq_spectralNorm K,
      ← spectralNorm.eq_of_tower (K := K) (L := EF) x,
      ← NormedAlgebra.norm_eq_spectralNorm K]
  let frobFE : EF ≃ₐ[K] EF :=
    (canonicalArithmeticFrobenius F n).restrictScalars K
  let sigma : Gal(UK/K) := frobFE.restrictNormal UK
  have hsigma_commutes (x : UK) :
      iUE (sigma x) = canonicalArithmeticFrobenius F n (iUE x) := by
    exact AlgEquiv.restrictNormal_commutes frobFE UK x
  have hcard : localResidueCardinality F = localResidueCardinality K := by
    change localResidueCard F = localResidueCard K
    exact residue_totally_ramified K F htotal
  have hsigma : sigma = canonicalArithmeticFrobenius K n := by
    apply (canonicalUnramifiedResidue K n).injective
    apply DFunLike.ext _ _
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    rw [canonical_unramified_residue K n sigma,
      canonical_unramified_residue K n
        (canonicalArithmeticFrobenius K n)]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply (NormedField.valuation (K := UK)).mem_maximalIdeal_iff.mpr
    rw [NormedField.valuation_apply]
    rw [← NNReal.coe_lt_coe]
    change ‖sigma (y : UK) - canonicalArithmeticFrobenius K n (y : UK)‖ < 1
    rw [← hiNorm]
    have hy : ‖(y : UK)‖ ≤ 1 := by
      exact_mod_cast y.property
    have hyE : ‖iUE (y : UK)‖ ≤ 1 := by
      rw [hiNorm]
      exact hy
    have hK := subextension_arithmetic_frobenius K n
      (y : UK) hy
    have hF := subextension_arithmetic_frobenius F n
      (iUE (y : UK)) hyE
    rw [map_sub, hsigma_commutes]
    have hmapK :
        ‖iUE (canonicalArithmeticFrobenius K n (y : UK)) -
            iUE ((y : UK) ^ localResidueCardinality K)‖ < 1 := by
      rw [← map_sub, hiNorm]
      exact hK
    have hmapPow :
        iUE ((y : UK) ^ localResidueCardinality K) =
          iUE (y : UK) ^ localResidueCardinality F := by
      rw [map_pow, hcard]
    rw [hmapPow] at hmapK
    have hmapKrev :
        ‖iUE (y : UK) ^ localResidueCardinality F -
          iUE (canonicalArithmeticFrobenius K n (y : UK))‖ < 1 := by
      rw [norm_sub_rev]
      exact hmapK
    have htriangle := IsUltrametricDist.norm_add_le_max
      (canonicalArithmeticFrobenius F n (iUE (y : UK)) -
        iUE (y : UK) ^ localResidueCardinality F)
      (iUE (y : UK) ^ localResidueCardinality F -
        iUE (canonicalArithmeticFrobenius K n (y : UK)))
    have hadd :
        (canonicalArithmeticFrobenius F n (iUE (y : UK)) -
            iUE (y : UK) ^ localResidueCardinality F) +
          (iUE (y : UK) ^ localResidueCardinality F -
            iUE (canonicalArithmeticFrobenius K n (y : UK))) =
          canonicalArithmeticFrobenius F n (iUE (y : UK)) -
            iUE (canonicalArithmeticFrobenius K n (y : UK)) := by ring
    rw [hadd] at htriangle
    exact htriangle.trans_lt (max_lt hF hmapKrev)
  let g : Gal(UK/K) ≃* Gal(EF/F) :=
    (tensorCompositumGalois K UK F hT).trans e.autCongr
  change g (canonicalArithmeticFrobenius K n) = _
  rw [← hsigma]
  apply AlgEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (fun a b ↦ a + b) hx hy
  | tmul x y =>
      simp only [g, MulEquiv.trans_apply, AlgEquiv.autCongr_apply,
        AlgEquiv.trans_apply, e.symm_apply_apply,
        tensor_compositum_galois,
        tensor_compositum_tmul]
      rw [he_tmul, he_tmul]
      rw [map_mul, (canonicalArithmeticFrobenius F n).commutes,
        hsigma_commutes]

end

end Towers.CField.LBrauer

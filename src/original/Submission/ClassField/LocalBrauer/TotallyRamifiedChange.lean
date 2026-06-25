import Submission.ClassField.LocalBrauer.TotallyRamifiedTransport
import Submission.ClassField.LocalBrauer.LinearlyDisjointChange
import Submission.ClassField.LocalBrauer.CanonicalInvariantAssembly

/-!
# Canonical carry classes across a totally ramified base change

Scalar extension through a totally ramified local extension sends the
Frobenius-normalized unramified carry class to the power prescribed by the
extension degree.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open Submission.NumberTheory.Milne
open BGroups CProduca
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

set_option maxHeartbeats 5000000 in
-- Comparing the canonical carry classes after totally ramified base change
-- unfolds a large transported cocycle calculation.
set_option synthInstance.maxHeartbeats 500000 in
-- The tensor-product inclusions require the complete scalar-tower instance chain.
/-- Totally ramified scalar extension raises a Frobenius-normalized carry
class to the extension degree. -/
theorem change_totally_ramified
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (htotal : TotallyRamified 𝒪[K] 𝒪[F]
      (IsLocalRing.maximalIdeal 𝒪[K])) :
    brauerBaseChange K F
        (CProduc.brauerClass K (canonicalUnramifiedLevel K n)
          (galoisCarryCocycle K
            (levelZMod K n)
            (canonicalLocalUniformizer K))) =
      (CProduc.brauerClass F (canonicalUnramifiedLevel F n)
        (galoisCarryCocycle F
          (levelZMod F n)
          (canonicalLocalUniformizer F))) ^ Module.finrank K F := by
  letI : (IsDiscreteValuationRing.maximalIdeal 𝒪[F]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).asIdeal := by
    have hp0 : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ :=
      IsDiscreteValuationRing.not_a_field 𝒪[K]
    obtain ⟨P, hPprime, hPover, _hmap, _hram, _hunique⟩ := htotal
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
    have hPmax : P = IsLocalRing.maximalIdeal 𝒪[F] :=
      IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
    simpa only [hPmax] using hPover
  let U := canonicalUnramifiedLevel K n
  let E := canonicalUnramifiedLevel F n
  letI : Algebra.IsAlgebraic K U := Algebra.IsAlgebraic.of_finite K U
  letI : NontriviallyNormedField U :=
    FLExt.nontriviallyNormedField K U
  letI : NormedAlgebra K U := spectralNorm.normedAlgebra K U
  letI : IsUltrametricDist U := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel U := FLExt.valuativeRel K U
  letI : Valuation.Compatible (NormedField.valuation (K := U)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := U))
  letI : IsNonarchimedeanLocalField U :=
    FLExt.nonarchimedeanLocalField K U
  letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField F E
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel E := FLExt.valuativeRel F E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField F E
  let T := U ⊗[K] F
  let hT : IsField T :=
    level_totally_ramified
      K F n htotal
  letI : Field T := hT.toField
  letI : Module.Finite F T := by
    letI : Module.Finite F (F ⊗[K] U) := Module.Finite.base_change K F U
    exact Module.Finite.equiv
      (Algebra.TensorProduct.commRight K F U).toLinearEquiv
  letI : IsGalois F T := tensor_compositum K U F hT
  let e : T ≃ₐ[F] E := Classical.choice
    (nonempty_totally_ramified
      K F n htotal)
  let iUE : U →+* E :=
    e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := U) (B := F))
  let g : Gal(U/K) ≃* Gal(E/F) :=
    (tensorCompositumGalois K U F hT).trans e.autCongr
  let eK : Multiplicative (ZMod n) ≃* Gal(U/K) :=
    levelZMod K n
  let eF : Multiplicative (ZMod n) ≃* Gal(E/F) := eK.trans g
  have hgFrob : g (canonicalArithmeticFrobenius K n) =
      canonicalArithmeticFrobenius F n :=
    tensor_arithmetic_frobenius
      K F n htotal hT e
  have heF : eF = levelZMod F n := by
    apply MulEquiv.ext
    intro z
    have hz : z = (Multiplicative.ofAdd (1 : ZMod n)) ^ z.toAdd.val := by
      apply Multiplicative.toAdd.injective
      simp
    rw [hz, map_pow, map_pow]
    congr 1
    change g (eK (Multiplicative.ofAdd (1 : ZMod n))) =
      levelZMod F n
        (Multiplicative.ofAdd (1 : ZMod n))
    rw [level_frobenius_z,
      level_frobenius_z, hgFrob]
  have hi : ∀ sigma : Gal(U/K), ∀ x : U,
      iUE (sigma x) = g sigma (iUE x) := by
    intro sigma x
    have he_cancel (z : T) : e.symm (e.toRingEquiv z) = z :=
      e.symm_apply_apply z
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, MulEquiv.trans_apply,
      tensor_compositum_galois, AlgEquiv.autCongr_apply,
      AlgEquiv.trans_apply, iUE, g]
    rw [he_cancel]
    exact congrArg e
      (tensor_include_equivariant K U F hT sigma x)
  have hbase : ∀ x : K,
      iUE (algebraMap K U x) = algebraMap F E (algebraMap K F x) := by
    intro x
    change e (algebraMap K U x ⊗ₜ[K] (1 : F)) =
      algebraMap F E (algebraMap K F x)
    rw [← e.commutes]
    apply congrArg e
    change algebraMap K U x ⊗ₜ[K] (1 : F) =
      (1 : U) ⊗ₜ[K] algebraMap K F x
    rw [← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply']
  have hcoeff : ∀ (x : U) (y : F),
      e (x ⊗ₜ[K] y) = iUE x * algebraMap F E y := by
    intro x y
    change e (x ⊗ₜ[K] y) =
      e (x ⊗ₜ[K] (1 : F)) * algebraMap F E y
    rw [← e.commutes, ← map_mul]
    congr 1
    rw [show algebraMap F T y = (1 : U) ⊗ₜ[K] y by rfl]
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hchange :
      brauerBaseChange K F
          (CProduc.brauerClass K U
            (galoisCarryCocycle K eK (canonicalLocalUniformizer K))) =
        CProduc.brauerClass F E
          (galoisCarryCocycle F eF
            (Units.map (algebraMap K F) (canonicalLocalUniformizer K))) := by
    exact brauer_base_carry iUE g hi hbase e hcoeff
      eK eF (fun _ ↦ rfl) (canonicalLocalUniformizer K)
  rw [hchange, heF]
  obtain ⟨hResidueK, hUnitK, horderK, _⟩ :=
    unramified_level_data K n
  letI : Algebra (Valued.ResidueField K) (Valued.ResidueField U) := hResidueK
  let NK := FLExt.integerUnitNorm K U
  have hNormK : UnramifiedLocalData K U NK :=
    FLExt.unramified_data_unit K U
      hResidueK hUnitK
  have horderNormK : ∀ x : Uˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K U x)) =
        (n : ℤ) * localUnitOrder U (Additive.ofMul x) := by
    intro x
    rw [show localNormUnits K U x = Units.map (Algebra.norm K) x by rfl]
    apply UOExt.order_norm_finrankeq K U
    · exact
        { order_algebraMap := horderK
          order_aut := FLExt.unit_order_aut K U }
    · exact unramified_level_finrank K n
  obtain ⟨hResidueF, hUnitF, horderF, _⟩ :=
    unramified_level_data F n
  letI : Algebra (Valued.ResidueField F) (Valued.ResidueField E) := hResidueF
  let NF := FLExt.integerUnitNorm F E
  have hNormF : UnramifiedLocalData F E NF :=
    FLExt.unramified_data_unit F E
      hResidueF hUnitF
  have horderNormF : ∀ x : Eˣ,
      localUnitOrder F
          (Additive.ofMul (localNormUnits F E x)) =
        (n : ℤ) * localUnitOrder E (Additive.ofMul x) := by
    intro x
    rw [show localNormUnits F E x = Units.map (Algebra.norm F) x by rfl]
    apply UOExt.order_norm_finrankeq F E
    · exact
        { order_algebraMap := horderF
          order_aut := FLExt.unit_order_aut F E }
    · exact unramified_level_finrank F n
  let invF := unramifiedInvariantEquiv F E
    (levelZMod F n) hn
      NF hNormF horderNormF
  let cMap := unramifiedCarryRelative F E
    (levelZMod F n)
      (Units.map (algebraMap K F) (canonicalLocalUniformizer K))
  let cF := unramifiedCarryRelative F E
    (levelZMod F n)
      (canonicalLocalUniformizer F)
  change (cMap : BrauerGroup F) = ((cF : BrauerGroup F) ^ Module.finrank K F)
  suffices hc : cMap = cF ^ Module.finrank K F by
    exact congrArg Subtype.val hc
  apply invF.injective
  have htransport :=
    unramified_totally_ramified
      K U F E htotal eK
        (levelZMod F n) hn
        NK hNormK horderNormK NF hNormF horderNormF
          (canonicalLocalUniformizer K)
  rw [map_pow]
  change invF cMap = (invF cF) ^ Module.finrank K F
  rw [htransport]
  have hKcarry :
      unramifiedInvariantEquiv K U eK hn NK hNormK horderNormK
          (unramifiedCarryRelative K U eK
            (canonicalLocalUniformizer K)) =
        Multiplicative.ofAdd (localDivTorsion n) :=
    unramified_equiv_carry K U eK hn NK hNormK horderNormK
      (canonicalLocalUniformizer K) (canonical_uniformizer_order K)
  have hFcarry : invF cF =
      Multiplicative.ofAdd (localDivTorsion n) := by
    apply unramified_equiv_carry F E
    exact canonical_uniformizer_order F
  rw [hKcarry, hFcarry]

end

end Submission.CField.LBrauer

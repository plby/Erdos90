import Towers.ClassField.LocalBrauer.CanonicalUnramifiedData
import Towers.ClassField.LocalBrauer.LinearlyDisjointChange
import Towers.ClassField.LocalBrauer.CanonicalCarryMul
import Towers.ClassField.LocalBrauer.TensorProductGalois
import Towers.ClassField.LocalBrauer.TotallyCanonicalTransport
import Towers.NumberTheory.Locals.LocalUnramifiedDecomposition

/-!
# Splitting a carry class by a totally ramified extension

This is the totally ramified arithmetic step in the direct attack on Lemma
III.2.2.  A degree-`n` totally ramified extension kills every power of the
degree-`n` unramified carry class.  The proof transports the crossed product
through the field-valued tensor compositum and then uses norm/order
coordinates on the resulting unramified extension.
-/

namespace Towers.CField.LClass

noncomputable section

universe u

open ValuativeRel
open Towers.NumberTheory.Milne
open BGroups CProduca LBrauer
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (K F : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]
  [Algebra K F] [FiniteDimensional K F]
  [Algebra 𝒪[K] 𝒪[F]] [Module.Finite 𝒪[K] 𝒪[F]]
  [Module.IsTorsionFree 𝒪[K] 𝒪[F]]
  [IsScalarTower 𝒪[K] K F] [IsScalarTower 𝒪[K] 𝒪[F] F]

private abbrev canonicalField (B : Type u)
    [NontriviallyNormedField B] [IsUltrametricDist B] [ValuativeRel B]
    [IsNonarchimedeanLocalField B]
    [Valuation.Compatible (NormedField.valuation (K := B))]
    (n : ℕ) := canonicalUnramifiedLevel B n

set_option maxHeartbeats 2000000 in
-- The tensor-compositum Galois equivalence has deeply dependent instances.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the tensor-product inclusions requires the full scalar-tower instance chain.
/-- A degree-`n` totally ramified extension kills the degree-`n` carry
crossed-product class. -/
theorem brauer_totally_ramified
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (hdegree : Module.finrank K F = n)
    (htotal : TotallyRamified 𝒪[K] 𝒪[F]
      (IsLocalRing.maximalIdeal 𝒪[K]))
    (a : Kˣ) :
    brauerBaseChange K F
        (CProduc.brauerClass K (canonicalField K n)
          (galoisCarryCocycle K
            (galZMod K n) a)) = 1 := by
  letI : (IsDiscreteValuationRing.maximalIdeal 𝒪[F]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).asIdeal := by
    have hp0 : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ :=
      IsDiscreteValuationRing.not_a_field 𝒪[K]
    obtain ⟨P, hPprime, hPover, _hmap, _hram, _hunique⟩ := htotal
    have hP0 : P ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
    have hPmax : P = IsLocalRing.maximalIdeal 𝒪[F] :=
      IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
    simpa only [hPmax] using hPover
  let U := canonicalField K n
  let E := canonicalField F n
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
    galZMod K n
  let eF : Multiplicative (ZMod n) ≃* Gal(E/F) := eK.trans g
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
            (galoisCarryCocycle K eK a)) =
        CProduc.brauerClass F E
          (galoisCarryCocycle F eF
            (Units.map (algebraMap K F) a)) := by
    exact brauer_base_carry iUE g hi hbase e hcoeff
      eK eF (fun _ ↦ rfl) a
  rw [hchange]
  obtain ⟨hResidueK, hUnitK, horderK, _⟩ :=
    unramified_level_data K n
  letI : Algebra 𝓀[K] 𝓀[U] := hResidueK
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
  letI : Algebra 𝓀[F] 𝓀[E] := hResidueF
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
  let invF := unramifiedInvariantEquiv F E eF hn NF hNormF horderNormF
  let cF := unramifiedCarryRelative F E eF
    (Units.map (algebraMap K F) a)
  change (cF : BrauerGroup F) = 1
  suffices hc : cF = 1 by exact congrArg Subtype.val hc
  apply invF.injective
  have htransport :=
    unramified_totally_ramified
      K U F E htotal eK eF hn NK hNormK horderNormK
        NF hNormF horderNormF a
  change invF cF = invF 1
  rw [map_one, htransport, hdegree]
  let xK := unramifiedInvariantEquiv K U eK hn
    NK hNormK horderNormK
      (unramifiedCarryRelative K U eK a)
  change xK ^ n = 1
  apply Multiplicative.toAdd.injective
  change n • xK.toAdd = 0
  apply Subtype.ext
  exact xK.toAdd.property

/-- The same splitting statement for every power of the carry cocycle. -/
theorem carry_totally_ramified
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (hdegree : Module.finrank K F = n)
    (htotal : TotallyRamified 𝒪[K] 𝒪[F]
      (IsLocalRing.maximalIdeal 𝒪[K]))
    (a : Kˣ) (j : ℕ) :
    brauerBaseChange K F
        (CProduc.brauerClass K (canonicalField K n)
          ((galoisCarryCocycle K
            (galZMod K n) a) ^ j)) = 1 := by
  let U := canonicalField K n
  let c := galoisCarryCocycle K
    (galZMod K n) a
  have hpow : CProduc.brauerClass K U (c ^ j) =
      (CProduc.brauerClass K U c) ^ j := by
    have hrelative : CProduc.relativeBrauerClass K U (c ^ j) =
        (CProduc.relativeBrauerClass K U c) ^ j := by
      change
        (CProduc.hRelativeBrauer K U)
            (MHTwo.mk (c ^ j)) =
          ((CProduc.hRelativeBrauer K U)
            (MHTwo.mk c)) ^ j
      rw [← map_pow, MHTwo.mk_pow]
    exact congrArg Subtype.val hrelative
  rw [hpow, map_pow,
    brauer_totally_ramified
      K F n hn hdegree htotal a, one_pow]

/-- A totally ramified extension whose degree is the degree of a local
central division algebra splits that algebra. -/
theorem split_totally_ramified
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (hdegree : Module.finrank K F = Nat.sqrt (Module.finrank K D))
    (htotal : TotallyRamified 𝒪[K] 𝒪[F]
      (IsLocalRing.maximalIdeal 𝒪[K])) :
    ISBy K F D := by
  let n := Nat.sqrt (Module.finrank K D)
  have hnPos : 0 < n := by
    dsimp only [n]
    exact Nat.sqrt_pos.2 Module.finrank_pos
  letI : NeZero n := ⟨hnPos.ne'⟩
  by_cases hnOne : n = 1
  · have horder :
        orderOf (brauerClass K (centralDivisionCSA K D)) = 1 := by
      rw [brauer_division_finrank]
      exact hnOne
    have hclass : brauerClass K (centralDivisionCSA K D) = 1 :=
      orderOf_eq_one_iff.mp horder
    apply (brauer_relative_split
      K F (centralDivisionCSA K D)).1
    rw [relative_brauer_group, hclass, map_one]
  · have hn : 1 < n :=
      (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨hnPos.ne', hnOne⟩
    obtain ⟨j, _hj, ⟨eD⟩⟩ :=
      alg_carry_algebra K D (by simpa [n] using hn)
    have hclass : brauerClass K (centralDivisionCSA K D) =
        CProduc.brauerClass K (canonicalUnramifiedLevel K n)
          ((canonicalCarryCocycle K n) ^ j) := by
      apply (brauer_class K _ _).2
      exact brauer_equivalent_alg K _ _ eD
    apply (brauer_relative_split
      K F (centralDivisionCSA K D)).1
    rw [relative_brauer_group, hclass]
    change brauerBaseChange K F
        (CProduc.brauerClass K (canonicalField K n)
          ((galoisCarryCocycle K
            (galZMod K n)
              (canonicalLocalUniformizer K)) ^ j)) = 1
    exact carry_totally_ramified
      K F n hn (by simpa [n] using hdegree) htotal
        (canonicalLocalUniformizer K) j

end

end Towers.CField.LClass

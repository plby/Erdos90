import Towers.FieldTheory.CentralEmbeddingBrauer
import Towers.FieldTheory.CentralEmbeddingLocal
import Towers.FieldTheory.CentralEmbeddingRelative
import Towers.ClassField.Shifting.AdditiveHomZero
import Towers.ClassField.LocalBrauer.FiniteExtensionOrder
import Towers.ClassField.LocalBrauer.SpectralNormData
import Towers.ClassField.LocalBrauer.UnramifiedH2
import Towers.NumberTheory.Completions.UnramifiedCompletion

/-!
# Local central obstructions with finite-order coefficients

This file connects the central-extension obstruction to the unit-valued
cohomology calculation for unramified local extensions.
-/

noncomputable section

namespace Towers
namespace TBluepr

open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.BGroups
open Towers.CField.Shifting
open CategoryTheory
open CategoryTheory.Limits
open ValuativeRel
open IsDedekindDomain NumberField
open scoped Pointwise

attribute [local instance] Units.mulDistribMulActionRight

universe u v w

/-- Normalized additive order, written as a homomorphism from field units to
the multiplicative presentation of `ℤ`. -/
def localOrderHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd
    (localUnitOrder K (Additive.ofMul x))
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact map_add (localUnitOrder K)
      (Additive.ofMul x) (Additive.ofMul y)

/-- Galois automorphisms of a finite local extension preserve normalized
order. -/
theorem local_order_aut
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    (sigma : Gal(L/K)) (x : Lˣ) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    localOrderHom L (sigma • x) =
      localOrderHom L x := by
  apply Multiplicative.toAdd.injective
  exact FLExt.unit_order_aut K L sigma x

/-- A finite-order field unit has normalized order zero. -/
theorem local_order_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (hn : 0 < n) (x : Kˣ) (hx : x ^ n = 1) :
    localOrderHom K x = 1 := by
  apply Multiplicative.toAdd.injective
  have hxadd : n • Additive.ofMul x = 0 := by
    apply Additive.toMul.injective
    simpa using hx
  have horder := congrArg (localUnitOrder K) hxadd
  rw [map_nsmul, map_zero] at horder
  change localUnitOrder K (Additive.ofMul x) = 0
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_eq_zero.mp (by simpa [nsmul_eq_mul] using horder)).resolve_left hnz

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
/-- A central obstruction with finite-order coefficients has zero normalized
order.  This is the valuation-zero input for the unramified quotient in the
tame inflation--restriction argument. -/
theorem central_extension_galois
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (n : ℕ) (hn : 0 < n)
    (hkernel : ∀ z : q.ker, z ^ n = 1) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    letI : MulDistribMulAction Gal(L/K) (Multiplicative ℤ) :=
      trivialDistribAction Gal(L/K) (Multiplicative ℤ)
    MHTwo.mapCoefficientsHom (localOrderHom L)
        (fun sigma x ↦ by
          change localOrderHom L (sigma • x) =
            localOrderHom L x
          exact local_order_aut K L sigma x)
        (centralExtensionClass q hq hcentral galoisEquiv
          kernelToUnits hfixed) = 1 := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : MulDistribMulAction Gal(L/K) (Multiplicative ℤ) :=
    trivialDistribAction Gal(L/K) (Multiplicative ℤ)
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  let orderEquivariance : ∀ sigma : Gal(L/K), ∀ x : Lˣ,
      localOrderHom L (sigma • x) =
        sigma • localOrderHom L x := by
    intro sigma x
    change localOrderHom L (sigma • x) =
      localOrderHom L x
    exact local_order_aut K L sigma x
  let compositeEquivariance : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      ((localOrderHom L).comp kernelToUnits) (sigma • z) =
        sigma • ((localOrderHom L).comp kernelToUnits) z := by
    intro sigma z
    rw [show sigma • z = z from rfl]
    rfl
  let restricted : MHTwo Gal(L/K) q.ker :=
    MHTwo.restrictionHom galoisEquiv.toMonoidHom
      (fun _ _ ↦ rfl)
      (extensionObstructionClass q hq hcentral)
  change MHTwo.mapCoefficientsHom (localOrderHom L)
      orderEquivariance
      (MHTwo.mapCoefficientsHom kernelToUnits
        (fun sigma z ↦ (hfixed sigma z).symm) restricted) = 1
  rw [MHTwo.coefficients_hom_comp
    (f := kernelToUnits) (g := localOrderHom L)
    (fG := fun sigma z ↦ (hfixed sigma z).symm)
    (gG := orderEquivariance)
    (gfG := compositeEquivariance)]
  apply MHTwo.coefficients_hom_forall
  intro z
  apply local_order_pow L n hn
  rw [← map_pow, hkernel z, map_one]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 3000000 in
/-- On a cyclic unramified local extension, normalized order detects the
field-unit `H²` class.  The proof is the cyclic parameter calculation:
valuation zero modulo the degree makes the parameter a norm, using
surjectivity of the norm on valuation-ring units. -/
theorem unramified_cyclic_order
    (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [NontriviallyNormedField L] [IsUltrametricDist L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [Valuation.Compatible (NormedField.valuation (K := L))]
    [Algebra K L] [Module.Finite K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField 𝒪[K])
      (IsLocalRing.ResidueField 𝒪[L])]
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K))
    (horderAut : ∀ sigma : Gal(L/K), ∀ z : Lˣ,
      localUnitOrder L (Additive.ofMul (sigma • z)) =
        localUnitOrder L (Additive.ofMul z))
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ)
    (hN : UnramifiedLocalData K L N)
    (horderAlgebraMap : ∀ a : Kˣ,
      localUnitOrder L
          (Additive.ofMul (Units.map (algebraMap K L) a)) =
        localUnitOrder K (Additive.ofMul a))
    (horderNorm : ∀ z : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L z)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul z))
    (x : MHTwo Gal(L/K) Lˣ)
    (hxorder :
      letI : MulDistribMulAction Gal(L/K) (Multiplicative ℤ) :=
        trivialDistribAction Gal(L/K) (Multiplicative ℤ)
      MHTwo.mapCoefficientsHom (localOrderHom L)
          (fun sigma z ↦ by
            change localOrderHom L (sigma • z) =
              localOrderHom L z
            apply Multiplicative.toAdd.injective
            exact horderAut sigma z)
          x = 1) :
    x = 1 := by
  let C := Multiplicative (ZMod n)
  letI : MulDistribMulAction Gal(L/K) (Multiplicative ℤ) :=
    trivialDistribAction Gal(L/K) (Multiplicative ℤ)
  letI : MulDistribMulAction C Lˣ :=
    GroupH2.pulledAction eGal
  letI : MulDistribMulAction C (Multiplicative ℤ) :=
    trivialDistribAction C (Multiplicative ℤ)
  let orderEquivarianceGal : ∀ sigma : Gal(L/K), ∀ z : Lˣ,
      localOrderHom L (sigma • z) =
        sigma • localOrderHom L z := by
    intro sigma z
    change localOrderHom L (sigma • z) =
      localOrderHom L z
    apply Multiplicative.toAdd.injective
    exact horderAut sigma z
  let orderEquivarianceC : ∀ c : C, ∀ z : Lˣ,
      localOrderHom L (c • z) =
        c • localOrderHom L z := by
    intro c z
    change localOrderHom L (eGal c • z) =
      localOrderHom L z
    exact orderEquivarianceGal (eGal c) z
  induction x using Quotient.inductionOn with
  | _ c =>
      let cC : NMCocycl₂ (G := C) (M := Lˣ) :=
        NMCocycl₂.restrict eGal.toMonoidHom
          (fun _ _ ↦ rfl) c
      let dC : NMCocycl₂ (G := C) (M := Multiplicative ℤ) :=
        NMCocycl₂.mapCoefficients
          (localOrderHom L) orderEquivarianceC cC
      have hxorderC : MHTwo.mk dC = 1 := by
        have h := congrArg
          (MHTwo.restrictionHom eGal.toMonoidHom
            (fun _ _ ↦ rfl)) hxorder
        rw [MHTwo.restriction_hom_coefficients
          (r := eGal.toMonoidHom)
          (hM := fun _ _ ↦ rfl) (hN := fun _ _ ↦ rfl)
          (f := localOrderHom L)
          (fG := orderEquivarianceGal)
          (fH := orderEquivarianceC)] at h
        exact h
      have hdCoh : MHTwo.IsCohomologous dC 1 :=
        (MHTwo.mk_eq_iff dC 1).1 (by simpa using hxorderC)
      obtain ⟨z, hz⟩ :=
        (CyclicH2.cohomologous_parameter_div
          (n := n) (M := Multiplicative ℤ) hn dC 1).1 hdCoh
      have hparameterOrder :
          CyclicH2.parameter dC =
            localOrderHom L (CyclicH2.parameter cC) := by
        simp [dC, CyclicH2.parameter]
      have horderParameter :
          localUnitOrder L
              (Additive.ofMul (CyclicH2.parameter cC)) =
            (n : ℤ) * z.toAdd := by
        have hz' : CyclicH2.parameter dC =
            (CyclicH2.norm (n := n) (M := Multiplicative ℤ) z :
              Multiplicative ℤ) := by
          simpa using hz
        rw [hparameterOrder, CyclicH2.norm_coe] at hz'
        have hzadd := congrArg Multiplicative.toAdd hz'
        simpa [nsmul_eq_mul] using hzadd
      let piC : CyclicH2.invariants (n := n) (M := Lˣ) :=
        ⟨CyclicH2.parameter cC, CyclicH2.parameter_mem_invariants cC⟩
      let piG : FMAct.invariants Gal(L/K) Lˣ :=
        GroupH2.invariantsMulEquiv eGal piC
      let a : Kˣ :=
        (baseUnitsInvariants K L).symm piG
      have haMap : Units.map (algebraMap K L) a =
          CyclicH2.parameter cC := by
        have ha := (baseUnitsInvariants K L).apply_symm_apply piG
        have hpi : (piG : Lˣ) = CyclicH2.parameter cC := rfl
        exact congrArg Subtype.val ha |>.trans hpi
      have haOrder : localUnitOrder K (Additive.ofMul a) =
          (n : ℤ) * z.toAdd := by
        rw [← horderAlgebraMap a, haMap]
        exact horderParameter
      have haKer : a ∈ (localOrderMod K n).ker := by
        rw [MonoidHom.mem_ker]
        apply Multiplicative.toAdd.injective
        change ((localUnitOrder K (Additive.ofMul a) : ℤ) : ZMod n) = 0
        rw [haOrder]
        simp
      have haNorm : a ∈ (localNormUnits K L).range := by
        rw [← ker_mod_range
          K L N hN horderNorm]
        exact haKer
      obtain ⟨t, ht⟩ := haNorm
      have hpiGNorm : FMAct.norm Gal(L/K) Lˣ t = piG := by
        rw [← base_units_invariants K L t, ht]
        exact (baseUnitsInvariants K L).apply_symm_apply piG
      have hpiCNorm :
          (CyclicH2.norm (n := n) (M := Lˣ) t :
              CyclicH2.invariants (n := n) (M := Lˣ)) = piC := by
        apply (GroupH2.invariantsMulEquiv eGal).injective
        rw [GroupH2.invariants_mul_norm]
        exact hpiGNorm
      have hcCoh : MHTwo.IsCohomologous cC 1 :=
        (CyclicH2.cohomologous_parameter_div
          (n := n) (M := Lˣ) hn cC 1).2 ⟨t, by
            simpa [piC] using congrArg Subtype.val hpiCNorm.symm⟩
      have hcC : MHTwo.mk cC = 1 :=
        (MHTwo.mk_eq_iff cC 1).2 hcCoh
      let hinv : ∀ sigma : Gal(L/K), ∀ z : Lˣ,
          sigma • z = eGal.symm sigma • z := by
        intro sigma z
        change sigma • z = eGal (eGal.symm sigma) • z
        rw [eGal.apply_symm_apply]
      have hleft :
          MHTwo.restrictionHom eGal.symm.toMonoidHom hinv
              (MHTwo.restrictionHom eGal.toMonoidHom
                (fun _ _ ↦ rfl) (MHTwo.mk c)) =
            MHTwo.mk c := by
        change MHTwo.mk
            (NMCocycl₂.restrict eGal.symm.toMonoidHom hinv
              (NMCocycl₂.restrict eGal.toMonoidHom
                (fun _ _ ↦ rfl) c)) = MHTwo.mk c
        apply congrArg MHTwo.mk
        ext p
        change ((c (eGal (eGal.symm p.1), eGal (eGal.symm p.2)) : Lˣ) : L) =
          ((c p : Lˣ) : L)
        rw [eGal.apply_symm_apply, eGal.apply_symm_apply]
      have hcC' :
          MHTwo.restrictionHom eGal.toMonoidHom
              (fun _ _ ↦ rfl) (MHTwo.mk c) = 1 := by
        simpa [cC] using hcC
      calc
        MHTwo.mk c =
            MHTwo.restrictionHom eGal.symm.toMonoidHom hinv
              (MHTwo.restrictionHom eGal.toMonoidHom
                (fun _ _ ↦ rfl) (MHTwo.mk c)) := hleft.symm
        _ = MHTwo.restrictionHom eGal.symm.toMonoidHom hinv 1 := by
          rw [hcC']
        _ = 1 := map_one _

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 3000000 in
/-- A finite formally unramified integral model supplies all arithmetic data
needed by the valuation detector for cyclic local `H²`. -/
theorem unramified_cyclic_model
    (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Type u) [CommRing U]
    [Algebra (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra U L]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) U L]
    [IsIntegralClosure U
      (Valuation.integer (ValuativeRel.valuation K)) L]
    [Module.Finite (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra.FormallyUnramified
      (Valuation.integer (ValuativeRel.valuation K)) U]
    [IsLocalRing U]
    [IsLocalHom
      (algebraMap (Valuation.integer (ValuativeRel.valuation K)) U)]
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K))
    (x : MHTwo Gal(L/K) Lˣ)
    (hxorder :
      letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
      letI : NontriviallyNormedField L :=
        FLExt.nontriviallyNormedField K L
      letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
      letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel L := FLExt.valuativeRel K L
      letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
        Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
      letI : IsNonarchimedeanLocalField L :=
        FLExt.nonarchimedeanLocalField K L
      letI : MulDistribMulAction Gal(L/K) (Multiplicative ℤ) :=
        trivialDistribAction Gal(L/K) (Multiplicative ℤ)
      MHTwo.mapCoefficientsHom (localOrderHom L)
          (fun sigma z ↦ by
            change localOrderHom L (sigma • z) =
              localOrderHom L z
            exact local_order_aut K L sigma z)
          x = 1) :
    x = 1 := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  obtain ⟨hResidueAlgebra, hUnit⟩ :=
    FLExt.residue_unramified_model
      K L U
  letI : Algebra
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation K)))
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation L))) :=
    hResidueAlgebra
  let hNorm :=
    FLExt.unramified_data_unit
      K L hResidueAlgebra hUnit
  have hdegree : Module.finrank K L = n := by
    calc
      Module.finrank K L = Nat.card Gal(L/K) :=
        (IsGalois.card_aut_eq_finrank K L).symm
      _ = Nat.card (Multiplicative (ZMod n)) :=
        (Nat.card_congr eGal.toEquiv).symm
      _ = n := by simp
  let hOrder : UOExt K L :=
    { order_algebraMap :=
        algebra_integral_model K L U
      order_aut := FLExt.unit_order_aut K L }
  apply unramified_cyclic_order
    K L n hn eGal
    (FLExt.unit_order_aut K L)
    (FLExt.integerUnitNorm K L) hNorm
    (algebra_integral_model K L U)
    (fun z ↦ by
      change localUnitOrder K
          (Additive.ofMul (Units.map (Algebra.norm K) z)) = _
      exact hOrder.order_norm_finrankeq K L hdegree z)
    x hxorder

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 2000000 in
/-- If the unit-valued second cohomology of a local Galois extension
vanishes, then every central obstruction whose coefficient embedding has
finite order vanishes after mapping into the coefficient field. -/
theorem integer_units_subsingleton
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel L]
    [MulSemiringAction Gal(L/K)
      (Valuation.integer (ValuativeRel.valuation L))]
    [Subsingleton (MHTwo Gal(L/K)
      (Valuation.integer (ValuativeRel.valuation L))ˣ)]
    (hcoe : ∀ (sigma : Gal(L/K))
      (z : (Valuation.integer (ValuativeRel.valuation L))ˣ),
      (((sigma • z :
          (Valuation.integer (ValuativeRel.valuation L))ˣ) :
            Valuation.integer (ValuativeRel.valuation L)) : L) =
        sigma • (((z :
          (Valuation.integer (ValuativeRel.valuation L))ˣ) :
            Valuation.integer (ValuativeRel.valuation L)) : L))
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (n : ℕ) [NeZero n]
    (hkernel : ∀ z : q.ker, z ^ n = 1) :
    centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  let restricted : MHTwo Gal(L/K) q.ker :=
    MHTwo.restrictionHom galoisEquiv.toMonoidHom
      (fun _ _ => rfl)
      (extensionObstructionClass q hq hcentral)
  change MHTwo.mapCoefficientsHom kernelToUnits
      (fun sigma z => (hfixed sigma z).symm) restricted = 1
  exact h_units_subsingleton
    (n := n) (hcoe := hcoe) (phi := kernelToUnits)
    (hphi := fun sigma z => (hfixed sigma z).symm)
    (hpow := fun z => by rw [← map_pow, hkernel z, map_one])
    restricted

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 3000000 in
/-- A cyclic finite local extension with surjective norm on valuation-ring
units kills every finite-order central obstruction.  Unramified extensions
satisfy the norm hypothesis by local field theory. -/
theorem central_cyclic_surjective
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (m : ℕ) [NeZero m]
    (eGal : Multiplicative (ZMod m) ≃* Gal(L/K))
    (hNorm :
      letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
      letI : NontriviallyNormedField L :=
        FLExt.nontriviallyNormedField K L
      letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
      letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel L := FLExt.valuativeRel K L
      Function.Surjective (FLExt.integerUnitNorm K L))
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (n : ℕ) [NeZero n]
    (hkernel : ∀ z : q.ker, z ^ n = 1) :
    centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1 := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : MulSemiringAction Gal(L/K)
      (Valuation.integer (ValuativeRel.valuation L)) :=
    FLExt.integerGaloisAction K L
  letI : Subsingleton (MHTwo Gal(L/K)
      (Valuation.integer (ValuativeRel.valuation L))ˣ) :=
    integer_subsingleton_surjective
      K L m eGal hNorm
  exact
    integer_units_subsingleton
      (fun sigma z => algebraMap.coe_smul'
        (B := Valuation.integer (ValuativeRel.valuation L))
        (C := L) sigma
          (z : Valuation.integer (ValuativeRel.valuation L)))
      q hq hcentral galoisEquiv kernelToUnits hfixed n hkernel

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 3000000 in
/-- A cyclic local extension with a finite formally unramified integral
model has trivial finite-order central obstruction. -/
theorem unramified_integral_model
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (U : Type u) [CommRing U]
    [Algebra (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra U L]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) U L]
    [IsIntegralClosure U
      (Valuation.integer (ValuativeRel.valuation K)) L]
    [Module.Finite (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra.FormallyUnramified
      (Valuation.integer (ValuativeRel.valuation K)) U]
    [IsLocalRing U]
    [IsLocalHom
      (algebraMap (Valuation.integer (ValuativeRel.valuation K)) U)]
    (m : ℕ) [NeZero m]
    (eGal : Multiplicative (ZMod m) ≃* Gal(L/K))
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (n : ℕ) [NeZero n]
    (hkernel : ∀ z : q.ker, z ^ n = 1) :
    centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1 := by
  refine central_cyclic_surjective
    K L m eGal ?_ q hq hcentral galoisEquiv kernelToUnits hfixed n hkernel
  · letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    obtain ⟨hResidueAlgebra, hUnit⟩ :=
      FLExt.residue_unramified_model
        K L U
    letI : Algebra
        (IsLocalRing.ResidueField
          (Valuation.integer (ValuativeRel.valuation K)))
        (IsLocalRing.ResidueField
          (Valuation.integer (ValuativeRel.valuation L))) :=
      hResidueAlgebra
    let hLocal :=
      FLExt.unramified_data_unit
        K L hResidueAlgebra hUnit
    exact unramified_units_surjective K L
      (FLExt.integerUnitNorm K L) hLocal

/-- A finite formally unramified local integral model.  Completion of a
number-field extension at an unramified prime is the principal source of this
data. -/
structure UnramifiedModelData
    (A F : Type u) [CommRing A] [Field F] [Algebra A F] where
  model : Type u
  [modelCommRing : CommRing model]
  [modelAlgebra : Algebra A model]
  [modelToField : Algebra model F]
  [modelTower : IsScalarTower A model F]
  [modelIntegralClosure : IsIntegralClosure model A F]
  [modelFinite : Module.Finite A model]
  [modelUnramified : Algebra.FormallyUnramified A model]
  [modelLocal : IsLocalRing model]
  [modelLocalHom : IsLocalHom (algebraMap A model)]

attribute [instance]
  UnramifiedModelData.modelCommRing
  UnramifiedModelData.modelAlgebra
  UnramifiedModelData.modelToField
  UnramifiedModelData.modelTower
  UnramifiedModelData.modelIntegralClosure
  UnramifiedModelData.modelFinite
  UnramifiedModelData.modelUnramified
  UnramifiedModelData.modelLocal
  UnramifiedModelData.modelLocalHom

/-- Every nonzero prime ideal of `ℤ` is generated by a natural prime. -/
lemma int_ideal_rational
    (P : Ideal ℤ) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ q : ℕ, Nat.Prime q ∧ P = Ideal.rationalPrimeIdeal q := by
  let a : ℤ := Submodule.IsPrincipal.generator P
  have hspan : Ideal.span ({a} : Set ℤ) = P :=
    P.span_singleton_generator
  have ha : a ≠ 0 := by
    intro ha
    apply hP
    rw [← hspan, ha]
    simp
  have haprime : Prime a :=
    (Ideal.span_singleton_prime ha).mp (hspan ▸ inferInstance)
  let q : ℕ := a.natAbs
  have hq : Nat.Prime q := Int.prime_iff_natAbs_prime.mp haprime
  refine ⟨q, hq, ?_⟩
  rw [← hspan]
  unfold Ideal.rationalPrimeIdeal
  apply Ideal.span_singleton_eq_span_singleton.mpr
  apply Int.natAbs_eq_iff_associated.mp
  exact Int.natAbs_natCast q

set_option synthInstance.maxHeartbeats 500000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
/-- A prime whose relative ramification index is at most two is unramified
in a finite Galois `3`-extension. -/
theorem number_unramified_group
    {K L : Type*}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hpgroup : IsPGroup 3 Gal(L/K))
    (Q : Ideal (NumberField.RingOfIntegers L))
    [Q.IsPrime] (hQ0 : Q ≠ ⊥)
    (he : (Q.under (NumberField.RingOfIntegers K)).ramificationIdx Q ≤ 2) :
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q := by
  let P := Q.under (NumberField.RingOfIntegers K)
  letI : Q.LiesOver P := inferInstance
  have hP0 : P ≠ ⊥ :=
    Ideal.under_ne_bot (NumberField.RingOfIntegers K) hQ0
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  have he' : P.ramificationIdx Q ≤ 2 := by
    simpa [P] using he
  letI : MulSemiringAction Gal(L/K)
      (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction
      (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup Gal(L/K)
      (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K)
      (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  letI : Field (NumberField.RingOfIntegers K ⧸ P) :=
    Ideal.Quotient.field P
  letI : Field (NumberField.RingOfIntegers L ⧸ Q) :=
    Ideal.Quotient.field Q
  letI : IsGalois (NumberField.RingOfIntegers K ⧸ P)
      (NumberField.RingOfIntegers L ⧸ Q) :=
    { __ := Ideal.Quotient.normal
        (A := NumberField.RingOfIntegers K) (G := Gal(L/K)) P Q }
  letI : Algebra.IsSeparable (NumberField.RingOfIntegers K ⧸ P)
      (NumberField.RingOfIntegers L ⧸ Q) := inferInstance
  let I := Q.inertia Gal(L/K)
  have hcardI : Nat.card I = P.ramificationIdx Q := by
    calc
      Nat.card I = P.ramificationIdxIn
          (NumberField.RingOfIntegers L) :=
        Ideal.card_inertia_eq_ramificationIdxIn P hP0 Q
      _ = P.ramificationIdx Q :=
        Ideal.ramificationIdxIn_eq_ramificationIdx P Q Gal(L/K)
  have hIp : IsPGroup 3 I := hpgroup.to_subgroup I
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hIp
  have hcardOne : Nat.card I = 1 := by
    cases n with
    | zero => simpa using hn
    | succ n =>
        have hthree : 3 ≤ Nat.card I := by
          rw [hn, pow_succ]
          have hpos : 0 < 3 ^ n := pow_pos (by norm_num) n
          omega
        rw [hcardI] at hthree
        omega
  apply (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hQ0).mpr
  change P.ramificationIdx Q = 1
  rw [← hcardI, hcardOne]

/-- A chosen upper completion at a finite place is cyclic unramified when it
has a cyclic Galois group and its valuation integers have a finite formally
unramified integral model over the base valuation integers. -/
def CyclicUnramifiedCompletion
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)] : Prop := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨Towers.CField.Ideles.absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    Towers.CField.Ideles.placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    Towers.CField.Ideles.placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    Towers.CField.Ideles.placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    Towers.CField.Ideles.placeNonarchimedeanField P
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  let A := Valuation.integer (ValuativeRel.valuation v.Completion)
  letI : Algebra A w.1.Completion :=
    Algebra.ofSubring A
  exact ∃ degree : ℕ, 0 < degree ∧
    Nonempty (Multiplicative (ZMod degree) ≃*
      Gal(w.1.Completion/v.Completion)) ∧
    Nonempty (UnramifiedModelData A w.1.Completion)

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- Completion at a globally unramified prime has cyclic local Galois group
and a finite formally unramified integral model. -/
theorem cyclic_unramified_completion
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    (hUnramified : ∀ Q : HeightOneSpectrum
        (NumberField.RingOfIntegers L),
      Q.asIdeal.LiesOver P.asIdeal →
        Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers K) Q.asIdeal) :
    CyclicUnramifiedCompletion P w := by
  let v := (FinitePlace.mk P).val
  let hv := Towers.CField.Ideles.absolute_value_nontrivial P
  let hvna : IsNonarchimedean v := fun x y ↦ (FinitePlace.mk P).add_le x y
  letI : Fact v.IsNontrivial := ⟨hv⟩
  letI : IsUltrametricDist v.Completion :=
    Towers.CField.Ideles.placeUltrametricDist P
  let hw := Towers.NumberTheory.Milne.absolute_extension_nontrivial
    v w
  let hwna :=
    Towers.NumberTheory.Milne.absolute_extension_nonarchimedean
      v w
  let Q := Towers.NumberTheory.Milne.nonarchimedeanHeightSpectrum
    w.1 hw hwna
  letI : Q.asIdeal.LiesOver P.asIdeal :=
    Towers.NumberTheory.Milne.nonarchimedean_spectrum_lies
      P w.1 w.2 hw hwna
  let hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.asIdeal :=
    hUnramified Q inferInstance
  letI : Fact w.1.IsNontrivial := ⟨hw⟩
  letI : NontriviallyNormedField v.Completion :=
    Towers.CField.Ideles.placeNontriviallyNormed P
  letI : IsUltrametricDist w.1.Completion :=
    Towers.NumberTheory.Milne.absoluteUltrametricDist
      w.1 hwna
  letI : ValuativeRel v.Completion :=
    Towers.CField.Ideles.placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    Towers.CField.Ideles.placeNonarchimedeanField P
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  let hFinite : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : FiniteDimensional v.Completion w.1.Completion := hFinite
  let hGalois : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  letI : IsGalois v.Completion w.1.Completion := hGalois
  let hSeparable : Algebra.IsSeparable v.Completion w.1.Completion :=
    IsGalois.to_isSeparable
  letI : MulSemiringAction Gal(L/K)
      (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction
      (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  have hDecompositionCyclic :
      IsCyclic (MulAction.stabilizer Gal(L/K) Q.asIdeal) :=
    Towers.NumberTheory.Milne.decomposition_cyclic_unramified
      P Q hQ
  have hAbsoluteCyclic :
      IsCyclic
        (Towers.NumberTheory.Milne.absoluteValueDecomposition
          v w.1) := by
    rw [← Towers.NumberTheory.Milne.centered_stabilizer_decomposition
      v w.1 hw hwna]
    exact hDecompositionCyclic
  have hCompletionCyclic : IsCyclic Gal(w.1.Completion/v.Completion) :=
    (Towers.NumberTheory.Milne.decompositionCompletionExtension
      v w.1).isCyclic.mp hAbsoluteCyclic
  letI : IsCyclic Gal(w.1.Completion/v.Completion) := hCompletionCyclic
  letI : Finite Gal(w.1.Completion/v.Completion) :=
    IsGaloisGroup.finite Gal(w.1.Completion/v.Completion)
      v.Completion w.1.Completion
  let degree := Nat.card Gal(w.1.Completion/v.Completion)
  have hdegree : 0 < degree := Nat.card_pos
  obtain ⟨generator, hgenerator⟩ :=
    IsCyclic.exists_generator (α := Gal(w.1.Completion/v.Completion))
  let cyclicEquiv : Multiplicative (ZMod degree) ≃*
      Gal(w.1.Completion/v.Completion) :=
    zmodMulEquivOfGenerator hgenerator rfl
  let A₀ := Valuation.integer (ValuativeRel.valuation v.Completion)
  let A := Towers.NumberTheory.Milne.completionIntegerRing v
  let B := Towers.NumberTheory.Milne.completionIntegerRing w.1
  letI : Algebra A B :=
    Towers.NumberTheory.Milne.completionIntegerLies
      v w.1 w.2
  let e₀ : A₀ ≃+* A :=
    Towers.CField.LBrauer.valuativeIntegerNorm
      v.Completion
  letI : Algebra A₀ B :=
    ((algebraMap A B).comp e₀.toRingHom).toAlgebra
  letI : Algebra B w.1.Completion := B.subtype.toAlgebra
  letI : Algebra A₀ w.1.Completion := Algebra.ofSubring A₀
  letI : IsScalarTower A₀ B w.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hAlgebraic : Algebra.IsAlgebraic v.Completion w.1.Completion :=
    Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion
  let eA :=
    Towers.NumberTheory.Milne.centeredIntegerAdic
      v hv hvna
  letI : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA.symm
  let hModuleFiniteA : Module.Finite A B :=
    Towers.NumberTheory.Milne.completion_integer_module
      v w.1 w.2 hFinite hSeparable
  letI : Module.Finite A B := hModuleFiniteA
  let hModuleFinite : Module.Finite A₀ B := by
    apply Module.Finite.of_equiv_equiv e₀.symm (RingEquiv.refl B)
    ext x
    rfl
  letI : Module.Finite A₀ B := hModuleFinite
  let hUnramifiedA : Algebra.FormallyUnramified A B :=
    Towers.NumberTheory.Milne.completion_formally_unramified
      P w.1 w.2 hw hwna hQ hFinite hSeparable
  letI : Algebra.FormallyUnramified A B := hUnramifiedA
  let hLocalHomA : IsLocalHom (algebraMap A B) :=
    Towers.NumberTheory.Milne.completion_integer_lies
      v w.1 w.2
  letI : IsLocalHom (algebraMap A B) := hLocalHomA
  letI : IsLocalHom e₀.toRingHom :=
    IsLocalHom.of_surjective e₀.toRingHom e₀.surjective
  let hLocalHom : IsLocalHom (algebraMap A₀ B) := by
    change IsLocalHom ((algebraMap A B).comp e₀.toRingHom)
    infer_instance
  letI : IsLocalHom (algebraMap A₀ B) := hLocalHom
  let eB :=
    Towers.NumberTheory.Milne.centeredIntegerAdic
      w.1 hw hwna
  letI : Finite (IsLocalRing.ResidueField A₀) :=
    Towers.CField.LBrauer.local_field_residue
      v.Completion
  letI : Finite (IsLocalRing.ResidueField B) := by
    letI : Finite (IsLocalRing.ResidueField
        (Q.adicCompletionIntegers L)) :=
      Towers.CField.Ideles.adicResidueField
        Q
    exact Finite.of_equiv
      (IsLocalRing.ResidueField (Q.adicCompletionIntegers L))
      (IsLocalRing.ResidueField.mapEquiv eB).symm.toEquiv
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) := by infer_instance
  let hUnramified : Algebra.FormallyUnramified A₀ B := by
    apply Algebra.FormallyUnramified.of_map_maximalIdeal
    calc
      (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ B) =
          ((IsLocalRing.maximalIdeal A₀).map e₀.toRingHom).map
            (algebraMap A B) := by
        rw [Ideal.map_map]
        rfl
      _ = (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
        congr 1
        exact IsLocalRing.map_ringEquiv_maximalIdeal e₀
      _ = IsLocalRing.maximalIdeal B :=
        Algebra.FormallyUnramified.map_maximalIdeal
  letI : Algebra.IsIntegral A₀ B := Algebra.IsIntegral.of_finite A₀ B
  letI : IsFractionRing B w.1.Completion :=
    (Valuation.integer.integers
      (NormedField.valuation (K := w.1.Completion))).isFractionRing
  letI : IsIntegrallyClosed B :=
    (Valuation.integer.integers
      (NormedField.valuation (K := w.1.Completion))).isIntegrallyClosed
  let hIntegralClosure : IsIntegralClosure B A₀ w.1.Completion :=
    IsIntegralClosure.of_isIntegrallyClosed B A₀ w.1.Completion
  unfold CyclicUnramifiedCompletion
  dsimp only
  refine ⟨degree, hdegree, ⟨cyclicEquiv⟩, ⟨?_⟩⟩
  exact
    { model := B
      modelCommRing := inferInstance
      modelAlgebra := inferInstance
      modelToField := inferInstance
      modelTower := inferInstance
      modelIntegralClosure := hIntegralClosure
      modelFinite := hModuleFinite
      modelUnramified := hUnramified
      modelLocal := inferInstance
      modelLocalHom := hLocalHom }

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- A cyclic unramified completion kills the corresponding localization of a
finite-order central obstruction.  This packages the unramified local norm
calculation together with the completion/restriction comparison for crossed
products. -/
theorem brauer_change_completion
    {Q : Type v} {G : Type w} [Group Q] [Group G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (n : ℕ) [NeZero n] (hkernel : ∀ z : q.ker, z ^ n = 1)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    [Finite (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)]
    [Nonempty (Towers.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(L/K)
      (Towers.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    (hdata : CyclicUnramifiedCompletion P w) :
    let v := (FinitePlace.mk P).val
    letI : Algebra K v.Completion :=
      Towers.NumberTheory.Milne.completionBaseAlgebra v
    brauerBaseChange K v.Completion
        (extensionRelativeBrauer q hq hcentral galoisEquiv
          kernelToUnits hfixed : BrauerGroup K) = 1 := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨Towers.CField.Ideles.absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    Towers.CField.Ideles.placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    Towers.CField.Ideles.placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    Towers.CField.Ideles.placeValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    Towers.CField.Ideles.placeNonarchimedeanField P
  letI : Algebra v.Completion w.1.Completion :=
    (Towers.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionGalois v w
  let hvna : IsNonarchimedean v := fun x y ↦ (FinitePlace.mk P).add_le x y
  let D := Towers.NumberTheory.Milne.completionDecompositionField
    v hvna w
  let A := Valuation.integer (ValuativeRel.valuation v.Completion)
  letI : Algebra A w.1.Completion :=
    Algebra.ofSubring A
  change ∃ degree : ℕ, 0 < degree ∧
      Nonempty (Multiplicative (ZMod degree) ≃*
        Gal(w.1.Completion/v.Completion)) ∧
      Nonempty (UnramifiedModelData A w.1.Completion) at hdata
  obtain ⟨degree, hdegree, ⟨galoisCyclic⟩, ⟨data⟩⟩ := hdata
  letI : NeZero degree := ⟨hdegree.ne'⟩
  letI : CommRing data.model := data.modelCommRing
  letI : Algebra A data.model := data.modelAlgebra
  letI : Algebra data.model w.1.Completion := data.modelToField
  letI : IsScalarTower A data.model w.1.Completion := data.modelTower
  letI : IsIntegralClosure data.model A w.1.Completion :=
    data.modelIntegralClosure
  letI : Module.Finite A data.model := data.modelFinite
  letI : Algebra.FormallyUnramified A data.model := data.modelUnramified
  letI : IsLocalRing data.model := data.modelLocal
  letI : IsLocalHom (algebraMap A data.model) := data.modelLocalHom
  let f := completionDecomposition v hvna w galoisEquiv
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  let e := centralExtensionPullback q f
  let phiLocal := completionKernelUnits v w kernelToUnits
  have hfixedLocal : ∀ sigma : Gal(w.1.Completion/v.Completion),
      ∀ z : q.ker, sigma • phiLocal z = phiLocal z :=
    completion_units_fixed v hvna w kernelToUnits hfixed
  have hkernelPullback (z : p.ker) : z ^ n = 1 := by
    apply e.injective
    rw [map_pow, hkernel (e z), map_one]
  have hpzero :
      centralExtensionClass p hp hpc
          (MulEquiv.refl Gal(w.1.Completion/v.Completion))
          (phiLocal.comp e.toMonoidHom)
          (fun sigma z ↦ hfixedLocal sigma (e z)) = 1 :=
    @unramified_integral_model
      (CentralExtensionPullback q f) Gal(w.1.Completion/v.Completion)
      inferInstance inferInstance
      v.Completion w.1.Completion
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      data.model data.modelCommRing data.modelAlgebra data.modelToField
      data.modelTower data.modelIntegralClosure data.modelFinite
      data.modelUnramified data.modelLocal data.modelLocalHom
      degree inferInstance galoisCyclic
      p hp hpc (MulEquiv.refl Gal(w.1.Completion/v.Completion))
      (phiLocal.comp e.toMonoidHom)
      (fun sigma z ↦ hfixedLocal sigma (e z)) n inferInstance
      hkernelPullback
  apply brauer_change_obstruction
    q hq hcentral galoisEquiv kernelToUnits hfixed v hvna w
  rw [← central_extension_pullback
    q hq hcentral f phiLocal hfixedLocal]
  exact hpzero

set_option maxHeartbeats 2000000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- A tame local central obstruction vanishes once normalized order detects
the descended class on the unramified quotient.  The inertia restriction is
killed by a primitive root, while inflation for trivial integer coefficients
is injective because a finite group has no nonzero homomorphism to `Z`. -/
theorem mapped_obstruction_detector
    {Q G F : Type} [Group Q] [Finite Q] [Group G] [Finite G]
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [MulSemiringAction G F] [FaithfulSMul G F]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (I : Subgroup G) [I.Normal]
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (eI : Multiplicative (ZMod n) ≃* I)
    (phi : q.ker →* Fˣ) (hphi : Function.Injective phi)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (m : ℕ) (hm : 0 < m) (hkernel : ∀ z : q.ker, z ^ m = 1)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (horder : orderOf (q x) = n)
    (zeta : Fˣ) (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (hzetaFixed :
      letI : MulDistribMulAction I Fˣ :=
        (inferInstance : MulDistribMulAction G Fˣ).compHom Fˣ I.subtype
      ∀ i : I, i • zeta = zeta)
    (horderAut : ∀ g : G, ∀ z : Fˣ,
      localOrderHom F (g • z) =
        localOrderHom F z)
    (hdetector :
      letI : MulDistribMulAction G (Multiplicative ℤ) :=
        trivialDistribAction G (Multiplicative ℤ)
      ∀ y : groupCohomology
        ((Rep.ofMulDistribMulAction G Fˣ).quotientToInvariants I) 2,
      groupCohomology.map (MonoidHom.id (G ⧸ I))
          ((Rep.quotientToInvariantsFunctor ℤ I).map
            (MHTwo.coefficientRepHom
              (localOrderHom F)
              (fun g z ↦ by
                change localOrderHom F (g • z) =
                  localOrderHom F z
                exact horderAut g z))) 2 y = 0 →
        y = 0) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction G (Multiplicative ℤ) :=
    trivialDistribAction G (Multiplicative ℤ)
  let iAction : MulSemiringAction I F :=
    MulSemiringAction.compHom (R := F) I.subtype
  letI : MulSemiringAction I F := iAction
  let iFaithful : @FaithfulSMul I F iAction.toSMul :=
    { eq_of_smul_eq_smul := fun {a b} hab ↦ by
        apply Subtype.ext
        exact FaithfulSMul.eq_of_smul_eq_smul
          (M := G) (α := F) hab }
  letI : @FaithfulSMul I F iAction.toSMul := iFaithful
  have hH1F : IsZero (groupCohomology
      (Rep.res I.subtype (Rep.ofMulDistribMulAction G Fˣ)) 1) := by
    change IsZero (groupCohomology.H1
      (Rep.ofMulDistribMulAction I Fˣ))
    exact h_faithful_action (G := I) (F := F)
  have hH1Z : IsZero (groupCohomology
      (Rep.res I.subtype
        (Rep.ofMulDistribMulAction G (Multiplicative ℤ))) 1) := by
    change IsZero (groupCohomology (Rep.trivial ℤ I ℤ) 1)
    exact cohomology_trivial_int I
  let obstruction := extensionObstructionClass q hq hcentral
  let mapped := MHTwo.mapCoefficientsHom phi
    (fun g z ↦ (hfixed g z).symm) obstruction
  let ord := localOrderHom F
  let hord : ∀ g : G, ∀ z : Fˣ, ord (g • z) = g • ord z := by
    intro g z
    change localOrderHom F (g • z) =
      localOrderHom F z
    exact horderAut g z
  have hmap : MHTwo.mapCoefficientsHom ord hord mapped = 1 := by
    let compositeEquivariance : ∀ g : G, ∀ z : q.ker,
        (ord.comp phi) (g • z) = g • (ord.comp phi) z := by
      intro g z
      change ord (phi z) = ord (phi z)
      rfl
    rw [MHTwo.coefficients_hom_comp
      (f := phi) (g := ord)
      (fG := fun g z ↦ (hfixed g z).symm)
      (gG := hord) (gfG := compositeEquivariance)]
    apply MHTwo.coefficients_hom_forall
    intro z
    apply local_order_pow F m hm
    rw [← map_pow, hkernel z, map_one]
  apply MHTwo.eq_oneinflation_restricdetecto
    I mapped ord hord hH1F hH1Z
  · simpa using hdetector
  · exact mapped_restriction_primitive
      q hq hcentral I n hn eI phi hphi hfixed x hx horder
        zeta hzeta hzetaFixed
  · exact hmap

end TBluepr
end Towers

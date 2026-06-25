import Towers.ClassField.LocalBrauer.CanonicalUnramifiedData
import Towers.ClassField.LocalBrauer.IntegralModelFrobenius
import Towers.NumberTheory.Locals.UnramifiedExtensions

/-!
# Identifying an unramified integral model with the canonical level

Finite formally unramified DVR models with the same residue degree are
unique.  Passing to fraction fields identifies their fraction field with the
canonical unramified level.
-/

namespace Towers.CField.LClass

noncomputable section

universe u v

open ValuativeRel
open Towers.NumberTheory.Milne
open Towers.CField.LBrauer
open scoped NNReal NormedField

attribute [local instance] NormedField.toValued

private abbrev baseInteger (K : Type u) [NontriviallyNormedField K]
    [ValuativeRel K] := Valuation.integer (ValuativeRel.valuation K)

set_option maxHeartbeats 1000000 in
-- Both integral models carry dependent fraction-field and residue towers.
set_option synthInstance.maxHeartbeats 200000 in
/-- The fraction field of a finite formally unramified model of degree `f`
is the canonical unramified degree-`f` field. -/
theorem alg_level_model
    (K : Type u) (U F : Type v)
    [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [HenselianLocalRing U]
    [Field F] [Algebra K F]
    [Algebra (baseInteger K) U] [Module.Finite (baseInteger K) U]
    [Module.IsTorsionFree (baseInteger K) U]
    [Algebra.IsIntegral (baseInteger K) U]
    [Algebra.FormallyUnramified (baseInteger K) U]
    [IsLocalHom (algebraMap (baseInteger K) U)]
    [Algebra U F] [IsFractionRing U F]
    [Algebra (baseInteger K) F]
    [IsScalarTower (baseInteger K) U F]
    [IsScalarTower (baseInteger K) K F]
    [FiniteDimensional K F]
    (f : ℕ) [NeZero f] (hdegree : Module.finrank K F = f) :
    Nonempty (F ≃ₐ[K] canonicalUnramifiedLevel K f) := by
  let A := baseInteger K
  let C := canonicalUnramifiedLevel K f
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : HenselianLocalRing A := integer_henselian_ring K
  letI : IsFractionRing A K :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
  letI : Finite (IsLocalRing.ResidueField A) :=
    local_field_residue K
  letI : Algebra.IsAlgebraic K C := Algebra.IsAlgebraic.of_finite K C
  letI : NontriviallyNormedField C :=
    FLExt.nontriviallyNormedField K C
  letI : NormedAlgebra K C := spectralNorm.normedAlgebra K C
  letI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel C := FLExt.valuativeRel K C
  letI : Valuation.Compatible (NormedField.valuation (K := C)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := C))
  letI : IsNonarchimedeanLocalField C :=
    FLExt.nonarchimedeanLocalField K C
  let N := Valuation.integer (NormedField.valuation (K := C))
  letI : IsDiscreteValuationRing N := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation C)) :=
      discrete_valuation_ring C
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm C)
  letI : HenselianLocalRing N := valued_henselian_ring C
  letI : Algebra A N := valuativeSpectralAlgebra K C
  obtain ⟨hNfinite, hNunramified, hNtower, hNclosure⟩ :=
    level_spectral_data K f
  letI : Module.Finite A N := hNfinite
  letI : Algebra.FormallyUnramified A N := hNunramified
  letI : IsScalarTower A N C := hNtower
  letI : IsIntegralClosure N A C := hNclosure
  letI : Module.IsTorsionFree A N :=
    IsIntegralClosure.isTorsionFree A C
  letI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  letI : IsLocalHom (algebraMap A N) :=
    Algebra.IsIntegral.isLocalHom A N
  have hresU : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField U) = f := by
    rw [← formally_unramified_fraction
      A U K F, hdegree]
  have hresN : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField N) = f := by
    rw [← formally_unramified_fraction
      A N K C, unramified_level_finrank K f]
  let p := ringChar (IsLocalRing.ResidueField A)
  letI : Fact p.Prime :=
    ⟨CharP.char_is_prime (IsLocalRing.ResidueField A) p⟩
  letI : CharP (IsLocalRing.ResidueField A) p := ringChar.charP _
  obtain ⟨eUN⟩ :=
    nonempty_formally_finrank
      A U N p (hresU.trans hresN.symm)
  exact ⟨IsFractionRing.fieldEquivOfAlgEquiv K F C eUN⟩

end

end Towers.CField.LClass

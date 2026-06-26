import Towers.ClassField.UnramifiedCohom.FixedFieldUnits
import Towers.ClassField.LocalBrauer.SpectralIntegerClosure
import Towers.ClassField.LocalBrauer.UnitH2

/-!
# Integral-closure units and spectral units at a finite local layer

The fixed-field calculation for Corollary III.1.6 naturally produces the
integral closure of the base integer ring.  Proposition III.1.1 is stated
using the spectral valuation integers of the finite extension.  These are
canonically equivalent integral-closure models, and the equivalence is
Galois equivariant.
-/

namespace Towers.CField.UCohom

noncomputable section

open CategoryTheory
open Towers.CField.LBrauer
open ValuativeRel

attribute [local instance] Units.mulDistribMulActionRight

private abbrev A (K : Type) [NontriviallyNormedField K]
    [ValuativeRel K] := Valuation.integer (ValuativeRel.valuation K)

variable (K F : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field F] [Algebra K F] [Module.Finite K F] [IsGalois K F]

set_option maxHeartbeats 800000 in
-- Both canonical integral models carry deeply inferred Galois actions.
set_option synthInstance.maxHeartbeats 300000 in
/-- The units of the literal integral closure and the spectral valuation
integers are canonically isomorphic as integral Galois representations. -/
noncomputable def spectralRepIso :
    letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    letI : NontriviallyNormedField F :=
      FLExt.nontriviallyNormedField K F
    letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
    letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel F := FLExt.valuativeRel K F
    letI : MulSemiringAction Gal(F/K) 𝒪[F] :=
      FLExt.integerGaloisAction K F
    let U := integralClosure (A K) F
    letI : MulSemiringAction Gal(F/K) U :=
      IsIntegralClosure.MulSemiringAction (A K) K F U
    Rep.ofMulDistribMulAction Gal(F/K) Uˣ ≅
      Rep.ofMulDistribMulAction Gal(F/K) 𝒪[F]ˣ := by
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := F)) := spectralValuationExtension K F
  let U := integralClosure (A K) F
  letI : MulSemiringAction Gal(F/K) U :=
    IsIntegralClosure.MulSemiringAction (A K) K F U
  letI : MulSemiringAction Gal(F/K) 𝒪[F] :=
    FLExt.integerGaloisAction K F
  let N := Valuation.integer (NormedField.valuation (K := F))
  letI : Algebra (A K) N := valuativeSpectralAlgebra K F
  letI : IsScalarTower (A K) N F :=
    valuativeSpectralTower K F
  let eNorm := valuativeSpectralInteger K F U
  let eOut := valuativeIntegerNorm F
  let eRing : U ≃+* 𝒪[F] := eNorm.toRingEquiv.trans eOut.symm
  have eRing_coe (x : U) : ((eRing x : 𝒪[F]) : F) = (x : F) := by
    change ((eOut.symm (eNorm x) : 𝒪[F]) : F) = (x : F)
    change ((eNorm x : N) : F) = (x : F)
    exact valuative_spectral_integer K F U x
  let eUnits : Uˣ ≃* 𝒪[F]ˣ := Units.mapEquiv eRing.toMulEquiv
  let eAdd : Additive Uˣ ≃+ Additive 𝒪[F]ˣ := eUnits.toAdditive
  let eRep :
      (Rep.ofMulDistribMulAction Gal(F/K) Uˣ).ρ.Equiv
        (Rep.ofMulDistribMulAction Gal(F/K) 𝒪[F]ˣ).ρ :=
    Representation.Equiv.mk eAdd.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro u
      let uu : Uˣ :=
        (Rep.toAdditive (M := Gal(F/K)) (G := Uˣ) u).toMul
      change Additive.ofMul (eUnits (g • uu)) =
        Additive.ofMul (g • eUnits uu)
      apply Additive.toMul.injective
      change eUnits (g • uu) = g • eUnits uu
      apply Units.ext
      change eRing (g • (uu : U)) = g • eRing (uu : U)
      apply Subtype.ext
      change ((eRing (g • (uu : U)) : 𝒪[F]) : F) =
        (((g • eRing (uu : U) : 𝒪[F]) : 𝒪[F]) : F)
      calc
        ((eRing (g • (uu : U)) : 𝒪[F]) : F) =
            ((g • (uu : U) : U) : F) := eRing_coe _
        _ = g ((uu : U) : F) :=
          algebraMap.coe_smul' (B := U) (C := F) g (uu : U)
        _ = g ((eRing (uu : U) : 𝒪[F]) : F) := by
          exact congrArg g (eRing_coe (uu : U)).symm
        _ = ((g • eRing (uu : U) : 𝒪[F]) : F) :=
          (algebraMap.coe_smul' (B := 𝒪[F]) (C := F) g
            (eRing (uu : U))).symm)
  exact Rep.mkIso eRep

end

end Towers.CField.UCohom

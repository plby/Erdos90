import Submission.ClassField.LocalBrauer.SpectralUnramifiedOrder
import Submission.ClassField.LocalBrauer.PrincipalNormApproximation

/-!
# Norm data from an unramified integral model

A finite formally unramified local integral-closure model transports to the
spectral valuation integers.  The residue norm identity and the trace-one
principal-unit correction then give the full generator-free unit norm data.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open IsLocalRing ValuativeRel
open scoped BigOperators

private abbrev A (K : Type u) [NontriviallyNormedField K]
    [ValuativeRel K] := Valuation.integer (ValuativeRel.valuation K)

namespace FLExt

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

/-- A finite formally unramified local integral model supplies all unit norm
data for the canonical spectral local-field structure on its fraction
field. -/
theorem unramified_unit_model
    (U : Type u) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Module.Finite (A K) U] [Algebra.FormallyUnramified (A K) U]
    [IsLocalRing U] [IsLocalHom (algebraMap (A K) U)] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      nonarchimedeanLocalField K L
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : (ValuativeRel.valuation K).HasExtension
        (ValuativeRel.valuation L) := by
      constructor
      exact (ValuativeRel.isEquiv (ValuativeRel.valuation K)
        (NormedField.valuation (K := K))).trans
          ((Valuation.HasExtension.val_isEquiv_comap
            (vR := NormedField.valuation (K := K))
            (vA := NormedField.valuation (K := L))).trans
              ((ValuativeRel.isEquiv (ValuativeRel.valuation L)
                (NormedField.valuation (K := L))).symm.comap
                  (algebraMap K L)))
    UnramifiedUnitData K L (integerUnitNorm K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
    constructor
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation K)
      (NormedField.valuation (K := K))).trans
        ((Valuation.HasExtension.val_isEquiv_comap
          (vR := NormedField.valuation (K := K))
          (vA := NormedField.valuation (K := L))).trans
            ((ValuativeRel.isEquiv (ValuativeRel.valuation L)
              (NormedField.valuation (K := L))).symm.comap
                (algebraMap K L)))
  let B := 𝒪[L]
  have hBL : B = Valuation.integer
      (NormedField.valuation (K := L)) := valuative_integer_norm L
  letI : Algebra (A K) (Valuation.integer
      (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  letI : IsScalarTower (A K) (Valuation.integer
      (NormedField.valuation (K := L))) L :=
    valuativeSpectralTower K L
  let eBL : B ≃+* Valuation.integer
      (NormedField.valuation (K := L)) := RingEquiv.subringCongr hBL
  let eBLAlg : B ≃ₐ[A K] Valuation.integer
      (NormedField.valuation (K := L)) :=
    AlgEquiv.ofRingEquiv (f := eBL) (fun _ ↦ Subtype.ext rfl)
  letI : Module.Finite (A K) (Valuation.integer
      (NormedField.valuation (K := L))) :=
    spectral_module_model K L U
  letI : Algebra.FormallyUnramified (A K) (Valuation.integer
      (NormedField.valuation (K := L))) :=
    spectral_formally_model K L U
  letI : Module.Finite (A K) B :=
    Module.Finite.equiv eBLAlg.symm.toLinearEquiv
  letI : Algebra.FormallyUnramified (A K) B :=
    Algebra.FormallyUnramified.of_equiv eBLAlg.symm
  letI : IsIntegralClosure B (A K) L :=
    IsIntegralClosure.of_isIntegrallyClosed B (A K) L
  let G := Gal(L/K)
  letI : Fintype G := Fintype.ofFinite G
  letI : MulSemiringAction G B :=
    IsIntegralClosure.MulSemiringAction (A K) K L B
  letI : IsGaloisGroup G (A K) B :=
    IsGaloisGroup.of_isFractionRing G (A K) B K L
  letI : Finite (ResidueField B) := local_field_residue L
  have hprod (v : Bˣ) :
      algebraMap (A K) B (integerUnitNorm K L v : A K) =
        ∏ g : G, g • (v : B) := by
    apply IsFractionRing.injective B L
    calc
      algebraMap B L (algebraMap (A K) B
          (integerUnitNorm K L v : A K)) =
          algebraMap K L (Algebra.norm K (v : L)) := by
        change algebraMap K L
            (((integerUnitNorm K L v : A K) : K)) =
          algebraMap K L (Algebra.norm K (v : L))
        rw [integer_norm_coe]
      _ = ∏ g : G, g (v : L) := by
        rw [Algebra.norm_eq_prod_automorphisms]
        apply Finset.prod_congr
        · ext g
          simp
        · intro g _
          rfl
      _ = algebraMap B L (∏ g : G, g • (v : B)) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro g _
        exact (algebraMap.coe_smul' (B := B) (C := L) g (v : B)).symm
  refine
    { principal_mem := ?_
      residue_norm := ?_
      successive_approximation := ?_ }
  · intro m v hv
    exact sub_galois_product
      (G := G) (algebraMap (A K) B) m
      (integerUnitNorm K L v : A K) (v : B)
      (maximal_comap_formally m)
      (hprod v) hv
  · intro v
    apply Units.ext
    change residue (A K) (integerUnitNorm K L v : A K) =
      Algebra.norm (ResidueField (A K)) (residue B (v : B))
    exact residue_galois_unramified
      (A := A K) (B := B) (G := G)
      (IsDiscreteValuationRing.not_a_field (A K))
      (IsDiscreteValuationRing.not_a_field B)
      (integerUnitNorm K L v : A K) (v : B) (hprod v)
  · intro m hm u
    obtain ⟨v, hv, huv⟩ :=
      principal_formally_unramified
        (A := A K) (B := B) (G := G) (integerUnitNorm K L)
        hprod m hm u.1 u.2
    exact ⟨⟨v, hv⟩, huv⟩

/-- Existential packaging of the canonical residue-field algebra together
with the unit norm data. -/
theorem residue_unramified_model
    (U : Type u) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Module.Finite (A K) U] [Algebra.FormallyUnramified (A K) U]
    [IsLocalRing U] [IsLocalHom (algebraMap (A K) U)] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      nonarchimedeanLocalField K L
    ∃ hResidueAlgebra : Algebra (ResidueField (A K)) (ResidueField 𝒪[L]),
      letI : Algebra (ResidueField (A K)) (ResidueField 𝒪[L]) :=
        hResidueAlgebra
      UnramifiedUnitData K L (integerUnitNorm K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
    constructor
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation K)
      (NormedField.valuation (K := K))).trans
        ((Valuation.HasExtension.val_isEquiv_comap
          (vR := NormedField.valuation (K := K))
          (vA := NormedField.valuation (K := L))).trans
            ((ValuativeRel.isEquiv (ValuativeRel.valuation L)
              (NormedField.valuation (K := L))).symm.comap
                (algebraMap K L)))
  refine ⟨inferInstance, ?_⟩
  exact unramified_unit_model K L U

end FLExt

end

end Submission.CField.LBrauer

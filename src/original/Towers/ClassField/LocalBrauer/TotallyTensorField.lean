import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Towers.ClassField.LocalBrauer.TensorProductGalois
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedData
import Towers.NumberTheory.Locals.TotallyRamifiedEisenstein
import Towers.NumberTheory.Locals.UnramifiedExtensions

/-!
# Tensor products of unramified and totally ramified local extensions

This file proves the field-valuedness input needed by the tensor-compositum
Galois package.  The proof uses an Eisenstein generator of the totally
ramified extension.  Formal unramifiedness identifies maximal ideals, and
faithful flatness shows that the constant coefficient remains outside the
square of the maximal ideal after base change.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open Algebra IsLocalRing Polynomial
open Towers.NumberTheory.Milne
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- An Eisenstein polynomial stays Eisenstein after a finite torsion-free
formally unramified extension of discrete valuation rings. -/
theorem Polynomial.IsEisensteinAt.map_forma
    {A B : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsLocalHom (algebraMap A B)] [Algebra.FormallyUnramified A B]
    {f : A[X]}
    (hf : f.IsEisensteinAt (maximalIdeal A)) (hmonic : f.Monic) :
    (f.map (algebraMap A B)).IsEisensteinAt (maximalIdeal B) := by
  letI : Module.Free A B := Module.free_of_finite_type_torsion_free'
  letI : Module.FaithfullyFlat A B := inferInstance
  apply (hmonic.map (algebraMap A B)).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  · intro n hn
    rw [hmonic.natDegree_map (algebraMap A B)] at hn
    rw [coeff_map, ← Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B)]
    exact Ideal.mem_map_of_mem (algebraMap A B) (hf.mem hn)
  · intro hmem
    apply hf.notMem
    have hmap :
        ((maximalIdeal A) ^ 2).map (algebraMap A B) =
          (maximalIdeal B) ^ 2 := by
      rw [Ideal.map_pow, Algebra.FormallyUnramified.map_maximalIdeal]
    have hmem' : algebraMap A B (f.coeff 0) ∈
        ((maximalIdeal A) ^ 2).map (algebraMap A B) := by
      simpa [coeff_map, hmap] using hmem
    have hcomap : f.coeff 0 ∈
        (((maximalIdeal A) ^ 2).map (algebraMap A B)).comap
          (algebraMap A B) := hmem'
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hcomap

variable (A B C K U F : Type u)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [Field K] [Field U] [Field F]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [IsLocalHom (algebraMap A B)] [Algebra.FormallyUnramified A B]
  [Algebra A C] [Module.Finite A C] [Module.IsTorsionFree A C]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B U] [IsFractionRing B U]
  [Algebra C F] [IsFractionRing C F]
  [Algebra K U] [Algebra K F]
  [Algebra A U] [Algebra A F]
  [IsScalarTower A B U] [IsScalarTower A K U]
  [IsScalarTower A C F] [IsScalarTower A K F]
  [FiniteDimensional K U] [FiniteDimensional K F]

include B in
omit [FiniteDimensional K U] in
/-- The tensor product of a finite unramified extension and a finite totally
ramified extension of fraction fields is a field. -/
theorem formally_totally_ramified
    (htotal : Towers.NumberTheory.Milne.TotallyRamified
      A C (maximalIdeal A)) :
    IsField (U ⊗[K] F) := by
  obtain ⟨alpha, halpha, heis, hgen⟩ :=
    fraction_eisenstein_ramified
      A C K F htotal
  let alphaF : F := algebraMap C F alpha
  have hgenAlg : Algebra.adjoin K ({alphaF} : Set F) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic alphaF), hgen]
    rfl
  let pb : PowerBasis K F :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral alphaF) hgenAlg
  have hpbgen : pb.gen = alphaF :=
    PowerBasis.ofAdjoinEqTop_gen (Algebra.IsIntegral.isIntegral alphaF) hgenAlg
  let pA : A[X] := minpoly A alpha
  let pB : B[X] := pA.map (algebraMap A B)
  have hpAmonic : pA.Monic := minpoly.monic halpha
  have hpBeis : pB.IsEisensteinAt (maximalIdeal B) :=
    Towers.CField.LBrauer.Polynomial.IsEisensteinAt.map_forma
      heis hpAmonic
  have hpBirred : Irreducible pB := by
    apply hpBeis.irreducible (IsLocalRing.maximalIdeal.isMaximal B).isPrime
      (hpAmonic.map (algebraMap A B)).isPrimitive
    rw [hpAmonic.natDegree_map]
    exact minpoly.natDegree_pos halpha
  let q : U[X] := pB.map (algebraMap B U)
  have hqmonic : q.Monic :=
    (hpAmonic.map (algebraMap A B)).map (algebraMap B U)
  have hqirred : Irreducible q := by
    exact (hpAmonic.map (algebraMap A B)).irreducible_iff_irreducible_map_fraction_map.mp
      hpBirred
  let E := AdjoinRoot q
  letI : Fact (Irreducible q) := ⟨hqirred⟩
  letI : Field E := inferInstance
  letI : IsScalarTower K U E := inferInstance
  have hpK : minpoly K alphaF = pA.map (algebraMap A K) := by
    exact minpoly.isIntegrallyClosed_eq_field_fractions K F halpha
  have hq : q = (minpoly K pb.gen).map (algebraMap K U) := by
    rw [hpbgen, hpK]
    dsimp only [q, pB, pA]
    rw [map_map, map_map]
    congr 1
    exact (IsScalarTower.algebraMap_eq A B U).symm.trans
      (IsScalarTower.algebraMap_eq A K U)
  have hroot : aeval (AdjoinRoot.root q) (minpoly K pb.gen) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, IsScalarTower.algebraMap_eq K U E,
      ← map_map, ← hq]
    exact AdjoinRoot.isRoot_root q
  let fF : F →ₐ[K] E := pb.lift (AdjoinRoot.root q) hroot
  let f : U ⊗[K] F →ₐ[U] E :=
    AlgHom.liftEquiv K U F E fF
  letI : Module.Finite U E := (AdjoinRoot.powerBasis' hqmonic).finite
  have hf_surjective : Function.Surjective f := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← AdjoinRoot.adjoinRoot_eq_top (f := q)]
    apply Algebra.adjoin_le
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨(1 : U) ⊗ₜ[K] pb.gen, ?_⟩
    simp [f, fF]
  have hfinrank : Module.finrank U (U ⊗[K] F) = Module.finrank U E := by
    calc
      Module.finrank U (U ⊗[K] F) = Module.finrank K F :=
        Module.finrank_baseChange (R := U) (S := K) (M' := F)
      _ = pb.dim := pb.finrank
      _ = (minpoly K pb.gen).natDegree := pb.natDegree_minpoly.symm
      _ = q.natDegree := by rw [hq, (minpoly.monic pb.isIntegral_gen).natDegree_map]
      _ = Module.finrank U E := (AdjoinRoot.powerBasis' hqmonic).finrank.symm
  have hf_injective : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).2
      hf_surjective
  exact (AlgEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩).toMulEquiv.isField
    (Field.toIsField E)

section CanonicalLevel

open ValuativeRel

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

set_option maxHeartbeats 1000000 in
-- Unfolding the canonical level's transported integral model is deep.
set_option synthInstance.maxHeartbeats 200000 in
-- The tensor-field proof synthesizes both transported local-field structures.
omit [IsUltrametricDist F]
  [Valuation.Compatible (NormedField.valuation (K := F))] in
/-- A canonical unramified level and a totally ramified local extension are
linearly disjoint in the concrete sense that their tensor product is a
field. -/
theorem level_totally_ramified
    (n : ℕ) [NeZero n]
    (htotal : Towers.NumberTheory.Milne.TotallyRamified
      𝒪[K] 𝒪[F] (maximalIdeal 𝒪[K])) :
    IsField (canonicalUnramifiedLevel K n ⊗[K] F) := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing N := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E)) :=
      discrete_valuation_ring E
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm E)
  letI : Algebra 𝒪[K] N := valuativeSpectralAlgebra K E
  obtain ⟨hfinite, hunramified, htower, hclosure⟩ :=
    level_spectral_data K n
  letI : Module.Finite 𝒪[K] N := hfinite
  letI : Algebra.FormallyUnramified 𝒪[K] N := hunramified
  letI : IsScalarTower 𝒪[K] N E := htower
  letI : IsIntegralClosure N 𝒪[K] E := hclosure
  letI : Module.IsTorsionFree 𝒪[K] E :=
    Module.IsTorsionFree.trans_faithfulSMul 𝒪[K] K E
  letI : Module.IsTorsionFree 𝒪[K] N :=
    IsIntegralClosure.isTorsionFree 𝒪[K] E
  letI : Algebra.IsIntegral 𝒪[K] N := Algebra.IsIntegral.of_finite 𝒪[K] N
  letI : IsLocalHom (algebraMap 𝒪[K] N) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap 𝒪[K] N)).out 4 0).mp
    exact ((IsLocalRing.maximal_ideal_unique 𝒪[K]).unique
      (inferInstance : (IsLocalRing.maximalIdeal 𝒪[K]).IsMaximal)
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (IsLocalRing.maximalIdeal N))).symm
  exact formally_totally_ramified
    (A := 𝒪[K]) (B := N) (C := 𝒪[F]) (K := K) (U := E) (F := F) htotal

end CanonicalLevel

end

end Towers.CField.LBrauer

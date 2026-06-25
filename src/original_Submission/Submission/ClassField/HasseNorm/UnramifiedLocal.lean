import Submission.ClassField.Ideles.IdeleNorm
import Submission.ClassField.Ideles.PrincipalUnitsSubgroup
import Submission.ClassField.GrunwaldWang.AlgebraGlobalCompatibility
import Submission.NumberTheory.Completions.AdicLocalRing
import Submission.ClassField.LocalBrauer.IntegralModelFrobenius
import Submission.ClassField.Ideles.FinitePlaceCompletion

/-!
# Unramified finite-place norms for the Hasse norm theorem

This file transports Proposition III.1.2 to the precise prime-adic
completion coordinates used by the idèle norm.
-/

namespace Submission.CField.HNorm

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.UCohom
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.GWang
open scoped Topology

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

@[reducible]
noncomputable def adicNontriviallyNormed
    {K : Type*} [Field K] [NumberField K]
    (P : HeightOneSpectrum (RingOfIntegers K)) :
    NontriviallyNormedField (P.adicCompletion K) := by
  let F := P.adicCompletion K
  let hnormed : NormedField F :=
    { (inferInstance : NormedField F) with
      toField := (inferInstance : Field F) }
  let hnontriviallyNormed : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F (WithZero (Multiplicative ℤ))
  have hnormWitness : ∃ x : F, x ≠ 0 ∧ ‖x‖ ≠ 1 := by
    letI := hnontriviallyNormed
    obtain ⟨x, hxpos, hxlt⟩ := NormedField.exists_norm_lt_one F
    exact ⟨x, norm_pos_iff.mp hxpos, ne_of_lt hxlt⟩
  exact @NontriviallyNormedField.ofNormNeOne F hnormed hnormWitness

@[reducible]
noncomputable def adicValuativeRel
    {K : Type*} [Field K] [NumberField K]
    (P : HeightOneSpectrum (RingOfIntegers K)) :
    letI : NontriviallyNormedField (P.adicCompletion K) :=
      adicNontriviallyNormed P
    ValuativeRel (P.adicCompletion K) :=
  ValuativeRel.ofValuation
    (NormedField.valuation (K := P.adicCompletion K))

@[reducible]
noncomputable def adicNonarchimedeanField
    {K : Type*} [Field K] [NumberField K]
    (P : HeightOneSpectrum (RingOfIntegers K)) :
    letI : NontriviallyNormedField (P.adicCompletion K) :=
      adicNontriviallyNormed P
    letI : ValuativeRel (P.adicCompletion K) :=
      adicValuativeRel P
    IsNonarchimedeanLocalField (P.adicCompletion K) := by
  letI : NontriviallyNormedField (P.adicCompletion K) :=
    adicNontriviallyNormed P
  letI : IsUltrametricDist (P.adicCompletion K) := by infer_instance
  letI : ValuativeRel (P.adicCompletion K) :=
    adicValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := P.adicCompletion K)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := P.adicCompletion K))
  haveI htop : IsValuativeTopology (P.adicCompletion K) := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : P.adicCompletion K) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := P.adicCompletion K)))ˣ,
          {x | (NormedField.valuation
            (K := P.adicCompletion K)).restrict x < γ.1} ⊆ s from
      (NormedField.toValued
        (K := P.adicCompletion K)).is_topological_valuation s]
    simpa using (NormedField.valuation (K := P.adicCompletion K))
      |>.exists_setOf_restrict_le_iff 0 s
  letI hcompact : LocallyCompactSpace (P.adicCompletion K) :=
    adicLocallySpace P
  haveI hnontrivial : ValuativeRel.IsNontrivial (P.adicCompletion K) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := P.adicCompletion K))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent completion-coordinate tower requires a larger search budget.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- The integral semilocal completion coordinate agrees with the global
integer embedding. -/
theorem adic_integer_global
    (P : HeightOneSpectrum (RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    let R := RingOfIntegers K
    let S := RingOfIntegers L
    let q := upperPrime (K := K) (L := L) P Q
    let C := P.adicCompletionIntegers K
    let D := q.adicCompletionIntegers L
    let hP : P.asIdeal.map (algebraMap R S) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    letI : Algebra C D :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    ∀ r : R, algebraMap C D (algebraMap R C r) =
      algebraMap S D (algebraMap R S r) := by
  dsimp only
  let R := RingOfIntegers K
  let S := RingOfIntegers L
  let q := upperPrime (K := K) (L := L) P Q
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let D := q.adicCompletionIntegers L
  let E := q.adicCompletion L
  let hP : P.asIdeal.map (algebraMap R S) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C D :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra D E := D.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C D E :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Algebra C F := C.subtype.toAlgebra
  letI : IsScalarTower C F E :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  intro r
  apply Subtype.ext
  change algebraMap D E (algebraMap C D (algebraMap R C r)) =
    algebraMap D E (algebraMap S D (algebraMap R S r))
  have hfield := RingHom.congr_fun
    (factor_algebra_global (K := K) (L := L) P Q)
    (algebraMap R K r)
  calc
    algebraMap D E (algebraMap C D (algebraMap R C r)) =
        algebraMap C E (algebraMap R C r) :=
      (IsScalarTower.algebraMap_apply C D E (algebraMap R C r)).symm
    _ = algebraMap F E (algebraMap C F (algebraMap R C r)) :=
      adic_integer_algebra
        (K := K) (L := L) P hP Q (algebraMap R C r)
    _ = algebraMap F E (algebraMap K F (algebraMap R K r)) := by rfl
    _ =
        algebraMap L E (algebraMap K L (algebraMap R K r)) := hfield
    _ = algebraMap L E (algebraMap S L (algebraMap R S r)) := by
      congr 1
    _ = algebraMap D E (algebraMap S D (algebraMap R S r)) := by rfl

set_option synthInstance.maxHeartbeats 300000 in
-- The completed semilocal coordinate algebra requires a larger search budget.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- Global unramifiedness makes the lower completed maximal ideal extend to
the upper completed maximal ideal. -/
theorem adic_maximal_unramified
    (P : HeightOneSpectrum (RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt (RingOfIntegers K)
      (upperPrime (K := K) (L := L) P Q).asIdeal) :
    let R := RingOfIntegers K
    let S := RingOfIntegers L
    let q := upperPrime (K := K) (L := L) P Q
    let C := P.adicCompletionIntegers K
    let D := q.adicCompletionIntegers L
    let hP : P.asIdeal.map (algebraMap R S) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    letI : Algebra C D :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    (IsLocalRing.maximalIdeal C).map (algebraMap C D) =
      IsLocalRing.maximalIdeal D := by
  dsimp only
  let R := RingOfIntegers K
  let S := RingOfIntegers L
  let q := upperPrime (K := K) (L := L) P Q
  let C := P.adicCompletionIntegers K
  let D := q.adicCompletionIntegers L
  let hP : P.asIdeal.map (algebraMap R S) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra C D :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : q.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Q)).symm
  letI := Localization.AtPrime.algebraOfLiesOver P.asIdeal q.asIdeal
  let A := Localization.AtPrime q.asIdeal
  let f : A →+* D := primeAdicIntegers (K := L) q
  have hloc : P.asIdeal.map (algebraMap R A) =
      IsLocalRing.maximalIdeal A :=
    ((Algebra.isUnramifiedAt_iff_map_eq R P.asIdeal q.asIdeal).mp hQ).2
  have hcomp : f.comp (algebraMap R A) =
      (algebraMap C D).comp (algebraMap R C) := by
    apply DFunLike.ext _ _
    intro r
    change f (algebraMap R A r) = algebraMap C D (algebraMap R C r)
    rw [show f (algebraMap R A r) =
        algebraMap S D (algebraMap R S r) by
      exact adic_integers_algebra (K := L) q
        (algebraMap R S r)]
    exact (adic_integer_global
      (K := K) (L := L) P Q r).symm
  calc
    (IsLocalRing.maximalIdeal C).map (algebraMap C D) =
        (P.asIdeal.map (algebraMap R C)).map (algebraMap C D) := by
      rw [adic_integers_maximal (K := K) P]
    _ = P.asIdeal.map ((algebraMap C D).comp (algebraMap R C)) :=
      Ideal.map_map (algebraMap R C) (algebraMap C D)
    _ = P.asIdeal.map (f.comp (algebraMap R A)) := by rw [hcomp]
    _ = (P.asIdeal.map (algebraMap R A)).map f :=
      (Ideal.map_map (algebraMap R A) f).symm
    _ = (IsLocalRing.maximalIdeal A).map f := by rw [hloc]
    _ = IsLocalRing.maximalIdeal D :=
      maximal_completion_integers (K := L) q

set_option synthInstance.maxHeartbeats 300000 in
-- The local-field and integral-closure structures are transported together.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- If the chosen upper prime is unramified, every unit in the lower
prime-adic completion is the norm of an *upper local unit*.  Keeping the
integrality of the witness is the form needed for the local-unit factors in
the restricted-product cohomology calculation. -/
theorem units_surjective_unramified
    (P : HeightOneSpectrum (RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt (RingOfIntegers K)
      (upperPrime (K := K) (L := L) P Q).asIdeal) :
    ∀ x : IdeleUnitSubgroup (RingOfIntegers K) K P,
      ∃ y : IdeleUnitSubgroup (RingOfIntegers L) L
          (upperPrime (K := K) (L := L) P Q),
        finiteCompletionNorm (K := K) (L := L) P Q y.1 = x.1 := by
  let R := RingOfIntegers K
  let S := RingOfIntegers L
  let q := upperPrime (K := K) (L := L) P Q
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let D := q.adicCompletionIntegers L
  let E := q.adicCompletion L
  let hP : P.asIdeal.map (algebraMap R S) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Module.Finite F E :=
    finite_completion_module (K := K) (L := L) P Q
  letI : Algebra C D :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Module.Finite C D :=
    adic_integer_module (K := K) (L := L) P hP Q
  letI : Algebra D E := D.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C D E :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Algebra C F := C.subtype.toAlgebra
  letI : IsScalarTower C F E :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  have hmax : (IsLocalRing.maximalIdeal C).map (algebraMap C D) =
      IsLocalRing.maximalIdeal D :=
    adic_maximal_unramified
      (K := K) (L := L) P Q hQ
  letI : NontriviallyNormedField F :=
    adicNontriviallyNormed P
  letI : IsUltrametricDist F := by infer_instance
  letI : ValuativeRel F := adicValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    adicNonarchimedeanField P
  let A := Valuation.integer (ValuativeRel.valuation F)
  let eA : A ≃+* C :=
    (valuativeIntegerNorm F).trans
      (normedIntegerIntegers P)
  letI : Algebra A D := RingHom.toAlgebra <|
    (algebraMap C D).comp eA.toRingHom
  letI : Module.Finite A D := by
    apply Module.Finite.of_equiv_equiv eA.symm (RingEquiv.refl D)
    ext x
    rfl
  let hTowerADE : IsScalarTower A D E :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext a
      change algebraMap F E (a : F) =
        algebraMap D E (algebraMap C D (eA a))
      calc
        algebraMap F E (a : F) =
            algebraMap F E ((eA a : C) : F) := by rfl
        _ = algebraMap C E (eA a) :=
          (IsScalarTower.algebraMap_apply C F E (eA a)).symm
        _ = algebraMap D E (algebraMap C D (eA a)) :=
          IsScalarTower.algebraMap_apply C D E (eA a)
  letI : IsScalarTower A D E := hTowerADE
  letI : IsScalarTower
      (Valuation.integer (ValuativeRel.valuation F)) D E := by
    change IsScalarTower A D E
    exact hTowerADE
  have hmaxA : (IsLocalRing.maximalIdeal A).map (algebraMap A D) =
      IsLocalRing.maximalIdeal D := by
    calc
      (IsLocalRing.maximalIdeal A).map (algebraMap A D) =
          ((IsLocalRing.maximalIdeal A).map eA.toRingHom).map
            (algebraMap C D) := by
        rw [Ideal.map_map]
        rfl
      _ = (IsLocalRing.maximalIdeal C).map (algebraMap C D) := by
        exact congrArg (fun I : Ideal C ↦ I.map (algebraMap C D))
          (IsLocalRing.map_ringEquiv_maximalIdeal eA)
      _ = IsLocalRing.maximalIdeal D := hmax
  letI : IsLocalHom (algebraMap A D) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A D)).out 2 0).mp
      (le_of_eq hmaxA)
  letI : Finite (IsLocalRing.ResidueField A) := by
    letI : Finite (IsLocalRing.ResidueField C) :=
      adicResidueField P
    exact Finite.of_equiv (IsLocalRing.ResidueField C)
      (IsLocalRing.ResidueField.mapEquiv eA).symm.toEquiv
  letI : Finite (IsLocalRing.ResidueField D) :=
    adicResidueField q
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField D) := by infer_instance
  letI : Algebra.FormallyUnramified A D :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmaxA
  letI : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal D) :=
    unramified_maximal_formally A D
  letI : Algebra.IsIntegral A D := Algebra.IsIntegral.of_finite A D
  letI : IsFractionRing D E :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := S) (K := L) (v := q)).isFractionRing
  letI : IsIntegralClosure D A E :=
    IsIntegralClosure.of_isIntegrallyClosed D A E
  intro x
  let c : C := ⟨(x.1 : F), x.2.1⟩
  have hcunit : IsUnit c := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mp x.2
  let cu : Cˣ := hcunit.unit
  have hcu : (cu : C) = c := hcunit.unit_spec
  let u : Aˣ := Units.map eA.symm.toMonoidHom cu
  have hu : (((u : A) : F)) = (x.1 : F) := by
    change ((eA.symm (cu : C) : A) : F) = (x.1 : F)
    rw [hcu]
    rfl
  have hsurjective :=
    @model_units_surjective
      F E
      (inferInstance : NontriviallyNormedField F)
      (inferInstance : IsUltrametricDist F)
      (inferInstance : ValuativeRel F)
      (inferInstance : IsNonarchimedeanLocalField F)
      (inferInstance :
        Valuation.Compatible (NormedField.valuation (K := F)))
      (inferInstance : Field E)
      (inferInstance : Algebra F E)
      (inferInstance : Module.Finite F E)
      D
      (inferInstance : CommRing D)
      (inferInstance : Algebra A D)
      (inferInstance : Algebra D E)
      hTowerADE
      (inferInstance : IsIntegralClosure D A E)
      (inferInstance : Module.Finite A D)
      (inferInstance : IsLocalRing D)
      (inferInstance :
        Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal D))
  obtain ⟨y, hy⟩ := hsurjective u
  let z : Eˣ := Units.map D.subtype.toMonoidHom y
  have hzunit : z ∈ IdeleUnitSubgroup S L q := by
    rw [Submonoid.mem_units_iff]
    exact ⟨y.val.property, y.inv.property⟩
  refine ⟨⟨z, hzunit⟩, ?_⟩
  apply Units.ext
  change Algebra.norm F ((z : E)) = (x.1 : F)
  exact hy.trans hu

set_option synthInstance.maxHeartbeats 300000 in
-- This is the range-valued consequence used by the localization support proof.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- If the chosen upper prime is unramified, every unit in the lower
prime-adic completion is a norm from the chosen upper completion. -/
theorem units_range_unramified
    (P : HeightOneSpectrum (RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt (RingOfIntegers K)
      (upperPrime (K := K) (L := L) P Q).asIdeal) :
    IdeleUnitSubgroup (RingOfIntegers K) K P ≤
      (finiteCompletionNorm (K := K) (L := L) P Q).range := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    units_surjective_unramified
      (K := K) (L := L) P Q hQ ⟨x, hx⟩
  exact ⟨y.1, hy⟩

end

end Submission.CField.HNorm

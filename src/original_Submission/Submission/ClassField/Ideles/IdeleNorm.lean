import Submission.NumberTheory.Completions.CompletionNormTrace
import Submission.NumberTheory.Completions.SemilocalCoordinateAlgebra
import Submission.NumberTheory.Completions.CoordinateCompatibility
import Submission.ClassField.Ideles.Ideles


/-!
# Local coordinates of the idele norm

For a finite extension of number fields, the norm at a finite base place is
the product of the field norms over all completed places above it.  This file
constructs those local homomorphisms using the semilocal completion
decomposition already available in the ANT development.
-/

namespace Submission.CField.Ideles

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The finite set of primes above a fixed finite prime, represented as the
prime factors of its extension to the upper integer ring. -/
abbrev UpperPrimeFactors
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  (UniqueFactorizationMonoid.factors
    (P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)))).toFinset

/-- The upper height-one prime represented by a factor in
`UpperPrimeFactors`. -/
abbrev upperPrime
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    HeightOneSpectrum (NumberField.RingOfIntegers L) :=
  factorHeightSpectrum
    (P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L))) Q

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
private theorem mapped_prime_bot
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot P.ne_bot

set_option synthInstance.maxHeartbeats 300000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
-- Injectivity is checked after including both valuation rings into their
-- completed fraction fields.
omit [FiniteDimensional K L] in
private theorem integer_torsion_free
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    let C := P.adicCompletionIntegers K
    let B := (upperPrime (K := K) (L := L) P Q).adicCompletionIntegers L
    letI : Algebra C B :=
      adicCompletionAlgebra
        (K := K) (L := L) P (mapped_prime_bot (K := K) (L := L) P) Q
    Module.IsTorsionFree C B := by
  let hP := mapped_prime_bot (K := K) (L := L) P
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let vQ := upperPrime (K := K) (L := L) P Q
  let B := vQ.adicCompletionIntegers L
  let E := vQ.adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C F E :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.val_injective
  apply (algebraMap F E).injective
  calc
    algebraMap F E (x : F) = algebraMap C E x :=
      (adic_integer_algebra
        (K := K) (L := L) P hP Q x).symm
    _ = algebraMap C E y := congrArg (fun z : B => (z : E)) hxy
    _ = algebraMap F E (y : F) :=
      adic_integer_algebra
        (K := K) (L := L) P hP Q y

omit [FiniteDimensional K L] in
theorem upperPrime_under
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    (upperPrime (K := K) (L := L) P Q).under
        (NumberField.RingOfIntegers K) = P := by
  apply HeightOneSpectrum.ext_iff.mpr
  have hmem : (Q.1 : Ideal (NumberField.RingOfIntegers L)) ∈
      UniqueFactorizationMonoid.normalizedFactors
        (P.asIdeal.map (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L))) := by
    have h := Multiset.mem_toFinset.mp Q.property
    rwa [UniqueFactorizationMonoid.factors_eq_normalizedFactors] at h
  apply ((Ideal.liesOver_iff_dvd_map
    (upperPrime (K := K) (L := L) P Q).isPrime.ne_top).mpr ?_).over.symm
  change (Q.1 : Ideal (NumberField.RingOfIntegers L)) ∣
    P.asIdeal.map (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L))
  exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem

set_option synthInstance.maxHeartbeats 300000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
-- The scalar-extension decomposition supplies the finite coordinate through
-- a dependent product of all completions above the base prime.
omit [FiniteDimensional K L] in
theorem finite_completion_module
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    letI : Algebra (P.adicCompletion K)
        ((upperPrime (K := K) (L := L) P Q).adicCompletion L) :=
      adicFactorAlgebra
        (K := K) (L := L) P (mapped_prime_bot (K := K) (L := L) P) Q
    Module.Finite (P.adicCompletion K)
      ((upperPrime (K := K) (L := L) P Q).adicCompletion L) := by
  let hP := mapped_prime_bot (K := K) (L := L) P
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let vQ := upperPrime (K := K) (L := L) P Q
  let B := vQ.adicCompletionIntegers L
  let E := vQ.adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C B E :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C F E :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Module.Finite C B :=
    adic_integer_module (K := K) (L := L) P hP Q
  letI : Algebra.IsIntegral C B :=
    adic_integer_integral (K := K) (L := L) P hP Q
  letI : Module.IsTorsionFree C B :=
    integer_torsion_free (K := K) (L := L) P Q
  letI : FaithfulSMul C B := by
    rw [faithfulSMul_iff_algebraMap_injective,
      ← Module.isTorsionFree_iff_algebraMap_injective]
    infer_instance
  letI : IsFractionRing C F :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := NumberField.RingOfIntegers K) (K := K) (v := P)).isFractionRing
  letI : IsFractionRing B E :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := NumberField.RingOfIntegers L) (K := L) (v := vQ)).isFractionRing
  apply FiniteDimensional.of_finrank_pos
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing C F B E]
  exact Module.finrank_pos

/-- The field norm on one completed factor above a finite base prime. -/
noncomputable def finiteCompletionNorm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    ((upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ →*
      (P.adicCompletion K)ˣ := by
  let hP := mapped_prime_bot (K := K) (L := L) P
  letI : Algebra (P.adicCompletion K)
      ((upperPrime (K := K) (L := L) P Q).adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  letI : Module.Finite (P.adicCompletion K)
      ((upperPrime (K := K) (L := L) P Q).adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P Q
  exact Units.map (Algebra.norm (P.adicCompletion K))

set_option synthInstance.maxHeartbeats 300000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1500000 in
omit [FiniteDimensional K L] in
/-- A completed field norm carries an upper valuation-ring unit to a lower
valuation-ring unit. -/
theorem completion_unit_subgroup
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (z : ((upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ)
    (hz : z ∈ (Submonoid.ofClass
      ((upperPrime (K := K) (L := L) P Q).adicCompletionIntegers L)).units) :
    finiteCompletionNorm (K := K) (L := L) P Q z ∈
      (Submonoid.ofClass (P.adicCompletionIntegers K)).units := by
  let hP := mapped_prime_bot (K := K) (L := L) P
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let vQ := upperPrime (K := K) (L := L) P Q
  let B := vQ.adicCompletionIntegers L
  let E := vQ.adicCompletion L
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C B E :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C F E :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Module.Finite F E :=
    finite_completion_module (K := K) (L := L) P Q
  letI : Algebra.IsIntegral C B :=
    adic_integer_integral (K := K) (L := L) P hP Q
  letI : Module.IsTorsionFree C B :=
    integer_torsion_free (K := K) (L := L) P Q
  letI : IsFractionRing C F :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := NumberField.RingOfIntegers K) (K := K) (v := P)).isFractionRing
  letI : IsFractionRing B E :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := NumberField.RingOfIntegers L) (K := L) (v := vQ)).isFractionRing
  let uB : Bˣ :=
    Submonoid.unitsEquivUnitsType (Submonoid.ofClass B) ⟨z, hz⟩
  let uC : Cˣ := Units.map (Algebra.intNorm C B) uB
  have hnorm : finiteCompletionNorm (K := K) (L := L) P Q z =
      Units.map (algebraMap C F) uC := by
    apply Units.ext
    change Algebra.norm F (z : E) = algebraMap C F (Algebra.intNorm C B (uB : B))
    rw [Algebra.algebraMap_intNorm (K := F) (L := E)]
    rfl
  rw [hnorm]
  exact ⟨uC.val.property, uC.inv.property⟩

/-- The finite-place coordinate of the idele norm: multiply the completed
field norms over every prime above `P`. -/
noncomputable def finiteNorm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FiniteIdeles (NumberField.RingOfIntegers L) L →*
      (P.adicCompletion K)ˣ where
  toFun x := ∏ Q : UpperPrimeFactors (K := K) (L := L) P,
    finiteCompletionNorm (K := K) (L := L) P Q
      (x.1 (upperPrime (K := K) (L := L) P Q))
  map_one' := by
    change (∏ Q : UpperPrimeFactors (K := K) (L := L) P,
      finiteCompletionNorm (K := K) (L := L) P Q 1) = 1
    simp
  map_mul' x y := by
    change (∏ Q : UpperPrimeFactors (K := K) (L := L) P,
      finiteCompletionNorm (K := K) (L := L) P Q
        (x.1 (upperPrime (K := K) (L := L) P Q) *
          y.1 (upperPrime (K := K) (L := L) P Q))) = _
    simp only [map_mul, Finset.prod_mul_distrib]

omit [FiniteDimensional K L] in
private theorem idele_norm_eventually
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L) :
    ∀ᶠ P in Filter.cofinite,
      finiteNorm (K := K) (L := L) P x ∈
        IdeleUnitSubgroup (NumberField.RingOfIntegers K) K P := by
  classical
  let badUpper : Set (HeightOneSpectrum (NumberField.RingOfIntegers L)) :=
    {Q | x.1 Q ∉ IdeleUnitSubgroup
      (NumberField.RingOfIntegers L) L Q}
  have hbadUpper : badUpper.Finite := by
    exact Filter.eventually_cofinite.mp x.property
  let contract : HeightOneSpectrum (NumberField.RingOfIntegers L) →
      HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    fun Q ↦ Q.under (NumberField.RingOfIntegers K)
  have hbadLower : (contract '' badUpper).Finite := hbadUpper.image contract
  rw [Filter.eventually_cofinite]
  refine hbadLower.subset ?_
  intro P hP
  by_contra hPimage
  apply hP
  change (∏ Q : UpperPrimeFactors (K := K) (L := L) P,
    finiteCompletionNorm (K := K) (L := L) P Q
      (x.1 (upperPrime (K := K) (L := L) P Q))) ∈
        IdeleUnitSubgroup (NumberField.RingOfIntegers K) K P
  apply Subgroup.prod_mem
  intro Q _
  apply completion_unit_subgroup (K := K) (L := L)
  by_contra hQ
  apply hPimage
  refine ⟨upperPrime (K := K) (L := L) P Q, hQ, ?_⟩
  exact upperPrime_under (K := K) (L := L) P Q

/-- The norm on finite ideles, with the coordinate at `P` equal to the
product of the local norms over all primes above `P`. -/
noncomputable def finiteIdeleNorm :
    FiniteIdeles (NumberField.RingOfIntegers L) L →*
      FiniteIdeles (NumberField.RingOfIntegers K) K where
  toFun x := RestrictedProduct.mk
    (fun P ↦ finiteNorm (K := K) (L := L) P x)
    (idele_norm_eventually (K := K) (L := L) x)
  map_one' := by
    apply RestrictedProduct.ext
    intro P
    change finiteNorm (K := K) (L := L) P 1 = 1
    exact map_one (finiteNorm (K := K) (L := L) P)
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro P
    change finiteNorm (K := K) (L := L) P (x * y) =
      finiteNorm (K := K) (L := L) P x *
        finiteNorm (K := K) (L := L) P y
    exact map_mul (finiteNorm (K := K) (L := L) P) x y

omit [FiniteDimensional K L] in
@[simp]
theorem finite_idele_norm
    (x : FiniteIdeles (NumberField.RingOfIntegers L) L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (finiteIdeleNorm (K := K) (L := L) x).1 P =
      finiteNorm (K := K) (L := L) P x :=
  rfl

/-- The infinite places of `L` above a fixed infinite place of `K`. -/
abbrev InfinitePlacesAbove
    (v : NumberField.InfinitePlace K) :=
  {w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v}

noncomputable local instance infinitePlacesAboveFintype
    (v : NumberField.InfinitePlace K) :
    Fintype (InfinitePlacesAbove (K := K) (L := L) v) := by
  exact infiniteCor84ExtensionsFintype v

set_option synthInstance.maxHeartbeats 300000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
omit [NumberField L] in
omit [NumberField K] in
theorem infinite_completion_module
    (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toAlgebra
    Module.Finite v.1.Completion w.1.1.Completion := by
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  letI : Module.Finite v.1.Completion (v.1.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.1.Completion L
  letI : Module.Finite v.1.Completion (L ⊗[K] v.1.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.1.Completion L).toLinearEquiv
  exact Module.Finite.of_surjective
    (infiniteTensorPlace v w).toLinearMap
    (infinite_tensor_surjective v w)

/-- The field norm from one archimedean completion above `v`. -/
noncomputable def infiniteCompletionNorm
    (v : NumberField.InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    w.1.1.Completionˣ →* v.1.Completionˣ := by
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  exact Units.map (Algebra.norm v.1.Completion)

/-- The coordinate of the infinite idele norm at `v`. -/
noncomputable def infiniteNorm
    (v : NumberField.InfinitePlace K) :
    (InfiniteAdeleRing L)ˣ →* v.1.Completionˣ := by
  classical
  exact
    { toFun := fun x => ∏ w : InfinitePlacesAbove (K := K) (L := L) v,
        infiniteCompletionNorm (K := K) (L := L) v w
          (MulEquiv.piUnits x w.1)
      map_one' := by
        apply Finset.prod_eq_one
        intro w _
        rw [show MulEquiv.piUnits (1 : (InfiniteAdeleRing L)ˣ) w.1 = 1 by
          exact congrFun (map_one (MulEquiv.piUnits :
            (InfiniteAdeleRing L)ˣ ≃*
              ((w : InfinitePlace L) → w.1.Completionˣ))) w.1]
        exact map_one (infiniteCompletionNorm (K := K) (L := L) v w)
      map_mul' := by
        intro x y
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro w _
        rw [show MulEquiv.piUnits (x * y) w.1 =
            MulEquiv.piUnits x w.1 * MulEquiv.piUnits y w.1 by
          exact congrFun (map_mul (MulEquiv.piUnits :
            (InfiniteAdeleRing L)ˣ ≃*
              ((w : InfinitePlace L) → w.1.Completionˣ)) x y) w.1]
        exact map_mul (infiniteCompletionNorm (K := K) (L := L) v w) _ _ }

omit [NumberField L] in
@[simp]
theorem infinite_norm
    (v : NumberField.InfinitePlace K) (x : (InfiniteAdeleRing L)ˣ) :
    infiniteNorm (K := K) (L := L) v x =
      ∏ w : InfinitePlacesAbove (K := K) (L := L) v,
        infiniteCompletionNorm (K := K) (L := L) v w
          (MulEquiv.piUnits x w.1) :=
  by
    classical
    rfl

/-- The norm on the archimedean component of the ideles. -/
noncomputable def infiniteIdeleNorm :
    (InfiniteAdeleRing L)ˣ →* (InfiniteAdeleRing K)ˣ where
  toFun x := MulEquiv.piUnits.symm
    (fun v ↦ infiniteNorm (K := K) (L := L) v x)
  map_one' := by
    apply MulEquiv.piUnits.injective
    funext v
    rw [MulEquiv.apply_symm_apply, map_one]
    exact (congrFun (map_one (MulEquiv.piUnits :
      (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.1.Completionˣ))) v).symm
  map_mul' x y := by
    apply MulEquiv.piUnits.injective
    funext v
    rw [MulEquiv.apply_symm_apply, map_mul]
    simpa only [MulEquiv.apply_symm_apply] using
      (congrFun (map_mul (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.1.Completionˣ))
          (MulEquiv.piUnits.symm
            (fun v ↦ infiniteNorm (K := K) (L := L) v x))
          (MulEquiv.piUnits.symm
            (fun v ↦ infiniteNorm (K := K) (L := L) v y))) v).symm

omit [NumberField L] in
@[simp]
theorem infinite_idele
    (x : (InfiniteAdeleRing L)ˣ) (v : NumberField.InfinitePlace K) :
    MulEquiv.piUnits (infiniteIdeleNorm (K := K) (L := L) x) v =
      infiniteNorm (K := K) (L := L) v x := by
  exact congrFun (MulEquiv.apply_symm_apply (MulEquiv.piUnits :
    (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.1.Completionˣ))
      (fun v ↦ infiniteNorm (K := K) (L := L) v x)) v

/-- The global idele norm, formed from its archimedean and finite
components. -/
noncomputable def ideleNorm :
    IdeleGroup (NumberField.RingOfIntegers L) L →*
      IdeleGroup (NumberField.RingOfIntegers K) K :=
  (infiniteIdeleNorm (K := K) (L := L)).prodMap
    (finiteIdeleNorm (K := K) (L := L))

@[simp]
theorem ideleNorm_apply
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    ideleNorm (K := K) (L := L) x =
      (infiniteIdeleNorm (K := K) (L := L) x.1,
        finiteIdeleNorm (K := K) (L := L) x.2) :=
  rfl

/-- The subgroup of ideles which are norms from `L`. -/
def ideleNormSubgroup :
    Subgroup (IdeleGroup (NumberField.RingOfIntegers K) K) :=
  (ideleNorm (K := K) (L := L)).range

end

end Submission.CField.Ideles

import Mathlib.GroupTheory.QuotientGroup.Basic
import Towers.NumberTheory.Completions.DifferentCompletionConcrete
import Towers.NumberTheory.Completions.PureTensorLocalization
import Towers.ClassField.Ideles.IdeleNorm


/-!
# The norm on idele class groups

The idele norm descends to idele classes once one knows that it sends a
principal idele to the principal idele of the field norm.  This file isolates
that arithmetic compatibility from the formal quotient construction.  It also
identifies the range of the descended map with the image in the idele class
group of the idele-norm subgroup used in Chapter V, Section 5.
-/

namespace Towers.CField.Ideles

open Ideal IsDedekindDomain NumberField nonZeroDivisors
open Towers.NumberTheory.Milne
open scoped TensorProduct

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

set_option synthInstance.maxHeartbeats 300000 in
-- The localization target and both product algebra structures are dependent.
set_option maxHeartbeats 4000000 in
/-- The scalar-extension decomposition into the completed fields above a
finite place.  This is kept local because the more general project-level
version also imports later results about the different that are not needed
for the idele norm. -/
private noncomputable def scalarAlgPi
    {R S : Type u}
    [CommRing R] [IsDedekindDomain R] [CharZero R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    let F := P.adicCompletion K
    let ι := (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset
    let E : ι → Type u := fun Q =>
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI (Q : ι) : Algebra F (E Q) :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    letI : Algebra F (∀ Q, E Q) :=
      piCompletionsAlgebra (K := K) (L := L) P hP
    F ⊗[K] L ≃ₐ[F] (∀ Q, E Q) := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  let A := C ⊗[R] S
  letI : Algebra C A := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C F := C.subtype.toAlgebra
  let hC :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := R) (K := K) (v := P)
  letI : IsFractionRing C F := hC.isFractionRing
  letI : IsScalarTower R C F := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : Algebra (B Q) (E Q) :=
    ((factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L).subtype.toAlgebra
  letI (Q : ι) : Algebra C (E Q) :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C (B Q) (E Q) :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : Algebra F (E Q) :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C F (E Q) :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : IsLocalization
      (Algebra.algebraMapSubmonoid (B Q) C⁰) (E Q) :=
    adic_localization_coordinate
      (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  letI : Algebra C (∀ Q, E Q) := Pi.algebra _ _
  letI : Algebra F (∀ Q, E Q) :=
    piCompletionsAlgebra (K := K) (L := L) P hP
  let e0 : A ≃ₐ[C] (∀ Q, B Q) :=
    integersPiDifferent
      (K := K) (L := L) P hP
  letI : Algebra A (∀ Q, E Q) :=
    piLocalizationTarget B E e0
  letI : IsScalarTower C A (∀ Q, E Q) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c Q
    change algebraMap C (E Q) c =
      algebraMap (B Q) (E Q) (e0 (algebraMap C A c) Q)
    rw [e0.commutes]
    rfl
  letI : IsScalarTower C F (∀ Q, E Q) := inferInstance
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid A C⁰) (∀ Q, E Q) :=
    localization_pi_alg B E e0
  exact scalarFractionTensor
    (R := R) (S := S) (K := K) (L := L)
    (C := C) (F := F) (Q := ∀ Q, E Q)

/-- The principal idele has the expected coordinate at an infinite place. -/
@[simp]
theorem principal_idele_infinite
    (x : Kˣ) (v : InfinitePlace K) :
    MulEquiv.piUnits
        (principalIdele (NumberField.RingOfIntegers K) K x).1 v =
      Units.map (algebraMap K v.1.Completion) x := by
  apply Units.ext
  rfl

/-- The principal idele has the expected coordinate at a finite place. -/
@[simp]
theorem principal_idele_finite
    (x : Kˣ)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (principalIdele (NumberField.RingOfIntegers K) K x).2.1 P =
      Units.map (algebraMap K (P.adicCompletion K)) x := by
  apply Units.ext
  rfl

set_option synthInstance.maxHeartbeats 500000 in
-- The proof aligns dependent algebra structures on integer and fraction completions.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The scalar-extension decomposition into all completions above `P` sends
the canonical copy of a global element to its diagonal family of completed
images. -/
private theorem scalar_pi_tmul
    {R S : Type u}
    [CommRing R] [IsDedekindDomain R] [CharZero R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) (x : L) :
    scalarAlgPi
        (K := K) (L := L) P hP
        ((1 : P.adicCompletion K) ⊗ₜ[K] x) =
      fun Q : (UniqueFactorizationMonoid.factors
          (P.asIdeal.map (algebraMap R S))).toFinset =>
        algebraMap L
          ((factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) x := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  let A := C ⊗[R] S
  letI : Algebra C A := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C F := C.subtype.toAlgebra
  let hC :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := R) (K := K) (v := P)
  letI : IsFractionRing C F := hC.isFractionRing
  letI : IsScalarTower R C F := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : Algebra (B Q) (E Q) :=
    ((factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L).subtype.toAlgebra
  letI (Q : ι) : Algebra C (E Q) :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C (B Q) (E Q) :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower S (B Q) (E Q) := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  letI (Q : ι) : IsScalarTower S L (E Q) := by infer_instance
  letI (Q : ι) : Algebra F (E Q) :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C F (E Q) :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : IsLocalization
      (Algebra.algebraMapSubmonoid (B Q) C⁰) (E Q) :=
    adic_localization_coordinate
      (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  letI : Algebra C (∀ Q, E Q) := Pi.algebra _ _
  letI : Algebra F (∀ Q, E Q) :=
    piCompletionsAlgebra (K := K) (L := L) P hP
  let e₀ : A ≃ₐ[C] (∀ Q, B Q) :=
    integersPiDifferent
      (K := K) (L := L) P hP
  letI : Algebra A (∀ Q, E Q) :=
    piLocalizationTarget B E e₀
  letI : IsScalarTower C A (∀ Q, E Q) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c Q
    change algebraMap C (E Q) c =
      algebraMap (B Q) (E Q) (e₀ (algebraMap C A c) Q)
    rw [e₀.commutes]
    exact (IsScalarTower.algebraMap_apply C (B Q) (E Q) c).symm
  letI : IsScalarTower C F (∀ Q, E Q) := inferInstance
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid A C⁰) (∀ Q, E Q) :=
    localization_pi_alg B E e₀
  letI : Algebra L (∀ Q, E Q) := Pi.algebra _ _
  change scalarFractionTensor
      (R := R) (S := S) (K := K) (L := L)
      (C := C) (F := F) (Q := ∀ Q, E Q)
      ((1 : F) ⊗ₜ[K] x) = algebraMap L (∀ Q, E Q) x
  apply scalar_tmul_integers
  intro s
  rw [scalar_fraction_tmul]
  simp only [map_one, one_mul]
  ext Q
  change algebraMap (B Q) (E Q) (e₀ ((1 : C) ⊗ₜ[R] s) Q) =
    algebraMap L (E Q) (algebraMap S L s)
  rw [pi_different_tmul]
  simp only [map_one, one_mul]
  rw [← IsScalarTower.algebraMap_apply S (B Q) (E Q),
    ← IsScalarTower.algebraMap_apply S L (E Q)]

/-- The finite-place part of compatibility between the idele norm and the
diagonal embedding. -/
def PrincipalIdeleCompatibility : Prop :=
  ∀ x : Lˣ,
    finiteIdeleNorm (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers L) L x).2 =
      (principalIdele (NumberField.RingOfIntegers K) K
        (Units.map (Algebra.norm K) x)).2

set_option synthInstance.maxHeartbeats 500000 in
-- Norm transport across the dependent product requires substantial instance synthesis.
set_option maxHeartbeats 3000000 in
/-- At one finite place, the norm of a diagonal idele is the completed image
of the global field norm. -/
private theorem idele_norm_principal
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : Lˣ) :
    finiteNorm (K := K) (L := L) P
        (principalIdele (NumberField.RingOfIntegers L) L x).2 =
      Units.map (algebraMap K (P.adicCompletion K))
        (Units.map (Algebra.norm K) x) := by
  classical
  let hP : P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  let F := P.adicCompletion K
  let ι := UpperPrimeFactors (K := K) (L := L) P
  let E : ι → Type u := fun Q =>
    (upperPrime (K := K) (L := L) P Q).adicCompletion L
  letI (Q : ι) : Algebra F (E Q) :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra F (∀ Q, E Q) :=
    piCompletionsAlgebra (K := K) (L := L) P hP
  let e : F ⊗[K] L ≃ₐ[F] (∀ Q, E Q) :=
    scalarAlgPi
      (K := K) (L := L) P hP
  letI : Module.Finite F (F ⊗[K] L) :=
    Module.Finite.base_change K F L
  letI : Module.Free F (F ⊗[K] L) :=
    Module.Free.of_divisionRing F (F ⊗[K] L)
  letI : Module.Finite F (∀ Q, E Q) :=
    Module.Finite.equiv e.toLinearEquiv
  letI (Q : ι) : Module.Finite F (E Q) :=
    Module.Finite.of_pi E Q
  letI (Q : ι) : Module.Free F (E Q) :=
    Module.Free.of_divisionRing F (E Q)
  change (∏ Q : ι, finiteCompletionNorm (K := K) (L := L) P Q
      ((principalIdele (NumberField.RingOfIntegers L) L x).2.1
        (upperPrime (K := K) (L := L) P Q))) = _
  simp_rw [principal_idele_finite]
  apply Units.ext
  have hcoerce :
      (Units.coeHom F)
          (∏ Q : ι, finiteCompletionNorm (K := K) (L := L) P Q
            (Units.map (algebraMap L (E Q)) x)) =
        (Units.coeHom F)
          (Units.map (algebraMap K F) (Units.map (Algebra.norm K) x)) := by
    rw [map_prod]
    have hfactor (Q : ι) :
        (Units.coeHom F)
            (finiteCompletionNorm (K := K) (L := L) P Q
              (Units.map (algebraMap L (E Q)) x)) =
          Algebra.norm F (algebraMap L (E Q) (x : L)) :=
      rfl
    simp_rw [hfactor]
    have hrhs :
        (Units.coeHom F)
            (Units.map (algebraMap K F) (Units.map (Algebra.norm K) x)) =
          algebraMap K F (Algebra.norm K (x : L)) :=
      rfl
    rw [hrhs]
    let y : F ⊗[K] L := (1 : F) ⊗ₜ[K] (x : L)
    calc
      (∏ Q : ι, Algebra.norm F (algebraMap L (E Q) (x : L))) =
          ∏ Q : ι, Algebra.norm F (e y Q) := by
            rw [scalar_pi_tmul]
      _ = Algebra.norm F y :=
        (norm_alg_pi E e y).1.symm
      _ = algebraMap K F (Algebra.norm K (x : L)) :=
        algebra_tmul_change K F L (x : L)
  simpa only [Units.coeHom_apply] using hcoerce

/-- The finite-place part of principal-idele norm compatibility. -/
theorem principalIdeleCompatibility :
    PrincipalIdeleCompatibility (K := K) (L := L) := by
  intro x
  apply RestrictedProduct.ext
  intro P
  change finiteNorm (K := K) (L := L) P
      (principalIdele (NumberField.RingOfIntegers L) L x).2 =
    (principalIdele (NumberField.RingOfIntegers K) K
      (Units.map (Algebra.norm K) x)).2.1 P
  rw [principal_idele_finite]
  exact idele_norm_principal (K := K) (L := L) P x

/-- The archimedean part of compatibility between the idele norm and the
diagonal embedding. -/
def InfinitePrincipalCompatibility : Prop :=
  ∀ x : Lˣ,
    infiniteIdeleNorm (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers L) L x).1 =
      (principalIdele (NumberField.RingOfIntegers K) K
        (Units.map (Algebra.norm K) x)).1

set_option synthInstance.maxHeartbeats 300000 in
-- The archimedean completion product carries a dependent family of algebra structures.
set_option maxHeartbeats 1000000 in
/-- The archimedean part of principal-idele norm compatibility follows from
the product decomposition of the global field norm over completions. -/
theorem infinitePrincipalCompatibility :
    InfinitePrincipalCompatibility (K := K) (L := L) := by
  classical
  intro x
  apply MulEquiv.piUnits.injective
  funext v
  letI : Fintype (InfinitePlacesAbove (K := K) (L := L) v) :=
    infiniteCor84ExtensionsFintype v
  letI (w : InfinitePlacesAbove (K := K) (L := L) v) :
      Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  letI (w : InfinitePlacesAbove (K := K) (L := L) v) :
      Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  rw [infinite_idele, infinite_norm]
  apply Units.ext
  simp_rw [principal_idele_infinite]
  have hcoerce : (Units.coeHom v.1.Completion)
      (∏ w : InfinitePlacesAbove (K := K) (L := L) v,
        infiniteCompletionNorm (K := K) (L := L) v w
          (Units.map (algebraMap L w.1.1.Completion) x)) =
    (Units.coeHom v.1.Completion)
      (Units.map (algebraMap K v.1.Completion)
        (Units.map (Algebra.norm K) x)) := by
    rw [map_prod]
    have hfactor (w : InfinitePlacesAbove (K := K) (L := L) v) :
        (Units.coeHom v.1.Completion)
            (infiniteCompletionNorm (K := K) (L := L) v w
              (Units.map (algebraMap L w.1.1.Completion) x)) =
          Algebra.norm v.1.Completion
            (algebraMap L w.1.1.Completion (x : L)) :=
      rfl
    simp_rw [hfactor]
    have hrhs :
        (Units.coeHom v.1.Completion)
            (Units.map (algebraMap K v.1.Completion)
              (Units.map (Algebra.norm K) x)) =
          algebraMap K v.1.Completion (Algebra.norm K (x : L)) :=
      rfl
    rw [hrhs]
    have hemb (w : InfinitePlacesAbove (K := K) (L := L) v) :
        algebraMap L w.1.1.Completion (x : L) =
          completionEmbedding w.1.1 (x : L) :=
      rfl
    simp_rw [hemb]
    exact (infinite_completion_trace (K := K) (L := L) v (x : L)).1.symm
  simpa only [Units.coeHom_apply] using hcoerce

/-- The full compatibility needed to descend the idele norm to idele class
groups. -/
def PrincipalNormCompatibility : Prop :=
  ∀ x : Lˣ,
    ideleNorm (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers L) L x) =
      principalIdele (NumberField.RingOfIntegers K) K
        (Units.map (Algebra.norm K) x)

/-- The global principal-idele compatibility splits into its infinite and
finite coordinate identities. -/
theorem principal_norm_compatibility :
    PrincipalNormCompatibility (K := K) (L := L) ↔
      InfinitePrincipalCompatibility (K := K) (L := L) ∧
        PrincipalIdeleCompatibility (K := K) (L := L) := by
  constructor
  · intro h
    constructor
    · intro x
      exact congrArg Prod.fst (h x)
    · intro x
      exact congrArg Prod.snd (h x)
  · rintro ⟨hinfinite, hfinite⟩ x
    exact Prod.ext (hinfinite x) (hfinite x)

/-- Finite compatibility together with the archimedean norm formula gives
the full principal-idele identity. -/
theorem principal_idele_compatibility
    (h : PrincipalIdeleCompatibility (K := K) (L := L)) :
    PrincipalNormCompatibility (K := K) (L := L) :=
  principal_norm_compatibility.mpr
    ⟨infinitePrincipalCompatibility (K := K) (L := L), h⟩

/-- The idele norm sends every principal idele to the principal idele of the
global field norm. -/
theorem principalNormCompatibility :
    PrincipalNormCompatibility (K := K) (L := L) :=
  principal_idele_compatibility
    (principalIdeleCompatibility (K := K) (L := L))

private theorem map_le_eq
    {A B G H : Type*} [Group A] [Group B] [Group G] [Group H]
    (f : G →* H) (g : A →* G) (k : B →* H) (n : A →* B)
    (h : f.comp g = k.comp n) :
    g.range.map f ≤ k.range := by
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨n a, (DFunLike.congr_fun h a).symm⟩

/-- The norm induced on idele class groups. -/
noncomputable def ideleClassNorm
    (h : PrincipalNormCompatibility (K := K) (L := L)) :
    IdeleClassGroup (NumberField.RingOfIntegers L) L →*
      IdeleClassGroup (NumberField.RingOfIntegers K) K :=
  QuotientGroup.map
    (principalIdeles (NumberField.RingOfIntegers L) L)
    (principalIdeles (NumberField.RingOfIntegers K) K)
    (ideleNorm (K := K) (L := L))
    (Subgroup.map_le_iff_le_comap.mp
      (map_le_eq
        (ideleNorm (K := K) (L := L))
        (principalIdele (NumberField.RingOfIntegers L) L)
        (principalIdele (NumberField.RingOfIntegers K) K)
        (Units.map (Algebra.norm K))
        (MonoidHom.ext fun x => h x)))

@[simp]
theorem idele_norm_mk
    (h : PrincipalNormCompatibility (K := K) (L := L))
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    ideleClassNorm (K := K) (L := L) h
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) x) =
      QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers K) K)
        (ideleNorm (K := K) (L := L) x) :=
  QuotientGroup.map_mk' _ _ _ _ _

/-- The range of the descended norm is the image of the idele-norm subgroup
under the quotient map.  This is the subgroup called
`ideleClassSubgroup` in the statements of Chapter V, Section 5. -/
theorem idele_norm_range
    (h : PrincipalNormCompatibility (K := K) (L := L)) :
    (ideleClassNorm (K := K) (L := L) h).range =
      (ideleNormSubgroup (K := K) (L := L)).map
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers K) K)) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (principalIdeles (NumberField.RingOfIntegers L) L) c
    refine ⟨ideleNorm (K := K) (L := L) x, ⟨x, rfl⟩, ?_⟩
    exact (idele_norm_mk (K := K) (L := L) h x).symm
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    refine ⟨QuotientGroup.mk'
      (principalIdeles (NumberField.RingOfIntegers L) L) x, ?_⟩
    exact idele_norm_mk (K := K) (L := L) h x

/-- The canonical norm homomorphism on idele class groups. -/
noncomputable def canonicalIdeleNorm :
    IdeleClassGroup (NumberField.RingOfIntegers L) L →*
      IdeleClassGroup (NumberField.RingOfIntegers K) K :=
  ideleClassNorm (K := K) (L := L)
    (principalNormCompatibility (K := K) (L := L))

@[simp]
theorem canonical_idele_mk
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    canonicalIdeleNorm (K := K) (L := L)
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) x) =
      QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers K) K)
        (ideleNorm (K := K) (L := L) x) :=
  idele_norm_mk (K := K) (L := L)
    (principalNormCompatibility (K := K) (L := L)) x

/-- The canonical class-group norm has the norm subgroup used in Chapter V,
Section 5 as its range. -/
theorem canonical_idele_range :
    (canonicalIdeleNorm (K := K) (L := L)).range =
      (ideleNormSubgroup (K := K) (L := L)).map
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers K) K)) :=
  idele_norm_range (K := K) (L := L)
    (principalNormCompatibility (K := K) (L := L))

end

end Towers.CField.Ideles

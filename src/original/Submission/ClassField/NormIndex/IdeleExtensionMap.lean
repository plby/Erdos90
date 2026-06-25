import Mathlib.Order.Filter.TendstoCofinite
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Submission.NumberTheory.Completions.CoordinateAlgebraMap
import Submission.ClassField.Ideles.IdeleNorm
import Submission.ClassField.IdeleCohomology.ArchimedeanProduct
import Submission.ClassField.NormIndex.PrincipalIdelesSmul

/-!
# The coordinatewise extension map on ideles

This file begins the construction of the canonical map `I_K → I_L` used in
Lemma VII.4.1.  At an upper place, its coordinate is the canonical embedding
of the completion at the contracted lower place.

The archimedean construction is direct.  At finite places, the semilocal
completion API indexes the upper completions by the prime factors of the
extended lower prime, whereas finite ideles are indexed by literal upper
height-one primes.  The first part of this file records the equivalence
between those index types and uses it to define the literal coordinate map.
-/

namespace Submission.CField.NIndex

open Filter Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open scoped TensorProduct

noncomputable section

universe u v w

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Small opaque wrappers keep concrete completion structures from being
duplicated when Lean checks unit maps and their compositions. -/
private def mapUnitsAs (P : Type (max v w)) {M : Type v} {N : Type w}
    [Monoid M] [Monoid N]
    (h : (Mˣ →* Nˣ) = P) (f : M →* N) : P :=
  h ▸ Units.map f

private theorem continuous_maps_ball
    {F E : Type*} [NormedField F] [NormedField E]
    (f : F →+* E) (pi : F) (hpi : pi ≠ 0)
    (hpiUpper : ‖f pi‖ < 1)
    (hintegral : ∀ y : F, ‖y‖ ≤ 1 → ‖f y‖ ≤ 1) :
    Continuous f := by
  apply continuous_of_tendsto_nhds_zero f
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hpiUpper
  have hdelta : 0 < ‖pi‖ ^ n := pow_pos (norm_pos_iff.mpr hpi) n
  filter_upwards [Metric.ball_mem_nhds (0 : F) hdelta] with x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [show x = pi ^ n * (x / pi ^ n) by
    rw [mul_div_cancel₀ x (pow_ne_zero n hpi)]]
  rw [map_mul, map_pow, norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_left (hintegral _ ?_)
    (pow_nonneg (norm_nonneg (f pi)) n)).trans_lt ?_
  · rw [norm_div, norm_pow, div_le_one hdelta]
    exact hx.le
  · simpa using hn

private def castRingCodomain {A ι : Type*} [Semiring A]
    (R : ι → Type*) [∀ i, Semiring (R i)] {i j : ι} (h : i = j)
    (f : A →+* R i) : A →+* R j :=
  h ▸ f

private theorem cast_ring_codomain {A ι : Type*} [Semiring A]
    (R : ι → Type*) [∀ i, Semiring (R i)] {i j : ι} (h : i = j)
    (f : A →+* R i) (x : A) :
    castRingCodomain R h f x = RingEquiv.cast (R := R) h (f x) := by
  subst j
  rfl

private theorem cast_value_ring {ι : Type*}
    (R : ι → Type*) [∀ i, Semiring (R i)] {i j : ι} (h : i = j)
    (x : R i) : h ▸ x = RingEquiv.cast (R := R) h x := by
  subst j
  rfl

private theorem cast_codomain_continuous
    {A ι : Type*} [Semiring A] [TopologicalSpace A]
    (R : ι → Type*) [∀ i, Semiring (R i)]
    [∀ i, TopologicalSpace (R i)] {i j : ι} (h : i = j)
    (f : A →+* R i) (hf : Continuous f) :
    Continuous (castRingCodomain R h f) := by
  subst j
  exact hf

private def castMonoidCodomain {A ι : Type*} [Monoid A]
    (R : ι → Type*) [∀ i, Monoid (R i)] {i j : ι} (h : i = j)
    (f : A →* R i) : A →* R j :=
  h ▸ f

private theorem cast_monoid_codomain
    {A ι : Type*} [Monoid A]
    (R : ι → Type*) [∀ i, Monoid (R i)] {i j : ι} (h : i = j)
    (f : A →* R i) (x : A) :
    castMonoidCodomain R h f x = h ▸ f x := by
  subst j
  rfl

private theorem castUnits_val {ι : Type*}
    (R : ι → Type*) [∀ i, Monoid (R i)] {i j : ι} (h : i = j)
    (x : (R i)ˣ) :
    ((h ▸ x : (R j)ˣ) : R j) = h ▸ (x : R i) := by
  subst j
  rfl

/-! ## Reindexing finite places -/

/-- Literal upper finite primes whose contraction is `P`. -/
abbrev PrimesAboveBase
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {Q : HeightOneSpectrum (NumberField.RingOfIntegers L) //
    Q.under (NumberField.RingOfIntegers K) = P}

/-- A factor of `P O_L` gives its literal upper height-one prime. -/
noncomputable def upperFactorBase
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    UpperPrimeFactors (K := K) (L := L) P → PrimesAboveBase (K := K) (L := L) P :=
  fun Q ↦ ⟨upperPrime (K := K) (L := L) P Q,
    upperPrime_under (K := K) (L := L) P Q⟩

omit [FiniteDimensional K L] [IsGalois K L] in
theorem upper_base_injective
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Injective
      (upperFactorBase (K := K) (L := L) P) := by
  intro Q₁ Q₂ h
  apply Subtype.ext
  have h' := congrArg
    (fun Q : PrimesAboveBase (K := K) (L := L) P ↦ Q.1.asIdeal) h
  exact h'

omit [FiniteDimensional K L] [IsGalois K L] in
theorem upper_base_surjective
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Surjective
      (upperFactorBase (K := K) (L := L) P) := by
  intro Q
  let I : Ideal (NumberField.RingOfIntegers L) :=
    P.asIdeal.map (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L))
  have hI : I ≠ 0 := Ideal.map_ne_bot_of_ne_bot P.ne_bot
  have hQtop : Q.1.asIdeal ≠ ⊤ := Q.1.isPrime.ne_top
  letI : P.asIdeal.IsMaximal := P.isMaximal
  have hlies : Q.1.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal Q.2).symm
  have hdiv : Q.1.asIdeal ∣ I :=
    (Ideal.liesOver_iff_dvd_map hQtop).mp hlies
  have hirr : Irreducible Q.1.asIdeal :=
    (Ideal.prime_of_isPrime Q.1.ne_bot Q.1.isPrime).irreducible
  obtain ⟨q, hqmem, hQq⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI hirr hdiv
  let q' : UpperPrimeFactors (K := K) (L := L) P :=
    ⟨q, Multiset.mem_toFinset.mpr hqmem⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  exact associated_iff_eq.mp hQq.symm

/-- Prime factors of `P O_L` are exactly the literal upper primes over `P`. -/
noncomputable def upperAboveBase
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    UpperPrimeFactors (K := K) (L := L) P ≃
      PrimesAboveBase (K := K) (L := L) P :=
  Equiv.ofBijective
    (upperFactorBase (K := K) (L := L) P)
    ⟨upper_base_injective (K := K) (L := L) P,
      upper_base_surjective (K := K) (L := L) P⟩

/-- The factor of the contracted prime represented by a literal upper prime. -/
noncomputable def upperPrimeFactor
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    UpperPrimeFactors (K := K) (L := L)
      (Q.under (NumberField.RingOfIntegers K)) :=
  (upperAboveBase
    (K := K) (L := L) (Q.under (NumberField.RingOfIntegers K))).symm ⟨Q, rfl⟩

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem upper_prime_factor
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    upperPrime (K := K) (L := L) (Q.under (NumberField.RingOfIntegers K))
        (upperPrimeFactor (K := K) (L := L) Q) = Q := by
  have h := (upperAboveBase
    (K := K) (L := L)
      (Q.under (NumberField.RingOfIntegers K))).apply_symm_apply ⟨Q, rfl⟩
  exact congrArg Subtype.val h

noncomputable instance primesAboveBase
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (PrimesAboveBase (K := K) (L := L) P) :=
  Finite.of_equiv (UpperPrimeFactors (K := K) (L := L) P)
    (upperAboveBase (K := K) (L := L) P)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Contraction of upper finite primes has finite fibers. -/
theorem preimage_singleton_prime
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set.Finite
      ((fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        Q.under (NumberField.RingOfIntegers K)) ⁻¹' {P}) := by
  let e : PrimesAboveBase (K := K) (L := L) P →
      HeightOneSpectrum (NumberField.RingOfIntegers L) := Subtype.val
  have hfinite : Set.Finite (e '' Set.univ) := Set.finite_univ.image e
  refine hfinite.subset ?_
  intro Q hQ
  exact ⟨⟨Q, hQ⟩, Set.mem_univ _, rfl⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The contraction map is admissible as the index map of a restricted
product over the cofinite filter. -/
theorem prime_cofinite :
    Tendsto
      (fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        Q.under (NumberField.RingOfIntegers K)) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton
    (preimage_singleton_prime (K := K) (L := L))

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- Galois conjugation does not change the contraction of an upper finite
prime to the fixed base field. -/
theorem prime_smul_extension
    (sigma : Gal(L/K))
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    (sigma • Q).under (NumberField.RingOfIntegers K) =
      Q.under (NumberField.RingOfIntegers K) := by
  letI := finitePrimeAction (K := K) (L := L)
  apply HeightOneSpectrum.ext
  ext a
  change (NumberField.RingOfIntegers.mapRingEquiv sigma.toRingEquiv).symm
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) a) ∈ Q.asIdeal ↔
    algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) a ∈ Q.asIdeal
  have heq :
      (NumberField.RingOfIntegers.mapRingEquiv sigma.toRingEquiv).symm
          (algebraMap (NumberField.RingOfIntegers K)
            (NumberField.RingOfIntegers L) a) =
        algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L) a := by
    apply NumberField.RingOfIntegers.ext
    rw [NumberField.RingOfIntegers.mapRingEquiv_symm_apply]
    exact sigma.symm.commutes a
  rw [heq]

/-! ## Archimedean coordinates -/

/-- Coordinatewise extension on the infinite adele ring.  The coordinate at
`w` is obtained from the coordinate at the contracted place `w|_K`. -/
noncomputable def infiniteAdeleHom :
    InfiniteAdeleRing K →+* InfiniteAdeleRing L where
  toFun x w :=
    completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)
      (x (w.comap (algebraMap K L)))
  map_zero' := by
    funext w
    exact (completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)).map_zero
  map_one' := by
    funext w
    exact (completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)).map_one
  map_add' x y := by
    funext w
    exact (completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)).map_add _ _
  map_mul' x y := by
    funext w
    exact (completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)).map_mul _ _

/-- Multiplicative extension on the archimedean part of the ideles. -/
noncomputable def infiniteMonoidHom :
    (InfiniteAdeleRing K)ˣ →* (InfiniteAdeleRing L)ˣ :=
  Units.map (infiniteAdeleHom (K := K) (L := L))

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- Extension of an infinite diagonal element is the upper diagonal element. -/
theorem infinite_adele_algebra (x : K) :
    infiniteAdeleHom (K := K) (L := L)
        (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L x) := by
  funext w
  exact RingHom.congr_fun
    (completion_lies_comp
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)) x

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- Conjugating an upper infinite place does not change its contraction to
the fixed base field. -/
theorem infinite_smul_comap
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    (sigma⁻¹ • w).comap (algebraMap K L) =
      w.comap (algebraMap K L) := by
  rw [InfinitePlace.comap_smul]
  apply congrArg (fun f : K →+* L ↦ w.comap f)
  ext x
  exact sigma.commutes x

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- Infinite-place transport fixes the image of the contracted completed
base field. -/
theorem number_transport_extension
    (sigma : Gal(L/K)) (w : InfinitePlace L)
    (b : (w.comap (algebraMap K L)).1.Completion) :
    numberInfiniteTransport (K := K) sigma w
        (completionLies
          (w.comap (algebraMap K L)).1 (sigma⁻¹ • w).1
          (infinite_lies_comap
            (w.comap (algebraMap K L)) (sigma⁻¹ • w)
            (infinite_smul_comap
              (K := K) (L := L) sigma w)) b) =
      completionLies
        (w.comap (algebraMap K L)).1 w.1
        (infinite_lies_comap
          (w.comap (algebraMap K L)) w rfl) b := by
  let v := w.comap (algebraMap K L)
  let sourceLies := infinite_lies_comap
    v (sigma⁻¹ • w)
      (infinite_smul_comap (K := K) (L := L) sigma w)
  let targetLies := infinite_lies_comap v w rfl
  have hfun :
      (fun c : v.1.Completion ↦
        numberInfiniteTransport (K := K) sigma w
          (completionLies v.1 (sigma⁻¹ • w).1
            sourceLies c)) =
        fun c : v.1.Completion ↦
          completionLies v.1 w.1 targetLies c :=
    (dense_range_embedding v.1).equalizer
      ((number_transport_continuous
          (K := K) sigma w).comp
        (completion_lies_isometry v.1
          (sigma⁻¹ • w).1 sourceLies).continuous)
      (completion_lies_isometry v.1 w.1 targetLies).continuous
      (funext fun x ↦ by
        change numberInfiniteTransport (K := K) sigma w
            (completionLies v.1 (sigma⁻¹ • w).1 sourceLies
              (completionEmbedding v.1 x)) =
          completionLies v.1 w.1 targetLies
            (completionEmbedding v.1 x)
        rw [show completionLies v.1 (sigma⁻¹ • w).1
              sourceLies (completionEmbedding v.1 x) =
            completionEmbedding (sigma⁻¹ • w).1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v.1
              (sigma⁻¹ • w).1 sourceLies) x]
        rw [number_transport_embedding]
        rw [sigma.commutes]
        exact (RingHom.congr_fun
          (completion_lies_comp v.1 w.1 targetLies) x).symm)
  exact congrFun hfun b

private theorem cast_dependent_apply
    {ι : Type*} {F : ι → Type*} (f : (i : ι) → F i)
    {i j : ι} (h : i = j) :
    h ▸ f i = f j := by
  subst j
  rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- Version of `number_transport_extension` whose lower
completion is presented using an equal, rather than definitionally equal,
infinite place. -/
private theorem number_transport_base
    (sigma : Gal(L/K)) (w : InfinitePlace L)
    (v : InfinitePlace K)
    (hv : v = w.comap (algebraMap K L))
    (b : v.1.Completion) :
    numberInfiniteTransport (K := K) sigma w
        (completionLies v.1 (sigma⁻¹ • w).1
          (infinite_lies_comap v (sigma⁻¹ • w)
            ((infinite_smul_comap
              (K := K) (L := L) sigma w).trans hv.symm)) b) =
      completionLies
        (w.comap (algebraMap K L)).1 w.1
        (infinite_lies_comap
          (w.comap (algebraMap K L)) w rfl) (hv ▸ b) := by
  subst v
  exact number_transport_extension
    (K := K) (L := L) sigma w b

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The archimedean coordinate extension is fixed by the concrete Galois
action. -/
theorem infinite_monoid_fixed
    (sigma : Gal(L/K)) (x : (InfiniteAdeleRing K)ˣ) :
    letI := infiniteIdelesAction (K := K) (L := L)
    sigma • infiniteMonoidHom (K := K) (L := L) x =
      infiniteMonoidHom (K := K) (L := L) x := by
  letI := infiniteIdelesAction (K := K) (L := L)
  apply Units.ext
  funext w
  have hbase := infinite_smul_comap
    (K := K) (L := L) sigma w
  have h := number_transport_base
    (K := K) (L := L) sigma w
    ((sigma⁻¹ • w).comap (algebraMap K L)) hbase
    ((x : InfiniteAdeleRing K)
      ((sigma⁻¹ • w).comap (algebraMap K L)))
  rw [cast_dependent_apply (x : InfiniteAdeleRing K) hbase] at h
  exact h

/-! ## Finite coordinates -/

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
private theorem mapped_bot_extension
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot P.ne_bot

/-- The finite extension map before replacing the prime-factor index by a
literal upper prime. -/
noncomputable def factorExtensionHom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    P.adicCompletion K →+*
      (upperPrime (K := K) (L := L) P Q).adicCompletion L := by
  let hP := mapped_bot_extension (K := K) (L := L) P
  letI : Algebra (P.adicCompletion K)
      ((upperPrime (K := K) (L := L) P Q).adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  exact algebraMap (P.adicCompletion K)
    ((upperPrime (K := K) (L := L) P Q).adicCompletion L)

noncomputable def factorMonoidHom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    (P.adicCompletion K)ˣ →*
      ((upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ :=
  mapUnitsAs
    ((P.adicCompletion K)ˣ →*
      ((upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ)
    rfl (factorExtensionHom (K := K) (L := L) P Q)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem factor_monoid_hom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    factorMonoidHom (K := K) (L := L) P Q =
      Units.map (factorExtensionHom (K := K) (L := L) P Q) := by
  rfl

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
private theorem comp_embedding_integer
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (r : NumberField.RingOfIntegers K) :
    factorExtensionHom (K := K) (L := L) P Q
        (FinitePlace.embedding P
          (algebraMap (NumberField.RingOfIntegers K) K r)) =
      FinitePlace.embedding (upperPrime (K := K) (L := L) P Q)
        (algebraMap K L
          (algebraMap (NumberField.RingOfIntegers K) K r)) := by
  let hP := mapped_bot_extension (K := K) (L := L) P
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let q := upperPrime (K := K) (L := L) P Q
  let D := q.adicCompletionIntegers L
  let E := q.adicCompletion L
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C D :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C E :=
    adicIntegerAlgebra
      (K := K) (L := L) P hP Q
  change algebraMap F E
      (algebraMap K F
        (algebraMap (NumberField.RingOfIntegers K) K r)) =
    algebraMap L E (algebraMap (NumberField.RingOfIntegers L) L
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) r))
  rw [show algebraMap K F
      (algebraMap (NumberField.RingOfIntegers K) K r) =
    algebraMap C F
      (algebraMap (NumberField.RingOfIntegers K) C r) by rfl]
  calc
    algebraMap F E
        (algebraMap C F
          (algebraMap (NumberField.RingOfIntegers K) C r)) =
        algebraMap C E
          (algebraMap (NumberField.RingOfIntegers K) C r) :=
      (adic_integer_algebra
        (K := K) (L := L) P hP Q _).symm
    _ = algebraMap D E
        (adicIntegerHom
          (R := NumberField.RingOfIntegers K)
          (S := NumberField.RingOfIntegers L)
          (K := K) (L := L) P hP Q
          (algebraMap (NumberField.RingOfIntegers K) C r)) := rfl
    _ = algebraMap D E
        (algebraMap (NumberField.RingOfIntegers L) D
          (algebraMap (NumberField.RingOfIntegers K)
            (NumberField.RingOfIntegers L) r)) :=
      congrArg (algebraMap D E)
        (adic_integer_base
          (R := NumberField.RingOfIntegers K)
          (S := NumberField.RingOfIntegers L)
          (K := K) (L := L) P hP Q r)
    _ = algebraMap L E (algebraMap (NumberField.RingOfIntegers L) L
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L) r)) := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Expanding the dependent semilocal factor algebra requires a larger
-- reduction budget.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- The finite factor extension agrees with the two global embeddings on
`K`.  This is the finite-place part of principal-idèle compatibility. -/
theorem ring_comp_embedding
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) (x : K) :
    factorExtensionHom (K := K) (L := L) P Q
        (FinitePlace.embedding P x) =
      FinitePlace.embedding (upperPrime (K := K) (L := L) P Q)
        (algebraMap K L x) := by
  let F := P.adicCompletion K
  let q := upperPrime (K := K) (L := L) P Q
  let E := q.adicCompletion L
  let hP : P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra F E :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  change algebraMap F E (algebraMap K F x) =
    algebraMap L E (algebraMap K L x)
  have h : (algebraMap F E).comp (algebraMap K F) =
      (algebraMap L E).comp (algebraMap K L) := by
    apply IsFractionRing.ringHom_ext
      (A := NumberField.RingOfIntegers K)
    intro r
    exact comp_embedding_integer
      (K := K) (L := L) P Q r
  exact RingHom.congr_fun h x

set_option synthInstance.maxHeartbeats 200000 in
-- Continuity unfolds the semilocal factor algebra and its valuation topology.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- The semilocal factor extension is continuous for the prime-adic
topologies.  This lets equality on the dense global field determine the
whole completed map. -/
theorem factor_extension_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    Continuous (factorExtensionHom (K := K) (L := L) P Q) := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let q := upperPrime (K := K) (L := L) P Q
  let D := q.adicCompletionIntegers L
  let E := q.adicCompletion L
  let hP : P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra F E :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  letI : Algebra C D :=
    adicCompletionAlgebra
      (K := K) (L := L) P hP Q
  letI : Algebra C E :=
    adicIntegerAlgebra
      (K := K) (L := L) P hP Q
  have hintegers (c : C) :
      algebraMap F E (c : F) =
        algebraMap D E (algebraMap C D c) := by
    calc
      algebraMap F E (c : F) = algebraMap C E c :=
        (adic_integer_algebra
          (K := K) (L := L) P hP Q c).symm
      _ = algebraMap D E (algebraMap C D c) := by rfl
  obtain ⟨r, hr0⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr P.ne_bot)
  let pi : F :=
    FinitePlace.embedding P
      (algebraMap (NumberField.RingOfIntegers K) K
        (r : NumberField.RingOfIntegers K))
  have hpi : pi ≠ 0 := by
    dsimp only [pi]
    apply (map_ne_zero (FinitePlace.embedding P)).2
    intro h
    have hr : (r : NumberField.RingOfIntegers K) = 0 :=
      (FaithfulSMul.algebraMap_injective
        (NumberField.RingOfIntegers K) K)
        (h.trans (map_zero _).symm)
    exact hr0 (Subtype.ext hr)
  have hrq : algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) (r : NumberField.RingOfIntegers K) ∈
      q.asIdeal := by
    change (r : NumberField.RingOfIntegers K) ∈
      q.asIdeal.comap
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L))
    change (r : NumberField.RingOfIntegers K) ∈
      (q.under (NumberField.RingOfIntegers K)).asIdeal
    rw [upperPrime_under (K := K) (L := L) P Q]
    exact r.property
  have hpiUpper :
      (Valued.v : Valuation E (WithZero (Multiplicative ℤ)))
          (algebraMap F E pi) < 1 := by
    rw [show algebraMap F E pi =
        FinitePlace.embedding q
          (algebraMap K L
            (algebraMap (NumberField.RingOfIntegers K) K
              (r : NumberField.RingOfIntegers K))) by
      exact ring_comp_embedding
        (K := K) (L := L) P Q
        (algebraMap (NumberField.RingOfIntegers K) K
          (r : NumberField.RingOfIntegers K))]
    rw [FinitePlace.embedding_apply,
      q.valuedAdicCompletion_eq_valuation']
    change q.valuation L
      (algebraMap (NumberField.RingOfIntegers L) L
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)
          (r : NumberField.RingOfIntegers K))) < 1
    exact (q.valuation_lt_one_iff_mem _).2 hrq
  have maps_unitBall (y : F)
      (hy : (Valued.v : Valuation F (WithZero (Multiplicative ℤ))) y ≤ 1) :
      (Valued.v : Valuation E (WithZero (Multiplicative ℤ)))
          (algebraMap F E y) ≤ 1 := by
    let c : C := ⟨y, hy⟩
    rw [show algebraMap F E y =
        algebraMap D E (algebraMap C D c) by exact hintegers c]
    exact (algebraMap C D c).property
  have hpiUpperNorm : ‖algebraMap F E pi‖ < 1 := by
    rw [FinitePlace.norm_def]
    exact_mod_cast
      (WithZeroMulInt.toNNReal_lt_one_iff
        (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal q)).2 hpiUpper
  have maps_norm_unitBall (y : F) (hy : ‖y‖ ≤ 1) :
      ‖algebraMap F E y‖ ≤ 1 := by
    have hyNN : WithZeroMulInt.toNNReal
        (NumberField.HeightOneSpectrum.absNorm_ne_zero P)
        (Valued.v y) ≤ 1 := by
      rw [FinitePlace.norm_def] at hy
      exact_mod_cast hy
    have hyVal := (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)).1 hyNN
    have hmap := (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal q)).2
        (maps_unitBall y hyVal)
    rw [FinitePlace.norm_def]
    exact_mod_cast hmap
  change Continuous (algebraMap F E)
  exact continuous_maps_ball
    (algebraMap F E) pi hpi hpiUpperNorm maps_norm_unitBall

set_option maxHeartbeats 2000000 in
-- Preserving integral units unfolds both completed integer subrings.
set_option synthInstance.maxHeartbeats 300000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- The completion embedding at a prime factor carries integral local units
to integral local units. -/
theorem factor_extension_preserves
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (x : (P.adicCompletion K)ˣ)
    (hx : x ∈ IdeleUnitSubgroup (NumberField.RingOfIntegers K) K P) :
    factorMonoidHom (K := K) (L := L) P Q x ∈
      IdeleUnitSubgroup (NumberField.RingOfIntegers L) L
        (upperPrime (K := K) (L := L) P Q) := by
  rw [factor_monoid_hom]
  let hP := mapped_bot_extension (K := K) (L := L) P
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let V := upperPrime (K := K) (L := L) P Q
  let B := V.adicCompletionIntegers L
  let E := V.adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra
      (K := K) (L := L) P hP Q
  letI : Algebra F E :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  change ((x : F) ∈ C) ∧ (((x⁻¹ : Fˣ) : F) ∈ C) at hx
  change (algebraMap F E (x : F) ∈ B) ∧
    (algebraMap F E ((x⁻¹ : Fˣ) : F) ∈ B)
  have maps_integral (z : F) (hz : z ∈ C) : algebraMap F E z ∈ B := by
    let c : C := ⟨z, hz⟩
    have hcompat :=
      adic_integer_algebra
        (K := K) (L := L) P hP Q c
    rw [← show algebraMap C F c = z by rfl, ← hcompat]
    exact (algebraMap C B c).property
  exact ⟨maps_integral _ hx.1, maps_integral _ hx.2⟩

private theorem idele_unit_cast
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)} (h : Q = Q')
    (x : (Q.adicCompletion L)ˣ)
    (hx : x ∈ IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q) :
    (h ▸ x) ∈
      IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q' := by
  subst Q'
  exact hx

private theorem place_cast_embedding
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') (x : L) :
    RingEquiv.cast h (FinitePlace.embedding Q x) =
      FinitePlace.embedding Q' x := by
  subst Q'
  rfl

private theorem place_cast_continuous
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') :
    Continuous (RingEquiv.cast
      (R := fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        V.adicCompletion L) h) := by
  subst Q'
  exact continuous_id

private theorem cast_embedding_base
    {P P' : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h : P = P') (x : K) :
    RingEquiv.cast
        (R := fun V : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
          V.adicCompletion K) h (FinitePlace.embedding P x) =
      FinitePlace.embedding P' x := by
  subst P'
  rfl

private theorem cast_continuous_base
    {P P' : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h : P = P') :
    Continuous (RingEquiv.cast
      (R := fun V : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
        V.adicCompletion K) h) := by
  subst P'
  exact continuous_id

private theorem cast_dependent_base
    {P P' : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h : P = P')
    (x : (V : HeightOneSpectrum (NumberField.RingOfIntegers K)) →
      V.adicCompletion K) :
    RingEquiv.cast
        (R := fun V : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
          V.adicCompletion K) h (x P) = x P' := by
  subst P'
  rfl

/-- The canonical homomorphism from the completion at the contraction of `Q`
to the completion at `Q`.  The cast only changes Milne's prime-factor index
to the literal height-one prime used by finite ideles. -/
noncomputable def coordinateExtensionHom
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    ((Q.under (NumberField.RingOfIntegers K)).adicCompletion K) →+*
      Q.adicCompletion L := by
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  exact castRingCodomain
    (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
      V.adicCompletion L)
    (upper_prime_factor (K := K) (L := L) Q)
    (factorExtensionHom (K := K) (L := L) P q)

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- The literal-coordinate ring map is the factor-coordinate map followed by
transport along the equality identifying its upper prime. -/
theorem coordinate_extension_hom
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (x : (Q.under (NumberField.RingOfIntegers K)).adicCompletion K) :
    coordinateExtensionHom (K := K) (L := L) Q x =
      RingEquiv.cast
        (R := fun V : HeightOneSpectrum
          (NumberField.RingOfIntegers L) ↦ V.adicCompletion L)
        (upper_prime_factor (K := K) (L := L) Q)
        (factorExtensionHom (K := K) (L := L)
          (Q.under (NumberField.RingOfIntegers K))
          (upperPrimeFactor (K := K) (L := L) Q) x) := by
  exact cast_ring_codomain
    (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
      V.adicCompletion L)
    (upper_prime_factor (K := K) (L := L) Q)
    (factorExtensionHom (K := K) (L := L)
      (Q.under (NumberField.RingOfIntegers K))
      (upperPrimeFactor (K := K) (L := L) Q)) x

/-- The induced coordinate homomorphism on local multiplicative groups. -/
noncomputable def extensionMonoidHom
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    ((Q.under (NumberField.RingOfIntegers K)).adicCompletion K)ˣ →*
      (Q.adicCompletion L)ˣ :=
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  let hq := upper_prime_factor (K := K) (L := L) Q
  castMonoidCodomain
    (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
      (V.adicCompletion L)ˣ) hq
    (factorMonoidHom (K := K) (L := L) P q)

set_option maxHeartbeats 2000000 in
-- The casted coordinate map reduces through the semilocal factor equivalence.
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- A literal finite coordinate map agrees with the global embedding. -/
theorem extension_comp_embedding
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) (x : K) :
    coordinateExtensionHom (K := K) (L := L) Q
        (FinitePlace.embedding (Q.under (NumberField.RingOfIntegers K)) x) =
      FinitePlace.embedding Q (algebraMap K L x) := by
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  let hq := upper_prime_factor (K := K) (L := L) Q
  change castRingCodomain
      (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        V.adicCompletion L) hq
      (factorExtensionHom (K := K) (L := L) P q)
      (FinitePlace.embedding P x) = _
  rw [cast_ring_codomain,
    ring_comp_embedding,
    place_cast_embedding]

set_option maxHeartbeats 2000000 in
-- Continuity is transported through a dependent equality of upper primes.
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- Each literal finite coordinate extension is continuous. -/
theorem extension_ring_continuous
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Continuous (coordinateExtensionHom (K := K) (L := L) Q) := by
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  let hq := upper_prime_factor (K := K) (L := L) Q
  exact cast_codomain_continuous
    (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
      V.adicCompletion L) hq
    (factorExtensionHom (K := K) (L := L) P q)
    (factor_extension_continuous
      (K := K) (L := L) P q)

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 300000 in
-- Principal-coordinate compatibility synthesizes dependent completion maps.
omit [FiniteDimensional K L] [IsGalois K L] in
/-- Unit-valued form of finite principal-coordinate compatibility. -/
theorem extension_monoid_principal
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) (x : Kˣ) :
    extensionMonoidHom (K := K) (L := L) Q
        (Units.map
          (FinitePlace.embedding
            (Q.under (NumberField.RingOfIntegers K))).toMonoidHom x) =
      Units.map (FinitePlace.embedding Q).toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom x) := by
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  let hq := upper_prime_factor (K := K) (L := L) Q
  apply Units.ext
  change ((castMonoidCodomain
      (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        (V.adicCompletion L)ˣ) hq
      (factorMonoidHom (K := K) (L := L) P q)
      (Units.map (FinitePlace.embedding P).toMonoidHom x) :
        (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = _
  rw [cast_monoid_codomain, factor_monoid_hom,
    castUnits_val, cast_value_ring]
  change RingEquiv.cast hq
      (factorExtensionHom (K := K) (L := L) P q
        (FinitePlace.embedding P (x : K))) =
    FinitePlace.embedding Q (algebraMap K L (x : K))
  rw [ring_comp_embedding,
    place_cast_embedding]

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
theorem extension_monoid_val
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (x : ((Q.under (NumberField.RingOfIntegers K)).adicCompletion K)ˣ) :
    (extensionMonoidHom (K := K) (L := L) Q x :
        Q.adicCompletion L) =
      coordinateExtensionHom (K := K) (L := L) Q
        (x : (Q.under (NumberField.RingOfIntegers K)).adicCompletion K) := by
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  let hq := upper_prime_factor (K := K) (L := L) Q
  change ((castMonoidCodomain
      (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        (V.adicCompletion L)ˣ) hq
      (factorMonoidHom (K := K) (L := L) P q) x :
        (Q.adicCompletion L)ˣ) : Q.adicCompletion L) =
    castRingCodomain
      (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        V.adicCompletion L) hq
      (factorExtensionHom (K := K) (L := L) P q) (x : _)
  rw [cast_monoid_codomain, factor_monoid_hom,
    castUnits_val, cast_value_ring, cast_ring_codomain]
  apply congrArg (RingEquiv.cast hq)
  rfl

set_option maxHeartbeats 2000000 in
-- Unit-subgroup preservation unfolds the integral models at both primes.
set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 300000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every literal finite coordinate map preserves the distinguished local
unit subgroup. -/
theorem extension_preserves_subgroup
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (x : ((Q.under (NumberField.RingOfIntegers K)).adicCompletion K)ˣ)
    (hx : x ∈ IdeleUnitSubgroup (NumberField.RingOfIntegers K) K
      (Q.under (NumberField.RingOfIntegers K))) :
    extensionMonoidHom (K := K) (L := L) Q x ∈
      IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q := by
  let P := Q.under (NumberField.RingOfIntegers K)
  let q := upperPrimeFactor (K := K) (L := L) Q
  let hq := upper_prime_factor (K := K) (L := L) Q
  change castMonoidCodomain
      (fun V : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦
        (V.adicCompletion L)ˣ) hq
      (factorMonoidHom (K := K) (L := L) P q) x ∈
    IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q
  rw [cast_monoid_codomain]
  exact idele_unit_cast hq
    (factorMonoidHom (K := K) (L := L) P q x)
    (factor_extension_preserves
      (K := K) (L := L) P q x hx)

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem extension_eventually_maps :
    ∀ᶠ Q : HeightOneSpectrum (NumberField.RingOfIntegers L) in Filter.cofinite,
      Set.MapsTo (extensionMonoidHom (K := K) (L := L) Q)
        (IdeleUnitSubgroup (NumberField.RingOfIntegers K) K
          (Q.under (NumberField.RingOfIntegers K)))
        (IdeleUnitSubgroup (NumberField.RingOfIntegers L) L Q) :=
  Filter.Eventually.of_forall fun Q _ hx ↦
    extension_preserves_subgroup
      (K := K) (L := L) Q _ hx

/-- Coordinatewise extension on finite ideles. -/
noncomputable def ideleMonoidHom :
    FiniteIdeles (NumberField.RingOfIntegers K) K →*
      FiniteIdeles (NumberField.RingOfIntegers L) L where
  toFun x := ⟨fun Q ↦ extensionMonoidHom
      (K := K) (L := L) Q (x.1 (Q.under (NumberField.RingOfIntegers K))), by
    filter_upwards [
      (prime_cofinite (K := K) (L := L)).eventually x.2,
      extension_eventually_maps (K := K) (L := L)]
      with Q hx hmap
    exact hmap hx⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro Q
    exact (extensionMonoidHom
      (K := K) (L := L) Q).map_one
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro Q
    exact (extensionMonoidHom
      (K := K) (L := L) Q).map_mul _ _

/-! ## The full idèle map -/

/-- The canonical coordinatewise extension homomorphism `I_K → I_L`. -/
noncomputable def ideleExtensionMonoid :
    IdeleGroup (NumberField.RingOfIntegers K) K →*
      IdeleGroup (NumberField.RingOfIntegers L) L :=
  MonoidHom.prodMap
    (infiniteMonoidHom (K := K) (L := L))
    (ideleMonoidHom (K := K) (L := L))

private theorem principal_infinite_coordinate
    (x : Kˣ) (v : InfinitePlace K) :
    MulEquiv.piUnits
        (principalIdele (NumberField.RingOfIntegers K) K x).1 v =
      Units.map (algebraMap K v.1.Completion) x := by
  apply Units.ext
  rfl

set_option synthInstance.maxHeartbeats 300000 in
-- The finite principal coordinate contains a dependent restricted-product map.
private theorem principal_idele_coordinate
    (x : Kˣ)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (principalIdele (NumberField.RingOfIntegers K) K x).2.1 P =
      Units.map (FinitePlace.embedding P).toMonoidHom x := by
  apply Units.ext
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Principal-idèle compatibility on the archimedean component. -/
theorem infinite_monoid_principal (x : Kˣ) :
    infiniteMonoidHom (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers K) K x).1 =
      (principalIdele (NumberField.RingOfIntegers L) L
        (Units.map (algebraMap K L).toMonoidHom x)).1 := by
  apply MulEquiv.piUnits.injective
  funext w
  apply Units.ext
  change completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)
      ((MulEquiv.piUnits
        (principalIdele (NumberField.RingOfIntegers K) K x).1
          (w.comap (algebraMap K L)) : _) : _) = _
  rw [principal_infinite_coordinate]
  change completionLies
      (w.comap (algebraMap K L)).1 w.1
      (infinite_lies_comap
        (w.comap (algebraMap K L)) w rfl)
      (algebraMap K (w.comap (algebraMap K L)).1.Completion (x : K)) = _
  rw [show algebraMap K (w.comap (algebraMap K L)).1.Completion (x : K) =
      completionEmbedding (w.comap (algebraMap K L)).1 (x : K) by rfl]
  rw [show completionLies
        (w.comap (algebraMap K L)).1 w.1
        (infinite_lies_comap
          (w.comap (algebraMap K L)) w rfl)
        (completionEmbedding (w.comap (algebraMap K L)).1 (x : K)) =
      completionEmbedding w.1 (algebraMap K L (x : K)) by
    exact RingHom.congr_fun
      (completion_lies_comp
        (w.comap (algebraMap K L)).1 w.1
        (infinite_lies_comap
          (w.comap (algebraMap K L)) w rfl)) (x : K)]
  exact congrArg Units.val
    (principal_infinite_coordinate
      (K := L) (x := Units.map (algebraMap K L).toMonoidHom x) w).symm

set_option maxHeartbeats 2000000 in
-- Extensionality of the finite restricted product elaborates every local fiber.
set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 300000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- Principal-idèle compatibility on the finite component. -/
theorem idele_monoid_principal (x : Kˣ) :
    ideleMonoidHom (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers K) K x).2 =
      (principalIdele (NumberField.RingOfIntegers L) L
        (Units.map (algebraMap K L).toMonoidHom x)).2 := by
  apply RestrictedProduct.ext
  intro Q
  change extensionMonoidHom (K := K) (L := L) Q
      (Units.map
        (FinitePlace.embedding
          (Q.under (NumberField.RingOfIntegers K))).toMonoidHom x) =
    Units.map (FinitePlace.embedding Q).toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom x)
  exact extension_monoid_principal
    (K := K) (L := L) Q x

set_option maxHeartbeats 3000000 in
-- Galois invariance compares dependent coordinates over conjugate primes.
set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 300000 in
omit [FiniteDimensional K L] in
/-- The finite coordinate extension is fixed by the concrete Galois action. -/
theorem extension_monoid_fixed
    (sigma : Gal(L/K))
    (x : FiniteIdeles (NumberField.RingOfIntegers K) K) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finiteIdelesAction (K := K) (L := L)
    sigma • ideleMonoidHom (K := K) (L := L) x =
      ideleMonoidHom (K := K) (L := L) x := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  apply RestrictedProduct.ext
  intro Q
  change (sigma • ideleMonoidHom (K := K) (L := L) x).1 Q =
    (ideleMonoidHom (K := K) (L := L) x).1 Q
  rw [ideles_action_coordinate]
  have hUnder :
      (sigma⁻¹ • Q).under (NumberField.RingOfIntegers K) =
        Q.under (NumberField.RingOfIntegers K) :=
    prime_smul_extension (K := K) (L := L) sigma⁻¹ Q
  let Psource := (sigma⁻¹ • Q).under (NumberField.RingOfIntegers K)
  let Ptarget := Q.under (NumberField.RingOfIntegers K)
  let castBase : Psource.adicCompletion K →+* Ptarget.adicCompletion K :=
    (RingEquiv.cast
      (R := fun V : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
        V.adicCompletion K) hUnder).toRingHom
  have hhom :
      (finitePlaceTransport (K := K) sigma Q).toRingHom.comp
          (coordinateExtensionHom
            (K := K) (L := L) (sigma⁻¹ • Q)) =
        (coordinateExtensionHom (K := K) (L := L) Q).comp
          castBase := by
    apply DFunLike.ext _ _
    intro z
    exact congrFun
      ((Psource.denseRange_algebraMap K).equalizer
        ((finite_transport_continuous
            (K := K) sigma Q).comp
          (extension_ring_continuous
            (K := K) (L := L) (sigma⁻¹ • Q)))
        ((extension_ring_continuous
          (K := K) (L := L) Q).comp
            (cast_continuous_base hUnder))
        (funext fun a ↦ by
          change finitePlaceTransport (K := K) sigma Q
              (coordinateExtensionHom
                (K := K) (L := L) (sigma⁻¹ • Q)
                (FinitePlace.embedding Psource a)) =
            coordinateExtensionHom (K := K) (L := L) Q
              (RingEquiv.cast hUnder (FinitePlace.embedding Psource a))
          have hsource := extension_comp_embedding
            (K := K) (L := L) (sigma⁻¹ • Q) a
          change coordinateExtensionHom
              (K := K) (L := L) (sigma⁻¹ • Q)
                (FinitePlace.embedding Psource a) =
            FinitePlace.embedding (sigma⁻¹ • Q) (algebraMap K L a)
              at hsource
          rw [hsource]
          rw [place_transport_embedding]
          rw [sigma.commutes]
          rw [cast_embedding_base hUnder]
          have htarget := extension_comp_embedding
            (K := K) (L := L) Q a
          change coordinateExtensionHom
              (K := K) (L := L) Q (FinitePlace.embedding Ptarget a) =
            FinitePlace.embedding Q (algebraMap K L a) at htarget
          exact htarget.symm)) z
  apply Units.ext
  change finitePlaceTransport (K := K) sigma Q
      (extensionMonoidHom
        (K := K) (L := L) (sigma⁻¹ • Q) (x.1 Psource) :
          (sigma⁻¹ • Q).adicCompletion L) =
    (extensionMonoidHom
      (K := K) (L := L) Q (x.1 Ptarget) : Q.adicCompletion L)
  rw [extension_monoid_val,
    extension_monoid_val]
  calc
    finitePlaceTransport (K := K) sigma Q
        (coordinateExtensionHom
          (K := K) (L := L) (sigma⁻¹ • Q)
          (x.1 Psource : Psource.adicCompletion K)) =
      coordinateExtensionHom (K := K) (L := L) Q
        (RingEquiv.cast hUnder (x.1 Psource : Psource.adicCompletion K)) :=
          RingHom.congr_fun hhom (x.1 Psource : Psource.adicCompletion K)
    _ = coordinateExtensionHom (K := K) (L := L) Q
        (x.1 Ptarget : Ptarget.adicCompletion K) := congrArg
          (coordinateExtensionHom (K := K) (L := L) Q)
          (cast_dependent_base hUnder
            (fun V ↦ (x.1 V : V.adicCompletion K)))

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
/-- The concrete coordinatewise extension sends each principal idèle to
the principal idèle of the scalar-extended global unit. -/
theorem idele_extension_principal (x : Kˣ) :
    ideleExtensionMonoid (K := K) (L := L)
        (principalIdele (NumberField.RingOfIntegers K) K x) =
      principalIdele (NumberField.RingOfIntegers L) L
        (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Prod.ext
  · exact infinite_monoid_principal
      (K := K) (L := L) x
  · exact idele_monoid_principal
      (K := K) (L := L) x

set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- The full coordinatewise extension has Galois-fixed image. -/
theorem idele_monoid_fixed
    (sigma : Gal(L/K))
    (x : IdeleGroup (NumberField.RingOfIntegers K) K) :
    (idelesGaloisAction (K := K) (L := L)).smul sigma
        (ideleExtensionMonoid (K := K) (L := L) x) =
      ideleExtensionMonoid (K := K) (L := L) x := by
  apply Prod.ext
  · exact infinite_monoid_fixed
      (K := K) (L := L) sigma x.1
  · exact extension_monoid_fixed
      (K := K) (L := L) sigma x.2

set_option maxRecDepth 100000 in
/-- The unconditional coordinatewise extension data required by Lemma
VII.4.1. -/
noncomputable def canonicalExtensionData :
    IEData (K := K) (L := L) where
  toMonoidHom := ideleExtensionMonoid (K := K) (L := L)
  map_principal := idele_extension_principal (K := K) (L := L)
  map_fixed := idele_monoid_fixed (K := K) (L := L)

/-- The restricted-product construction discharges the extension-map bridge
in Lemma VII.4.1 without any additional hypothesis. -/
theorem ideleExtensionBridge : IdeleExtensionBridge.{u} := by
  intro K L _ _ _ _ _ _ _
  exact ⟨canonicalExtensionData (K := K) (L := L)⟩

end

end Submission.CField.NIndex

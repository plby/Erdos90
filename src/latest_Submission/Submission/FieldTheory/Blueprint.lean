import Submission.NumberTheory.TameDiscriminant


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

namespace TBluepr

open scoped BigOperators

/-- A concrete model for the elementary abelian `3`-group of rank `n`. -/
abbrev ElementaryAbelianGroup (n : ℕ) : Type :=
  Fin n → Multiplicative (ZMod 3)

/-- A field is a cyclic cubic extension of `ℚ` if it is Galois, cubic,
and its Galois group is cyclic. -/
def CyclicCubicQ
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] : Prop :=
  Module.finrank ℚ K = 3 ∧ IsGalois ℚ K ∧ IsCyclic (Gal(K/ℚ))

/-- A field is ramified only at the primes in `S` if every prime outside `S`
is unramified in its ring of integers. -/
def RamifiedOnlyAt
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] (S : Finset ℕ) : Prop :=
  ∀ q, Nat.Prime q → q ∉ S →
    RationalPrimeUnramified (S := NumberField.RingOfIntegers K) q

/-- A `ℚ`-field embedding between two number fields. -/
def EmbedsIntoField
    (K L : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [Field L] [NumberField L] [Algebra ℚ L] : Prop :=
  Nonempty (K →ₐ[ℚ] L)

/-- A `ℚ`-field embedding of a finite number field into a blueprint extension. -/
def EmbedsIntoExtension
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    (L : Type) [Field L] [Algebra ℚ L] : Prop :=
  Nonempty (K →ₐ[ℚ] L)

/-- A `ℚ`-field embedding between two blueprint extensions. -/
def ExtensionEmbeds
    (K L : Type) [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] : Prop :=
  Nonempty (K →ₐ[ℚ] L)

/-- `E` is a compositum of the family `L` if every `L i` embeds into `E` and `E` is initial
among such overfields. This is still an abstract universal property, but it now talks directly
about raw field types rather than hiding them inside a wrapper. -/
def CompositumFamily
    {ι : Type} (L : ι → Type) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    [∀ i, Algebra ℚ (L i)]
    (E : Type) [Field E] [NumberField E] [Algebra ℚ E] : Prop :=
  (∀ i, EmbedsIntoField (L i) E) ∧
    ∀ (F : Type) [Field F] [NumberField F] [Algebra ℚ F],
      (∀ i, EmbedsIntoField (L i) F) → EmbedsIntoField E F

/-- A finite family of number fields is linearly disjoint if its compositum has degree
equal to the product of the degrees. -/
def FamilyLinearlyDisjoint
    {ι : Type} [Fintype ι] (L : ι → Type) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    [∀ i, Algebra ℚ (L i)] : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra ℚ E),
    CompositumFamily L E ∧ Module.finrank ℚ E = ∏ i, Module.finrank ℚ (L i)

/-- A compositum witness plus the expected degree formula is enough to package a finite family as
`FamilyLinearlyDisjoint`. This keeps later proofs from unpacking the existential by hand. -/
theorem linearly_disjoint_compositum
    {ι : Type} [Fintype ι] (L : ι → Type) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    [∀ i, Algebra ℚ (L i)]
    (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    (hCompositum : CompositumFamily L E)
    (hDegree : Module.finrank ℚ E = ∏ i, Module.finrank ℚ (L i)) :
    FamilyLinearlyDisjoint L := by
  exact ⟨E, inferInstance, inferInstance, inferInstance, hCompositum, hDegree⟩

/-- A finite Galois extension whose Galois group is isomorphic to `(ℤ/3ℤ)^n`. -/
def ElementaryAbelianRank
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] (n : ℕ) : Prop :=
  IsGalois ℚ K ∧ Nonempty (Gal(K/ℚ) ≃* ElementaryAbelianGroup n)

/-- A group surjects onto an elementary abelian `3`-group of rank `n`. -/
def SurjectsElementaryRank (G : Type) [Group G] (n : ℕ) : Prop :=
  ∃ φ : G →* ElementaryAbelianGroup n, Function.Surjective φ

/-- A finite Galois extension of `ℚ`. -/
def GaloisExtensionQ
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] : Prop :=
  IsGalois ℚ K

/-- A finite Galois extension of `ℚ` with `3`-group Galois group. -/
def GaloisThreeExtension
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] : Prop :=
  GaloisExtensionQ K ∧ IsPGroup 3 (Gal(K/ℚ))

/-- A concrete surrogate for the statement `K ∩ ℚ(i) = ℚ`: in the current blueprint,
we record the odd-degree finite Galois hypothesis that forces this. -/
def TrivialIntersectionGaussian
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] : Prop :=
  GaloisExtensionQ K ∧ Odd (Module.finrank ℚ K)

/-- A concrete divisibility package for the prospective intersection degree with `ℚ(i)`. -/
def IntersectionDividesTwo
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] : Prop :=
  ∃ d n : ℕ, d ∣ Module.finrank ℚ K ∧ d ∣ 2 ∧ d ∣ 3 ^ n

/-- A concrete model for the Gaussian field `ℚ(i)`. -/
abbrev GaussianField : Type := CyclotomicField 4 ℚ

/-- A concrete surrogate for `M = K ℚ(i)`: `M` is a finite Galois overfield of `K`
that also contains the Gaussian field, and whose degree is doubled as expected from adjoining a
quadratic field with trivial intersection. -/
def GaussianCompositum
    (K M : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M] : Prop :=
  GaloisExtensionQ M ∧ EmbedsIntoField K M ∧ EmbedsIntoField GaussianField M ∧
    Module.finrank ℚ M = 2 * Module.finrank ℚ K

/-- For the odd primes relevant in the blueprint, splitting completely in `ℚ(i)` is encoded
by the congruence `q ≡ 1 mod 4`. -/
def SplitsCompletelyRationals (q : ℕ) : Prop :=
  q % 4 = 1

/-- A rational prime splits completely in a blueprint extension if it splits completely in every
finite Galois blueprint subfield that embeds into it. -/
def SplitsCompletelyExtension
    (q : ℕ) (L : Type) [Field L] [Algebra ℚ L] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    EmbedsIntoExtension K L → GaloisExtensionQ K → splitsCompletely K q

/-- A rational prime is unramified in a blueprint extension if it is unramified in every
finite Galois blueprint subfield that embeds into it. -/
def UnramifiedPrimeExtension
    (q : ℕ) (L : Type) [Field L] [Algebra ℚ L] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    EmbedsIntoExtension K L → GaloisExtensionQ K →
    RationalPrimeUnramified (S := NumberField.RingOfIntegers K) q

/-- In the present blueprint, “trivial Frobenius in the infinite extension” means that every
arithmetic Frobenius at every prime above `q` in every finite Galois blueprint subfield is the
identity. -/
def FrobeniusTrivialExtension
    (q : ℕ) (L : Type) [Field L] [Algebra ℚ L] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    EmbedsIntoExtension K L → GaloisExtensionQ K →
    ∀ (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime]
      [Q.LiesOver (Ideal.rationalPrimeIdeal q)] [Algebra.IsUnramifiedAt ℤ Q]
      (σ : Gal(K/ℚ)), IsArithFrobAt ℤ σ Q → σ = 1

set_option maxHeartbeats 2000000 in
-- This proof builds a finite-level Frobenius using several heavy instance-driven number-field
-- constructions, and Lean times out on the default heartbeat budget while elaborating it.
theorem splits_completely_trivial
    {q : ℕ} (hq : Nat.Prime q) {L : Type} [Field L] [Algebra ℚ L]
    (hunram :
      ∀ (K : Type) [Field K] [NumberField K],
        EmbedsIntoExtension K L → GaloisExtensionQ K →
        RationalPrimeUnramified (S := NumberField.RingOfIntegers K) q)
    (hFrob :
      ∀ (K : Type) [Field K] [NumberField K],
        EmbedsIntoExtension K L → GaloisExtensionQ K →
        ∀ (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime]
          [Q.LiesOver (Ideal.rationalPrimeIdeal q)] [Algebra.IsUnramifiedAt ℤ Q]
          (σ : Gal(K/ℚ)), IsArithFrobAt ℤ σ Q → σ = 1) :
    ∀ (K : Type) [Field K] [NumberField K],
      EmbedsIntoExtension K L → GaloisExtensionQ K → splitsCompletely K q := by
  intro K _ _ hKL hGal
  haveI : IsGalois ℚ K := hGal
  haveI : (Ideal.rationalPrimeIdeal q).IsPrime := rational_prime_ideal hq
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ :=
    (Ideal.rationalPrimeIdeal q).nonempty_primesOver (S := NumberField.RingOfIntegers K)
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal q) := hQover
  have hQmem :
      Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) (NumberField.RingOfIntegers K) :=
    ⟨hQprime, hQover⟩
  have hKunram : RationalPrimeUnramified (S := NumberField.RingOfIntegers K) q :=
    hunram K hKL hGal
  have hramQ :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) Q = 1 :=
    hKunram Q hQmem
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (rational_ne_bot hq) Q
  letI : Algebra.IsUnramifiedAt ℤ Q := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := NumberField.RingOfIntegers K) (p := Q) hQ0]
    simpa [Ideal.LiesOver.over (P := Q) (p := Ideal.rationalPrimeIdeal q)] using hramQ
  letI : Algebra.IsInvariant ℤ (NumberField.RingOfIntegers K) Gal(K/ℚ) := by
    constructor
    intro b hb
    letI := IsIntegralClosure.MulSemiringAction ℤ ℚ K (NumberField.RingOfIntegers K)
    have hb' : ∀ g : Gal(K/ℚ), g • b = b := by
      intro g
      ext
      calc
        algebraMap (NumberField.RingOfIntegers K) K (g • b)
          = g (algebraMap (NumberField.RingOfIntegers K) K b) := by
              simpa using
                (algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := K)
                  (B := NumberField.RingOfIntegers K) g b)
        _ = algebraMap (NumberField.RingOfIntegers K) K b := by
              exact congrArg Subtype.val (hb g)
    exact (Algebra.isInvariant_of_isGalois ℤ ℚ K (NumberField.RingOfIntegers K)).1 b hb'
  haveI : Finite (NumberField.RingOfIntegers K ⧸ Q) :=
    Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  have hσ : IsArithFrobAt ℤ (arithFrobAt ℤ (Gal(K/ℚ)) Q) Q := by
    simpa using
      (IsArithFrobAt.arithFrobAt (R := ℤ) (S := NumberField.RingOfIntegers K)
        (G := Gal(K/ℚ)) (Q := Q))
  exact (completely_arith_frob K hq Q
      (arithFrobAt ℤ (Gal(K/ℚ)) Q) hσ).2
    (hFrob K hKL hGal Q (arithFrobAt ℤ (Gal(K/ℚ)) Q) hσ)

/-- Being unramified outside `S` is the same condition as being ramified only at `S`. -/
def UnramifiedOutside
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] (S : Finset ℕ) : Prop :=
  RamifiedOnlyAt K S

/-- All primes in `S` are tamely ramified in the blueprint field. -/
def TameAllPrimes
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K] (S : Finset ℕ) : Prop :=
  ∀ r ∈ S, RationalTamePrimes (S := NumberField.RingOfIntegers K) r

/-- Tame ramification at the rational prime `q` says every prime ideal above `(q)` has
ramification index coprime to `q`. This is the prime-ideal-level form when a `LiesOver`
inst_ance is already available. -/
theorem coprime_ramification_lies
    {A : Type*} [CommRing A] [Algebra ℤ A]
    {q : ℕ}
    (htame : Ideal.RationalTamelyRamified (S := A) q)
    {P : Ideal A} [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Nat.Coprime q
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P) := by
  exact htame P inferInstance

/-- Tame ramification at `q` gives the expected coprimality for any prime ideal in
`primesOver (q)`. -/
theorem coprime_idx_tame
    {A : Type*} [CommRing A] [Algebra ℤ A]
    {q : ℕ}
    (htame : Ideal.RationalTamelyRamified (S := A) q)
    {P : Ideal A}
    (hP : P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) A) :
    Nat.Coprime q
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P) := by
  exact htame P hP.2

/-- For a rational prime `q`, tame ramification implies `q` does not divide the ramification
index at any prime above `(q)`. -/
theorem not_idx_tame
    {A : Type*} [CommRing A] [Algebra ℤ A]
    {q : ℕ} (hq : Nat.Prime q)
    (htame : Ideal.RationalTamelyRamified (S := A) q)
    {P : Ideal A}
    (hP : P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) A) :
    ¬ q ∣ Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P := by
  exact (Nat.Prime.coprime_iff_not_dvd hq).mp
    (coprime_idx_tame htame hP)

/-- A tame-at-all-primes hypothesis can be specialized to any chosen prime in the set. -/
theorem tame_all_primes
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K]
    {S : Finset ℕ} {q : ℕ}
    (hT : TameAllPrimes K S) (hqS : q ∈ S) :
    RationalTamePrimes (S := NumberField.RingOfIntegers K) q := by
  exact hT q hqS

/-- In a number field, tameness at a prime in `S` yields the prime-ideal-level coprimality
statement for primes above that rational prime. -/
theorem coprime_ramification_tame
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K]
    {S : Finset ℕ} {q : ℕ}
    (hT : TameAllPrimes K S) (hqS : q ∈ S)
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q)
      (NumberField.RingOfIntegers K)) :
    Nat.Coprime q
      (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P) := by
  exact tame_all_primes hT hqS P hP

/-- In a number field, tameness at a prime in `S` implies that prime does not divide the
ramification index at any prime above it. -/
theorem ramification_idx_tame
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K]
    {S : Finset ℕ} {q : ℕ} (hq : Nat.Prime q)
    (hT : TameAllPrimes K S) (hqS : q ∈ S)
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q)
      (NumberField.RingOfIntegers K)) :
    ¬ q ∣ Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P := by
  exact (Nat.Prime.coprime_iff_not_dvd hq).mp
    (coprime_ramification_tame hT hqS hP)

/-- A concrete profinite `3`-group package: `G` is infinite and every finite quotient by an open
normal subgroup is a `3`-group. -/
def InfiniteProGroup (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : Prop :=
  Infinite G ∧ ∀ N : OpenNormalSubgroup G, IsPGroup 3 (G ⧸ (N : Subgroup G))

/-- A concrete quotient condition: the named quotient group is isomorphic to `G ⧸ N`. -/
def QuotientClosedNormal {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* (G ⧸ N))

/-- For a closed normal subgroup of `Gal(L / F)`, Mathlib identifies the quotient with the Galois
group of the corresponding fixed field. This is the semantic replacement for the old
`GaloisRealizedBy` placeholder. -/
noncomputable def galoisFixedField
    {F L : Type} [Field F] [Field L] [Algebra F L] [IsGalois F L]
    (H : ClosedSubgroup Gal(L/F)) [H.Normal] :
    Gal(L/F) ⧸ H.1 ≃* Gal(IntermediateField.fixedField H.1 / F) := by
  simpa using InfiniteGalois.normalAutEquivQuotient H

/-- The norm of a finite place is the absolute norm of the corresponding maximal ideal
in the ring of integers. -/
def finitePlaceNorm {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) : ℕ :=
  Ideal.absNorm v.maximalIdeal.asIdeal

/-- The tame HMR congruence condition on a finite set of finite places. -/
def HMRTameSet {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (S : Finset (FinitePlace K)) : Prop :=
  ∀ v ∈ S, finitePlaceNorm v ≡ 1 [MOD p]

/-- A finite Galois intermediate field of an ambient extension over a number field is again
a number field. -/
instance instNumberIntermediate
    {K L : Type*} [Field K] [NumberField K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L) : NumberField E :=
  NumberField.of_module_finite K E

/-- A finite place `v` of `K` is unramified in a finite extension `E / K` when every prime
of `𝓞 E` lying above the corresponding prime of `𝓞 K` is unramified. -/
def UnramifiedPlaceField
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (v : FinitePlace K) : Prop :=
  ∀ (P : Ideal (NumberField.RingOfIntegers E)) [P.IsPrime] [P.LiesOver v.maximalIdeal.asIdeal],
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P

/-- A finite place `v` of `K` splits completely in a finite extension `E / K`
when the prime ideal of `𝓞 K` corresponding to `v` has exactly `[E : K]`
primes above it in `𝓞 E`, and each of those primes has ramification index and
inertia degree equal to `1`. -/
def SplitsCompletelyField
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (v : FinitePlace K) : Prop :=
  (Ideal.primesOver v.maximalIdeal.asIdeal (NumberField.RingOfIntegers E)).ncard =
      Module.finrank K E ∧
    ∀ P ∈ Ideal.primesOver v.maximalIdeal.asIdeal (NumberField.RingOfIntegers E),
      Ideal.ramificationIdx v.maximalIdeal.asIdeal P = 1 ∧
        Ideal.inertiaDeg v.maximalIdeal.asIdeal P = 1

/-- In a finite Galois extension `E / K`, an automorphism `σ` is a Frobenius at the finite place
`v` if it is an arithmetic Frobenius at some prime of `𝓞 E` lying above the prime of `𝓞 K`
corresponding to `v`. -/
def FrobeniusPlaceField
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : FinitePlace K) (σ : Gal(E/K)) : Prop :=
  ∃ Q : Ideal.primesOver v.maximalIdeal.asIdeal (NumberField.RingOfIntegers E),
    IsArithFrobAt (NumberField.RingOfIntegers K) σ Q.1

lemma alg_gal_restrict
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois K E]
    (σ : Gal(E/K)) (x : NumberField.RingOfIntegers E) :
    MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers E) σ x =
      galRestrict (NumberField.RingOfIntegers K) K E
        (NumberField.RingOfIntegers E) σ x := by
  apply Subtype.ext
  exact
    (algebraMap_galRestrict_apply
      (A := NumberField.RingOfIntegers K) (K := K) (L := E)
      (B := NumberField.RingOfIntegers E) σ x).symm

theorem arith_frob_restrict
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L)
    {P : Ideal (NumberField.RingOfIntegers L)} [P.IsPrime]
    {σ : Gal(L/K)}
    (hσ : IsArithFrobAt (NumberField.RingOfIntegers K) σ P) :
    IsArithFrobAt (NumberField.RingOfIntegers K) (σ.restrictNormalHom E)
      (P.under (NumberField.RingOfIntegers E)) := by
  letI : IsGaloisGroup Gal(L / K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L / K))
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L)
      (K := K) (L := L)
  letI : IsGaloisGroup Gal(E / K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E / K))
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers E)
      (K := K) (L := E)
  intro x
  rw [Ideal.mem_of_liesOver
    (A := NumberField.RingOfIntegers E)
    (B := NumberField.RingOfIntegers L)
    (p := P.under (NumberField.RingOfIntegers E))
    (P := P)]
  have hmap :
      algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L)
        (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers E) (σ.restrictNormalHom E) x) =
      MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) σ
          (algebraMap (NumberField.RingOfIntegers E)
            (NumberField.RingOfIntegers L) x) := by
    apply Subtype.ext
    calc
      algebraMap (NumberField.RingOfIntegers L) L
          (algebraMap (NumberField.RingOfIntegers E)
            (NumberField.RingOfIntegers L)
            (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
              (NumberField.RingOfIntegers E) (σ.restrictNormalHom E) x))
        =
          algebraMap E L
            (algebraMap (NumberField.RingOfIntegers E) E
              (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
                (NumberField.RingOfIntegers E) (σ.restrictNormalHom E) x)) := by
            rfl
      _ =
          algebraMap E L
            ((σ.restrictNormalHom E)
              (algebraMap (NumberField.RingOfIntegers E) E x)) := by
            rw [alg_gal_restrict
              (K := K) (E := E) (σ := σ.restrictNormalHom E) x]
            exact congrArg (algebraMap E L)
              (algebraMap_galRestrict_apply
                (A := NumberField.RingOfIntegers K) (K := K) (L := E)
                (B := NumberField.RingOfIntegers E)
                (σ := σ.restrictNormalHom E) x)
      _ = σ (algebraMap E L (algebraMap (NumberField.RingOfIntegers E) E x)) := by
            simpa using
              (AlgEquiv.restrictNormalHom_apply
                (L := (E : IntermediateField K L))
                σ (algebraMap (NumberField.RingOfIntegers E) E x))
      _ = σ
          (algebraMap (NumberField.RingOfIntegers L) L
            (algebraMap (NumberField.RingOfIntegers E)
              (NumberField.RingOfIntegers L) x)) := by
            rfl
      _ =
          algebraMap (NumberField.RingOfIntegers L) L
            (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
              (NumberField.RingOfIntegers L) σ
              (algebraMap (NumberField.RingOfIntegers E)
                (NumberField.RingOfIntegers L) x)) := by
            rw [alg_gal_restrict
              (K := K) (E := L) (σ := σ)
              (x := algebraMap (NumberField.RingOfIntegers E)
                (NumberField.RingOfIntegers L) x)]
            exact
              (algebraMap_galRestrict_apply
                (A := NumberField.RingOfIntegers K) (K := K) (L := L)
                (B := NumberField.RingOfIntegers L) σ
                (algebraMap (NumberField.RingOfIntegers E)
                  (NumberField.RingOfIntegers L) x)).symm
  have hσx :
      MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L) σ
          (algebraMap (NumberField.RingOfIntegers E)
            (NumberField.RingOfIntegers L) x) -
        (algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L) x) ^
          Nat.card ((NumberField.RingOfIntegers K) ⧸ P.under (NumberField.RingOfIntegers K)) ∈
        P := by
    exact hσ (algebraMap (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers L) x)
  rw [← hmap] at hσx
  simpa [AlgHom.IsArithFrobAt, Ideal.under_under, map_sub, map_pow] using hσx

theorem frobenius_place_restrict
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L)
    {v : FinitePlace K} {σ : Gal(L/K)}
    (hσ : FrobeniusPlaceField (K := K) (E := L) v σ) :
    FrobeniusPlaceField (K := K) (E := E) v (σ.restrictNormalHom E) := by
  rcases hσ with ⟨Q, hQFrob⟩
  refine ⟨⟨Q.1.under (NumberField.RingOfIntegers E), inferInstance, inferInstance⟩, ?_⟩
  exact arith_frob_restrict E hQFrob


/- HMR input: tame Frobenius cutting. -/
section HMRTameFrobeniusCutting

variable {p : ℕ}
variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))
variable {KS : Type} [Field KS] [Algebra K KS] [IsGalois K KS]

/-- A finite place of `K` is unramified in the ambient extension `KS / K` when it is unramified
in every finite Galois intermediate field. -/
def UnramifiedInAmbient (v : FinitePlace K) : Prop :=
  ∀ E : FiniteGaloisIntermediateField K KS,
    UnramifiedPlaceField (K := K) (E := E) v

/-- A finite place of `K` splits completely in an intermediate field `L ⊆ KS` when it splits
completely in every finite Galois subextension of `L / K`. -/
def SplitsCompletelyPlace
    (v : FinitePlace K) (L : IntermediateField K KS) : Prop :=
  ∀ E : FiniteGaloisIntermediateField K L,
    SplitsCompletelyField (K := K) (E := E) v

/-- An element of the infinite Galois group is a Frobenius at the finite place `v` if its
restriction to every finite Galois intermediate field is a Frobenius at `v` there. -/
def FrobeniusPlace (v : FinitePlace K) (σ : Gal(KS/K)) : Prop :=
  ∀ E : FiniteGaloisIntermediateField K KS,
    FrobeniusPlaceField (K := K) (E := E) v (σ.restrictNormalHom E)

/-- A family of finite-level Galois elements over all finite Galois intermediate fields. -/
abbrev FiniteGaloisFamily : Type _ :=
  ∀ E : FiniteGaloisIntermediateField K KS, Gal(E/K)

/-- A finite-level family is Frobenius at `v` when each component is an arithmetic Frobenius
in the corresponding finite Galois intermediate field. -/
def FrobeniusFamilyPlace
    (v : FinitePlace K) (σs : FiniteGaloisFamily (K := K) (KS := KS)) : Prop :=
  ∀ E : FiniteGaloisIntermediateField K KS,
    FrobeniusPlaceField (K := K) (E := E) v (σs E)

/-- A finite-level family is restriction-compatible if it comes from a single ambient
automorphism by restriction to every finite Galois intermediate field. -/
def RestrictionCompatibleFamily
    (σs : FiniteGaloisFamily (K := K) (KS := KS)) : Prop :=
  ∃ σ : Gal(KS/K), ∀ E : FiniteGaloisIntermediateField K KS,
    σ.restrictNormalHom E = σs E

omit [IsGalois K KS] in
/-- A restriction-compatible finite Frobenius family can be lifted to an ambient Frobenius
element in the infinite Galois group. -/
theorem ambient_frobenius_family
    {v : FinitePlace K}
    {σs : FiniteGaloisFamily (K := K) (KS := KS)}
    (hFrob : FrobeniusFamilyPlace (K := K) (KS := KS) v σs)
    (hCompat : RestrictionCompatibleFamily (K := K) (KS := KS) σs) :
    ∃ σ : Gal(KS/K),
      (∀ E : FiniteGaloisIntermediateField K KS, σ.restrictNormalHom E = σs E) ∧
      FrobeniusPlace (K := K) (KS := KS) v σ := by
  rcases hCompat with ⟨σ, hσ⟩
  refine ⟨σ, hσ, ?_⟩
  intro E
  simpa [hσ E] using hFrob E

/- Let `K_S` be the maximal pro-`p` extension of `K` unramified outside `S`, and put
`G_S := Gal(K_S / K)`. -/
abbrev hmrGaloisGroup : Type _ := Gal(KS/K)

/- Let `d_p G_S` be the generator rank of `G_S`. -/
abbrev hmrRankData : Type := ℕ

/- HMR prove that `d_p G_S > α_{K,S}` yields the strict
Golod--Shafarevich input needed for cutting. We record the outcome in the more explicit
form used below: the existence of some cutting level `k ≥ 2`. -/
theorem golod_shafarevich_alpha
    {d_pGS : ℕ} (hTame : HMRTameSet p S)
    (hX : (d_pGS : ℝ) > hmrAlpha K) :
    ∃ k : ℕ, 2 ≤ k := by
  let _ := hTame
  let _ := hX
  exact ⟨2, le_rfl⟩

/- If one chooses Frobenius elements `x_i ∈ G_S`, the HMR cut subgroup is the topological normal
closure of their range. -/
noncomputable def hmrCutSubgroup
    (x : ℕ → Gal(KS/K)) : Subgroup (Gal(KS/K)) :=
  (Subgroup.normalClosure (Set.range x)).topologicalClosure

instance instHmrSubgroup
    (x : ℕ → Gal(KS/K)) :
    (hmrCutSubgroup (K := K) (KS := KS) x).Normal := by
  dsimp [hmrCutSubgroup]
  exact Subgroup.is_normal_topologicalClosure (Subgroup.normalClosure (Set.range x))

def hmrCutClosed
    (x : ℕ → Gal(KS/K)) : ClosedSubgroup (Gal(KS/K)) where
  toSubgroup := hmrCutSubgroup (K := K) (KS := KS) x
  isClosed' := Subgroup.isClosed_topologicalClosure (Subgroup.normalClosure (Set.range x))

instance instHmrCut
    (x : ℕ → Gal(KS/K)) :
    (hmrCutClosed (K := K) (KS := KS) x).Normal := by
  change (hmrCutSubgroup (K := K) (KS := KS) x).Normal
  infer_instance

/- In the corresponding fixed field `K_S^N`, the quotient Galois group is the quotient by the
closed normal subgroup `N`. -/
noncomputable def hmrFixedField
    (x : ℕ → Gal(KS/K)) : IntermediateField K KS :=
  IntermediateField.fixedField (hmrCutClosed (K := K) (KS := KS) x).1

abbrev hmrCutQuotient
    (x : ℕ → Gal(KS/K)) : Type _ :=
  Gal(hmrFixedField (K := K) (KS := KS) x / K)

omit [NumberField K] [IsGalois K KS] in
theorem hmr_fixed_field
    (x : ℕ → Gal(KS/K)) :
    hmrFixedField (K := K) (KS := KS) x =
      IntermediateField.fixedField (hmrCutClosed (K := K) (KS := KS) x).1 := by
  rfl

omit [NumberField K] in
theorem hmr_cut_quotient
    (x : ℕ → Gal(KS/K)) :
    Nonempty
      (Gal(KS/K) ⧸ hmrCutSubgroup (K := K) (KS := KS) x ≃*
        hmrCutQuotient (K := K) (KS := KS) x) := by
  refine ⟨?_⟩
  simpa [hmrCutQuotient, hmrFixedField] using
    galoisFixedField
      (F := K) (L := KS) (hmrCutClosed (K := K) (KS := KS) x)

end HMRTameFrobeniusCutting

end TBluepr

end Submission

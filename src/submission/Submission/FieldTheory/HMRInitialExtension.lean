import Submission.FieldTheory.Blueprint
import Submission.FieldTheory.Compositum
import Submission.FieldTheory.RationalFinitePlace
import Submission.NumberTheory.CyclotomicCubic
import Submission.Group.ElementaryAbelianZassenhaus


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

open NumberField

namespace Submission
namespace TBluepr

/- Construction of the initial tame pro-`3` extension. -/
def initialRamifiedPrimes : Finset ℕ := {7, 13, 19, 31, 37}

/- We take `p = 3`. -/
def initialPrimeParameter : ℕ := 3

/- We take `K = ℚ`. -/
abbrev initialBaseField := ℚ

/- We take `S = {7,13,19,31,37}`. -/
theorem ramified_primes :
    initialRamifiedPrimes = ({7, 13, 19, 31, 37} : Finset ℕ) := by
  rfl

/- Every prime in `S` is prime. -/
theorem ramified_primes_prime :
    ∀ r ∈ initialRamifiedPrimes, Nat.Prime r := by
  intro r hr
  fin_cases hr <;> decide

/- Each prime in `S` is congruent to `1 mod 3`. -/
theorem ramified_primes_mod :
    ∀ r ∈ initialRamifiedPrimes, r ≡ 1 [MOD 3] := by
  intro r hr
  fin_cases hr <;> decide

/- None of the five initial ramified primes is the pro-prime `3`. -/
theorem ramified_primes_ne :
    ∀ r ∈ initialRamifiedPrimes, r ≠ 3 := by
  intro r hr
  fin_cases hr <;> norm_num

/- Let `Q_S^(3)` denote the compositum inside `AlgebraicClosure ℚ` of all finite Galois
`3`-extensions of `ℚ` unramified outside `S`. This is the honest ambient field used below for the
intended maximal pro-`3` extension. -/
noncomputable def initialProIntermediate :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
      IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes},
    E.1.toIntermediateField

abbrev initialProExtension := ↥initialProIntermediate

noncomputable instance instInitialExtension : Field initialProExtension :=
  inferInstance

noncomputable instance instProExtension :
    Algebra ℚ initialProExtension :=
  initialProIntermediate.algebra

instance instInitialPro : Normal ℚ initialProExtension := by
  simpa [initialProExtension, initialProIntermediate] using
    (IntermediateField.normal_iSup
      (F := ℚ) (K := AlgebraicClosure ℚ)
      (t := fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
          IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} =>
        E.1.toIntermediateField)
      (h := fun E => by
        letI : IsGalois ℚ E.1 := E.1.isGalois
        simpa using (IsGalois.to_normal (F := ℚ) (E := E.1))))

instance instSeparablePro :
    Algebra.IsSeparable ℚ initialProExtension := by
  simpa [initialProExtension, initialProIntermediate] using
    (IntermediateField.isSeparable_iSup
      (F := ℚ) (E := AlgebraicClosure ℚ)
      (t := fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
          IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} =>
        E.1.toIntermediateField)
      (h := fun E => by
        letI : IsGalois ℚ E.1 := E.1.isGalois
        simpa using (IsGalois.to_isSeparable (F := ℚ) (E := E.1))))

instance instGaloisPro : IsGalois ℚ initialProExtension := by
  exact ⟨⟩

/- Put `G := Gal(Q_S^(3)/ℚ)`. -/
abbrev initialGaloisGroup := Gal(initialProExtension/ℚ)

/- Let `G = G₁ ⊇ G₂ ⊇ G₃ ⊇ ···` be the Zassenhaus filtration of `G`. -/
def initialZassenhausFiltration : ℕ → Subgroup initialGaloisGroup :=
  zassenhausFiltration initialPrimeParameter initialGaloisGroup

/- We record the least rank `n ≥ 5` for which `G` surjects onto `(ℤ / 3ℤ)^n`. This packages
the concrete lower-bound information used later without pretending that the full abstract
pro-`3` generator rank has already been formalized. -/
noncomputable def initialGeneratorRank : ℕ :=
  sInf {n : ℕ | 5 ≤ n ∧ SurjectsElementaryRank initialGaloisGroup n}

/- For each `r ∈ S`, let `E_r` be the unique cyclic cubic subfield of `ℚ(ζ_r)`, viewed inside
`AlgebraicClosure ℚ` via a chosen `ℚ`-embedding. -/
noncomputable def initialCubicEmbedding (r : {s // s ∈ initialRamifiedPrimes}) :
    CyclotomicField r.1 ℚ →ₐ[ℚ] AlgebraicClosure ℚ :=
  IsAlgClosed.lift

noncomputable def initialIntermediateField
    (r : {s // s ∈ initialRamifiedPrimes}) :
    IntermediateField ℚ (AlgebraicClosure ℚ) := by
  let hrp : Nat.Prime r.1 := ramified_primes_prime r.1 r.2
  let hr3 : r.1 ≡ 1 [MOD 3] := ramified_primes_mod r.1 r.2
  letI : NeZero r.1 := ⟨hrp.ne_zero⟩
  letI : NeZero (r.1 : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  exact
    (galoisCubicSubfield (r := r.1) (K := CyclotomicField r.1 ℚ) hrp hr3).map
      (initialCubicEmbedding r)

abbrev initialCubicField (r : {s // s ∈ initialRamifiedPrimes}) : Type :=
  ↥(initialIntermediateField r)

noncomputable instance instFieldCubic (r : {s // s ∈ initialRamifiedPrimes}) :
    Field (initialCubicField r) :=
  inferInstance

instance instInitialCubic (r : {s // s ∈ initialRamifiedPrimes}) :
    NumberField (initialCubicField r) := by
  let hrp : Nat.Prime r.1 := ramified_primes_prime r.1 r.2
  let hr3 : r.1 ≡ 1 [MOD 3] := ramified_primes_mod r.1 r.2
  letI : NeZero r.1 := ⟨hrp.ne_zero⟩
  letI : NeZero (r.1 : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  let E : IntermediateField ℚ (CyclotomicField r.1 ℚ) :=
    galoisCubicSubfield (r := r.1) (K := CyclotomicField r.1 ℚ) hrp hr3
  letI : NumberField ↥E := inferInstance
  simpa [initialCubicField, initialIntermediateField, E, hrp, hr3] using
    (NumberField.of_ringEquiv
      (K := ↥E)
      (L := ↥(E.map (initialCubicEmbedding r)))
      (IntermediateField.equivMap E (initialCubicEmbedding r)).toRingEquiv :
      NumberField ↥(E.map (initialCubicEmbedding r)))

noncomputable instance instRatCubic (r : {s // s ∈ initialRamifiedPrimes}) :
    Algebra ℚ (initialCubicField r) :=
  (initialIntermediateField r).algebra

instance instInitialFamily :
    ∀ r : {s // s ∈ initialRamifiedPrimes}, Field (initialCubicField r) :=
  fun r => instFieldCubic r

instance instCubicFamily :
    ∀ r : {s // s ∈ initialRamifiedPrimes}, NumberField (initialCubicField r) :=
  fun r => instInitialCubic r

instance instRatFamily :
    ∀ r : {s // s ∈ initialRamifiedPrimes}, Algebra ℚ (initialCubicField r) :=
  fun r => instRatCubic r

/- By Standard lemma 1, `E_r/ℚ` is cyclic of degree `3` and is ramified only at `r`. -/
theorem initial_cubic_cyclic
    (r : {s // s ∈ initialRamifiedPrimes}) :
    CyclicCubicQ (initialCubicField r) := by
  let hrp : Nat.Prime r.1 := ramified_primes_prime r.1 r.2
  let hr3 : r.1 ≡ 1 [MOD 3] := ramified_primes_mod r.1 r.2
  letI : NeZero r.1 := ⟨hrp.ne_zero⟩
  letI : NeZero (r.1 : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  let E : IntermediateField ℚ (CyclotomicField r.1 ℚ) :=
    galoisCubicSubfield (r := r.1) (K := CyclotomicField r.1 ℚ) hrp hr3
  letI : Algebra ℚ ↥E := E.algebra'
  let e : ↥E ≃ₐ[ℚ] initialCubicField r := by
    simpa [initialCubicField, initialIntermediateField, E, hrp, hr3] using
      (IntermediateField.equivMap E (initialCubicEmbedding r))
  rcases galois_subfield_spec (K := CyclotomicField r.1 ℚ) hrp hr3 with ⟨hE_deg, hE_gal⟩
  haveI : IsGalois ℚ ↥E := hE_gal
  have hdeg : Module.finrank ℚ (initialCubicField r) = 3 := by
    rw [← e.toLinearEquiv.finrank_eq, hE_deg]
  have hgal : IsGalois ℚ (initialCubicField r) := IsGalois.of_algEquiv e
  have hcycE : IsCyclic (Gal(↥E/ℚ)) := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card Gal(↥E/ℚ) = 3 := by
      rw [IsGalois.card_aut_eq_finrank, hE_deg]
    exact isCyclic_of_prime_card hcard
  have hcyc : IsCyclic (Gal(initialCubicField r/ℚ)) := by
    letI : IsCyclic (Gal(↥E/ℚ)) := hcycE
    exact isCyclic_of_surjective (AlgEquiv.autCongr e) (AlgEquiv.autCongr e).surjective
  exact ⟨hdeg, hgal, hcyc⟩

theorem initial_ramification_idx
    (r : {s // s ∈ initialRamifiedPrimes}) :
    RationalRamificationIdx (S := 𝓞 (initialCubicField r)) r.1 3 := by
  let hrp : Nat.Prime r.1 := ramified_primes_prime r.1 r.2
  let hr3 : r.1 ≡ 1 [MOD 3] := ramified_primes_mod r.1 r.2
  letI : NeZero r.1 := ⟨hrp.ne_zero⟩
  letI : NeZero (r.1 : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  let E : IntermediateField ℚ (CyclotomicField r.1 ℚ) :=
    galoisCubicSubfield (r := r.1) (K := CyclotomicField r.1 ℚ) hrp hr3
  letI : Algebra ℚ ↥E := E.algebra'
  let e : ↥E ≃ₐ[ℚ] initialCubicField r := by
    simpa [initialCubicField, initialIntermediateField, E, hrp, hr3] using
      (IntermediateField.equivMap E (initialCubicEmbedding r))
  let e0 : 𝓞 ↥E ≃ₐ[ℤ] 𝓞 (initialCubicField r) :=
    (e.restrictScalars ℤ).mapIntegralClosure
  intro P hP
  let Q : Ideal (𝓞 ↥E) := P.comap e0
  have hQ : Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal r.1) (𝓞 ↥E) := by
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal r.1) := hP.2
    exact ⟨inferInstance, inferInstance⟩
  have hQe :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r.1) Q = 3 :=
    subfield_ramification_idx (K := CyclotomicField r.1 ℚ) hrp hr3 Q hQ
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r.1) P
      =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r.1) Q := by
            symm
            exact (Ideal.rationalPrimeIdeal r.1).ramificationIdx_comap_eq e0 P
    _ = 3 := hQe

theorem initial_cubic_self
    (r : {s // s ∈ initialRamifiedPrimes}) :
    ¬ RationalPrimeUnramified (S := 𝓞 (initialCubicField r)) r.1 := by
  intro hUnram
  let rI : Ideal ℤ := Ideal.rationalPrimeIdeal r.1
  letI : rI.IsPrime := rational_prime_ideal (ramified_primes_prime r.1 r.2)
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := rI.nonempty_primesOver (S := 𝓞 (initialCubicField r))
  have h1 :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r.1) P = 1 :=
    hUnram P ⟨hPprime, hPover⟩
  have h3 :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r.1) P = 3 :=
    initial_ramification_idx r P ⟨hPprime, hPover⟩
  omega

theorem initial_ramified_only
    (r : {s // s ∈ initialRamifiedPrimes}) :
    RamifiedOnlyAt (initialCubicField r) {r.1} := by
  intro q hq hqr
  let hrp : Nat.Prime r.1 := ramified_primes_prime r.1 r.2
  let hr3 : r.1 ≡ 1 [MOD 3] := ramified_primes_mod r.1 r.2
  letI : NeZero r.1 := ⟨hrp.ne_zero⟩
  letI : NeZero (r.1 : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  let E : IntermediateField ℚ (CyclotomicField r.1 ℚ) :=
    galoisCubicSubfield (r := r.1) (K := CyclotomicField r.1 ℚ) hrp hr3
  letI : Algebra ℚ ↥E := E.algebra'
  let e : ↥E ≃ₐ[ℚ] initialCubicField r := by
    simpa [initialCubicField, initialIntermediateField, E, hrp, hr3] using
      (IntermediateField.equivMap E (initialCubicEmbedding r))
  let e0 : 𝓞 ↥E ≃ₐ[ℤ] 𝓞 (initialCubicField r) :=
    (e.restrictScalars ℤ).mapIntegralClosure
  have hqr' : q ≠ r.1 := by
    intro hEq
    apply hqr
    simp [hEq]
  have hEunr : RationalPrimeUnramified (S := 𝓞 ↥E) q :=
    galois_subfield_away (K := CyclotomicField r.1 ℚ) hrp hr3 hq hqr'
  intro P hP
  let Q : Ideal (𝓞 ↥E) := P.comap e0
  have hQ : Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) (𝓞 ↥E) := by
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
    exact ⟨inferInstance, inferInstance⟩
  have hQe :
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) Q = 1 :=
    hEunr Q hQ
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P
      =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) Q := by
            symm
            simpa [Q] using
              (Ideal.ramificationIdx_comap_eq
                (R := ℤ) (S := 𝓞 ↥E) (S₁ := 𝓞 (initialCubicField r))
                (p := Ideal.rationalPrimeIdeal q) e0 P)
    _ = 1 := hQe

/- By Standard lemma 1, each `E_r` is totally real. -/
theorem initial_totally_real
    (r : {s // s ∈ initialRamifiedPrimes}) :
    NumberField.IsTotallyReal (initialCubicField r) := by
  let hrp : Nat.Prime r.1 := ramified_primes_prime r.1 r.2
  let hr3 : r.1 ≡ 1 [MOD 3] := ramified_primes_mod r.1 r.2
  letI : NeZero r.1 := ⟨hrp.ne_zero⟩
  letI : NeZero (r.1 : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  let E : IntermediateField ℚ (CyclotomicField r.1 ℚ) :=
    galoisCubicSubfield (r := r.1) (K := CyclotomicField r.1 ℚ) hrp hr3
  letI : NumberField ↥E := inferInstance
  let e : ↥E ≃ₐ[ℚ] initialCubicField r := by
    simpa [initialCubicField, initialIntermediateField, E, hrp, hr3] using
      (IntermediateField.equivMap E (initialCubicEmbedding r))
  letI : NumberField.IsTotallyReal ↥E :=
    subfield_totally_real (K := CyclotomicField r.1 ℚ) hrp hr3
  exact NumberField.IsTotallyReal.ofRingEquiv e.toRingEquiv

/- Therefore `E_r ⊆ Q_S^(3)`. -/
theorem initial_embeds_pro
    (r : {s // s ∈ initialRamifiedPrimes}) :
    EmbedsIntoExtension (initialCubicField r) initialProExtension := by
  letI : IsGalois ℚ ↥(initialIntermediateField r) :=
    (initial_cubic_cyclic r).2.1
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    .mk (initialIntermediateField r)
  have hPGroup : IsPGroup 3 (Gal(E/ℚ)) := by
    apply IsPGroup.of_card (n := 1)
    have hdeg : Module.finrank ℚ E = 3 := by
      simpa [E, initialCubicField] using (initial_cubic_cyclic r).1
    simpa using (IsGalois.card_aut_eq_finrank (E := E) (F := ℚ)).trans hdeg
  have hUnramified : UnramifiedOutside E initialRamifiedPrimes := by
    intro q hq hqS
    have hqr : q ∉ ({r.1} : Finset ℕ) := by
      rw [Finset.mem_singleton]
      intro hqr
      exact hqS (hqr ▸ r.2)
    simpa [E, initialCubicField, UnramifiedOutside] using
      (initial_ramified_only r q hq hqr)
  let x :
      {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
        IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} :=
    ⟨E, hPGroup, hUnramified⟩
  have hle : initialIntermediateField r ≤ initialProIntermediate := by
    simpa [x, E, initialProIntermediate] using
      (le_iSup
        (fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
            IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} =>
          E.1.toIntermediateField)
        x)
  exact ⟨IntermediateField.inclusion hle⟩

/- A finite subcompositum of the cubic fields `E_r`. -/
noncomputable def cubicFinsetCompositum
    (T : Finset {s // s ∈ initialRamifiedPrimes}) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ r ∈ T, initialIntermediateField r

noncomputable def initialCyclotomicIntermediate
    (r : {s // s ∈ initialRamifiedPrimes}) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  (⊤ : IntermediateField ℚ (CyclotomicField r.1 ℚ)).map (initialCubicEmbedding r)

theorem initial_intermediate_cyclotomic
    (r : {s // s ∈ initialRamifiedPrimes}) :
    initialIntermediateField r ≤ initialCyclotomicIntermediate r := by
  let hrp : Nat.Prime r.1 := ramified_primes_prime r.1 r.2
  let hr3 : r.1 ≡ 1 [MOD 3] := ramified_primes_mod r.1 r.2
  letI : NeZero r.1 := ⟨hrp.ne_zero⟩
  letI : NeZero (r.1 : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  change
    (galoisCubicSubfield (r := r.1) (K := CyclotomicField r.1 ℚ) hrp hr3).map
        (initialCubicEmbedding r) ≤
      (⊤ : IntermediateField ℚ (CyclotomicField r.1 ℚ)).map (initialCubicEmbedding r)
  exact IntermediateField.map_mono (initialCubicEmbedding r) le_top

theorem initial_cyclotomic_intermediate
    (r : {s // s ∈ initialRamifiedPrimes}) :
    IsCyclotomicExtension {r.1} ℚ ↥(initialCyclotomicIntermediate r) := by
  letI : NeZero r.1 := ⟨(ramified_primes_prime r.1 r.2).ne_zero⟩
  letI : NeZero (r.1 : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (ramified_primes_prime r.1 r.2).ne_zero⟩
  letI : IsCyclotomicExtension {r.1} ℚ (CyclotomicField r.1 ℚ) :=
    CyclotomicField.isCyclotomicExtension r.1 ℚ
  let e : CyclotomicField r.1 ℚ ≃ₐ[ℚ] ↥(initialCyclotomicIntermediate r) := by
    simpa [initialCyclotomicIntermediate] using
      (((IntermediateField.topEquiv :
          (⊤ : IntermediateField ℚ (CyclotomicField r.1 ℚ)) ≃ₐ[ℚ]
            CyclotomicField r.1 ℚ).symm).trans
        (IntermediateField.equivMap
          (⊤ : IntermediateField ℚ (CyclotomicField r.1 ℚ))
          (initialCubicEmbedding r)))
  exact IsCyclotomicExtension.equiv (S := {r.1}) (A := ℚ) (B := CyclotomicField r.1 ℚ) e

noncomputable def initialFinsetCompositum
    (T : Finset {s // s ∈ initialRamifiedPrimes}) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ r ∈ T, initialCyclotomicIntermediate r

theorem finset_compositum_cyclotomic
    (T : Finset {s // s ∈ initialRamifiedPrimes}) :
    cubicFinsetCompositum T ≤ initialFinsetCompositum T := by
  refine iSup_le fun r => iSup_le fun hrT => ?_
  exact le_iSup_of_le r <| le_iSup_of_le hrT <|
    initial_intermediate_cyclotomic r

theorem initial_finset_compositum
    (T : Finset {s // s ∈ initialRamifiedPrimes}) :
    ∃ n, n ∣ ∏ r ∈ T, r.1 ∧
      IsCyclotomicExtension {n} ℚ ↥(initialFinsetCompositum T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨1, by simp, ?_⟩
      haveI : IsCyclotomicExtension {1} ℚ ℚ :=
        IsCyclotomicExtension.singleton_one_of_algebraMap_bijective
          (A := ℚ) (B := ℚ) (by intro x; exact ⟨x, rfl⟩)
      have hbot :
          initialFinsetCompositum ∅ =
            (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
        simp [initialFinsetCompositum]
      let e : ℚ ≃ₐ[ℚ] ↥(initialFinsetCompositum ∅) :=
        (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ)).symm.trans
          (IntermediateField.equivOfEq hbot.symm)
      simpa [initialFinsetCompositum] using
        (IsCyclotomicExtension.equiv (S := {1}) (A := ℚ) (B := ℚ) e)
  | insert r T hrT ih =>
      rcases ih with ⟨n, hndvd, hcycloT⟩
      haveI : IsCyclotomicExtension {r.1} ℚ ↥(initialCyclotomicIntermediate r) :=
        initial_cyclotomic_intermediate r
      haveI : IsCyclotomicExtension {n} ℚ ↥(initialFinsetCompositum T) := hcycloT
      haveI : NeZero r.1 := ⟨(ramified_primes_prime r.1 r.2).ne_zero⟩
      have hprod0 : ∏ s ∈ T, s.1 ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro s hs
        exact (ramified_primes_prime s.1 s.2).ne_zero
      have hn0 : n ≠ 0 := by
        intro hn0
        rcases hndvd with ⟨k, hk⟩
        rw [hn0, zero_mul] at hk
        exact hprod0 hk
      haveI : NeZero n := ⟨hn0⟩
      refine ⟨Nat.lcm r.1 n, ?_, ?_⟩
      · apply Nat.lcm_dvd
        · rw [Finset.prod_insert hrT]
          exact dvd_mul_right _ _
        · rcases hndvd with ⟨k, hk⟩
          rw [Finset.prod_insert hrT, hk]
          refine ⟨r.1 * k, by ring⟩
      · have hsup :
            IsCyclotomicExtension {Nat.lcm r.1 n} ℚ
              ↥(initialCyclotomicIntermediate r ⊔
                initialFinsetCompositum T) := by
            let F1 : IntermediateField ℚ (AlgebraicClosure ℚ) :=
              initialCyclotomicIntermediate r
            let F2 : IntermediateField ℚ (AlgebraicClosure ℚ) :=
              initialFinsetCompositum T
            have hF1 : IsCyclotomicExtension {r.1} ℚ ↥F1 := by
              dsimp [F1]
              exact initial_cyclotomic_intermediate r
            have hF2 : IsCyclotomicExtension {n} ℚ ↥F2 := by
              dsimp [F2]
              exact hcycloT
            letI : IsCyclotomicExtension {r.1} ℚ ↥F1.toSubalgebra := hF1
            letI : IsCyclotomicExtension {n} ℚ ↥F2.toSubalgebra := hF2
            letI : FiniteDimensional ℚ ↥F1 :=
              IsCyclotomicExtension.finite_of_singleton r.1 ℚ F1
            have hsub :
                IsCyclotomicExtension {Nat.lcm r.1 n} ℚ
                  (F1.toSubalgebra ⊔ F2.toSubalgebra : Subalgebra ℚ (AlgebraicClosure ℚ)) :=
              IsCyclotomicExtension.lcm_sup r.1 n F1.toSubalgebra F2.toSubalgebra
            change IsCyclotomicExtension {Nat.lcm r.1 n} ℚ
              ((F1 ⊔ F2 : IntermediateField ℚ (AlgebraicClosure ℚ)).toSubalgebra)
            rw [IntermediateField.sup_toSubalgebra_of_left]
            exact hsub
        have hEq :
            initialFinsetCompositum (insert r T) =
              initialCyclotomicIntermediate r ⊔
                initialFinsetCompositum T := by
          unfold initialFinsetCompositum
          apply le_antisymm
          · refine iSup_le fun r1 => iSup_le fun hr1 => ?_
            rcases Finset.mem_insert.mp hr1 with rfl | hr1T
            · exact le_sup_left
            · exact le_trans
                (le_iSup_of_le r1 <| le_iSup_of_le hr1T
                  (show initialCyclotomicIntermediate r1 ≤
                    initialCyclotomicIntermediate r1 from le_rfl))
                le_sup_right
          · refine sup_le ?_ ?_
            · exact le_iSup_of_le r <| le_iSup_of_le (Finset.mem_insert_self _ _) le_rfl
            · refine iSup_le fun r1 => iSup_le fun hr1T => ?_
              exact le_iSup_of_le r1 <| le_iSup_of_le (Finset.mem_insert_of_mem hr1T)
                (show initialCyclotomicIntermediate r1 ≤
                  initialCyclotomicIntermediate r1 from le_rfl)
        exact hEq ▸ hsup

theorem cubic_finset_compositum
    (T : Finset {s // s ∈ initialRamifiedPrimes}) :
    IsGalois ℚ ↥(cubicFinsetCompositum T) := by
  classical
  let ι := {r // r ∈ T}
  let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun r => initialIntermediateField r.1
  have hEq :
      cubicFinsetCompositum T = ⨆ r : ι, t r := by
    unfold cubicFinsetCompositum
    apply le_antisymm
    · refine iSup_le fun r => iSup_le fun hrT => ?_
      exact le_iSup_of_le ⟨r, hrT⟩ le_rfl
    · refine iSup_le fun r => ?_
      exact le_iSup_of_le r.1 <| le_iSup_of_le r.2 le_rfl
  have hnormal :
      Normal ℚ ↥(⨆ r : ι, t r) := by
    simpa [t] using
      (IntermediateField.normal_iSup
        (F := ℚ) (K := AlgebraicClosure ℚ) (t := t)
        (h := fun r => by
          letI : IsGalois ℚ ↥(initialIntermediateField r.1) :=
            (initial_cubic_cyclic r.1).2.1
          simpa using
            (IsGalois.to_normal (F := ℚ) (E := ↥(initialIntermediateField r.1)))))
  have hsep :
      Algebra.IsSeparable ℚ ↥(⨆ r : ι, t r) := by
    simpa [t] using
      (IntermediateField.isSeparable_iSup
        (F := ℚ) (E := AlgebraicClosure ℚ) (t := t)
        (h := fun r => by
          letI : IsGalois ℚ ↥(initialIntermediateField r.1) :=
            (initial_cubic_cyclic r.1).2.1
          simpa using
            (IsGalois.to_isSeparable (F := ℚ) (E := ↥(initialIntermediateField r.1)))))
  exact hEq ▸ { to_isSeparable := hsep, to_normal := hnormal }

/- A prime outside the chosen finite set of conductors is unramified in the corresponding finite
subcompositum of the cubic fields. This is the finite-compositum ramification input needed later
for the disjoint-ramification argument. -/
theorem cubic_finset_outside
    (T : Finset {s // s ∈ initialRamifiedPrimes}) :
    ∀ q, Nat.Prime q → q ∉ T.image Subtype.val →
      RationalPrimeUnramified (S := 𝓞 ↥(cubicFinsetCompositum T)) q := by
  intro q hq hqT
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := cubicFinsetCompositum T
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := initialFinsetCompositum T
  have hEK : E ≤ K := finset_compositum_cyclotomic T
  have hqprod : ¬ q ∣ ∏ r ∈ T, r.1 := by
    intro hprod
    obtain ⟨r, hrT, hqr⟩ :=
      (hq.prime.dvd_finsetProd_iff fun s : {s // s ∈ initialRamifiedPrimes} => s.1).1 <| by
        simpa using hprod
    have hrq : r.1 = q := by
      exact ((Nat.prime_dvd_prime_iff_eq hq (ramified_primes_prime r.1 r.2)).mp hqr).symm
    exact hqT <| Finset.mem_image.mpr ⟨r, hrT, hrq⟩
  rcases initial_finset_compositum T with ⟨n, hndvd, hcycloK⟩
  have hqndvdn : ¬ q ∣ n := fun hqn => hqprod (dvd_trans hqn hndvd)
  have hn0 : n ≠ 0 := by
    intro hn0
    exact hqndvdn (hn0.symm ▸ dvd_zero q)
  letI : NeZero n := ⟨hn0⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : IsCyclotomicExtension {n} ℚ ↥K := hcycloK
  letI : FiniteDimensional ℚ ↥K := IsCyclotomicExtension.finite_of_singleton n ℚ K
  letI : NumberField ↥K := NumberField.of_module_finite ℚ ↥K
  letI : IsGalois ℚ ↥K := IsCyclotomicExtension.isGalois (S := {n}) (K := ℚ) (L := ↥K)
  have hK_unram : RationalPrimeUnramified (S := 𝓞 ↥K) q := by
    let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
    have hramK : qI.ramificationIdxIn (𝓞 ↥K) = 1 := by
      simpa [qI, Ideal.rationalPrimeIdeal] using
        IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
          (m := n) (p := q) (K := ↥K) hqndvdn
    intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver qI := hP.2
    calc
      Ideal.ramificationIdx qI P
        = qI.ramificationIdxIn (𝓞 ↥K) := by
            symm
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := P) (G := Gal(↥K/ℚ))
      _ = 1 := hramK
  letI : FiniteDimensional ℚ ↥E := by
    change FiniteDimensional ℚ ↥(cubicFinsetCompositum T)
    exact IntermediateField.finiteDimensional_iSup_of_finset'
      (t := initialIntermediateField) (s := T) (fun r _ => inferInstance)
  letI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
  letI : IsGalois ℚ ↥E := cubic_finset_compositum T
  let E' : IntermediateField ℚ ↥K := E.restrict hEK
  let eE : ↥E ≃ₐ[ℚ] ↥E' := IntermediateField.restrict_algEquiv hEK
  letI : FiniteDimensional ℚ ↥E' :=
    FiniteDimensional.of_surjective eE.toLinearEquiv.toLinearMap eE.surjective
  letI : NumberField ↥E' := NumberField.of_module_finite ℚ ↥E'
  letI : IsGalois ℚ ↥E' := IsGalois.of_algEquiv eE
  have hE'_unram : RationalPrimeUnramified (S := 𝓞 ↥E') q :=
    rational_unramified_intermediate (K := ↥K) E' hq hK_unram
  exact rational_unramified_alg eE.symm hE'_unram

theorem initial_finset_outside
    (T : Finset {s // s ∈ initialRamifiedPrimes})
    {q : ℕ} (hq : Nat.Prime q)
    (hT : ∀ r ∈ T, q ≠ r.1) :
    RationalPrimeUnramified (S := 𝓞 ↥(cubicFinsetCompositum T)) q := by
  apply cubic_finset_outside T q hq
  intro hqT
  rcases Finset.mem_image.mp hqT with ⟨r, hrT, hrq⟩
  exact hT r hrT hrq.symm

/- Hence their compositum `E := ∏_{r ∈ S} E_r` is part of the construction. -/
noncomputable def initialCompositumIntermediate :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ r : {s // s ∈ initialRamifiedPrimes}, initialIntermediateField r

abbrev initialCubicCompositum : Type :=
  ↥initialCompositumIntermediate

noncomputable instance instInitialCompositum : Field initialCubicCompositum :=
  inferInstance

instance instCubicCompositum : NumberField initialCubicCompositum := by
  let ι := {s // s ∈ initialRamifiedPrimes}
  letI : Finite ι := by
    classical
    exact Finite.of_fintype ι
  letI : ∀ r : ι, FiniteDimensional ℚ ↥(initialIntermediateField r) := fun r => by
    change FiniteDimensional ℚ (initialCubicField r)
    infer_instance
  letI : FiniteDimensional ℚ ↥initialCompositumIntermediate := by
    delta initialCompositumIntermediate
    exact IntermediateField.finiteDimensional_iSup_of_finite
      (K := ℚ) (L := AlgebraicClosure ℚ) (ι := ι) (t := initialIntermediateField)
  exact NumberField.of_module_finite ℚ initialCubicCompositum

noncomputable instance instAlgebraCompositum : Algebra ℚ initialCubicCompositum :=
  initialCompositumIntermediate.algebra

theorem finset_compositum_univ :
    cubicFinsetCompositum
        (Finset.univ : Finset {s // s ∈ initialRamifiedPrimes}) =
      initialCompositumIntermediate := by
  change
    (⨆ r ∈ (Finset.univ : Finset {s // s ∈ initialRamifiedPrimes}),
      initialIntermediateField r) =
      (⨆ r : {s // s ∈ initialRamifiedPrimes}, initialIntermediateField r)
  simp

theorem initial_compositum_outside :
    UnramifiedOutside initialCubicCompositum initialRamifiedPrimes := by
  intro q hq hqS
  change RationalPrimeUnramified (S := 𝓞 ↥initialCompositumIntermediate) q
  have hE := finset_compositum_univ
  exact
    Eq.ndrec
      (motive := fun F : IntermediateField ℚ (AlgebraicClosure ℚ) =>
        RationalPrimeUnramified (S := 𝓞 ↥F) q)
      (cubic_finset_outside
        (Finset.univ : Finset {s // s ∈ initialRamifiedPrimes}) q hq
        (by simpa using hqS))
      hE

/- The field `E` is the compositum of the family `E_r`. -/
theorem initial_compositum :
    CompositumFamily initialCubicField initialCubicCompositum := by
  classical
  let ι := {s // s ∈ initialRamifiedPrimes}
  let p : ι → Polynomial ℚ := fun r =>
    letI : IsGalois ℚ (initialCubicField r) := (initial_cubic_cyclic r).2.1
    Classical.choose
      (IsGalois.is_separable_splitting_field (F := ℚ) (E := initialCubicField r))
  have hp_sep : ∀ r : ι, (p r).Separable := fun r =>
    letI : IsGalois ℚ (initialCubicField r) := (initial_cubic_cyclic r).2.1
    (Classical.choose_spec
      (IsGalois.is_separable_splitting_field (F := ℚ) (E := initialCubicField r))).1
  have hp_split : ∀ r : ι, (p r).IsSplittingField ℚ (initialCubicField r) := fun r =>
    letI : IsGalois ℚ (initialCubicField r) := (initial_cubic_cyclic r).2.1
    (Classical.choose_spec
      (IsGalois.is_separable_splitting_field (F := ℚ) (E := initialCubicField r))).2
  refine ⟨?_, ?_⟩
  · intro r
    refine ⟨IntermediateField.inclusion ?_⟩
    exact le_iSup initialIntermediateField r
  · intro F _ _ _ hF
    change EmbedsIntoField ↥initialCompositumIntermediate F
    let E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
      ⨆ r ∈ (Finset.univ : Finset ι), initialIntermediateField r
    have hnonzero : ∏ r ∈ (Finset.univ : Finset ι), p r ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro r hr
      exact (hp_sep r).ne_zero
    have hEqCompositum :
        initialCompositumIntermediate = E' := by
      change (⨆ r : ι, initialIntermediateField r) =
        (⨆ r ∈ (Finset.univ : Finset ι), initialIntermediateField r)
      simp
    have hsplitCompositum' :
        (∏ r ∈ (Finset.univ : Finset ι), p r).IsSplittingField ℚ ↥E' :=
      IntermediateField.isSplittingField_iSup
        (t := initialIntermediateField) (p := p) (s := Finset.univ)
        hnonzero (fun r _ => by simpa [initialCubicField] using hp_split r)
    have hsplitF :
        ((∏ r ∈ (Finset.univ : Finset ι), p r).map (algebraMap ℚ F)).Splits := by
      rw [Polynomial.map_prod]
      exact Polynomial.Splits.prod fun r _ => by
        letI : (p r).IsSplittingField ℚ (initialCubicField r) := hp_split r
        rcases hF r with ⟨φ⟩
        exact Polynomial.Splits.of_algHom
          (Polynomial.IsSplittingField.splits (L := initialCubicField r) (p r)) φ
    letI : (∏ r ∈ (Finset.univ : Finset ι), p r).IsSplittingField ℚ ↥E' :=
      hsplitCompositum'
    refine ⟨(Polynomial.IsSplittingField.lift ↥E'
      (∏ r ∈ (Finset.univ : Finset ι), p r) hsplitF).comp ?_⟩
    exact (IntermediateField.equivOfEq hEqCompositum).toAlgHom

/-!
The eventual proof of `cubic_compositum_five` naturally breaks into a sequence of
smaller steps:

1. Show the full compositum is already Galois over `ℚ`.
2. Record that each constituent cubic field has degree `3`.
3. Turn the constituent-wise degree computation into the global target `3 ^ 5`.
4. Translate that degree computation into a cardinality statement about the Galois group.
5. Separate the purely numerical input from the final explicit equivalence with
   `(ℤ / 3ℤ)^5`.

The lemmas below package those steps.
-/

/- The full compositum is already Galois because it is the finite univ-compositum of Galois
constituents. -/
lemma initial_compositum_galois :
    IsGalois ℚ initialCubicCompositum := by
  have hE := finset_compositum_univ
  exact
    Eq.ndrec
      (motive := fun F : IntermediateField ℚ (AlgebraicClosure ℚ) => IsGalois ℚ ↥F)
      (cubic_finset_compositum
        (Finset.univ : Finset {s // s ∈ initialRamifiedPrimes}))
      hE

/- The indexing set really has five elements. -/
lemma ramified_primes_card :
    Fintype.card {s // s ∈ initialRamifiedPrimes} = 5 := by
  simp [ramified_primes]

/- Each distinguished cubic subfield contributes degree `3`. -/
lemma initial_cubic_finrank
    (r : {s // s ∈ initialRamifiedPrimes}) :
    Module.finrank ℚ (initialCubicField r) = 3 := by
  simpa [CyclicCubicQ] using
    (initial_cubic_cyclic r).1

/- The product of the constituent degrees is a power of `3` indexed by the five ramified primes. -/
lemma initial_cubic_card :
    (∏ r : {s // s ∈ initialRamifiedPrimes},
      Module.finrank ℚ (initialCubicField r)) =
        3 ^ Fintype.card {s // s ∈ initialRamifiedPrimes} := by
  calc
    (∏ r : {s // s ∈ initialRamifiedPrimes},
        Module.finrank ℚ (initialCubicField r))
        = ∏ _r : {s // s ∈ initialRamifiedPrimes}, 3 := by
            simp [initial_cubic_finrank]
    _ = 3 ^ Fintype.card {s // s ∈ initialRamifiedPrimes} := by
          simp

/- Specializing the previous lemma gives the concrete target `3 ^ 5`. -/
lemma initial_cubic_five :
    (∏ r : {s // s ∈ initialRamifiedPrimes},
      Module.finrank ℚ (initialCubicField r)) = 3 ^ 5 := by
  calc
    (∏ r : {s // s ∈ initialRamifiedPrimes},
        Module.finrank ℚ (initialCubicField r))
        = 3 ^ Fintype.card {s // s ∈ initialRamifiedPrimes} :=
          initial_cubic_card
    _ = 3 ^ 5 := by
          rw [ramified_primes_card]

/- Galoisness converts the degree of the compositum into the cardinality of its automorphism
group. -/
lemma initial_compositum_finrank :
    Nat.card (Gal(initialCubicCompositum/ℚ)) =
      Module.finrank ℚ initialCubicCompositum := by
  letI : IsGalois ℚ initialCubicCompositum := initial_compositum_galois
  exact IsGalois.card_aut_eq_finrank (F := ℚ) (E := initialCubicCompositum)

/- We also record the same identity in the opposite direction because later degree arguments tend to
start from a `finrank` computation rather than a group-cardinality computation. -/
lemma initial_compositum_card :
    Module.finrank ℚ initialCubicCompositum =
      Nat.card (Gal(initialCubicCompositum/ℚ)) := by
  symm
  exact initial_compositum_finrank

/- Any future degree formula for the compositum immediately specializes to the target `3 ^ 5`. -/
lemma initial_compositum_formula
    (hDegree :
      Module.finrank ℚ initialCubicCompositum =
        ∏ r : {s // s ∈ initialRamifiedPrimes},
          Module.finrank ℚ (initialCubicField r)) :
    Module.finrank ℚ initialCubicCompositum = 3 ^ 5 := by
  calc
    Module.finrank ℚ initialCubicCompositum
        = ∏ r : {s // s ∈ initialRamifiedPrimes},
            Module.finrank ℚ (initialCubicField r) := hDegree
    _ = 3 ^ 5 := initial_cubic_five

/- Combining the previous two lemmas turns a degree formula into the cardinality statement needed
for the final classification step. -/
lemma compositum_five_formula
    (hDegree :
      Module.finrank ℚ initialCubicCompositum =
        ∏ r : {s // s ∈ initialRamifiedPrimes},
          Module.finrank ℚ (initialCubicField r)) :
    Nat.card (Gal(initialCubicCompositum/ℚ)) = 3 ^ 5 := by
  calc
    Nat.card (Gal(initialCubicCompositum/ℚ))
        = Module.finrank ℚ initialCubicCompositum :=
          initial_compositum_finrank
    _ = 3 ^ 5 :=
      initial_compositum_formula hDegree

/- Once an explicit equivalence with `(ℤ / 3ℤ)^5` is available, the target theorem is just a
packaging step. -/
lemma initial_cubic_compositum
    (e : Gal(initialCubicCompositum/ℚ) ≃* ElementaryAbelianGroup 5) :
    ElementaryAbelianRank initialCubicCompositum 5 := by
  exact ⟨initial_compositum_galois, ⟨e⟩⟩

/- To actually build the equivalence with `(ℤ / 3ℤ)^5`, we next rigidify the five ramified
primes into a concrete `Fin 5`-indexed family. This lets us apply the generic
`disjoint_before_ramification` theorem to successive prefixes of the family. -/

/-- A fixed ordering of the five ramified primes `7, 13, 19, 31, 37`. -/
noncomputable def initialRamifiedOrder : Fin 5 → {s // s ∈ initialRamifiedPrimes} := by
  intro i
  cases i with
  | mk n hn =>
      refine
        match n with
        | 0 => ⟨7, by simp [ramified_primes]⟩
        | 1 => ⟨13, by simp [ramified_primes]⟩
        | 2 => ⟨19, by simp [ramified_primes]⟩
        | 3 => ⟨31, by simp [ramified_primes]⟩
        | _ => ⟨37, by simp [ramified_primes]⟩

/-- The `Fin 5`-indexed family of cubic intermediate fields, ordered by
`initialRamifiedOrder`. -/
noncomputable def initialCubicIntermediate
    (i : Fin 5) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  initialIntermediateField (initialRamifiedOrder i)

/-- The finite set of ramified primes already used before stage `i`. -/
noncomputable def initialRamifiedPrefix
    (i : Fin 5) : Finset {s // s ∈ initialRamifiedPrimes} :=
  (Finset.univ.filter fun j : Fin 5 => j < i).image initialRamifiedOrder

/-- Each ordered constituent is still a cubic field. -/
lemma initial_cubic_intermediate
    (i : Fin 5) :
    Module.finrank ℚ ↥(initialCubicIntermediate i) = 3 := by
  simpa [initialCubicIntermediate, initialCubicField] using
    initial_cubic_finrank (initialRamifiedOrder i)

/-- Each ordered constituent is finite over `ℚ`. -/
lemma initial_intermediate_dimensional
    (i : Fin 5) :
    FiniteDimensional ℚ ↥(initialCubicIntermediate i) := by
  simpa [initialCubicIntermediate, initialCubicField] using
    (inferInstance : FiniteDimensional ℚ (initialCubicField (initialRamifiedOrder i)))

/-- Each ordered constituent is Galois over `ℚ`. -/
lemma initial_intermediate_galois
    (i : Fin 5) :
    IsGalois ℚ ↥(initialCubicIntermediate i) := by
  simpa [initialCubicIntermediate, initialCubicField] using
    (initial_cubic_cyclic (initialRamifiedOrder i)).2.1

/-- The compositum of the fields before stage `i` is exactly the finite compositum indexed by the
earlier ramified primes in the chosen order. -/
lemma compositum_before_finset
    (i : Fin 5) :
    compositumBefore initialCubicIntermediate i =
      cubicFinsetCompositum (initialRamifiedPrefix i) := by
  unfold compositumBefore compositum initialCubicIntermediate
    initialRamifiedPrefix cubicFinsetCompositum
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_iSup_of_le (initialRamifiedOrder j) <|
      le_iSup_of_le (Finset.mem_image.mpr ⟨j, hj, rfl⟩) le_rfl
  · refine iSup_le fun r => iSup_le fun hr => ?_
    rcases Finset.mem_image.mp hr with ⟨j, hj, rfl⟩
    exact le_iSup_of_le j <| le_iSup_of_le hj le_rfl

/-- Finite dimensionality of each earlier compositum, needed to talk about its ring of integers and
intermediate Galois subfields. -/
lemma compositum_before_dimensional
    (i : Fin 5) :
    FiniteDimensional ℚ ↥(compositumBefore initialCubicIntermediate i) := by
  rw [compositum_before_finset]
  exact IntermediateField.finiteDimensional_iSup_of_finset'
    (t := initialIntermediateField) (s := initialRamifiedPrefix i)
    (fun r _ => inferInstance)

/-- Each earlier compositum is already Galois over `ℚ`. -/
lemma compositum_before_galois
    (i : Fin 5) :
    IsGalois ℚ ↥(compositumBefore initialCubicIntermediate i) := by
  rw [compositum_before_finset]
  exact cubic_finset_compositum (initialRamifiedPrefix i)

/-- The chosen ordering never repeats a ramified prime before reaching stage `i`. -/
lemma ramified_val_ne
    {i j : Fin 5} (hj : j < i) :
    (initialRamifiedOrder j).1 ≠ (initialRamifiedOrder i).1 := by
  fin_cases i <;> fin_cases j <;> simp [initialRamifiedOrder] at hj ⊢

/-- Therefore the prime used at stage `i` is outside the support of the earlier compositum. -/
lemma initial_ramified_current
    (i : Fin 5) :
    ∀ r ∈ initialRamifiedPrefix i,
      (initialRamifiedOrder i).1 ≠ r.1 := by
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨j, hj, rfl⟩
  rcases Finset.mem_filter.mp hj with ⟨_, hjlt⟩
  simpa [eq_comm] using ramified_val_ne hjlt

/-- The prefix compositum is unramified at the new prime introduced at stage `i`. -/
lemma compositum_before_current
    (i : Fin 5) :
    RationalPrimeUnramified
      (S := 𝓞 ↥(compositumBefore initialCubicIntermediate i))
      (initialRamifiedOrder i).1 := by
  have hq : Nat.Prime (initialRamifiedOrder i).1 :=
    ramified_primes_prime _ (initialRamifiedOrder i).2
  rw [compositum_before_finset]
  exact initial_finset_outside
    (initialRamifiedPrefix i) hq
    (initial_ramified_current i)

/-- A ramification witness that is stable under passing to larger composita. We package
ramification through finite Galois subfields so that monotonicity is immediate. -/
def initialCubicRamified
    (q : ℕ) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Prop :=
  ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ),
    E ≤ K ∧ Nat.Prime q ∧ FiniteDimensional ℚ ↥E ∧ IsGalois ℚ ↥E ∧
      ¬ RationalPrimeUnramified (S := 𝓞 ↥E) q

/-- Ramification witnesses persist in larger composita. -/
lemma initial_ramified_mono
    {q : ℕ} {K M : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hKM : K ≤ M) :
    initialCubicRamified q K → initialCubicRamified q M := by
  rintro ⟨E, hEK, hq, hfin, hgal, hram⟩
  exact ⟨E, le_trans hEK hKM, hq, hfin, hgal, hram⟩

/-- The `i`-th cubic field really is ramified at its distinguished prime. -/
lemma intermediate_ramified_self
    (i : Fin 5) :
    initialCubicRamified (initialRamifiedOrder i).1
      (initialCubicIntermediate i) := by
  refine ⟨initialCubicIntermediate i, le_rfl, ?_,
    initial_intermediate_dimensional i, ?_, ?_⟩
  · exact ramified_primes_prime _ (initialRamifiedOrder i).2
  · exact initial_intermediate_galois i
  · simpa [initialCubicIntermediate, initialCubicField] using
      initial_cubic_self (initialRamifiedOrder i)

/-- No finite Galois subfield of the earlier compositum can ramify at the new prime, because the
whole earlier compositum is already unramified there. -/
lemma before_ramified_current
    (i : Fin 5) :
    ¬ initialCubicRamified (initialRamifiedOrder i).1
        (compositumBefore initialCubicIntermediate i) := by
  intro hram
  rcases hram with ⟨E, hE_le, hq, hE_fin, hE_gal, hE_ram⟩
  letI : FiniteDimensional ℚ ↥(compositumBefore initialCubicIntermediate i) :=
    compositum_before_dimensional i
  letI : NumberField ↥(compositumBefore initialCubicIntermediate i) :=
    NumberField.of_module_finite ℚ ↥(compositumBefore initialCubicIntermediate i)
  letI : IsGalois ℚ ↥(compositumBefore initialCubicIntermediate i) :=
    compositum_before_galois i
  let E' : IntermediateField ℚ ↥(compositumBefore initialCubicIntermediate i) :=
    E.restrict hE_le
  let eE : ↥E ≃ₐ[ℚ] ↥E' := IntermediateField.restrict_algEquiv hE_le
  letI : FiniteDimensional ℚ ↥E := hE_fin
  letI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
  letI : FiniteDimensional ℚ ↥E' :=
    FiniteDimensional.of_surjective eE.toLinearEquiv.toLinearMap eE.surjective
  letI : NumberField ↥E' := NumberField.of_module_finite ℚ ↥E'
  letI : IsGalois ℚ ↥E' := IsGalois.of_algEquiv eE
  have hprefix_unram :
      RationalPrimeUnramified
        (S := 𝓞 ↥(compositumBefore initialCubicIntermediate i))
        (initialRamifiedOrder i).1 :=
    compositum_before_current i
  have hE'_unram :
      RationalPrimeUnramified (S := 𝓞 ↥E') (initialRamifiedOrder i).1 :=
    rational_unramified_intermediate
      (K := ↥(compositumBefore initialCubicIntermediate i)) E' hq hprefix_unram
  have hE_unram :
      RationalPrimeUnramified (S := 𝓞 ↥E) (initialRamifiedOrder i).1 :=
    rational_unramified_alg eE.symm hE'_unram
  exact hE_ram hE_unram

/-- Applying the disjoint-ramification criterion to the explicit `Fin 5` ordering gives the
successive linear disjointness statements needed for the eventual degree computation. -/
lemma initial_disjoint_before :
    ∀ i,
      (compositumBefore initialCubicIntermediate i).LinearDisjoint
        (initialCubicIntermediate i) := by
  letI : ∀ i, FiniteDimensional ℚ ↥(initialCubicIntermediate i) := fun i =>
    initial_intermediate_dimensional i
  have hprimeDegree :
      ∀ i, Nat.Prime (Module.finrank ℚ ↥(initialCubicIntermediate i)) := by
    intro i
    simpa [initial_cubic_intermediate i] using
      (show Nat.Prime 3 by decide)
  have hgal :
      ∀ i,
        @IsGalois ℚ _ ↥(initialCubicIntermediate i) _
          (initialCubicIntermediate i).algebra' := by
    intro i
    exact initial_intermediate_galois i
  have hscalar :
      ∀ i,
        IsScalarTower ℚ ↥(initialCubicIntermediate i) (AlgebraicClosure ℚ) := by
    intro i
    exact IntermediateField.isScalarTower_mid'
      (K := ℚ) (S := initialCubicIntermediate i) (L := AlgebraicClosure ℚ)
  have hram :
      ∀ i, ∃ p : ℕ,
        initialCubicRamified p (initialCubicIntermediate i) ∧
          ¬ initialCubicRamified p
            (compositumBefore initialCubicIntermediate i) := by
    intro i
    exact ⟨(initialRamifiedOrder i).1,
      intermediate_ramified_self i,
      before_ramified_current i⟩
  exact disjoint_before_ramification
    (L := initialCubicIntermediate)
    (RamifiedAt := initialCubicRamified)
    hprimeDegree hgal hscalar hram
    (fun {p K M} hKM => initial_ramified_mono hKM)

lemma initial_ramified_surjective :
    Function.Surjective initialRamifiedOrder := by
  intro r
  rcases r with ⟨r, hr⟩
  rcases (by simpa [ramified_primes] using hr :
      r = 7 ∨ r = 13 ∨ r = 19 ∨ r = 31 ∨ r = 37) with
    rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

lemma intermediate_i_sup :
    (⨆ i : Fin 5, initialCubicIntermediate i) =
      initialCubicIntermediate 0 ⊔
        initialCubicIntermediate 1 ⊔
          initialCubicIntermediate 2 ⊔
            initialCubicIntermediate 3 ⊔
              initialCubicIntermediate 4 := by
  suffices
      ⨆ i ∈ (Finset.univ : Finset (Fin 5)), initialCubicIntermediate i =
        initialCubicIntermediate 0 ⊔
          initialCubicIntermediate 1 ⊔
            initialCubicIntermediate 2 ⊔
              initialCubicIntermediate 3 ⊔
                initialCubicIntermediate 4 by
    simp [← this]
  rw [← Finset.sup_eq_iSup, show (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} by rfl]
  simp [sup_assoc]

lemma intermediate_sup_compositum :
    initialCubicIntermediate 0 ⊔
        initialCubicIntermediate 1 ⊔
          initialCubicIntermediate 2 ⊔
            initialCubicIntermediate 3 ⊔
              initialCubicIntermediate 4 =
      initialCompositumIntermediate := by
  calc
    initialCubicIntermediate 0 ⊔
        initialCubicIntermediate 1 ⊔
          initialCubicIntermediate 2 ⊔
            initialCubicIntermediate 3 ⊔
              initialCubicIntermediate 4
      = ⨆ i : Fin 5, initialCubicIntermediate i := by
          symm
          exact intermediate_i_sup
    _ = initialCompositumIntermediate := by
          refine le_antisymm ?_ ?_
          · refine iSup_le fun i => ?_
            exact le_iSup initialIntermediateField (initialRamifiedOrder i)
          · refine iSup_le fun r => ?_
            rcases initial_ramified_surjective r with ⟨i, rfl⟩
            exact le_iSup initialCubicIntermediate i

lemma cubic_compositum_before :
    compositumBefore initialCubicIntermediate 0 = ⊥ := by
  simp [compositumBefore, compositum]

lemma initial_cubic_before :
    compositumBefore initialCubicIntermediate 1 =
      initialCubicIntermediate 0 := by
  simp [compositumBefore, compositum]

lemma compositum_before_two :
    compositumBefore initialCubicIntermediate 2 =
      initialCubicIntermediate 0 ⊔ initialCubicIntermediate 1 := by
  rw [compositumBefore, compositum,
    show (Finset.univ.filter fun j : Fin 5 => j < 2) = {0, 1} by rfl,
    ← Finset.sup_eq_iSup]
  simp

lemma initial_compositum_before :
    compositumBefore initialCubicIntermediate 3 =
      initialCubicIntermediate 0 ⊔
        initialCubicIntermediate 1 ⊔
          initialCubicIntermediate 2 := by
  rw [compositumBefore, compositum,
    show (Finset.univ.filter fun j : Fin 5 => j < 3) = {0, 1, 2} by rfl,
    ← Finset.sup_eq_iSup]
  simp [sup_assoc]

lemma compositum_before_four :
    compositumBefore initialCubicIntermediate 4 =
      initialCubicIntermediate 0 ⊔
        initialCubicIntermediate 1 ⊔
          initialCubicIntermediate 2 ⊔
            initialCubicIntermediate 3 := by
  rw [compositumBefore, compositum,
    show (Finset.univ.filter fun j : Fin 5 => j < 4) = {0, 1, 2, 3} by rfl,
    ← Finset.sup_eq_iSup]
  simp [sup_assoc]

lemma initial_compositum_five :
    Module.finrank ℚ initialCubicCompositum = 3 ^ 5 := by
  let L : Fin 5 → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    initialCubicIntermediate
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    ((((L 0) ⊔ (L 1)) ⊔ (L 2)) ⊔ (L 3)) ⊔ (L 4)
  have hM : M = initialCompositumIntermediate := by
    simpa [M, L] using intermediate_sup_compositum
  letI : FiniteDimensional ℚ ↥M := by
    rw [hM]
    infer_instance
  have h01_ld : (L 0).LinearDisjoint (L 1) := by
    simpa [L, initial_cubic_before] using
      initial_disjoint_before (1 : Fin 5)
  have h012_ld : ((L 0) ⊔ (L 1)).LinearDisjoint (L 2) := by
    simpa [L, compositum_before_two, sup_assoc] using
      initial_disjoint_before (2 : Fin 5)
  have h0123_ld :
      (((L 0) ⊔ (L 1)) ⊔ (L 2)).LinearDisjoint (L 3) := by
    simpa [L, initial_compositum_before, sup_assoc] using
      initial_disjoint_before (3 : Fin 5)
  have h01234_ld :
      ((((L 0) ⊔ (L 1)) ⊔ (L 2)) ⊔ (L 3)).LinearDisjoint (L 4) := by
    simpa [L, compositum_before_four, sup_assoc] using
      initial_disjoint_before (4 : Fin 5)
  have h01 :
      Module.finrank ℚ ↥((L 0) ⊔ (L 1)) = 3 * 3 := by
    calc
      Module.finrank ℚ ↥((L 0) ⊔ (L 1))
          = Module.finrank ℚ ↥(L 0) * Module.finrank ℚ ↥(L 1) :=
            h01_ld.finrank_sup
      _ = 3 * 3 := by
            simp [L, initial_cubic_intermediate]
  have h012 :
      Module.finrank ℚ ↥(((L 0) ⊔ (L 1)) ⊔ (L 2)) = (3 * 3) * 3 := by
    calc
      Module.finrank ℚ ↥(((L 0) ⊔ (L 1)) ⊔ (L 2))
          = Module.finrank ℚ ↥((L 0) ⊔ (L 1)) * Module.finrank ℚ ↥(L 2) :=
            h012_ld.finrank_sup
      _ = (3 * 3) * 3 := by
            rw [h01]
            simp [L, initial_cubic_intermediate]
  have h0123 :
      Module.finrank ℚ ↥((((L 0) ⊔ (L 1)) ⊔ (L 2)) ⊔ (L 3)) = ((3 * 3) * 3) * 3 := by
    calc
      Module.finrank ℚ ↥((((L 0) ⊔ (L 1)) ⊔ (L 2)) ⊔ (L 3))
          = Module.finrank ℚ ↥(((L 0) ⊔ (L 1)) ⊔ (L 2)) * Module.finrank ℚ ↥(L 3) :=
            h0123_ld.finrank_sup
      _ = ((3 * 3) * 3) * 3 := by
            rw [h012]
            simp [L, initial_cubic_intermediate]
  have h01234 :
      Module.finrank ℚ ↥(((((L 0) ⊔ (L 1)) ⊔ (L 2)) ⊔ (L 3)) ⊔ (L 4))
        = (((3 * 3) * 3) * 3) * 3 := by
    calc
      Module.finrank ℚ ↥(((((L 0) ⊔ (L 1)) ⊔ (L 2)) ⊔ (L 3)) ⊔ (L 4))
          = Module.finrank ℚ ↥((((L 0) ⊔ (L 1)) ⊔ (L 2)) ⊔ (L 3)) *
              Module.finrank ℚ ↥(L 4) :=
            h01234_ld.finrank_sup
      _ = (((3 * 3) * 3) * 3) * 3 := by
            rw [h0123]
            simp [L, initial_cubic_intermediate]
  calc
    Module.finrank ℚ initialCubicCompositum
        = Module.finrank ℚ ↥M := by
            simpa [initialCubicCompositum, L] using
              congrArg
                (fun F : IntermediateField ℚ (AlgebraicClosure ℚ) =>
                  Module.finrank ℚ ↥F)
                intermediate_sup_compositum.symm
    _ = (((3 * 3) * 3) * 3) * 3 := by simpa [M] using h01234
    _ = 3 ^ 5 := by norm_num

lemma initial_intermediate_compositum
    (i : Fin 5) :
    initialCubicIntermediate i ≤ initialCompositumIntermediate := by
  exact le_iSup initialIntermediateField (initialRamifiedOrder i)

noncomputable def initialCubicSubfield
    (i : Fin 5) : IntermediateField ℚ initialCubicCompositum :=
  (initialCubicIntermediate i).restrict
    (initial_intermediate_compositum i)

lemma initial_subfield_finrank
    (i : Fin 5) :
    Module.finrank ℚ ↥(initialCubicSubfield i) = 3 := by
  let e :
      ↥(initialCubicIntermediate i) ≃ₐ[ℚ] ↥(initialCubicSubfield i) :=
    IntermediateField.restrict_algEquiv
      (initial_intermediate_compositum i)
  rw [← e.toLinearEquiv.finrank_eq]
  exact initial_cubic_intermediate i

lemma initial_subfield_galois
    (i : Fin 5) :
    IsGalois ℚ ↥(initialCubicSubfield i) := by
  let e :
      ↥(initialCubicIntermediate i) ≃ₐ[ℚ] ↥(initialCubicSubfield i) :=
    IntermediateField.restrict_algEquiv
      (initial_intermediate_compositum i)
  letI : IsGalois ℚ ↥(initialCubicIntermediate i) :=
    initial_intermediate_galois i
  exact IsGalois.of_algEquiv e

noncomputable instance instCubicSubfield
    (i : Fin 5) : IsGalois ℚ ↥(initialCubicSubfield i) :=
  initial_subfield_galois i

lemma initial_subfield_cyclic
    (i : Fin 5) :
    IsCyclic (Gal(↥(initialCubicSubfield i)/ℚ)) := by
  let e :
      ↥(initialCubicIntermediate i) ≃ₐ[ℚ] ↥(initialCubicSubfield i) :=
    IntermediateField.restrict_algEquiv
      (initial_intermediate_compositum i)
  have hcyc : IsCyclic (Gal(↥(initialCubicIntermediate i)/ℚ)) := by
    simpa [initialCubicIntermediate, initialCubicField] using
      (initial_cubic_cyclic (initialRamifiedOrder i)).2.2
  letI : IsCyclic (Gal(↥(initialCubicIntermediate i)/ℚ)) := hcyc
  exact isCyclic_of_surjective (AlgEquiv.autCongr e) (AlgEquiv.autCongr e).surjective

lemma initial_cubic_subfield
    (i : Fin 5) :
    Nat.card (Gal(↥(initialCubicSubfield i)/ℚ)) = 3 := by
  letI : IsGalois ℚ ↥(initialCubicSubfield i) := initial_subfield_galois i
  calc
    Nat.card (Gal(↥(initialCubicSubfield i)/ℚ))
        = Module.finrank ℚ ↥(initialCubicSubfield i) :=
          IsGalois.card_aut_eq_finrank (F := ℚ) (E := ↥(initialCubicSubfield i))
    _ = 3 := initial_subfield_finrank i

lemma subfield_sup_top :
    initialCubicSubfield 0 ⊔
        initialCubicSubfield 1 ⊔
          initialCubicSubfield 2 ⊔
            initialCubicSubfield 3 ⊔
              initialCubicSubfield 4 =
      ⊤ := by
  apply (IntermediateField.lift_injective initialCompositumIntermediate)
  rw [IntermediateField.lift_top]
  repeat rw [IntermediateField.lift_sup]
  simpa [initialCubicSubfield] using
    intermediate_sup_compositum

set_option maxHeartbeats 800000 in
-- Constructing the combined restriction map across the five cubic subfields needs extra heartbeats.
set_option synthInstance.maxHeartbeats 100000 in
noncomputable def initial_restrict_pi :
    Gal(initialCubicCompositum/ℚ) →*
      (∀ i : Fin 5, Gal(↥(initialCubicSubfield i)/ℚ)) where
  toFun σ i := by
    letI : IsGalois ℚ ↥(initialCubicSubfield i) := initial_subfield_galois i
    exact AlgEquiv.restrictNormalHom (initialCubicSubfield i) σ
  map_one' := by
    funext i
    letI : IsGalois ℚ ↥(initialCubicSubfield i) := initial_subfield_galois i
    exact (AlgEquiv.restrictNormalHom (initialCubicSubfield i)).map_one
  map_mul' := by
    intro σ τ
    funext i
    letI : IsGalois ℚ ↥(initialCubicSubfield i) := initial_subfield_galois i
    exact (AlgEquiv.restrictNormalHom (initialCubicSubfield i)).map_mul σ τ

set_option maxHeartbeats 800000 in
-- Proving the restriction map is injective expands several fixed-field calculations at once.
set_option synthInstance.maxHeartbeats 100000 in
lemma compositum_restrict_pi :
    Function.Injective initial_restrict_pi := by
  refine (injective_iff_map_eq_one _).mpr ?_
  intro σ hσ
  have hfix : ∀ i : Fin 5, σ ∈ (initialCubicSubfield i).fixingSubgroup := by
    intro i
    letI : IsGalois ℚ ↥(initialCubicSubfield i) := initial_subfield_galois i
    letI : Normal ℚ ↥(initialCubicSubfield i) := IsGalois.to_normal
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hσi : AlgEquiv.restrictNormalHom (initialCubicSubfield i) σ = 1 := by
      exact congrFun hσ i
    have hσx :=
      congrArg
        (fun e : Gal(↥(initialCubicSubfield i)/ℚ) => e ⟨x, hx⟩)
        hσi
    have hσx' : σ x = x := by
      have hσx'' := congrArg Subtype.val hσx
      dsimp [AlgEquiv.restrictNormalHom, AlgEquiv.restrictNormal, AlgHom.restrictNormal'] at hσx''
      have hcomm :
          ↑((σ.restrictNormal ↥(initialCubicSubfield i)) ⟨x, hx⟩) = σ x := by
        exact
          AlgEquiv.restrictNormal_commutes
            (χ := σ) (E := initialCubicSubfield i) ⟨x, hx⟩
      exact hcomm.symm.trans hσx''
    exact hσx'
  have h34 :
      σ ∈
        (initialCubicSubfield 3 ⊔
          initialCubicSubfield 4).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfix 3, hfix 4⟩
  have h234 :
      σ ∈
        (initialCubicSubfield 2 ⊔
          (initialCubicSubfield 3 ⊔ initialCubicSubfield 4)).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfix 2, h34⟩
  have h1234 :
      σ ∈
        (initialCubicSubfield 1 ⊔
          (initialCubicSubfield 2 ⊔
            (initialCubicSubfield 3 ⊔ initialCubicSubfield 4))).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfix 1, h234⟩
  have h01234 :
      σ ∈
        (initialCubicSubfield 0 ⊔
          (initialCubicSubfield 1 ⊔
            (initialCubicSubfield 2 ⊔
              (initialCubicSubfield 3 ⊔
                initialCubicSubfield 4)))).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfix 0, h1234⟩
  rw [← Subgroup.mem_bot, ← IntermediateField.fixingSubgroup_top,
    ← subfield_sup_top]
  simpa [sup_assoc] using h01234

noncomputable def initial_subfield_z
    (i : Fin 5) :
    Gal(↥(initialCubicSubfield i)/ℚ) ≃* Multiplicative (ZMod 3) := by
  have hcyc : IsCyclic (Gal(↥(initialCubicSubfield i)/ℚ)) :=
    initial_subfield_cyclic i
  let e := (zmodCyclicMulEquiv
    (G := Gal(↥(initialCubicSubfield i)/ℚ)) hcyc).symm
  rw [initial_cubic_subfield i] at e
  exact e

/- The compositum `E` has Galois group `(ℤ / 3ℤ)^5`. -/
theorem cubic_compositum_five :
    ElementaryAbelianRank initialCubicCompositum 5 := by
  letI : IsGalois ℚ initialCubicCompositum := initial_compositum_galois
  let φ := initial_restrict_pi
  have hφ_inj : Function.Injective φ := compositum_restrict_pi
  have hfactor :
      ∀ i : Fin 5, Fintype.card (Gal(↥(initialCubicSubfield i)/ℚ)) = 3 := by
    intro i
    rw [← Nat.card_eq_fintype_card]
    exact initial_cubic_subfield i
  have hφ_card :
      Fintype.card (Gal(initialCubicCompositum/ℚ)) =
        Fintype.card (∀ i : Fin 5, Gal(↥(initialCubicSubfield i)/ℚ)) := by
    have hdom : Fintype.card (Gal(initialCubicCompositum/ℚ)) = 3 ^ 5 := by
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
      exact initial_compositum_five
    have hcod :
        Fintype.card (∀ i : Fin 5, Gal(↥(initialCubicSubfield i)/ℚ)) = 3 ^ 5 := by
      rw [Fintype.card_pi]
      simp [hfactor]
    exact hdom.trans hcod.symm
  have hφ_bij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, hφ_card⟩
  let eProd :
      Gal(initialCubicCompositum/ℚ) ≃*
        (∀ i : Fin 5, Gal(↥(initialCubicSubfield i)/ℚ)) :=
    MulEquiv.ofBijective φ hφ_bij
  let eFactors :
      (∀ i : Fin 5, Gal(↥(initialCubicSubfield i)/ℚ)) ≃*
        ElementaryAbelianGroup 5 :=
    MulEquiv.piCongrRight initial_subfield_z
  exact initial_cubic_compositum (eProd.trans eFactors)

/- By Standard lemma 2, the five fields `E_r` are linearly disjoint over `ℚ`. -/
theorem initial_linearly_disjoint :
    FamilyLinearlyDisjoint initialCubicField := by
  refine
    linearly_disjoint_compositum
      initialCubicField initialCubicCompositum
      initial_compositum ?_
  rcases cubic_compositum_five with ⟨hGal, ⟨e⟩⟩
  letI : IsGalois ℚ initialCubicCompositum := hGal
  have hdeg : Module.finrank ℚ initialCubicCompositum = 3 ^ 5 := by
    calc
      Module.finrank ℚ initialCubicCompositum = Nat.card (Gal(initialCubicCompositum/ℚ)) := by
        symm
        exact IsGalois.card_aut_eq_finrank (F := ℚ) (E := initialCubicCompositum)
      _ = Nat.card (ElementaryAbelianGroup 5) := Nat.card_congr e.toEquiv
      _ = 3 ^ 5 := by
        simp [ElementaryAbelianGroup]
  have hprod :
      ∏ r, Module.finrank ℚ (initialCubicField r) = 3 ^ 5 := by
    calc
      ∏ r, Module.finrank ℚ (initialCubicField r)
          = ∏ _r : {s // s ∈ initialRamifiedPrimes}, 3 := by
              refine Fintype.prod_congr _ _ ?_
              intro r
              simpa using (initial_cubic_cyclic r).1
      _ = 3 ^ 5 := by
        simp [ramified_primes]
  exact hdeg.trans hprod.symm

/- Since `E ⊆ Q_S^(3)`, we get a quotient `G ↠ (ℤ / 3ℤ)^5`. -/
set_option maxHeartbeats 800000 in
-- Building the ambient quotient map requires a large finite Galois bookkeeping proof.
set_option synthInstance.maxHeartbeats 100000 in
theorem surjects_rank_five :
    SurjectsElementaryRank initialGaloisGroup 5 := by
  rcases cubic_compositum_five with ⟨hGal, ⟨eGal⟩⟩
  letI : IsGalois ℚ initialCubicCompositum := hGal
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    .mk initialCompositumIntermediate
  have hPGroup : IsPGroup 3 (Gal(E/ℚ)) := by
    let hEA : IsPGroup 3 (ElementaryAbelianGroup 5) := by
      apply IsPGroup.of_card (n := 5)
      simp [ElementaryAbelianGroup]
    exact IsPGroup.of_equiv hEA eGal.symm
  have hUnramified : UnramifiedOutside E initialRamifiedPrimes := by
    simpa [E, initialCubicCompositum, UnramifiedOutside] using
      initial_compositum_outside
  let x :
      {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
        IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} :=
    ⟨E, hPGroup, hUnramified⟩
  have hle : initialCompositumIntermediate ≤ initialProIntermediate := by
    simpa [x, initialProIntermediate] using
      (le_iSup
        (fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
            IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes} =>
          E.1.toIntermediateField)
        x)
  let i : initialCubicCompositum →ₐ[ℚ] initialProExtension :=
    IntermediateField.inclusion hle
  let E' : IntermediateField ℚ initialProExtension := i.fieldRange
  let eField : initialCubicCompositum ≃ₐ[ℚ] E' := AlgEquiv.ofInjectiveField i
  letI : IsGalois ℚ E' := IsGalois.of_algEquiv eField
  refine
    ⟨eGal.toMonoidHom.comp
      ((AlgEquiv.autCongr eField).symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom E')), ?_⟩
  intro y
  obtain ⟨σ, rfl⟩ := eGal.surjective y
  let τ : Gal(↥E'/ℚ) := (AlgEquiv.autCongr eField) σ
  obtain ⟨g, hg⟩ :=
    (AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := ↥E') (E := initialProExtension)) τ
  refine ⟨g, ?_⟩
  change eGal (((AlgEquiv.autCongr eField).symm) ((AlgEquiv.restrictNormalHom ↥E') g)) = eGal σ
  rw [hg]
  simpa [τ] using congrArg eGal ((AlgEquiv.autCongr eField).symm_apply_apply σ)

/- Therefore `d_3 G ≥ 5`. -/
theorem initial_rank_nonempty :
    ({n : ℕ | 5 ≤ n ∧
        SurjectsElementaryRank initialGaloisGroup n} : Set ℕ).Nonempty := by
  refine ⟨5, ?_⟩
  exact ⟨le_rfl, surjects_rank_five⟩

theorem initial_generator_rank :
    initialGeneratorRank ∈
      ({n : ℕ |
        5 ≤ n ∧ SurjectsElementaryRank initialGaloisGroup n} : Set ℕ) := by
  exact Nat.sInf_mem initial_rank_nonempty

theorem initial_rank_five :
    5 ≤ initialGeneratorRank := by
  exact initial_generator_rank.1

end TBluepr
end Submission

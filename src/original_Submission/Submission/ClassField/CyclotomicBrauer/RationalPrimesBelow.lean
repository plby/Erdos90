import Submission.ClassField.CyclotomicBrauer.FinitePrime

/-!
# Chapter VII, Section 7, Lemma 7.3

Given a number field `K`, finitely many finite primes `S`, and `m > 0`,
Milne constructs a totally complex cyclic cyclotomic extension whose local
degrees above `S` are all divisible by `m`.

The proof first reduces from `K` to `ℚ`, replacing `m` by
`m * [K : ℚ]`.  Over `ℚ`, it constructs one cyclic prime-power cyclotomic
piece for every prime factor of that integer and takes their compositum.

The formal proof below carries out this reduction and the prime-factor
bookkeeping against the actual extension and completion-degree data proved in
`FinitePrime`.  Three arithmetic constructions not yet
packaged by the completion API are isolated separately:

* growth of local degrees in the rational prime-power cyclotomic tower;
* formation of the cyclic compositum of the coprime prime-power pieces;
* the final base-change/reduction step from `ℚ` to `K`.
-/

namespace Submission.CField.CBrauer

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.ICohomo

noncomputable section

universe u

local instance rationalPrimeDecidableEq :
    DecidableEq (finitePrime ℚ) := Classical.decEq _

/-- Contract a finite set of finite primes of `K` to the corresponding
finite primes of `ℚ`.  This is the set used in the first reduction of the
printed proof. -/
noncomputable def rationalPrimesBelow
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (finitePrime K)) :
    Finset (finitePrime ℚ) := by
  classical
  exact S.image fun P =>
    P.under (NumberField.RingOfIntegers ℚ)

/-- Every selected prime maps to the contracted rational-prime set. -/
noncomputable def rational_primes_below
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (finitePrime K)) (P : S) :
    rationalPrimesBelow K S := by
  classical
  exact ⟨P.1.under (NumberField.RingOfIntegers ℚ),
    Finset.mem_image.mpr ⟨P.1, P.2, rfl⟩⟩

/-- Contracting primes to `ℚ` preserves nonemptiness of the selected set. -/
theorem primes_below_nonempty
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (finitePrime K))
    (hS : S.Nonempty) :
    (rationalPrimesBelow K S).Nonempty := by
  obtain ⟨P, hP⟩ := hS
  exact ⟨P.under (NumberField.RingOfIntegers ℚ),
    Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩

/-- One rational prime-power component in Lemma 7.3.

The extension is cyclic cyclotomic, its local degrees at the selected
rational primes are divisible by `ell ^ a`, and its global degree is itself
a power of `ell`.  The last condition is what makes distinct components
have coprime degrees. -/
structure RationalPrimeBlock
    (S : Finset (finitePrime ℚ))
    (ell a : ℕ) where
  extension : FEData ℚ
  isCyclicCyclotomic : extension.IsCyclicCyclotomic
  hasLocalDegrees :
    extension.LocalDegreesDvd S (ell ^ a)
  degree_prime_power : ∃ r : ℕ,
    letI : Field extension.L := extension.fieldL
    letI : Algebra ℚ extension.L := extension.algebraKL
    Module.finrank ℚ extension.L = ell ^ r

/-- The trivial rational extension, used for the zero-exponent and empty-set
edge cases in the prime-power construction. -/
noncomputable def trivialRationalData :
    FEData ℚ where
  L := ℚ
  fieldL := inferInstance
  numberFieldL := inferInstance
  algebraKL := inferInstance
  finiteDimensionalKL := inferInstance
  isGaloisKL := inferInstance

/-- The trivial rational extension is cyclic cyclotomic (of conductor one). -/
theorem trivial_cyclic_cyclotomic :
    trivialRationalData.IsCyclicCyclotomic := by
  letI : Field trivialRationalData.L :=
    trivialRationalData.fieldL
  letI : NumberField trivialRationalData.L :=
    trivialRationalData.numberFieldL
  letI : Algebra ℚ trivialRationalData.L :=
    trivialRationalData.algebraKL
  letI : FiniteDimensional ℚ trivialRationalData.L :=
    trivialRationalData.finiteDimensionalKL
  letI : IsGalois ℚ trivialRationalData.L :=
    trivialRationalData.isGaloisKL
  have hcard : Nat.card Gal(trivialRationalData.L/ℚ) = 1 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Module.finrank_self ℚ
  letI : Subsingleton Gal(trivialRationalData.L/ℚ) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  letI : IsCyclic Gal(trivialRationalData.L/ℚ) :=
    inferInstance
  refine ⟨inferInstance, 1, trivialRationalData.L,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, trivial⟩
  exact IsCyclotomicExtension.singleton_one_of_algebraMap_bijective
    (A := ℚ) (B := trivialRationalData.L)
    (fun x ↦ ⟨x, rfl⟩)

/-- No local-degree growth is needed for the zero prime-power exponent. -/
noncomputable def rational_block_zero
    (S : Finset (finitePrime ℚ)) (ell : ℕ) :
    RationalPrimeBlock S ell 0 where
  extension := trivialRationalData
  isCyclicCyclotomic :=
    trivial_cyclic_cyclotomic
  hasLocalDegrees := by
    letI : Field trivialRationalData.L :=
      trivialRationalData.fieldL
    letI : NumberField trivialRationalData.L :=
      trivialRationalData.numberFieldL
    letI : Algebra ℚ trivialRationalData.L :=
      trivialRationalData.algebraKL
    letI : FiniteDimensional ℚ trivialRationalData.L :=
      trivialRationalData.finiteDimensionalKL
    letI : IsGalois ℚ trivialRationalData.L :=
      trivialRationalData.isGaloisKL
    let chosen : ∀ P : S,
        CompletionPlacesAbove
          (L := trivialRationalData.L)
          (FinitePlace.mk P.1).val := fun P ↦
      ⟨(FinitePlace.mk P.1).val, ⟨rfl⟩⟩
    refine ⟨chosen, ?_⟩
    intro P
    exact one_dvd _
  degree_prime_power := by
    refine ⟨0, ?_⟩
    exact (Module.finrank_self ℚ).trans (pow_zero ell).symm

/-- If there are no selected rational primes, the trivial extension is a
prime-power block for every exponent. -/
noncomputable def rational_block_empty
    (ell a : ℕ) :
    RationalPrimeBlock ∅ ell a where
  extension := trivialRationalData
  isCyclicCyclotomic :=
    trivial_cyclic_cyclotomic
  hasLocalDegrees := by
    dsimp only [FEData.LocalDegreesDvd]
    refine ⟨fun P ↦ ?_, ?_⟩
    · exact nomatch P.property
    · intro P
      exact nomatch P.property
  degree_prime_power := by
    refine ⟨0, ?_⟩
    exact (Module.finrank_self ℚ).trans (pow_zero ell).symm

/-- Numerical cancellation in the rational-to-`K` base-change step of
Lemma VII.7.3.  This form is useful when the local base degree is known to
divide a chosen global multiplier. -/
theorem dvd_base_change
    (m globalBaseDegree localBaseDegree rationalLocalDegree
      resultLocalDegree : ℕ)
    (hlocalPositive : 0 < localBaseDegree)
    (hlocalGlobal : localBaseDegree ∣ globalBaseDegree)
    (hglobalRational : m * globalBaseDegree ∣ rationalLocalDegree)
    (hintoCompositum : rationalLocalDegree ∣
      localBaseDegree * resultLocalDegree) :
    m ∣ resultLocalDegree := by
  obtain ⟨c, rfl⟩ := hlocalGlobal
  obtain ⟨a, rfl⟩ := hglobalRational
  obtain ⟨b, hb⟩ := hintoCompositum
  have hcancel : localBaseDegree * resultLocalDegree =
      localBaseDegree * (m * (c * a * b)) := by
    calc
      localBaseDegree * resultLocalDegree =
          (m * (localBaseDegree * c) * a) * b := hb
      _ = localBaseDegree * (m * (c * a * b)) := by ring
  have hresult : resultLocalDegree = m * (c * a * b) :=
    Nat.eq_of_mul_eq_mul_left hlocalPositive hcancel
  exact ⟨c * a * b, hresult⟩

/-- Corrected numerical cancellation using a factorial multiplier.  A local
completion degree need not divide the global degree for a non-Galois number
field (the summands in the local degree formula only add to the global
degree).  It is, however, positive and at most the global degree, hence
divides its factorial.  This is the multiplier needed for the unrestricted
rational-to-`K` reduction. -/
theorem dvd_change_factorial
    (m globalBaseDegree localBaseDegree rationalLocalDegree
      resultLocalDegree : ℕ)
    (hlocalPositive : 0 < localBaseDegree)
    (hlocalGlobal : localBaseDegree ≤ globalBaseDegree)
    (hglobalRational : m * globalBaseDegree.factorial ∣ rationalLocalDegree)
    (hintoCompositum : rationalLocalDegree ∣
      localBaseDegree * resultLocalDegree) :
    m ∣ resultLocalDegree := by
  exact dvd_base_change
    m globalBaseDegree.factorial localBaseDegree rationalLocalDegree
      resultLocalDegree hlocalPositive
      (Nat.dvd_factorial hlocalPositive hlocalGlobal)
      hglobalRational hintoCompositum

/-- The prime-power local-degree growth step in the rational cyclotomic
tower.  The odd- and two-primary fixed fields with their exact global
degrees are constructed in the companion `Lemma73*PrimePowerField` modules;
this bridge retains growth of their completed local degrees. -/
def RationalGrowthBridge : Prop :=
  ∀ (S : Finset (finitePrime ℚ))
    (ell a : ℕ),
    ell.Prime →
      Nonempty (RationalPrimeBlock S ell a)

/-- The genuine arithmetic core of prime-power growth: the exponent is
positive and at least one rational prime is prescribed.  The omitted edge
cases are discharged by the trivial blocks above. -/
def GrowthCoreBridge : Prop :=
  ∀ (S : Finset (finitePrime ℚ))
    (ell a : ℕ),
    S.Nonempty → 0 < a → ell.Prime →
      Nonempty (RationalPrimeBlock S ell a)

/-- Odd-primary part of the genuine growth core.  The ambient cyclic fixed
field and its global degree are constructed in
`Lemma73OddPrimePowerField`; this bridge retains the local-degree growth and
completion-tower work. -/
def OddGrowthCore : Prop :=
  ∀ (S : Finset (finitePrime ℚ))
    (ell a : ℕ),
    S.Nonempty → 0 < a → ell.Prime → ell ≠ 2 →
      Nonempty (RationalPrimeBlock S ell a)

/-- Exceptional two-primary part of the genuine growth core.  It is kept
separate because `(ZMod (2 ^ r))ˣ` is not cyclic for large `r`; one must
first quotient by the order-two factor before applying the local argument. -/
def TwoGrowthCore : Prop :=
  ∀ (S : Finset (finitePrime ℚ)) (a : ℕ),
    S.Nonempty → 0 < a →
      Nonempty (RationalPrimeBlock S 2 a)

/-- Strengthened two-primary growth retaining total complexity of the
diagonal fixed field.  This is the version used by the final compositum;
forgetting the subtype proof recovers the ordinary two-primary block. -/
def ComplexGrowthCore : Prop :=
  ∀ (S : Finset (finitePrime ℚ)) (a : ℕ),
    S.Nonempty → 0 < a →
      Nonempty {block : RationalPrimeBlock S 2 a //
        block.extension.IsTotallyComplex}

/-- Pointwise conductor growth can be made uniform over a finite set.  This
is the finite-set bookkeeping used after proving that every individual
rational prime eventually has the required local degree. -/
theorem exists_uniform_exponent
    {ι : Type*} [Finite ι]
    (P : ι → ℕ → Prop)
    (hmono : ∀ i r s, r ≤ s → P i r → P i s)
    (hexists : ∀ i, ∃ r, P i r) :
    ∃ R, ∀ i, P i R := by
  letI := Fintype.ofFinite ι
  choose r hr using hexists
  refine ⟨∑ i, r i, ?_⟩
  intro i
  apply hmono i (r i) (∑ j, r j) ?_ (hr i)
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)

/-- The odd-primary and two-primary constructions together give the full
positive-exponent, nonempty-prime growth core. -/
theorem growth_core_odd
    (hodd : OddGrowthCore)
    (htwo : TwoGrowthCore) :
    GrowthCoreBridge := by
  intro S ell a hS ha hell
  by_cases hell2 : ell = 2
  · subst ell
    exact htwo S a hS ha
  · exact hodd S ell a hS ha hell hell2

/-- Positive nonempty prime-power growth supplies the original growth bridge;
zero exponents and empty prime sets use the trivial rational extension. -/
theorem growth_bridge_core
    (hcore : GrowthCoreBridge) :
    RationalGrowthBridge := by
  intro S ell a hell
  by_cases ha : a = 0
  · subst a
    exact ⟨rational_block_zero S ell⟩
  by_cases hS : S.Nonempty
  · exact hcore S ell a hS (Nat.pos_of_ne_zero ha) hell
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact ⟨rational_block_empty ell a⟩

/-- Combine the rational prime-power blocks indexed by all prime divisors
of `N`.  Their global degrees are powers of distinct primes, so their
compositum is cyclic.  The construction also adds a complex cyclotomic
factor when necessary and preserves all local-degree divisibilities.

This bridge assumes the individual prime-power blocks; it is therefore
strictly narrower than Lemma 7.3 itself. -/
def RationalCompositumBridge : Prop :=
  ∀ (S : Finset (finitePrime ℚ)) (N : ℕ),
    N ≠ 0 →
    (∀ ell : N.primeFactors,
      RationalPrimeBlock
        S ell.1 (N.factorization ell.1)) →
    ∃ data : FEData ℚ,
      data.IsCyclicCyclotomic ∧
        data.IsTotallyComplex ∧
        data.LocalDegreesDvd S N

/-- The reduction from `ℚ` back to `K` used at the start of the source
proof.  Divisibility by `m * [K : ℚ]!` at the contracted rational primes
produces divisibility by `m` after forming the compositum with `K`.

The factorial is essential for arbitrary (not necessarily Galois) `K/ℚ`:
the local degree `[K_v : ℚ_p]` is at most `[K : ℚ]`, but need not divide it.

The conclusion concerns only extension and local-degree data; it contains no
Brauer class or Proposition 7.2 splitting assertion. -/
def ChangeRationalsBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (finitePrime K)) (m : ℕ),
    0 < m →
    ∀ data : FEData ℚ,
      data.IsCyclicCyclotomic →
      data.IsTotallyComplex →
      data.LocalDegreesDvd
        (rationalPrimesBelow K S)
        (m * (Module.finrank ℚ K).factorial) →
      ∃ result : FEData K,
        result.IsCyclicCyclotomic ∧
          result.IsTotallyComplex ∧
          result.LocalDegreesDvd S m

/-- The standalone Lemma 7.3 statement is exactly the construction input
used by Proposition 7.2. -/
theorem below_statement_bridge :
    (∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (finitePrime K)) (m : ℕ),
          0 < m →
            ∃ data : FEData K,
              data.IsCyclicCyclotomic ∧
                data.IsTotallyComplex ∧
                data.LocalDegreesDvd S m
    ) ↔ FinitePrime.{u} :=
  Iff.rfl

/-- Lemma 7.3 from rational prime-power local-degree growth, the coprime
cyclic-compositum construction, and the base-change reduction to `K`.

The selection of one block for each prime divisor and the positivity of
`m * [K : ℚ]` are proved here. -/
theorem below_arithmetic_bridges
    (hgrowth : RationalGrowthBridge)
    (hcompositum : RationalCompositumBridge)
    (hbaseChange : ChangeRationalsBridge.{u}) :
    (
      ∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (finitePrime K)) (m : ℕ),
          0 < m →
            ∃ data : FEData K,
              data.IsCyclicCyclotomic ∧
                data.IsTotallyComplex ∧
                data.LocalDegreesDvd S m) := by
  intro K _ _ S m hm
  let rationalPrimes := rationalPrimesBelow K S
  let N := m * (Module.finrank ℚ K).factorial
  have hN : N ≠ 0 := mul_ne_zero hm.ne' (Nat.factorial_ne_zero _)
  let blocks : ∀ ell : N.primeFactors,
      RationalPrimeBlock rationalPrimes ell.1
        (N.factorization ell.1) := fun ell =>
    Classical.choice
      (hgrowth rationalPrimes ell.1 (N.factorization ell.1)
        (Nat.prime_of_mem_primeFactors ell.2))
  obtain ⟨rationalExtension, hcyclic, hcomplex, hdegrees⟩ :=
    hcompositum rationalPrimes N hN blocks
  exact hbaseChange K S m hm rationalExtension
    hcyclic hcomplex hdegrees

/-- Lemma 7.3 in the exact bridge form consumed by Proposition 7.2. -/
theorem prime_rational_bridges
    (hgrowth : RationalGrowthBridge)
    (hcompositum : RationalCompositumBridge)
    (hbaseChange : ChangeRationalsBridge.{u}) :
    FinitePrime.{u} :=
  below_statement_bridge.mp
    (below_arithmetic_bridges
      hgrowth hcompositum hbaseChange)

/-- Sharp remaining boundary for Lemma VII.7.3: only positive-exponent
growth at a nonempty set of rational primes, the cyclic compositum, and the
field-theoretic base-change construction remain. -/
theorem core_rational_bridges
    (hgrowth : GrowthCoreBridge)
    (hcompositum : RationalCompositumBridge)
    (hbaseChange : ChangeRationalsBridge.{u}) :
    FinitePrime.{u} :=
  prime_rational_bridges
    (growth_bridge_core hgrowth)
    hcompositum hbaseChange

end

end Submission.CField.CBrauer

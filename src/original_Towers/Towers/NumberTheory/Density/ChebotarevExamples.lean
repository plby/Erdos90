import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Towers.NumberTheory.Galois.CyclotomicQuadraticFrobenius
import Towers.NumberTheory.Density.SplittingPrimeDensity

/-!
# Milne, Chapter 8, Examples 8.34 and 8.35

This file records the density consequences of Chebotarev for cyclotomic and
quadratic extensions.  A cyclotomic Frobenius class is indexed by a unit
modulo `n`, so every such class has density `1 / φ(n)`.  Mathlib's proof of
Dirichlet's theorem supplies the unconditional infinitude of primes in every
coprime arithmetic progression.

For a quadratic Galois extension, the identity Frobenius class is precisely
the completely split case and has density one half.
-/

namespace Towers.NumberTheory.Milne

open IsDedekindDomain NumberField
open scoped NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Milne, Example 8.34: under Chebotarev, each Frobenius class indexed by a
unit modulo `n` has density `1 / φ(n)`.  Together with the cyclotomic
Frobenius calculation, the class indexed by `a` is the congruence class `a`
modulo `n`. -/
theorem cyclotomic_density_chebotarev
    (n : ℕ) [NeZero n]
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses (ZMod n)ˣ)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (a : (ZMod n)ˣ) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk a))
      (1 / Nat.totient n) := by
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using
    (abelian_density_chebotarev K hcheb a)

/-- Every unit-indexed cyclotomic Frobenius class is infinite once
Chebotarev's density assertion is available. -/
theorem cyclotomic_infinite_chebotarev
    (n : ℕ) [NeZero n]
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses (ZMod n)ˣ)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (a : (ZMod n)ˣ) :
    (primesFrobeniusClass K frobeniusClass
      (ConjClasses.mk a)).Infinite := by
  apply Set.Infinite.prime_ideal_densi K
    (cyclotomic_density_chebotarev K n hcheb a)
  exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos n)))

/-- Milne's unconditional infinitude conclusion in Example 8.34: every
arithmetic progression `a, a + n, a + 2n, ...` with `gcd(a,n)=1` contains
infinitely many primes. -/
theorem coprime_arithmetic_progression
    {n a : ℕ} (hn : n ≠ 0) (ha : a.Coprime n) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD n]} :=
  Nat.infinite_setOf_prime_and_modEq hn ha

/-- The cyclotomic Frobenius-class map on the finite primes of `ℚ`, written
directly as `p ↦ [p]` in `(ZMod n)ˣ`.  The finite set of primes dividing the
chosen level is excluded; for a nonminimal level these need not all ramify. -/
noncomputable def rationalCyclotomicFrobenius
    (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 ℚ)) :
    Option (ConjClasses (ZMod n)ˣ) := by
  let p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
  exact if hp : p.Coprime n then
    some (ConjClasses.mk (ZMod.unitOfCoprime p hp))
  else none

private abbrev rationalPrimeFinite
    (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)

private def rationalPrimeIdeal
    (v : HeightOneSpectrum (𝓞 ℚ)) : Ideal ℤ :=
  Ideal.span {(rationalPrimeFinite v : ℤ)}

private instance rational_prime_ideal
    (v : HeightOneSpectrum (𝓞 ℚ)) : (rationalPrimeIdeal v).IsPrime :=
  Ideal.isPrime_of_prime
    (Ideal.prime_span_singleton_iff.mpr
      (Nat.prime_iff_prime_int.mp
        (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes).2))

/-- A chosen prime of a number field above the rational prime represented by
`v`.  Only its Frobenius conjugacy class will be used. -/
noncomputable def rationalCyclotomicAbove
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (rationalPrimeIdeal v).primesOver (𝓞 K) :=
  Classical.choice (Ideal.nonempty_primesOver (rationalPrimeIdeal v))

/-- The actual cyclotomic arithmetic-Frobenius class, transported through
`Gal(Q(zeta_n)/Q) ≃ (ZMod n)ˣ`.  The finitely many primes not coprime to the
chosen level are left undefined. -/
noncomputable def actualFrobeniusClass
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Option (ConjClasses (ZMod n)ˣ) := by
  let p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v
  if hp : p.1.Coprime n then
    let P := rationalCyclotomicAbove K v
    letI : Fact p.1.Prime := ⟨p.2⟩
    letI : P.1.IsPrime := P.2.1
    letI : P.1.LiesOver (rationalPrimeIdeal v) := P.2.2
    exact some (ConjClasses.mk
      (IsCyclotomicExtension.Rat.galEquivZMod n K
        (cyclotomicArithFrob (n := n) P.1)))
  else exact none

/-- Away from the finite level-divisor set, actual cyclotomic arithmetic
Frobenius is exactly the unit class `[p]`. -/
theorem actual_frobenius_class
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    actualFrobeniusClass K n v =
      rationalCyclotomicFrobenius n v := by
  let p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact p.1.Prime := ⟨p.2⟩
  by_cases hp : p.1.Coprime n
  · let P := rationalCyclotomicAbove K v
    letI : P.1.IsPrime := P.2.1
    letI : P.1.LiesOver (Ideal.span {(p.1 : ℤ)}) := P.2.2
    have hfrob := gal_arith_frob
      (K := K) (p := p.1) (n := n) P.1 hp
    simp only [actualFrobeniusClass,
      rationalCyclotomicFrobenius]
    rw [hfrob]
  · simp [actualFrobeniusClass,
      rationalCyclotomicFrobenius, hp, p]

/-- The finite primes of `ℚ` whose underlying rational prime lies in the
congruence class `k` modulo `n`. -/
def rationalCongruenceClass (n k : ℕ) :
    Set (HeightOneSpectrum (𝓞 ℚ)) :=
  {v | ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) ≡ k [MOD n]}

/-- The fiber of the explicit cyclotomic Frobenius-class map at `[k]` is
literally the rational-prime congruence class `k mod n`. -/
theorem primes_frobenius_congruence
    (n k : ℕ) [NeZero n] (hk : k.Coprime n) :
    primesFrobeniusClass ℚ (rationalCyclotomicFrobenius n)
        (ConjClasses.mk (ZMod.unitOfCoprime k hk)) =
      rationalCongruenceClass n k := by
  ext v
  let p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
  by_cases hp : p.Coprime n
  · change
      (if hp' : p.Coprime n then
          some (ConjClasses.mk (ZMod.unitOfCoprime p hp'))
        else none) = some (ConjClasses.mk (ZMod.unitOfCoprime k hk)) ↔
          p ≡ k [MOD n]
    rw [dif_pos hp, Option.some.injEq,
      ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]
    rw [Units.ext_iff, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime,
      ZMod.natCast_eq_natCast_iff]
  · have hnotmod : ¬p ≡ k [MOD n] := by
      intro hmod
      apply hp
      rw [← ZMod.isUnit_iff_coprime]
      have hcast : (p : ZMod n) = (k : ZMod n) :=
        (ZMod.natCast_eq_natCast_iff p k n).2 hmod
      rw [hcast]
      exact (ZMod.unitOfCoprime k hk).isUnit
    change
      (if hp' : p.Coprime n then
          some (ConjClasses.mk (ZMod.unitOfCoprime p hp'))
        else none) = some (ConjClasses.mk (ZMod.unitOfCoprime k hk)) ↔
          p ≡ k [MOD n]
    simp [hp, hnotmod]

/-- Milne, Example 8.34 in its literal arithmetic-progression form: assuming
Chebotarev for the cyclotomic Frobenius map, the rational primes congruent to
`k mod n` have density `1 / φ(n)` among all rational primes. -/
theorem rational_congruence_chebotarev
    (n k : ℕ) [NeZero n] (hk : k.Coprime n)
    (hcheb : ChebotarevDensityProperty ℚ
      (rationalCyclotomicFrobenius n)) :
    PNDensit ℚ (rationalCongruenceClass n k)
      (1 / Nat.totient n) := by
  rw [← primes_frobenius_congruence n k hk]
  exact cyclotomic_density_chebotarev ℚ n hcheb
    (ZMod.unitOfCoprime k hk)

/-- Milne, Example 8.34 for an actual cyclotomic extension: Chebotarev for
the transported arithmetic-Frobenius map gives density `1 / φ(n)` to the
literal congruence class `p ≡ k mod n`. -/
theorem congruence_density_chebotarev
    (n k : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    (hk : k.Coprime n)
    (hcheb : ChebotarevDensityProperty ℚ
      (actualFrobeniusClass K n)) :
    PNDensit ℚ (rationalCongruenceClass n k)
      (1 / Nat.totient n) := by
  have hmaps : actualFrobeniusClass K n =
      rationalCyclotomicFrobenius n := by
    funext v
    exact actual_frobenius_class K n v
  rw [hmaps] at hcheb
  exact rational_congruence_chebotarev n k hk hcheb

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A finite prime is inert in a quadratic extension when there is one prime
above it, with ramification index one and inertia degree two. -/
def InertAt (p : HeightOneSpectrum (𝓞 K)) : Prop :=
  (Ideal.primesOver p.asIdeal (𝓞 L)).ncard = 1 ∧
    ∀ P ∈ Ideal.primesOver p.asIdeal (𝓞 L),
      Ideal.ramificationIdx p.asIdeal P = 1 ∧
        Ideal.inertiaDeg p.asIdeal P = 2

/-- The finite primes inert in `L/K`. -/
def inertPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | InertAt K L p}

/-- In a quadratic Galois extension, the inert primes are exactly the
unramified primes that do not split completely. -/
theorem inert_compl_diff
    (hdegree : Module.finrank K L = 2) :
    inertPrimes K L = (splittingPrimes K L)ᶜ \ ramifiedPrimes K L := by
  classical
  ext p
  simp only [inertPrimes, Set.mem_setOf_eq, Set.mem_diff, Set.mem_compl_iff,
    splitting_primes]
  constructor
  · intro hinert
    constructor
    · intro hsplit
      have hcount := hsplit.1
      rw [hdegree] at hcount
      have : (1 : ℕ) = 2 := hinert.1.symm.trans hcount
      omega
    · intro hram
      rcases hram with ⟨P, hPprime, hP0, hPunder, hPe⟩
      have hPmem : P ∈ Ideal.primesOver p.asIdeal (𝓞 L) :=
        ⟨hPprime, ⟨hPunder.symm⟩⟩
      exact hPe (hinert.2 P hPmem).1
  · rintro ⟨hnotsplit, hnotram⟩
    let P : Ideal (𝓞 L) := (arithmeticFrobeniusAbove K L p).1
    have hPmem : P ∈ Ideal.primesOver p.asIdeal (𝓞 L) :=
      (arithmeticFrobeniusAbove K L p).2
    letI : P.IsPrime := hPmem.1
    letI : P.LiesOver p.asIdeal := hPmem.2
    have hPunder : P.under (𝓞 K) = p.asIdeal :=
      (Ideal.LiesOver.over (p := p.asIdeal) (P := P)).symm
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver p.ne_bot hPmem
    have heP : Ideal.ramificationIdx p.asIdeal P = 1 := by
      by_contra heP
      exact hnotram ⟨P, hPmem.1, hP0, hPunder, heP⟩
    letI := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    letI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
    have hmain :
        (Ideal.primesOver p.asIdeal (𝓞 L)).ncard *
            Ideal.inertiaDeg p.asIdeal P = 2 := by
      have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
        (p := p.asIdeal) (B := 𝓞 L) (G := Gal(L/K)) p.ne_bot
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx
          (p := p.asIdeal) (P := P) (B := 𝓞 L) (G := Gal(L/K)),
        Ideal.inertiaDegIn_eq_inertiaDeg
          (p := p.asIdeal) (P := P) (B := 𝓞 L) (G := Gal(L/K)),
        heP, one_mul, IsGalois.card_aut_eq_finrank, hdegree] at h
      exact h
    have hcount : (Ideal.primesOver p.asIdeal (𝓞 L)).ncard = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp
          ⟨Ideal.inertiaDeg p.asIdeal P, hmain.symm⟩ with hcount | hcount
      · exact hcount
      · have hfP : Ideal.inertiaDeg p.asIdeal P = 1 := by
          rw [hcount] at hmain
          omega
        exact (hnotsplit
          (splits_completely_prime K L p P hPmem heP hfP)).elim
    have hfP : Ideal.inertiaDeg p.asIdeal P = 2 := by
      rw [hcount, one_mul] at hmain
      exact hmain
    refine ⟨hcount, ?_⟩
    intro Q hQ
    letI : Q.IsPrime := hQ.1
    letI : Q.LiesOver p.asIdeal := hQ.2
    have hQunder : Q.under (𝓞 K) = p.asIdeal :=
      (Ideal.LiesOver.over (p := p.asIdeal) (P := Q)).symm
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ
    constructor
    · by_contra heQ
      exact hnotram ⟨Q, hQ.1, hQ0, hQunder, heQ⟩
    · calc
        Ideal.inertiaDeg p.asIdeal Q = Ideal.inertiaDeg p.asIdeal P :=
          Ideal.inertiaDeg_eq_of_isGaloisGroup p.asIdeal Q P Gal(L/K)
        _ = 2 := hfP

/-- Milne, Example 8.35, split half: in a quadratic Galois extension, the
completely split primes have density one half. -/
theorem quadratic_splitting_chebotarev
    (hdegree : Module.finrank K L = 2)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K (splittingPrimes K L) (1 / 2) := by
  simpa only [hdegree] using splitting_density_chebotarev K L hcheb

/-- Milne, Example 8.35, inert half: in a quadratic Galois extension, the
primes that remain prime have density one half. -/
theorem inert_density_chebotarev
    (hdegree : Module.finrank K L = 2)
    (hcheb : ChebotarevDensityTheorem K L) :
    PNDensit K (inertPrimes K L) (1 / 2) := by
  have hsplit := splitting_density_chebotarev K L hcheb
  rw [hdegree] at hsplit
  have hcompl := hsplit.compl K
  have hinert := hcompl.diff_of_finite K (finite_ramifiedPrimes K L)
  rw [inert_compl_diff K L hdegree]
  convert hinert using 1 ; norm_num

end

end Towers.NumberTheory.Milne

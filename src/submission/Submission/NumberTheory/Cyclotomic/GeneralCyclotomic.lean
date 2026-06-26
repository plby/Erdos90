import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Milne, Algebraic Number Theory, Theorem 6.4

The basic degree, Galois, integral-basis, and ramification results for cyclotomic fields.
-/

namespace Submission.NumberTheory.Milne

open NumberField
open scoped NumberField

/-- **Milne, Theorem 6.4(a).** The degree of the `n`th cyclotomic field is `φ(n)`. -/
theorem cyclotomic_finrank_totient (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    Module.finrank ℚ K = n.totient :=
  IsCyclotomicExtension.Rat.finrank n K

/-- The Galois-group form of Milne's basic cyclotomic theorem. -/
noncomputable def cyclotomicGalZ (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    Gal(K/ℚ) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod n K

/-- **Milne, Theorem 6.4(b).** Adjoining a primitive root over `ℤ` gives the full
ring of integers of the cyclotomic field. -/
noncomputable def cyclotomicAdjoinIntegers
    {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {zeta : K} (hzeta : IsPrimitiveRoot zeta n) :
    Algebra.adjoin ℤ ({zeta} : Set K) ≃ₐ[ℤ] NumberField.RingOfIntegers K :=
  hzeta.adjoinEquivRingOfIntegers

/-- The integral power basis `1, ζ, ..., ζ^(φ(n)-1)` from Theorem 6.4(b). -/
noncomputable def cyclotomicIntegralBasis
    {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {zeta : K} (hzeta : IsPrimitiveRoot zeta n) :
    PowerBasis ℤ (NumberField.RingOfIntegers K) :=
  hzeta.integralPowerBasis

@[simp]
theorem cyclotomic_basis_dim
    {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {zeta : K} (hzeta : IsPrimitiveRoot zeta n) :
    (cyclotomicIntegralBasis hzeta).dim = n.totient :=
  hzeta.integralPowerBasis_dim

/-- **Milne, Theorem 6.4(c).** A prime not dividing the conductor is unramified,
expressed by ramification index one. -/
theorem cyclotomic_ramification_dvd
    {n p : ℕ} [Fact p.Prime] [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (hp : ¬p ∣ n) :
    (Ideal.span {(p : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers K) = 1 :=
  IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hp

/-- **Milne, Theorem 6.4(c), ramification-index form.** If
`n = p^(k+1) m` with `p ∤ m`, then the ramification index of `p` is
`p^k (p-1) = φ(p^(k+1))`. -/
theorem cyclotomic_ramification_idx
    {n p k m : ℕ} [Fact p.Prime] [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (hn : n = p ^ (k + 1) * m) (hm : ¬p ∣ m) :
    (Ideal.span {(p : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers K) =
      p ^ k * (p - 1) :=
  IsCyclotomicExtension.Rat.ramificationIdxIn_eq n K hn hm

open scoped Classical in
/-- **Milne, Theorem 6.4(c), ideal-factorization form.** If
`n = p^(k+1) m` with `p ∤ m`, then `(p)` is the product of the distinct
primes above `p`, each raised to `φ(p^(k+1)) = p^k (p-1)`. -/
theorem cyclotomic_primes_pow
    {n p k m : ℕ} [Fact p.Prime] [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (hn : n = p ^ (k + 1) * m) (hm : ¬p ∣ m) :
    Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K))
        (Ideal.span {(p : ℤ)}) =
      ∏ P ∈ (Ideal.span {(p : ℤ)}).primesOver
          (NumberField.RingOfIntegers K), P ^ (p ^ k * (p - 1)) := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  letI : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hq : q ≠ 0 := by
    simp [q, (Fact.out : p.Prime).ne_zero]
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hq]
  apply Finset.prod_congr rfl
  intro P hP
  have hP' : P ∈ q.primesOver (NumberField.RingOfIntegers K) := by
    simpa [q] using hP
  letI : P.IsPrime := hP'.1
  letI : P.LiesOver q := hP'.2
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq n K P hn hm]

end Submission.NumberTheory.Milne

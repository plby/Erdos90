import Towers.ClassField.ReciprocityExistence.AwayCancellation
import Towers.ClassField.ReciprocityExistence.PadicLocalMap

/-!
# The literal conductor-prime factors in Example VII.8.2

The ramified local map constructed in `Example82PadicLocalMap` has source
`Q_p^x`, rather than a separate unit/uniformizer coordinate group.  Here we
evaluate that actual map on the three rational generators used in Example
VII.8.2: `-1`, the conductor prime, and a prime away from the conductor.
-/

namespace Towers.CField.RExist

open Polynomial
open Towers.CField.LTate

noncomputable section

/-- A degree-one finite extension has no nontrivial automorphisms. -/
private theorem galois_subsingleton_finrank
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hfinrank : Module.finrank K L = 1) :
    Subsingleton Gal(L/K) := by
  constructor
  intro σ τ
  ext x
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hfinrank
      (one_ne_zero : (1 : L) ≠ 0) x
  rw [← hc]
  change σ (c • (1 : L)) = τ (c • (1 : L))
  simp [Algebra.smul_def]

/-- The conductor `p^0 = 1` gives the trivial cyclotomic extension. -/
theorem cyclotomic_galois_subsingleton
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsCyclotomicExtension {p ^ 0} ℚ L] :
    Subsingleton Gal(L/ℚ) := by
  letI : IsCyclotomicExtension {1} ℚ L := by
    simpa using (inferInstance : IsCyclotomicExtension {p ^ 0} ℚ L)
  have hirr : Irreducible (Polynomial.cyclotomic 1 ℚ) := by
    simpa [Polynomial.cyclotomic_one] using
      (Polynomial.irreducible_X_sub_C (1 : ℚ))
  have hfinrank : Module.finrank ℚ L = 1 := by
    simpa using (IsCyclotomicExtension.finrank L hirr)
  exact galois_subsingleton_finrank hfinrank

/-- Thus at the degenerate prime-power level `r = 0`, every candidate local
map agrees with the explicit one.  The arithmetic normalization issue begins
only at positive conductor exponent. -/
theorem padic_cyclotomic_artin
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsCyclotomicExtension {p ^ 0} ℚ L]
    (f : ℚ_[p]ˣ →* Gal(L/ℚ)) :
    f = padicCyclotomicArtin p 0 L := by
  letI : Subsingleton Gal(L/ℚ) :=
    cyclotomic_galois_subsingleton p L
  apply MonoidHom.ext
  intro x
  exact @Subsingleton.elim Gal(L/ℚ) inferInstance _ _

/-- The conductor `2 = 2^1`, excluded from the source's nontrivial
calculation, likewise gives the trivial cyclotomic extension. -/
theorem two_cyclotomic_subsingleton
    (L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsCyclotomicExtension {2} ℚ L] :
    Subsingleton Gal(L/ℚ) := by
  have hfinrank : Module.finrank ℚ L = 1 := by
    simpa using (IsCyclotomicExtension.finrank L
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 2)))
  exact galois_subsingleton_finrank hfinrank

/-- Consequently every `Q_2^x`-valued candidate agrees with the explicit
local map at conductor `2`. -/
theorem local_cyclotomic_artin
    (L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsCyclotomicExtension {2} ℚ L]
    (f : ℚ_[2]ˣ →* Gal(L/ℚ)) :
    f = padicCyclotomicArtin 2 1 L := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclotomicExtension {2 ^ 1} ℚ L := by simpa
  letI : Subsingleton Gal(L/ℚ) := two_cyclotomic_subsingleton L
  apply MonoidHom.ext
  intro x
  exact @Subsingleton.elim Gal(L/ℚ) inferInstance _ _

/-- A `p`-adic unit, regarded as an element of `Q_p^x` through the valuation
ring identification used by the local unit--uniformizer decomposition. -/
noncomputable def padicIntUnit
    (p : ℕ) [Fact p.Prime] : ℤ_[p]ˣ →* ℚ_[p]ˣ :=
  ((Padic.mulValuation (p := p)).valuationSubring.unitGroup.subtype).comp
      (padicValuationInt p).symm.toMonoidHom

@[simp]
theorem padic_int_coe
    (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ((padicIntUnit p u : ℚ_[p]ˣ) : ℚ_[p]) = (u : ℤ_[p]) :=
  rfl

/-- A nonzero rational natural number, regarded as a unit of `Q_p`. -/
noncomputable def padicNatUnit
    (p q : ℕ) [Fact p.Prime] (hq : q ≠ 0) : ℚ_[p]ˣ :=
  Units.mk0 (q : ℚ_[p]) (by exact_mod_cast hq)

@[simp]
theorem padic_nat_coe
    (p q : ℕ) [Fact p.Prime] (hq : q ≠ 0) :
    ((padicNatUnit p q hq : ℚ_[p]ˣ) : ℚ_[p]) = q :=
  rfl

/-- The integral-unit lift of an away prime is literally that rational
prime inside `Q_p^x`. -/
theorem padic_int_away
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) :
    let hcop : p.Coprime q :=
      (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
    padicIntUnit p (awayPadicUnit p q hcop) =
      padicNatUnit p q hq.ne_zero := by
  let hcop : p.Coprime q :=
    (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
  dsimp only
  apply Units.ext
  rw [padic_int_coe, away_padic_val,
    padic_nat_coe]
  norm_num

/-- The literal `Q_p^x` form of the conductor-prime formula
`phi_p(u p^m) = [u^-1]`. -/
theorem padic_cyclotomic_zpow
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : ℤ_[p]ˣ) (m : ℤ) :
    padicCyclotomicArtin p r L
        (padicIntUnit p u *
          (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) ^ m) =
      padicCyclotomicAction p r
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        (L := L) u := by
  exact padic_artin_zpow
    p r L u m

/-- The actual ramified local map sends `-1` to complex conjugation. -/
theorem padic_artin_neg
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    padicCyclotomicArtin p r L (-1 : ℚ_[p]ˣ) =
      cyclotomicNegAutomorphism (p ^ r) L := by
  have hunit : padicIntUnit p (-1 : ℤ_[p]ˣ) =
      (-1 : ℚ_[p]ˣ) := by
    apply Units.ext
    simp
  rw [← hunit]
  have h := padic_cyclotomic_zpow
    p r L (-1 : ℤ_[p]ˣ) 0
  simpa using h.trans (padic_action_neg p r L)

/-- At the conductor prime, the literal local image of the rational prime
`q != p` is the inverse of arithmetic Frobenius at `q`. -/
theorem padic_artin_away
    (p r q : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (hq : q.Prime) (hqp : q ≠ p) :
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    let hcop : p.Coprime q :=
      (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
    padicCyclotomicArtin p r L
        (padicIntUnit p (awayPadicUnit p q hcop)) =
      (cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        hcopPow (L := L))⁻¹ := by
  let hcopPow : q.Coprime (p ^ r) :=
    ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
  let hcop : p.Coprime q :=
    (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
  dsimp only
  have h := padic_cyclotomic_zpow
    p r L (awayPadicUnit p q hcop) 0
  simpa using h.trans
    (padic_action_away p r q L hq hqp)

/-- The preceding away-prime formula, written on the literal rational
number `q` in `Q_p^x`. -/
theorem padic_artin_unit
    (p r q : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (hq : q.Prime) (hqp : q ≠ p) :
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    padicCyclotomicArtin p r L
        (padicNatUnit p q hq.ne_zero) =
      (cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        hcopPow (L := L))⁻¹ := by
  let hcopPow : q.Coprime (p ^ r) :=
    ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
  let hcop : p.Coprime q :=
    (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
  dsimp only
  rw [← padic_int_away p q hq hqp]
  exact padic_artin_away p r q L hq hqp

/-- The actual ramified local map kills the conductor prime itself. -/
theorem cyclotomic_artin_conductor
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    padicCyclotomicArtin p r L
        (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) = 1 :=
  padic_artin_uniformizer p r L

/-- The conductor-prime formula written with the same literal rational-unit
constructor used for away primes. -/
theorem padic_artin_conductor
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    padicCyclotomicArtin p r L
        (padicNatUnit p p (Fact.out : p.Prime).ne_zero) = 1 := by
  have hp : padicNatUnit p p (Fact.out : p.Prime).ne_zero =
      Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero := by
    apply Units.ext
    rfl
  rw [hp]
  exact cyclotomic_artin_conductor p r L

/-- The two literal local factors of the principal idèle `-1` cancel. -/
theorem neg_actual_factors
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    cyclotomicNegAutomorphism (p ^ r) L *
      padicCyclotomicArtin p r L (-1 : ℚ_[p]ˣ) = 1 := by
  rw [padic_artin_neg,
    cyclotomic_automorphism_self]

/-- The arithmetic-Frobenius factor at `q` and the literal ramified local
factor at `p` cancel for `q != p`. -/
theorem away_actual_factors
    (p r q : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (hq : q.Prime) (hqp : q ≠ p) :
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    let hcop : p.Coprime q :=
      (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
    cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        hcopPow (L := L) *
      padicCyclotomicArtin p r L
        (padicIntUnit p (awayPadicUnit p q hcop)) = 1 := by
  let hcopPow : q.Coprime (p ^ r) :=
    ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
  let hcop : p.Coprime q :=
    (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
  dsimp only
  rw [padic_artin_away p r q L hq hqp,
    mul_inv_cancel]

/-- The same cancellation, now literally evaluated at the rational prime
`q : Q_p^x`. -/
theorem away_literal_factors
    (p r q : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (hq : q.Prime) (hqp : q ≠ p) :
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        hcopPow (L := L) *
      padicCyclotomicArtin p r L
        (padicNatUnit p q hq.ne_zero) = 1 := by
  let hcopPow : q.Coprime (p ^ r) :=
    ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
  dsimp only
  rw [padic_artin_unit p r q L hq hqp,
    mul_inv_cancel]

end

end Towers.CField.RExist

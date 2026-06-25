import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Towers.ClassField.Reciprocity.Reciprocity

open scoped IsMulCommutative

/-!
# The rational generators used in Example VII.8.2

Milne reduces principal-idèle reciprocity for a rational cyclotomic field to
the elements `-1` and the positive rational primes.  This file records that
reduction for an arbitrary commutative-group-valued homomorphism on `ℚˣ`; the arithmetic
local-symbol calculations of Example VII.8.2 can therefore be supplied one
generator at a time.
-/

namespace Towers.CField.RExist

open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

/-- A nonzero natural number, regarded as a rational unit. -/
noncomputable def rationalNatUnit (n : ℕ) (hn : n ≠ 0) : ℚˣ :=
  Units.mk0 (n : ℚ) (by exact_mod_cast hn)

/-- A nonzero integer, regarded as a rational unit. -/
private noncomputable def rationalIntUnit (z : ℤ) (hz : z ≠ 0) : ℚˣ :=
  Units.mk0 (z : ℚ) (by exact_mod_cast hz)

private theorem rational_nat_factorization
    (n : ℕ) (hn : n ≠ 0) :
    rationalNatUnit n hn =
      ∏ p : n.primeFactors,
        rationalNatUnit p.1
          (Nat.prime_of_mem_primeFactors p.2).ne_zero ^ n.factorization p := by
  apply Units.ext
  change Units.coeHom ℚ (rationalNatUnit n hn) =
    Units.coeHom ℚ (∏ p : n.primeFactors,
      rationalNatUnit p.1
        (Nat.prime_of_mem_primeFactors p.2).ne_zero ^ n.factorization p)
  rw [map_prod]
  simp only [rationalNatUnit, Units.coeHom_apply, Units.val_mk0, map_pow]
  exact_mod_cast Nat.prod_pow_primeFactors_factorization hn

/-- A homomorphism out of `ℚˣ` is trivial once it is trivial on `-1` and on
every positive rational prime.  This is the exact generation step invoked in
Example VII.8.2 before the three displayed local-symbol calculations. -/
theorem rational_neg_primes
    {G : Type*} [Group G] [IsMulCommutative G] (f : ℚˣ →* G)
    (hneg : f (-1) = 1)
    (hprime : ∀ (p : ℕ) (hp : p.Prime),
      f (rationalNatUnit p hp.ne_zero) = 1) :
    ∀ x : ℚˣ, f x = 1 := by
  letI : CommGroup G := inferInstance
  have hnat (n : ℕ) (hn : n ≠ 0) :
      f (rationalNatUnit n hn) = 1 := by
    rw [rational_nat_factorization n hn, map_prod]
    apply Finset.prod_eq_one
    intro p _
    rw [map_pow, hprime p.1 (Nat.prime_of_mem_primeFactors p.2), one_pow]
  have hint (z : ℤ) (hz : z ≠ 0) :
      f (rationalIntUnit z hz) = 1 := by
    cases z with
    | ofNat n =>
        cases n with
        | zero => exact (hz rfl).elim
        | succ n =>
            simpa [rationalIntUnit, rationalNatUnit] using
              hnat (n + 1) (by omega)
    | negSucc n =>
        have hu : rationalIntUnit (Int.negSucc n) (by simp) =
            (-1 : ℚˣ) * rationalNatUnit (n + 1) (by omega) := by
          apply Units.ext
          simp [rationalIntUnit, rationalNatUnit]
        rw [hu, map_mul, hneg, hnat (n + 1) (by omega), one_mul]
  intro x
  let q : ℚ := x
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr x.ne_zero
  have hden : q.den ≠ 0 := q.den_nz
  let numUnit : ℚˣ := rationalIntUnit q.num hnum
  let denUnit : ℚˣ := rationalNatUnit q.den hden
  have hx : x = numUnit * denUnit⁻¹ := by
    apply Units.ext
    change q = (q.num : ℚ) * (q.den : ℚ)⁻¹
    rw [← div_eq_mul_inv]
    exact q.num_div_den.symm
  rw [hx, map_mul, map_inv, hint q.num hnum, hnat q.den hden,
    inv_one, one_mul]

/-- Example VII.8.2 may be checked on the displayed rational generators:
if the product of local symbols is trivial on `-1` and on every positive
prime, it is trivial on every rational principal idèle. -/
theorem rational_reciprocity_primes
    {G : Type*} [Group G] [IsMulCommutative G]
    (phi : IdeleGroup ℤ ℚ →* G)
    (hneg : phi (principalIdele ℤ ℚ (-1)) = 1)
    (hprime : ∀ (p : ℕ) (hp : p.Prime),
      phi (principalIdele ℤ ℚ (rationalNatUnit p hp.ne_zero)) = 1) :
    TrivialPrincipalIdeles ℤ ℚ G phi := by
  intro x
  exact rational_neg_primes
    (phi.comp (principalIdele ℤ ℚ)) hneg hprime x

/-- The literal three-case reduction in Example VII.8.2 for conductor
`ℓ ^ r`: it is enough to calculate the symbols of `-1`, of `ℓ`, and of
each prime `q ≠ ℓ`. -/
theorem rational_reciprocity_cases
    {G : Type*} [Group G] [IsMulCommutative G]
    (phi : IdeleGroup ℤ ℚ →* G)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hneg : phi (principalIdele ℤ ℚ (-1)) = 1)
    (hconductor :
      phi (principalIdele ℤ ℚ (rationalNatUnit ℓ hℓ.ne_zero)) = 1)
    (haway : ∀ (q : ℕ) (hq : q.Prime), q ≠ ℓ →
      phi (principalIdele ℤ ℚ (rationalNatUnit q hq.ne_zero)) = 1) :
    TrivialPrincipalIdeles ℤ ℚ G phi := by
  apply rational_reciprocity_primes phi hneg
  intro q hq
  by_cases hqℓ : q = ℓ
  · subst q
    exact hconductor
  · exact haway q hq hqℓ

end

end Towers.CField.RExist

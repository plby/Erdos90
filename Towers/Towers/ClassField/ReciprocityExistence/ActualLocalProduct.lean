import Towers.ClassField.ReciprocityExistence.PadicFactors
import Towers.ClassField.ReciprocityExistence.RationalCyclotomic

/-!
# Example VII.8.2 as a literal product of local maps

The source computes the global Artin value by multiplying its actual local
factors.  This file packages those three displayed computations with the
ramified factor evaluated on `Q_p^x`, then derives the earlier unit-coordinate
package and principal-idèle reciprocity.
-/

namespace Towers.CField.RExist

open Polynomial
open Towers.CField.LTate
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

/-- The conductor-one case is automatic, without any local calculation. -/
theorem principal_reciprocity_zero
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsCyclotomicExtension {p ^ 0} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ)) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 := by
  letI : Subsingleton Gal(L/ℚ) :=
    cyclotomic_galois_subsingleton p L
  intro x
  exact Subsingleton.elim _ _

/-- The source excludes conductor `2` from its calculation; the extension
is trivial, so reciprocity there is automatic as well. -/
theorem two_principal_reciprocity
    (L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsCyclotomicExtension {2} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ)) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 := by
  letI : Subsingleton Gal(L/ℚ) := two_cyclotomic_subsingleton L
  intro x
  exact Subsingleton.elim _ _

/-- The three displayed products in Example VII.8.2, using the literal
ramified local map on `Q_p^x`. -/
structure PAData
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ)) where
  neg_one_eq :
    phi (principalIdele ℤ ℚ (-1)) =
      cyclotomicNegAutomorphism (p ^ r) L *
        padicCyclotomicArtin p r L (-1 : ℚ_[p]ˣ)
  conductor_eq :
    phi (principalIdele ℤ ℚ
      (rationalNatUnit p (Fact.out : p.Prime).ne_zero)) =
      padicCyclotomicArtin p r L
        (padicNatUnit p p (Fact.out : p.Prime).ne_zero)
  away_eq : ∀ (q : ℕ) (hq : q.Prime) (hqp : q ≠ p),
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    phi (principalIdele ℤ ℚ (rationalNatUnit q hq.ne_zero)) =
      cyclotomicFrobenius
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
          hcopPow (L := L) *
        padicCyclotomicArtin p r L
          (padicNatUnit p q hq.ne_zero)

/-- The literal local-factor package implies the earlier coordinate package;
this is where the actual `Q_p^x` evaluations are converted to Milne's
inverse-unit notation. -/
theorem PAData.prime_power_artindata
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ))
    (D : PAData p r L phi) :
    PrimeArtinData p r L phi where
  neg_one_eq := by
    rw [D.neg_one_eq,
      padic_artin_neg,
      padic_action_neg]
  conductor_eq := by
    rw [D.conductor_eq]
    exact padic_artin_conductor p r L
  away_eq q hq hqp := by
    let hcopPow : q.Coprime (p ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp).pow_right r
    let hcop : p.Coprime q :=
      (Nat.coprime_primes (Fact.out : p.Prime) hq).2 hqp.symm
    dsimp only
    rw [D.away_eq q hq hqp]
    congr 1
    rw [← padic_int_away p q hq hqp]
    simpa using
      (padic_cyclotomic_zpow
        p r L (awayPadicUnit p q hcop) 0)

/-- **Example VII.8.2, prime-power case, with literal local factors.** -/
theorem reciprocity_actual_factors
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ))
    (D : PAData p r L phi) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 :=
  prime_principal_reciprocity p r L phi
    (D.prime_power_artindata p r L phi)

end

end Towers.CField.RExist

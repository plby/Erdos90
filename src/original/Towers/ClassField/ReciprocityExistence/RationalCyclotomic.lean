import Towers.ClassField.ReciprocityExistence.RationalGenerators
import Towers.ClassField.ReciprocityExistence.AwayCancellation

/-!
# Example VII.8.2 for a prime-power cyclotomic layer

This file packages exactly the three displayed local-symbol computations in
the source.  Once a product-of-local-symbols homomorphism has those values on
`-1`, on the conductor prime `ℓ`, and on each prime `q ≠ ℓ`, the explicit
cyclotomic cancellations prove principal-idèle reciprocity over `ℚ`.
-/

namespace Towers.CField.RExist

open Polynomial
open Towers.CField.LTate
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

/-- The three local-symbol calculations displayed in Example VII.8.2 for a
cyclotomic field of conductor `ℓ ^ r`.  No reciprocity conclusion is included
in the data. -/
structure PrimeArtinData
    (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ)) where
  neg_one_eq :
    phi (principalIdele ℤ ℚ (-1)) =
      cyclotomicNegAutomorphism (ℓ ^ r) L *
        padicCyclotomicAction ℓ r
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
          (L := L) (-1)
  conductor_eq :
    phi (principalIdele ℤ ℚ
      (rationalNatUnit ℓ (Fact.out : ℓ.Prime).ne_zero)) = 1
  away_eq : ∀ (q : ℕ) (hq : q.Prime) (hqℓ : q ≠ ℓ),
    let hcopPow : q.Coprime (ℓ ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : ℓ.Prime)).2 hqℓ).pow_right r
    let hcop : ℓ.Coprime q :=
      (Nat.coprime_primes (Fact.out : ℓ.Prime) hq).2 hqℓ.symm
    phi (principalIdele ℤ ℚ (rationalNatUnit q hq.ne_zero)) =
      cyclotomicFrobenius
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
          hcopPow (L := L) *
        padicCyclotomicAction ℓ r
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
          (L := L) (awayPadicUnit ℓ q hcop)

/-- **Example VII.8.2, prime-power case.**  The displayed local-symbol
values imply that the product map is trivial on every rational principal
idèle. -/
theorem prime_principal_reciprocity
    (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ))
    (D : PrimeArtinData ℓ r L phi) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 := by
  let e : Gal(L/ℚ) ≃* (ZMod (ℓ ^ r))ˣ :=
    IsCyclotomicExtension.autEquivPow L
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
  letI : IsMulCommutative Gal(L/ℚ) := by
    refine ⟨⟨fun σ τ ↦ e.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (e σ) (e τ)
  apply rational_neg_primes
    (phi.comp (principalIdele ℤ ℚ))
  · change phi (principalIdele ℤ ℚ (-1)) = 1
    rw [D.neg_one_eq]
    exact neg_factors_mul ℓ r L
  · intro q hq
    change phi (principalIdele ℤ ℚ (rationalNatUnit q hq.ne_zero)) = 1
    by_cases hqℓ : q = ℓ
    · subst q
      exact D.conductor_eq
    · rw [D.away_eq q hq hqℓ]
      exact away_prime_factors ℓ r q L hq hqℓ

end

end Towers.CField.RExist

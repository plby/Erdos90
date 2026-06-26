import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Towers.ClassField.ReciprocityExistence.RationalCyclotomic

/-!
# Reduction of Example VII.8.2 to prime-power conductors

The source reduces the cyclotomic extension of conductor `m` to the fields
of conductor `p ^ m.factorization p`, one for every prime divisor `p` of
`m`.  This file records the Chinese-remainder step underlying that
reduction, and then applies the standard compatibility between restriction
of cyclotomic automorphisms and reduction of their exponents.
-/

namespace Towers.CField.RExist

open scoped Function
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

/-- An element of `(ZMod m)ˣ` is one if it is one modulo every prime-power
factor of `m`.  This is the Chinese-remainder calculation used in the first
paragraph of Example VII.8.2. -/
theorem zmod_unit_components
    (m : ℕ) (hm : m ≠ 0) (u : (ZMod m)ˣ)
    (h : ∀ p : m.primeFactors,
      ((u : ZMod m).cast : ZMod (p.1 ^ m.factorization p.1)) = 1) :
    u = 1 := by
  letI : NeZero m := ⟨hm⟩
  apply Units.ext
  apply (ZMod.equivPi m hm).injective
  funext p
  letI : NeZero (p.1 ^ m.factorization p.1) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  rw [show ((1 : (ZMod m)ˣ) : ZMod m) = 1 by rfl, map_one]
  change ((ZMod.equivPi m hm) (u : ZMod m)) p = 1
  rw [← ZMod.natCast_zmod_val (u : ZMod m), map_natCast]
  have hp := h p
  rw [ZMod.cast_eq_val] at hp
  exact hp

/-- **Example VII.8.2, reduction to prime powers.**  An automorphism of a
rational cyclotomic field is the identity if its restriction to the
cyclotomic subfield belonging to every prime-power factor of the conductor
is the identity. -/
theorem cyclotomic_automorphism_restrictions
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (F : m.primeFactors → Type*)
    [∀ p, Field (F p)] [∀ p, NumberField (F p)]
    [∀ p, IsCyclotomicExtension
      {p.1 ^ m.factorization p.1} ℚ (F p)]
    [∀ p, Algebra (F p) L] [∀ p, IsGalois ℚ (F p)]
    (σ : Gal(L/ℚ))
    (hσ : ∀ p, σ.restrictNormal (F p) = 1) :
    σ = 1 := by
  let e : Gal(L/ℚ) ≃* (ZMod m)ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod m L
  apply e.injective
  have he : e σ = 1 := by
    apply zmod_unit_components m (NeZero.ne m)
    intro p
    have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    letI : NeZero (p.1 ^ m.factorization p.1) :=
      ⟨pow_ne_zero _ hp.ne_zero⟩
    have hdiv : p.1 ^ m.factorization p.1 ∣ m :=
      (hp.pow_dvd_iff_le_factorization (NeZero.ne m)).2 le_rfl
    have hcompat :=
      IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
        (n := m) (K := L) (m := p.1 ^ m.factorization p.1)
        (F p) hdiv σ
    have hcomponent :
        ZMod.unitsMap hdiv
          (IsCyclotomicExtension.Rat.galEquivZMod m L σ) = 1 := by
      rw [← hcompat, hσ p, map_one]
    exact congrArg Units.val hcomponent
  simpa [e] using he

/-- The first reduction in Example VII.8.2, stated for the product of local
Artin symbols: principal-idèle reciprocity for every prime-power restriction
implies principal-idèle reciprocity for the full cyclotomic field. -/
theorem cyclotomic_prime_restrictions
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (F : m.primeFactors → Type*)
    [∀ p, Field (F p)] [∀ p, NumberField (F p)]
    [∀ p, IsCyclotomicExtension
      {p.1 ^ m.factorization p.1} ℚ (F p)]
    [∀ p, Algebra (F p) L] [∀ p, IsGalois ℚ (F p)]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ))
    (hprimePower : ∀ (p : m.primeFactors) (x : ℚˣ),
      ((AlgEquiv.restrictNormalHom (F p)).comp phi)
        (principalIdele ℤ ℚ x) = 1) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 := by
  intro x
  apply cyclotomic_automorphism_restrictions m L F
  intro p
  exact hprimePower p x

/-- **Example VII.8.2, arbitrary conductor.**  If the three displayed
local-symbol calculations hold after restriction to each prime-power
cyclotomic layer, then the product of local symbols is trivial on every
rational principal idèle. -/
theorem cyclotomic_principal_reciprocity
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (F : m.primeFactors → Type*)
    [∀ p, Field (F p)] [∀ p, NumberField (F p)]
    [∀ p, IsCyclotomicExtension
      {p.1 ^ m.factorization p.1} ℚ (F p)]
    [∀ p, Algebra (F p) L] [∀ p, IsGalois ℚ (F p)]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ))
    (hdata : ∀ p : m.primeFactors,
      letI : Fact p.1.Prime :=
        ⟨Nat.prime_of_mem_primeFactors p.2⟩
      letI : NeZero (p.1 ^ m.factorization p.1) :=
        ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
      PrimeArtinData p.1 (m.factorization p.1) (F p)
        ((AlgEquiv.restrictNormalHom (F p)).comp phi)) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 := by
  apply cyclotomic_prime_restrictions m L F phi
  intro p x
  letI : Fact p.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  letI : NeZero (p.1 ^ m.factorization p.1) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  exact prime_principal_reciprocity
    p.1 (m.factorization p.1) (F p)
      ((AlgEquiv.restrictNormalHom (F p)).comp phi) (hdata p) x

end

end Towers.CField.RExist

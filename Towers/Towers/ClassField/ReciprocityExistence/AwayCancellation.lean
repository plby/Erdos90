import Towers.ClassField.LubinTate.CyclotomicResidueDegree

/-!
# The away-prime cancellation in Example VII.8.2

For the prime-power cyclotomic extension of conductor `ℓ ^ r`, a rational
prime `q ≠ ℓ` contributes arithmetic Frobenius at `q`.  At the ramified
prime `ℓ`, the same rational number is a unit and local reciprocity acts by
the inverse residue class.  This file proves that the two explicit Galois
actions cancel.
-/

namespace Towers.CField.RExist

open Polynomial
open Towers.CField.LTate

noncomputable section

/-- A rational prime `q ≠ ℓ`, regarded as an `ℓ`-adic integer unit. -/
noncomputable def awayPadicUnit
    (ℓ q : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime q) : ℤ_[ℓ]ˣ := by
  have hunit : IsUnit (q : ℤ_[ℓ]) :=
    PadicInt.isUnit_iff.mpr (by simpa using hcop)
  exact hunit.unit

@[simp]
theorem away_padic_val
    (ℓ q : ℕ) [Fact ℓ.Prime] (hcop : ℓ.Coprime q) :
    (awayPadicUnit ℓ q hcop : ℤ_[ℓ]) = q := by
  exact IsUnit.unit_spec _

/-- Reduction of the chosen `ℓ`-adic unit is the usual residue class of
`q` modulo `ℓ ^ r`. -/
theorem padic_reduction_away
    (ℓ r q : ℕ) [Fact ℓ.Prime]
    (hcop : ℓ.Coprime q) (hcopPow : q.Coprime (ℓ ^ r)) :
    padicUnitReduction ℓ r (awayPadicUnit ℓ q hcop) =
      ZMod.unitOfCoprime q hcopPow := by
  apply Units.ext
  change PadicInt.toZModPow r
      (awayPadicUnit ℓ q hcop : ℤ_[ℓ]) = (q : ZMod (ℓ ^ r))
  rw [away_padic_val]
  exact map_natCast _ _

/-- The explicit local factor at `ℓ` attached to the rational prime `q`
is the inverse of the arithmetic Frobenius factor at `q`. -/
theorem padic_action_away
    (ℓ r q : ℕ) [Fact ℓ.Prime]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L]
    (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    letI : NeZero (ℓ ^ r) :=
      ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
    let hcopPow : q.Coprime (ℓ ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : ℓ.Prime)).2 hqℓ).pow_right r
    let hcop : ℓ.Coprime q :=
      (Nat.coprime_primes (Fact.out : ℓ.Prime) hq).2 hqℓ.symm
    padicCyclotomicAction ℓ r
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
        (L := L) (awayPadicUnit ℓ q hcop) =
      (cyclotomicFrobenius
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
        hcopPow (L := L))⁻¹ := by
  letI : NeZero (ℓ ^ r) :=
    ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
  let hcopPow : q.Coprime (ℓ ^ r) :=
    ((Nat.coprime_primes hq (Fact.out : ℓ.Prime)).2 hqℓ).pow_right r
  have hcop : ℓ.Coprime q :=
    (Nat.coprime_primes (Fact.out : ℓ.Prime) hq).2 hqℓ.symm
  let hcycl := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r))
  change (IsCyclotomicExtension.autEquivPow L hcycl).symm
      (padicUnitReduction ℓ r (awayPadicUnit ℓ q hcop)⁻¹) =
    ((IsCyclotomicExtension.autEquivPow L hcycl).symm
      (ZMod.unitOfCoprime q hcopPow))⁻¹
  rw [map_inv, padic_reduction_away ℓ r q hcop hcopPow,
    map_inv]

/-- **Example VII.8.2, away-prime product.**  The Frobenius factor at
`q ≠ ℓ` and the inverse unit factor at `ℓ` multiply to the identity. -/
theorem away_prime_factors
    (ℓ r q : ℕ) [Fact ℓ.Prime]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L]
    (hq : q.Prime) (hqℓ : q ≠ ℓ) :
    letI : NeZero (ℓ ^ r) :=
      ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
    let hcopPow : q.Coprime (ℓ ^ r) :=
      ((Nat.coprime_primes hq (Fact.out : ℓ.Prime)).2 hqℓ).pow_right r
    let hcop : ℓ.Coprime q :=
      (Nat.coprime_primes (Fact.out : ℓ.Prime) hq).2 hqℓ.symm
    cyclotomicFrobenius
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
          hcopPow (L := L) *
        padicCyclotomicAction ℓ r
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
          (L := L) (awayPadicUnit ℓ q hcop) = 1 := by
  letI : NeZero (ℓ ^ r) :=
    ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
  let hcopPow : q.Coprime (ℓ ^ r) :=
    ((Nat.coprime_primes hq (Fact.out : ℓ.Prime)).2 hqℓ).pow_right r
  let hcop : ℓ.Coprime q :=
    (Nat.coprime_primes (Fact.out : ℓ.Prime) hq).2 hqℓ.symm
  dsimp only
  rw [padic_action_away ℓ r q L hq hqℓ,
    mul_inv_cancel]

/-! ### The ramified local map in unit/uniformizer coordinates -/

/-- The explicit local Artin homomorphism at the conductor prime, written in
the standard decomposition `ℤ_ℓˣ × ℤ` of `ℚ_ℓˣ`.  The extension is
totally ramified, so the uniformizer exponent has trivial image and only the
inverse unit action remains. -/
noncomputable def padicDecompositionArtin
    (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L] :
    ℤ_[ℓ]ˣ × Multiplicative ℤ →* Gal(L/ℚ) :=
  (padicCyclotomicAction ℓ r
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
    (L := L)).comp (MonoidHom.fst ℤ_[ℓ]ˣ (Multiplicative ℤ))

@[simp]
theorem cyclotomic_decomposition_artin
    (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L]
    (u : ℤ_[ℓ]ˣ) (s : Multiplicative ℤ) :
    padicDecompositionArtin ℓ r L (u, s) =
      padicCyclotomicAction ℓ r
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
        (L := L) u :=
  rfl

/-- The uniformizer part is trivial, which is the conductor-prime
calculation `φ_ℓ(ℓ) = 1` in Example VII.8.2. -/
theorem decomposition_artin_uniformizer
    (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L]
    (s : Multiplicative ℤ) :
    padicDecompositionArtin ℓ r L (1, s) = 1 := by
  rw [cyclotomic_decomposition_artin, map_one]

/-- The kernel of the explicit ramified local map is exactly the principal
unit congruence subgroup on the unit coordinate, with the whole uniformizer
factor in the kernel. -/
theorem padic_decomposition_artin
    (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L]
    (u : ℤ_[ℓ]ˣ) (s : Multiplicative ℤ) :
    padicDecompositionArtin ℓ r L (u, s) = 1 ↔
      (u : ℤ_[ℓ]) - 1 ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ r} := by
  rw [cyclotomic_decomposition_artin]
  exact padic_cyclotomic_action ℓ r
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r))) u

/-! ### The generator `-1` -/

/-- The cyclotomic automorphism represented by `-1` modulo `m`; over the
rationals this is complex conjugation. -/
noncomputable def cyclotomicNegAutomorphism
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ L] : Gal(L/ℚ) :=
  (IsCyclotomicExtension.autEquivPow L
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))).symm (-1)

/-- The preceding automorphism sends the chosen primitive root to its
inverse, so it is literally the complex-conjugation action used at the
infinite place in Example VII.8.2. -/
theorem cyclotomic_automorphism_zeta
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ L] :
    cyclotomicNegAutomorphism m L
        (IsCyclotomicExtension.zeta m ℚ L) =
      (IsCyclotomicExtension.zeta m ℚ L)⁻¹ := by
  rw [cyclotomicNegAutomorphism,
    cyclotomic_aut_zeta]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  change IsCyclotomicExtension.zeta (n + 1) ℚ L ^
      ((-1 : ZMod (n + 1)).val) = _
  rw [ZMod.val_neg_one]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact (IsCyclotomicExtension.zeta_spec (n + 1) ℚ L).pow_eq_one

/-- Complex conjugation has order at most two. -/
theorem cyclotomic_automorphism_self
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ L] :
    cyclotomicNegAutomorphism m L *
      cyclotomicNegAutomorphism m L = 1 := by
  let e := IsCyclotomicExtension.autEquivPow L
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  change e.symm (-1) * e.symm (-1) = 1
  rw [← e.symm.map_mul]
  have hneg : (-1 : (ZMod m)ˣ) * (-1) = 1 := by
    apply Units.ext
    simp
  rw [hneg, map_one]

/-- The ramified `ℓ`-adic unit action of `-1` is the cyclotomic
complex-conjugation automorphism. -/
theorem padic_action_neg
    (ℓ r : ℕ) [Fact ℓ.Prime]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L] :
    letI : NeZero (ℓ ^ r) :=
      ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
    padicCyclotomicAction ℓ r
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
        (L := L) (-1) =
      cyclotomicNegAutomorphism (ℓ ^ r) L := by
  letI : NeZero (ℓ ^ r) :=
    ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
  let hcycl := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r))
  change (IsCyclotomicExtension.autEquivPow L hcycl).symm
      (padicUnitReduction ℓ r ((-1 : ℤ_[ℓ]ˣ)⁻¹)) =
    (IsCyclotomicExtension.autEquivPow L hcycl).symm (-1)
  congr 1
  apply Units.ext
  simp [padicUnitReduction]

/-- **Example VII.8.2, the `-1` product.**  The infinite complex-conjugation
factor and the ramified `ℓ`-adic factor multiply to the identity. -/
theorem neg_factors_mul
    (ℓ r : ℕ) [Fact ℓ.Prime]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {ℓ ^ r} ℚ L] :
    letI : NeZero (ℓ ^ r) :=
      ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
    cyclotomicNegAutomorphism (ℓ ^ r) L *
      padicCyclotomicAction ℓ r
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (ℓ ^ r)))
        (L := L) (-1) = 1 := by
  letI : NeZero (ℓ ^ r) :=
    ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩
  rw [padic_action_neg ℓ r L,
    cyclotomic_automorphism_self]

end

end Towers.CField.RExist

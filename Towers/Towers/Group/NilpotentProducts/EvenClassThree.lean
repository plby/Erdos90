import Towers.Group.NilpotentProducts.ExceptionalTwoModel
import Towers.Group.NilpotentProducts.NaturalPowerCollection

/-!
# The coordinate order relations in Struik's Theorem 4
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton

variable {G : Type*} [Group G]

private lemma choose_two_mul
    {N L : ℕ} (hN : N = 2 * L) :
    Ring.choose (N : ℤ) 2 = (L : ℤ) * ((N : ℤ) - 1) := by
  have hdouble :
      2 * Ring.choose (N : ℤ) 2 =
        2 * ((L : ℤ) * ((N : ℤ) - 1)) := by
    calc
      2 * Ring.choose (N : ℤ) 2 =
          (N : ℤ) * ((N : ℤ) - 1) :=
        two_mul_choose _
      _ = 2 * ((L : ℤ) * ((N : ℤ) - 1)) := by
        rw [hN]
        push_cast
        ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hdouble

/-- Equation (27): an even order relation on the left input identifies
the half-order powers of the weight-two and repeated-left
commutators. -/
theorem half_even_order
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {N L : ℕ} (hN : N = 2 * L)
    (ha : a ^ N = 1) :
    hallCommutator a b ^ N =
      hallTripleCommutator a b a ^ L := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  have hDN :
      D ^ N = 1 :=
    triple_commutator_elementary hG4 ha
  have hcolNat :
      1 = C ^ N * D ^ N.choose 2 := by
    simpa [C, D, ha, hallCommutator] using
      (commutator_pow_elementary hG4 a b N)
  have hcol :
      1 = C ^ (N : ℤ) * D ^ Ring.choose (N : ℤ) 2 := by
    simpa [zpow_natCast, Ring.choose_natCast] using hcolNat
  have hDNz : D ^ (N : ℤ) = 1 := by simpa using hDN
  have hchoosePow :
      D ^ Ring.choose (N : ℤ) 2 = (D ^ (L : ℤ))⁻¹ := by
    rw [choose_two_mul hN]
    have hexponent :
        (L : ℤ) * ((N : ℤ) - 1) =
          (N : ℤ) * (L : ℤ) - (L : ℤ) := by ring
    rw [hexponent, zpow_sub, zpow_mul, hDNz, one_zpow, one_mul]
  have hEqZ : C ^ (N : ℤ) = D ^ (L : ℤ) := by
    rw [hchoosePow] at hcol
    exact eq_of_mul_inv_eq_one hcol.symm
  simpa [C, D] using hEqZ

/-- The symmetric form of equation (27), using an even order relation
on the right input. -/
theorem triple_half_even
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {N L : ℕ} (hN : N = 2 * L)
    (hb : b ^ N = 1) :
    hallCommutator a b ^ N =
      hallTripleCommutator a b b ^ L := by
  let C := hallCommutator a b
  let E := hallTripleCommutator a b b
  have hEN :
      E ^ N = 1 :=
    triple_middle_elementary hG4 hb
  have hcolNat :
      1 = C ^ N * E ^ N.choose 2 := by
    simpa [C, E, hb, hallCommutator] using
      (hall_commutator_elementary hG4 a b N)
  have hcol :
      1 = C ^ (N : ℤ) * E ^ Ring.choose (N : ℤ) 2 := by
    simpa [zpow_natCast, Ring.choose_natCast] using hcolNat
  have hENz : E ^ (N : ℤ) = 1 := by simpa using hEN
  have hchoosePow :
      E ^ Ring.choose (N : ℤ) 2 = (E ^ (L : ℤ))⁻¹ := by
    rw [choose_two_mul hN]
    have hexponent :
        (L : ℤ) * ((N : ℤ) - 1) =
          (N : ℤ) * (L : ℤ) - (L : ℤ) := by ring
    rw [hexponent, zpow_sub, zpow_mul, hENz, one_zpow, one_mul]
  have hEqZ : C ^ (N : ℤ) = E ^ (L : ℤ) := by
    rw [hchoosePow] at hcol
    exact eq_of_mul_inv_eq_one hcol.symm
  simpa [C, E] using hEqZ

/-- Equation (26): an even order relation on either input kills the
double-order power of their commutator. -/
theorem even_left_order
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {N L : ℕ} (hN : N = 2 * L)
    (ha : a ^ N = 1) :
    hallCommutator a b ^ (2 * N) = 1 := by
  let D := hallTripleCommutator a b a
  have hrelation :=
    half_even_order
      (a := a) (b := b) hG4 hN ha
  have hDN :
      D ^ N = 1 :=
    triple_commutator_elementary hG4 ha
  rw [show 2 * N = N * 2 by omega, pow_mul, hrelation, ← pow_mul,
    show L * 2 = N by omega, hDN]

/-- The replacement commutator `(a²,b)` has order dividing half the
even order of `a`. -/
theorem square_half_one
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {N L : ℕ} (hN : N = 2 * L)
    (ha : a ^ N = 1) :
    hallCommutator (a ^ (2 : ℤ)) b ^ L = 1 := by
  let C := hallCommutator a b
  let D := hallTripleCommutator a b a
  have hCD : Commute C D :=
    commute_triple_elementary hG4 C a b a
  have hrelation :
      C ^ N = D ^ L :=
    half_even_order hG4 hN ha
  have hDN :
      D ^ N = 1 :=
    triple_commutator_elementary hG4 ha
  rw [first_elementary hG4, zpow_ofNat]
  change (C ^ 2 * D) ^ L = 1
  rw [(hCD.pow_left 2).mul_pow L, ← pow_mul, ← hN, hrelation,
    ← pow_add, show L + L = N by omega, hDN]

/-- If the right input has the same even order, `(a,b²)` also has order
dividing half that order. -/
theorem commutator_square_half
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {N L : ℕ} (hN : N = 2 * L)
    (hb : b ^ N = 1) :
    hallCommutator a (b ^ (2 : ℤ)) ^ L = 1 := by
  let C := hallCommutator a b
  let E := hallTripleCommutator a b b
  have hCE : Commute C E :=
    commute_triple_elementary hG4 C a b b
  have hrelation :
      C ^ N = E ^ L :=
    triple_half_even hG4 hN hb
  have hEN :
      E ^ N = 1 :=
    triple_middle_elementary hG4 hb
  rw [second_elementary hG4, zpow_ofNat]
  change (C ^ 2 * E) ^ L = 1
  rw [(hCE.pow_left 2).mul_pow L, ← pow_mul, ← hN, hrelation,
    ← pow_add, show L + L = N by omega, hEN]

/-- Without equality of the two input orders, the full smaller order
still kills `(a,b²)`. -/
theorem hall_commutator_square
    (hG4 : Subgroup.lowerCentralSeries G 3 = ⊥)
    {a b : G} {N L : ℕ} (hN : N = 2 * L)
    (ha : a ^ N = 1) :
    hallCommutator a (b ^ (2 : ℤ)) ^ N = 1 := by
  let C := hallCommutator a b
  let E := hallTripleCommutator a b b
  have hCE : Commute C E :=
    commute_triple_elementary hG4 C a b b
  have hC :
      C ^ (2 * N) = 1 :=
    even_left_order hG4 hN ha
  have hEN :
      E ^ N = 1 :=
    triple_commutator_elementary hG4 ha
  rw [second_elementary hG4, zpow_ofNat]
  change (C ^ 2 * E) ^ N = 1
  rw [(hCE.pow_left 2).mul_pow N, ← pow_mul, hC, hEN, mul_one]

/-- Struik's fourth nilpotent product for cyclic orders `2 ^ rᵢ`. -/
abbrev EvenClassGroup {t : ℕ} (r : Fin t → ℕ) :=
  NilpotentCyclicProduct (singleModulus r) 4

/-- The canonical `i`th generator in Struik's Theorem 4 group. -/
def evenClassGenerator {t : ℕ} (r : Fin t → ℕ) (i : Fin t) :
    EvenClassGroup r :=
  nilpotentCyclicGenerator (singleModulus r) 4 i

theorem pair_pow_modulus
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (q : Pair t) :
    hallCommutator (evenClassGenerator r q.i) (evenClassGenerator r q.j) ^
      exceptionalPairModulus r q = 1 := by
  have h :=
    even_left_order
      (a := evenClassGenerator r q.i)
      (b := evenClassGenerator r q.j)
      (nilpotent_four_bot
        (singleModulus r))
      (single_two_left r hpos q.i)
      (nilpotent_cyclic_generator
        (singleModulus r) 4 q.i)
  simpa [exceptionalPairModulus, singleModulus,
    Nat.pow_succ, Nat.mul_comm] using h

theorem square_pow_modulus
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (q : Pair t) :
    hallCommutator
        (evenClassGenerator r q.i ^ (2 : ℤ))
        (evenClassGenerator r q.j) ^
      leftSquareModulus r q = 1 := by
  apply square_half_one
    (nilpotent_four_bot
      (singleModulus r))
    (single_two_left r hpos q.i)
  exact nilpotent_cyclic_generator
    (singleModulus r) 4 q.i

theorem pair_square_modulus
    {t : ℕ} (r : Fin t → ℕ) (hpos : ∀ i, 0 < r i)
    (q : Pair t) :
    hallCommutator
        (evenClassGenerator r q.i)
        (evenClassGenerator r q.j ^ (2 : ℤ)) ^
      pairSquareModulus r q = 1 := by
  by_cases heq : r q.i = r q.j
  · rw [pairSquareModulus, if_pos heq]
    apply commutator_square_half
      (nilpotent_four_bot
        (singleModulus r))
      (single_two_left r hpos q.i)
    simpa [singleModulus, heq] using
      nilpotent_cyclic_generator
        (singleModulus r) 4 q.j
  · rw [pairSquareModulus, if_neg heq]
    apply hall_commutator_square
      (nilpotent_four_bot
        (singleModulus r))
      (single_two_left r hpos q.i)
    exact nilpotent_cyclic_generator
      (singleModulus r) 4 q.i

theorem triple_first_modulus
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    hallTripleCommutator
        (evenClassGenerator r q.i)
        (evenClassGenerator r q.j)
        (evenClassGenerator r q.k) ^
      exceptionalResiduesModulus r q = 1 := by
  apply triple_commutator_elementary
    (nilpotent_four_bot
      (singleModulus r))
  exact nilpotent_cyclic_generator
    (singleModulus r) 4 q.i

theorem triple_second_modulus
    {t : ℕ} (r : Fin t → ℕ) (q : Triple t) :
    hallTripleCommutator
        (evenClassGenerator r q.j)
        (evenClassGenerator r q.k)
        (evenClassGenerator r q.i) ^
      exceptionalResiduesModulus r q = 1 := by
  apply triple_order_elementary
    (nilpotent_four_bot
      (singleModulus r))
  exact nilpotent_cyclic_generator
    (singleModulus r) 4 q.i

end P1960
end Struik

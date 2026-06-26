import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Milne, Class Field Theory, Proposition III.1.9

This file formalizes the finite cyclic calculation in Milne's proof.  The
fundamental factor set is obtained by recording whether addition of the
standard representatives in `ZMod n` carries.  We prove its normalized
cocycle identity and the product computation which sends the chosen
Frobenius generator to the class of the uniformizer.
-/

namespace Submission.CField.UCohom

noncomputable section

open scoped BigOperators

namespace FCarry

variable {n : ℕ} [NeZero n]

/-- Whether addition of the standard representatives in `ZMod n` crosses
the modulus. -/
def carry (a b : ZMod n) : ℕ :=
  if n ≤ a.val + b.val then 1 else 0

theorem val_add_carry (a b : ZMod n) :
    (a + b).val + n * carry a b = a.val + b.val := by
  by_cases h : n ≤ a.val + b.val
  · simp only [carry, if_pos h, mul_one]
    exact (ZMod.val_add_val_of_le h).symm
  · have hlt : a.val + b.val < n := Nat.lt_of_not_ge h
    simp only [carry, if_neg h, mul_zero, add_zero]
    exact ZMod.val_add_of_lt hlt

/-- The carry function is an additive normalized two-cocycle. -/
theorem carry_cocycle (a b c : ZMod n) :
    carry (a + b) c + carry a b =
      carry b c + carry a (b + c) := by
  have hab := val_add_carry a b
  have habc := val_add_carry (a + b) c
  have hbc := val_add_carry b c
  have habc' := val_add_carry a (b + c)
  have hassoc : (a + b + c).val = (a + (b + c)).val := by
    rw [add_assoc]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul :
      n * (carry (a + b) c + carry a b) =
        n * (carry b c + carry a (b + c)) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact Nat.eq_of_mul_eq_mul_left hn hmul

variable {M : Type*} [CommGroup M]

/-- Milne's factor set: `1` before a carry and `pi` after a carry. -/
def factorSet (pi : M) (a b : ZMod n) : M :=
  pi ^ carry a b

@[simp]
theorem factor_set_left (pi : M) (b : ZMod n) :
    factorSet pi 0 b = 1 := by
  simp [factorSet, carry, ZMod.val_lt]

@[simp]
theorem factor_set_right (pi : M) (a : ZMod n) :
    factorSet pi a 0 = 1 := by
  simp [factorSet, carry, ZMod.val_lt]

/-- The multiplicative two-cocycle identity for Milne's factor set, with
trivial action on the chosen element `pi`. -/
theorem factorSet_cocycle (pi : M) (a b c : ZMod n) :
    factorSet pi (a + b) c * factorSet pi a b =
      factorSet pi b c * factorSet pi a (b + c) := by
  simp only [factorSet, ← pow_add]
  exact congrArg (pi ^ ·) (carry_cocycle a b c)

omit [NeZero n] in
@[simp]
theorem set_no_carry (pi : M) (a b : ZMod n)
    (h : a.val + b.val < n) : factorSet pi a b = 1 := by
  simp [factorSet, carry, Nat.not_le.mpr h]

omit [NeZero n] in
@[simp]
theorem factor_set_carry (pi : M) (a b : ZMod n)
    (h : n ≤ a.val + b.val) : factorSet pi a b = pi := by
  simp [factorSet, carry, h]

omit [NeZero n] in
/-- The telescoping norm calculation in Proposition III.1.9:
`prod_(i=0)^(n-1) phi(sigma,sigma^i) = pi`. -/
theorem prod_set_generator (pi : M) (hn : 1 < n) :
    ∏ i ∈ Finset.range n,
      factorSet pi (1 : ZMod n) (i : ZMod n) = pi := by
  classical
  have hnpos : 0 < n := by omega
  have hpred : n - 1 < n := Nat.sub_lt hnpos Nat.zero_lt_one
  letI : Fact (1 < n) := ⟨hn⟩
  rw [Finset.prod_eq_single (n - 1)]
  · rw [factor_set_carry]
    rw [ZMod.val_one, ZMod.val_natCast_of_lt hpred]
    omega
  · intro i hi hine
    have hi_lt : i < n := Finset.mem_range.mp hi
    have hi_pred : i < n - 1 := by omega
    apply set_no_carry
    rw [ZMod.val_one, ZMod.val_natCast_of_lt hi_lt]
    omega
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hpred)).elim

end FCarry

end

end Submission.CField.UCohom

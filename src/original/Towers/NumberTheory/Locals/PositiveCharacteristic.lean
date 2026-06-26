import Towers.NumberTheory.Locals.NonarchimedeanCriterion
import Mathlib.Algebra.CharP.Basic

/-!
# Absolute values in positive characteristic

This file formalizes Corollary 7.3 of Milne's *Algebraic Number Theory*.
-/

namespace Towers.NumberTheory.Milne

section

variable {K : Type*} [Field K]

private theorem absolute_value_cast (v : AbsoluteValue K ℝ) (n : ℕ) :
    v (n : K) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      exact (v.add_le (n : K) 1).trans (by simpa using add_le_add_right ih 1)

/-- Milne, Corollary 7.3, with an explicit positive characteristic: every
real-valued absolute value on a field of characteristic `p ≠ 0` is
nonarchimedean. -/
theorem absolute_nonarchimedean_char
    (p : ℕ) [CharP K p] (hp : p ≠ 0) (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v := by
  rw [nonarchimedean_int_cast]
  refine ⟨p, fun m ↦ ?_⟩
  rw [CharP.intCast_eq_intCast_mod]
  have hpInt : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hnonneg : 0 ≤ m % (p : ℤ) := Int.emod_nonneg _ hpInt
  have hlt : m % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hcast : ((m % (p : ℤ) : ℤ) : K) = ((m % (p : ℤ)).toNat : K) := by
    calc
      ((m % (p : ℤ) : ℤ) : K) = ((((m % (p : ℤ)).toNat : ℕ) : ℤ) : K) :=
        congrArg (fun z : ℤ ↦ (z : K)) (Int.toNat_of_nonneg hnonneg).symm
      _ = ((m % (p : ℤ)).toNat : K) := by rw [Int.cast_natCast]
  have htoNat : (m % (p : ℤ)).toNat ≤ p := by omega
  rw [hcast]
  exact (absolute_value_cast v _).trans (by exact_mod_cast htoNat)

/-- Milne, Corollary 7.3, stated literally using the characteristic of the
field. -/
theorem charac_value_nonar
    (hK : ringChar K ≠ 0) (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v := by
  letI : CharP K (ringChar K) := ringChar.charP K
  exact absolute_nonarchimedean_char (ringChar K) hK v

end

end Towers.NumberTheory.Milne

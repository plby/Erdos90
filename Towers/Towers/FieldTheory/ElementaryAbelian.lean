import Towers.FieldTheory.Blueprint


namespace Towers
namespace TBluepr

/--
The elementary abelian target has exponent `3`.
-/
theorem elementary_abelian_one
    (a : ElementaryAbelianGroup 5) :
    a ^ (3 : ℕ) = 1 := by
  ext i
  simp only [Pi.pow_apply, toAdd_pow, nsmul_eq_mul, Nat.cast_ofNat, Pi.one_apply, toAdd_one,
    mul_eq_zero, toAdd_eq_zero]
  left
  change ((3 : ℕ) : ZMod 3) = 0
  decide

/--
Consequently every positive power `3^j` annihilates the elementary abelian
target.
-/
theorem elementary_abelian_pos
    (a : ElementaryAbelianGroup 5)
    {j : ℕ}
    (hj : 1 ≤ j) :
    a ^ (3 ^ j) = 1 := by
  cases j with
  | zero =>
      omega
  | succ j =>
      have hpow : 3 ^ (j + 1) = 3 * 3 ^ j := by
        rw [pow_succ']
      rw [hpow, pow_mul]
      rw [elementary_abelian_one]
      rw [one_pow]

end TBluepr
end Towers

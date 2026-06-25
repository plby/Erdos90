import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Milne, Algebraic Number Theory, the cyclotomic factorization in Theorem 6.8
-/

namespace Towers.NumberTheory.Milne

open Polynomial

/-- The roots of `X^n - 1` are the powers of a primitive `n`th root. -/
theorem x_sub_powers
    {K : Type*} [Field K] {n : ℕ} {zeta : K}
    (hzeta : IsPrimitiveRoot zeta n) (hn : 0 < n) :
    (X : K[X]) ^ n - 1 =
      ((Multiset.range n).map fun i ↦ X - C (zeta ^ i)).prod := by
  have hroots :
      ((X : K[X]) ^ n - C 1).roots =
        (Multiset.range n).map (zeta ^ ·) := by
    change nthRoots n (1 : K) = _
    rw [hzeta.nthRoots_eq (show (1 : K) ^ n = 1 by simp)]
    simp
  have hcard :
      Multiset.card (((X : K[X]) ^ n - C 1).roots) =
        ((X : K[X]) ^ n - C 1).natDegree := by
    rw [hroots, Multiset.card_map, Multiset.card_range, natDegree_X_pow_sub_C]
  have hprod :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (monic_X_pow_sub_C (1 : K) hn.ne') hcard
  rw [hroots, Multiset.map_map] at hprod
  simpa only [C_1] using hprod.symm

/-- For odd `n`, `X^n + 1` factors as the product of `X + ζ^i`. -/
theorem x_primitive_powers
    {K : Type*} [Field K] {n : ℕ} {zeta : K}
    (hzeta : IsPrimitiveRoot zeta n) (hn : Odd n) :
    (X : K[X]) ^ n + 1 =
      ((Multiset.range n).map fun i ↦ X + C (zeta ^ i)).prod := by
  have hnpos : 0 < n := hn.pos
  have hroots :
      ((X : K[X]) ^ n - C (-1)).roots =
        (Multiset.range n).map fun i ↦ -(zeta ^ i) := by
    change nthRoots n (-1 : K) = _
    rw [hzeta.nthRoots_eq (show (-1 : K) ^ n = -1 by simpa using hn.neg_one_pow)]
    simp
  have hcard :
      Multiset.card (((X : K[X]) ^ n - C (-1)).roots) =
        ((X : K[X]) ^ n - C (-1)).natDegree := by
    rw [hroots, Multiset.card_map, Multiset.card_range, natDegree_X_pow_sub_C]
  have hprod :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (monic_X_pow_sub_C (-1 : K) hnpos.ne') hcard
  rw [hroots, Multiset.map_map] at hprod
  simpa [Function.comp_def] using hprod.symm

/-- The homogeneous factorization used in Milne's proof of Theorem 6.8. -/
theorem primitive_root_powers
    {K : Type*} [Field K] {n : ℕ} {zeta x y : K}
    (hzeta : IsPrimitiveRoot zeta n) (hn : Odd n) :
    x ^ n + y ^ n =
      ((Multiset.range n).map fun i ↦ x + zeta ^ i * y).prod := by
  by_cases hy : y = 0
  · subst y
    simp [hn.pos.ne']
  have hpoly := congrArg (eval (x / y))
    (x_primitive_powers hzeta hn)
  simp only [eval_add, eval_pow, eval_X, eval_one, eval_multiset_prod,
    Multiset.map_map, eval_C, Function.comp_apply] at hpoly
  calc
    x ^ n + y ^ n = y ^ n * ((x / y) ^ n + 1) := by
      rw [div_pow, mul_add, mul_one, mul_div_cancel₀ _ (pow_ne_zero n hy)]
    _ = y ^ n *
        ((Multiset.range n).map fun i ↦ x / y + zeta ^ i).prod := by rw [hpoly]
    _ = ((Multiset.range n).map fun i ↦
        y * (x / y + zeta ^ i)).prod := by
      rw [Multiset.prod_map_mul]
      simp
    _ = ((Multiset.range n).map fun i ↦ x + zeta ^ i * y).prod := by
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro i _
      field_simp [hy]

end Towers.NumberTheory.Milne

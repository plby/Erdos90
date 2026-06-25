import Towers.ClassField.KummerTheory.PowerClasses
import Mathlib.FieldTheory.KummerExtension

/-!
# Chapter VIII, Section 1: local and global powers

Theorem 1.1 passes from local roots to completely split primes in a radical
extension and then invokes Chebotarev.  The project does not yet have the
completion/root-to-splitting-prime bridge needed to state that argument
without adding new interfaces.  The Kummer polynomial lemma and the two
coprime-exponent reductions used in Theorem 1.4 are exact and are recorded
here.
-/

namespace Towers.CField.LGPowers

open Polynomial

noncomputable section

/-- If a field contains a primitive `n`th root of unity, one root of
`X ^ n - a` forces the polynomial to split.  This is the first algebraic step
in Theorem 1.1. -/
theorem radical_splits_root
    {k : Type*} [Field k] {n : ℕ} {zeta alpha a : k}
    (hzeta : IsPrimitiveRoot zeta n) (halpha : alpha ^ n = a) :
    (X ^ n - C a).Splits :=
  X_pow_sub_C_splits_of_isPrimitiveRoot hzeta halpha

/-- An element killed by two coprime exponents is trivial. -/
theorem one_coprime_pow
    {G : Type*} [Group G] {m n : ℕ} (hmn : m.Coprime n)
    {x : G} (hm : x ^ m = 1) (hn : x ^ n = 1) : x = 1 := by
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hmn
    (orderOf_dvd_iff_pow_eq_one.mpr hm)
    (orderOf_dvd_iff_pow_eq_one.mpr hn)

/-- **Theorem VIII.1.4, Step 1.** If `m` and `n` are coprime and a group
element is both an `m`th and an `n`th power, it is an `(m*n)`th power. -/
theorem power_mul_coprime
    {G : Type*} [CommGroup G] {m n : ℕ} (hmn : m.Coprime n)
    {a : G} (hm : ∃ b : G, b ^ m = a) (hn : ∃ c : G, c ^ n = a) :
    ∃ d : G, d ^ (m * n) = a := by
  let H : Subgroup G := (powMonoidHom (m * n) : G →* G).range
  let q : G ⧸ H := QuotientGroup.mk' H a
  have hqm : q ^ m = 1 := by
    rcases hn with ⟨c, rfl⟩
    apply (QuotientGroup.eq_one_iff _).2
    change (c ^ n) ^ m ∈ H
    refine ⟨c, ?_⟩
    change c ^ (m * n) = (c ^ n) ^ m
    rw [mul_comm m n, pow_mul]
  have hqn : q ^ n = 1 := by
    rcases hm with ⟨b, rfl⟩
    apply (QuotientGroup.eq_one_iff _).2
    change (b ^ m) ^ n ∈ H
    refine ⟨b, ?_⟩
    change b ^ (m * n) = (b ^ m) ^ n
    rw [pow_mul]
  have hq : q = 1 := one_coprime_pow hmn hqm hqn
  have ha : a ∈ H := (QuotientGroup.eq_one_iff _).1 hq
  rcases ha with ⟨d, hd⟩
  exact ⟨d, hd⟩

/-- The quotient-group argument in Step 3 of Theorem 1.4.  A power class
killed by `p ^ r` and by an exponent coprime to `p` is trivial. -/
theorem power_class_coprime
    {K : Type*} [Field K] {p r d : ℕ} (hdp : d.Coprime p)
    (x : KTheory.PowerClassGroup K (p ^ r))
    (hd : x ^ d = 1) : x = 1 := by
  apply one_coprime_pow (hdp.pow_right r)
  · exact hd
  · exact KTheory.power_class_pow (p ^ r) x

end

end Towers.CField.LGPowers

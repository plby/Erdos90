import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Lemma VII.7.3: multiplicative-order growth

For distinct rational primes `p` and `ell`, the order of `p` modulo a
sufficiently high power of `ell` is divisible by any prescribed power of
`ell`.  This is the unramified local-degree growth used in the cyclotomic
construction of Lemma VII.7.3.

The proof does not require the full lifting-the-exponent formula.  Choose a
fixed exponent `d` for which `ell ∣ p ^ d - 1`, and write
`p ^ d - 1 = ell ^ m * b` with `ell ∤ b`.  Mathlib's computation of the
order of `1 + ell ^ m * b` modulo `ell ^ (a + m)` gives order `ell ^ a`.
This element is `p ^ d`, whose order divides the order of `p`.
-/

namespace Towers.CField.CBrauer

open scoped Nat

/-- Multiplicative order can only increase when the modulus is raised from
one power of `ell` to a higher power. -/
theorem order_cast_dvd
    (p ell r s : ℕ) (hrs : r ≤ s) :
    orderOf (p : ZMod (ell ^ r)) ∣
      orderOf (p : ZMod (ell ^ s)) := by
  let f : ZMod (ell ^ s) →* ZMod (ell ^ r) :=
    (ZMod.castHom (pow_dvd_pow ell hrs) (ZMod (ell ^ r))).toMonoidHom
  have h := orderOf_map_dvd f (p : ZMod (ell ^ s))
  have hf : f (p : ZMod (ell ^ s)) = (p : ZMod (ell ^ r)) := by
    change ZMod.cast (p : ZMod (ell ^ s)) = (p : ZMod (ell ^ r))
    exact ZMod.cast_natCast (pow_dvd_pow ell hrs) p
  rwa [hf] at h

/-- The common order-growth argument, parameterized by an exponent `d`
for which `ell ∣ p ^ d - 1`.  The numerical hypothesis on the exact
`ell`-adic exponent is precisely the hypothesis of
`ZMod.orderOf_one_add_mul_prime_pow`; it is automatic for odd `ell`, and
for `ell = 2` after taking `d = 2`. -/
theorem dvd_order_sub
    (p ell d a : ℕ) (hell : ell.Prime)
    (hpow : 1 < p ^ d) (hellDvd : ell ∣ p ^ d - 1)
    (hvaluation :
      padicValNat ell (p ^ d - 1) + 2 ≤
        ell * padicValNat ell (p ^ d - 1)) :
    ∃ r : ℕ, ell ^ a ∣ orderOf (p : ZMod (ell ^ r)) := by
  letI : Fact ell.Prime := ⟨hell⟩
  let N := p ^ d - 1
  let m := padicValNat ell N
  let b := N.divMaxPow ell
  have hN0 : N ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt hpow
  have hm0 : m ≠ 0 := by
    apply Nat.ne_of_gt
    exact one_le_padicValNat_of_dvd hN0 hellDvd
  have hb : ¬ell ∣ b := by
    exact Nat.not_dvd_divMaxPow hell.one_lt hN0
  have hdecomp : ell ^ m * b = N := by
    exact Nat.pow_padicValNat_mul_divMaxPow ell N
  have hpDecomp : p ^ d = 1 + ell ^ m * b := by
    dsimp only [N] at hdecomp hN0 ⊢
    omega
  have hbInt : ¬(ell : ℤ) ∣ (b : ℤ) := by
    exact_mod_cast hb
  refine ⟨a + m, ?_⟩
  have horder :
      orderOf (1 + ell ^ m * (b : ℤ) : ZMod (ell ^ (a + m))) =
        ell ^ a :=
    ZMod.orderOf_one_add_mul_prime_pow hell m hm0 hvaluation b hbInt a
  have hpCast :
      (p : ZMod (ell ^ (a + m))) ^ d =
        (1 + ell ^ m * (b : ℤ) : ZMod (ell ^ (a + m))) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Int.cast_natCast] using
      congrArg (fun n : ℕ ↦ (n : ZMod (ell ^ (a + m)))) hpDecomp
  calc
    ell ^ a = orderOf ((p : ZMod (ell ^ (a + m))) ^ d) := by
      rw [hpCast, horder]
    _ ∣ orderOf (p : ZMod (ell ^ (a + m))) := orderOf_pow_dvd d

/-- For distinct primes `p` and odd `ell`, arbitrary `ell`-power
divisibility occurs in the order of `p` modulo a sufficiently high power
of `ell`. -/
theorem odd_dvd_order
    (p ell a : ℕ) (hp : p.Prime) (hell : ell.Prime)
    (hell2 : ell ≠ 2) (hpell : p ≠ ell) :
    ∃ r : ℕ, ell ^ a ∣ orderOf (p : ZMod (ell ^ r)) := by
  letI : Fact ell.Prime := ⟨hell⟩
  have hcoprime : p.Coprime ell :=
    (Nat.coprime_primes hp hell).2 hpell
  have hdpos : 0 < ell - 1 := Nat.sub_pos_of_lt hell.one_lt
  have hpow : 1 < p ^ (ell - 1) :=
    one_lt_pow₀ hp.one_lt (Nat.ne_of_gt hdpos)
  have hfermat : p ^ (ell - 1) ≡ 1 [MOD ell] := by
    simpa [Nat.totient_prime hell] using
      Nat.ModEq.pow_totient hcoprime
  have hellDvd : ell ∣ p ^ (ell - 1) - 1 :=
    (Nat.modEq_iff_dvd' hpow.le).1 hfermat.symm
  have hmpos : 0 < padicValNat ell (p ^ (ell - 1) - 1) :=
    one_le_padicValNat_of_dvd (Nat.sub_ne_zero_of_lt hpow) hellDvd
  have hell3 : 3 ≤ ell := by
    omega
  apply dvd_order_sub
    p ell (ell - 1) a hell hpow hellDvd
  calc
    padicValNat ell (p ^ (ell - 1) - 1) + 2 ≤
        3 * padicValNat ell (p ^ (ell - 1) - 1) := by omega
    _ ≤ ell * padicValNat ell (p ^ (ell - 1) - 1) :=
      Nat.mul_le_mul_right _ hell3

/-- For an odd prime `p`, arbitrary two-power divisibility occurs in the
order of `p` modulo a sufficiently high power of two. -/
theorem two_dvd_order
    (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ r : ℕ, 2 ^ a ∣ orderOf (p : ZMod (2 ^ r)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpow : 1 < p ^ 2 := by
    exact one_lt_pow₀ hp.one_lt (by norm_num)
  have hfourDvd : 2 ^ 2 ∣ p ^ 2 - 1 := by
    have heightDvd : 8 ∣ p ^ 2 - 1 :=
      Nat.eight_dvd_sq_sub_one_of_odd hpodd
    exact (by norm_num : 2 ^ 2 ∣ 8).trans heightDvd
  have hm2 : 2 ≤ padicValNat 2 (p ^ 2 - 1) := by
    exact (padicValNat_dvd_iff_le
      (Nat.sub_ne_zero_of_lt hpow)).1 hfourDvd
  apply dvd_order_sub
    p 2 2 a Nat.prime_two hpow
    ((by norm_num : 2 ∣ 2 ^ 2).trans hfourDvd)
  omega

end Towers.CField.CBrauer

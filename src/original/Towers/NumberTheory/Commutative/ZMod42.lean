import Mathlib

/-!
# Milne, Algebraic Number Theory, Example 1.13(b)

Milne illustrates prime-ideal correspondence by listing the prime ideals of several elementary
rings. This file records the finite example `ℤ / 42ℤ` exactly.
-/

namespace Towers.NumberTheory.Milne

private theorem zmod_span_prime {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (Ideal.span ({(p : ZMod n)} : Set (ZMod n))).IsPrime := by
  let f : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    Ideal.isPrime_int_iff.mpr (Or.inr ⟨p, hp, rfl⟩)
  have hk : RingHom.ker f ≤ Ideal.span ({(p : ℤ)} : Set ℤ) := by
    rw [ZMod.ker_intCastRingHom, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_span_singleton]
    exact_mod_cast hpn
  have hprime := Ideal.map_isPrime_of_surjective (f := f) ZMod.intCast_surjective hk
  simpa [Ideal.map_span, f] using hprime

/-- The prime ideals of `ℤ / 42ℤ` are precisely `(2)`, `(3)`, and `(7)`.
This is the last list in Example 1.13(b). -/
theorem zmod_42_prime (I : Ideal (ZMod 42)) :
    I.IsPrime ↔
      I = Ideal.span ({2} : Set (ZMod 42)) ∨
      I = Ideal.span ({3} : Set (ZMod 42)) ∨
      I = Ideal.span ({7} : Set (ZMod 42)) := by
  let f : ℤ →+* ZMod 42 := Int.castRingHom (ZMod 42)
  constructor
  · intro hI
    letI : I.IsPrime := hI
    have hcomap : (I.comap f).IsPrime := Ideal.comap_isPrime f I
    have h42 : (42 : ℤ) ∈ I.comap f := by
      change ((42 : ℤ) : ZMod 42) ∈ I
      rw [show ((42 : ℤ) : ZMod 42) = 0 by decide]
      exact I.zero_mem
    rcases Ideal.isPrime_int_iff.mp hcomap with hbot | ⟨p, hp, heq⟩
    · rw [hbot] at h42
      norm_num at h42
    · have hpdivInt : (p : ℤ) ∣ (42 : ℤ) := by
        rw [← Ideal.mem_span_singleton, ← heq]
        exact h42
      have hpdiv : p ∣ 42 := Int.natCast_dvd_natCast.mp hpdivInt
      have hmap : I = Ideal.span ({(p : ZMod 42)} : Set (ZMod 42)) := by
        calc
          I = (I.comap f).map f :=
            (Ideal.map_comap_of_surjective f ZMod.intCast_surjective I).symm
          _ = (Ideal.span ({(p : ℤ)} : Set ℤ)).map f := by rw [heq]
          _ = Ideal.span ({(p : ZMod 42)} : Set (ZMod 42)) := by
            simp [Ideal.map_span, f]
      have hpFactor : p ∣ 2 * (3 * 7) := by simpa using hpdiv
      rcases hp.dvd_mul.mp hpFactor with hp2 | hp37
      · left
        rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2] at hmap
        exact hmap
      · rcases hp.dvd_mul.mp hp37 with hp3 | hp7
        · right; left
          rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3] at hmap
          exact hmap
        · right; right
          rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp7] at hmap
          exact hmap
  · rintro (rfl | rfl | rfl)
    · exact zmod_span_prime (by norm_num) (by norm_num)
    · exact zmod_span_prime (by norm_num) (by norm_num)
    · exact zmod_span_prime (by norm_num) (by norm_num)

end Towers.NumberTheory.Milne

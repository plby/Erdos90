import Mathlib

/-!
# Class Field Theory, Chapter I, Example 4.13

Milne's example uses a cyclic extension of degree four whose maximal
unramified subextension has degree two.  If the extension were a compositum
of that unramified quadratic extension and a totally ramified quadratic
extension, its Galois group would be a product of two groups of order two,
contradicting cyclicity.

The local-field and cyclotomic-extension assertions require the local
Kronecker--Weber infrastructure developed earlier in the section.  This file
records the elementary numerical and finite-group calculations on which the
final contradiction rests.
-/

namespace Towers.CField.Ramification

/-- The numerical choice in Example 4.13: `624 = 5^4 - 1`. -/
theorem five_four_sub : 5 ^ 4 - 1 = 624 := by
  norm_num

/-- The ambient cyclotomic level in Example 4.13 is `5 * 624 = 3120`. -/
theorem five_mul_624 : 5 * 624 = 3120 := by
  norm_num

/-- The group-theoretic contradiction in Example 4.13: a cyclic group of
order four is not the product of two cyclic groups of order two. -/
theorem not_nonempty_zmod :
    ¬ Nonempty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  rintro ⟨e⟩
  have hzmod_two (x : ZMod 2) : (2 : ℕ) • x = 0 := by
    have htwozero : (2 : ZMod 2) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod 2) 2 2).mpr dvd_rfl
    rw [two_nsmul, ← two_mul, htwozero, zero_mul]
  have htwo : (2 : ℕ) • e (1 : ZMod 4) = 0 := by
    apply Prod.ext
    · simpa using hzmod_two (e 1).1
    · simpa using hzmod_two (e 1).2
  have hone : (2 : ℕ) • (1 : ZMod 4) = 0 := by
    apply e.injective
    rw [map_zero, map_nsmul, htwo]
  have : (2 : ZMod 4) = 0 := by
    simpa using hone
  have hdvd : 4 ∣ 2 := (CharP.cast_eq_zero_iff (ZMod 4) 4 2).mp this
  omega

end Towers.CField.Ramification

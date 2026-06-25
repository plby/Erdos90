import Towers.NumberTheory.Quadratic.PrimeRepresentations

/-!
# Chapter VIII, Section 10, Example 10.1

The Hecke character and cubic-residue-symbol construction in the source needs
idele and Hecke-character interfaces that are not yet available.  The small
integral normalization at its algebraic core can nevertheless be proved from
Milne's representation theorem for primes congruent to one modulo three.
-/

namespace Towers.CField.ALSeries

open Towers.NumberTheory.Milne

/-- If an integer is represented by `x² + 3y²`, and one of the three natural
linear combinations is divisible by three, then the representation can be
normalized to `4p = A² + 27B²`. -/
theorem four_twenty_seven
    {p x y : ℤ} (hrep : p = x ^ 2 + 3 * y ^ 2)
    (hdiv : (3 : ℤ) ∣ y ∨ (3 : ℤ) ∣ x + y ∨ (3 : ℤ) ∣ x - y) :
    ∃ A B : ℤ, 4 * p = A ^ 2 + 27 * B ^ 2 := by
  rcases hdiv with hy | hxy | hxy
  · rcases hy with ⟨k, rfl⟩
    refine ⟨2 * x, 2 * k, ?_⟩
    nlinarith
  · rcases hxy with ⟨k, hk⟩
    refine ⟨x - 3 * y, k, ?_⟩
    have hk2 := congrArg (fun z : ℤ ↦ z ^ 2) hk
    nlinarith
  · rcases hxy with ⟨k, hk⟩
    refine ⟨x + 3 * y, k, ?_⟩
    have hk2 := congrArg (fun z : ℤ ↦ z ^ 2) hk
    nlinarith

/-- Modulo three, after `x² = 1`, one of `y`, `x+y`, or `x-y` vanishes. -/
private theorem modThree_normalization (x y : ℤ)
    (hx : (x : ZMod 3) ^ 2 = 1) :
    (3 : ℤ) ∣ y ∨ (3 : ℤ) ∣ x + y ∨ (3 : ℤ) ∣ x - y := by
  have hfinite : ∀ a b : ZMod 3, a ^ 2 = 1 →
      b = 0 ∨ a + b = 0 ∨ a - b = 0 := by decide
  rcases hfinite (x : ZMod 3) (y : ZMod 3) hx with hy | hxy | hxy
  · exact Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hy)
  · exact Or.inr <| Or.inl <|
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) 3).mp (by simpa using hxy)
  · exact Or.inr <| Or.inr <|
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) 3).mp (by simpa using hxy)

/-- **Example 10.1, integral normalization.** If a prime is one modulo three,
then it admits the form `4p = A² + 27B²` used to choose a primary factor in
the Eisenstein integers. -/
theorem sq_twenty_seven
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1) :
    ∃ A B : ℤ, 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2 := by
  have hp3 : p ≠ 3 := by
    intro hp
    subst p
    norm_num at hpmod
  obtain ⟨x, y, hrep⟩ :=
    (sq_add_mul p hp3).mpr hpmod
  have hpcast : (p : ZMod 3) = 1 := by
    simp [← ZMod.natCast_mod p 3, hpmod]
  have hx : (x : ZMod 3) ^ 2 = 1 := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hrep
    have hcast' : (p : ZMod 3) = (x : ZMod 3) ^ 2 := by
      calc
        (p : ZMod 3) = (x : ZMod 3) ^ 2 + 3 * (y : ZMod 3) ^ 2 := by
          simpa using hcast
        _ = (x : ZMod 3) ^ 2 := by
          have hthree : (3 : ZMod 3) = 0 := by decide
          rw [hthree, zero_mul, add_zero]
    calc
      (x : ZMod 3) ^ 2 = (p : ZMod 3) := hcast'.symm
      _ = 1 := hpcast
  exact four_twenty_seven hrep
    (modThree_normalization x y hx)

end Towers.CField.ALSeries

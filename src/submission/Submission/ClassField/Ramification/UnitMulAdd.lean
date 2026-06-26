import Mathlib.RingTheory.Valuation.Integers
import Submission.NumberTheory.Locals.RamificationGroups

/-!
# Class Field Theory, Chapter I, Proposition 4.1

The concrete Lubin--Tate fields `K_{π,n}` are not yet available in the
project.  This file proves the three algebraic and valuation-theoretic steps
in Milne's proof that do not require those fields: the factorization of one
successive torsion parameter, iteration of that factorization, and the exact
lower ramification break obtained from a uniformizer-difference formula.
-/

namespace Submission.CField.Ramification

open Submission.NumberTheory.Milne

noncomputable section

/-- The one-step calculation in Proposition 4.1.  If
`v (π / x^(q-1)) < 1`, the parenthesized factor in
`π*x + x^q = x^q * (1 + π/x^(q-1))` is a unit of the valuation ring. -/
theorem unit_pow_add
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (pi x : L) (q : ℕ) (hq : 0 < q) (hx : x ≠ 0)
    (hsmall : v (pi / x ^ (q - 1)) < 1) :
    ∃ u : v.integerˣ,
      pi * x + x ^ q = x ^ q * (((u : v.integer) : L)) := by
  let y : v.integer :=
    ⟨1 + pi / x ^ (q - 1),
      (v.mem_integer_iff _).mpr
        (le_of_eq (v.map_one_add_of_lt hsmall))⟩
  have hy : v ((y : v.integer) : L) = 1 :=
    v.map_one_add_of_lt hsmall
  let u : v.integerˣ :=
    ((Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers v)).mpr
        (by simpa only [Algebra.algebraMap_ofSubsemiring_apply] using hy)).unit
  refine ⟨u, ?_⟩
  change pi * x + x ^ q = x ^ q * (1 + pi / x ^ (q - 1))
  rw [mul_add, mul_one, add_comm]
  congr 1
  rw [← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero _ hx)).mpr
  calc
    (pi * x) * x ^ (q - 1) = pi * (x ^ (q - 1) * x) := by
      ac_rfl
    _ = pi * x ^ q := by
      rw [pow_sub_one_mul (Nat.ne_of_gt hq)]
    _ = x ^ q * pi := mul_comm _ _

/-- Iterating identities `x_j = x_{j+1}^q * unit` gives the exponent `q^i`
in Milne's formula `π_{n-i} = π_n^(q^i) * unit`. -/
theorem unit_iterate_factor
    {R : Type*} [CommRing R] (x : ℕ → R) (q m i : ℕ)
    (hstep : ∀ j, ∃ u : Rˣ, x j = x (j + 1) ^ q * (u : R)) :
    ∃ u : Rˣ, x m = x (m + i) ^ (q ^ i) * (u : R) := by
  induction i with
  | zero =>
      exact ⟨1, by simp⟩
  | succ i ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨w, hw⟩ := hstep (m + i)
      refine ⟨w ^ (q ^ i) * u, ?_⟩
      rw [hu, hw, mul_pow, ← pow_mul]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, pow_succ,
        Nat.add_assoc]
      rw [Nat.mul_comm q (q ^ i)]
      ring

/-- If an automorphism moves a uniformizer by exactly its `e`th power times
a unit, then its lower ramification break is exactly `e - 1`.  This is the
"by definition" step at the end of Milne's proof of Proposition 4.1. -/
theorem break_uniformizer_difference
    {A B G : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Group G] [MulSemiringAction G B]
    [SMulCommClass G A B]
    (Pi : B) (hPi : Irreducible Pi)
    (hgen : Algebra.adjoin A ({Pi} : Set B) = ⊤)
    (sigma : G) {e : ℕ} (he : 0 < e) (u : Bˣ)
    (hdiff : sigma • Pi - Pi = Pi ^ e * (u : B)) :
    sigma ∈ idealRamificationGroup (Ideal.span {Pi}) G (e - 1) ∧
      sigma ∉ idealRamificationGroup (Ideal.span {Pi}) G e := by
  constructor
  · rw [ideal_ramification_uniformizer
      (Ideal.span {Pi}) Pi hgen]
    rw [hdiff, Ideal.span_singleton_pow, Nat.sub_add_cancel he]
    exact Ideal.mem_span_singleton.mpr ⟨u, rfl⟩
  · rw [ideal_ramification_uniformizer
      (Ideal.span {Pi}) Pi hgen]
    intro hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have hassoc : Associated (sigma • Pi - Pi) (Pi ^ e) := by
      rw [hdiff]
      exact associated_mul_unit_left _ _ u.isUnit
    have hdiv : Pi ^ (e + 1) ∣ Pi ^ e :=
      hassoc.dvd_iff_dvd_right.mp hmem
    have : e + 1 ≤ e :=
      (pow_dvd_pow_iff hPi.ne_zero hPi.not_isUnit).mp hdiv
    omega

end

end Submission.CField.Ramification

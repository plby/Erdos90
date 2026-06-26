import Submission.NumberTheory.Locals.NewtonRootLifting
import Mathlib.NumberTheory.Padics.RingHoms


/-!
# Milne, Chapter 7, Exercise 7-3

We classify the integers `a` for which `7 X^2 = a` is soluble in the
`7`-adic integers.  The nonzero ones are exactly

`a = 7^(2m+1) b`,

where `m ≥ 0`, `7 ∤ b`, and the residue of `b` modulo `7` is one of
`1, 2, 4`.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

noncomputable section

local instance sevenPrimeFact_3 : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem padic_sq_seven
    {b : ℤ} (h7b : ¬(7 : ℤ) ∣ b) (hb : IsSquare (b : ZMod 7)) :
    ∃ y : ℤ_[7], y ^ 2 = b := by
  let F : ℤ[X] := X ^ 2 - C b
  obtain ⟨c, hc⟩ := hb
  let r : ℤ := c.val
  have hcr : (r : ZMod 7) = c := by
    simp [r]
  have hz : ((r ^ 2 : ℤ) : ZMod 7) = (b : ZMod 7) := by
    rw [Int.cast_pow, hcr]
    simpa [pow_two] using hc.symm
  have hdiv : (7 : ℤ) ∣ r ^ 2 - b := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using sub_eq_zero.mpr hz)
  have hF : F.aeval (r : ℤ_[7]) = ((r ^ 2 - b : ℤ) : ℤ_[7]) := by
    simp [F, aeval_def]
  have hFd : F.derivative.aeval (r : ℤ_[7]) = ((2 * r : ℤ) : ℤ_[7]) := by
    simp [F, aeval_def]
  have hr7 : ¬(7 : ℤ) ∣ r := by
    intro h
    have hczero : c = 0 := by
      exact hcr.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd r 7).2 h)
    apply h7b
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).1 (by simpa [hczero] using hc)
  have hderiv : ‖F.derivative.aeval (r : ℤ_[7])‖ = 1 := by
    rw [hFd, PadicInt.norm_intCast_eq_one_iff]
    have hrnonneg : 0 ≤ r := Int.natCast_nonneg _
    have hrlt : r < 7 := by
      change (c.val : ℤ) < 7
      exact_mod_cast c.val_lt
    interval_cases r
    case «0» => exact (hr7 (by norm_num)).elim
    all_goals decide
  have hvalue : ‖F.aeval (r : ℤ_[7])‖ < 1 := by
    rw [hF, PadicInt.norm_intCast_lt_one_iff]
    exact hdiv
  have hnewton :
      ‖F.aeval (r : ℤ_[7])‖ < ‖F.derivative.aeval (r : ℤ_[7])‖ ^ 2 := by
    simpa [hderiv] using hvalue
  obtain ⟨y, hy, -, -⟩ := padic_newton_root F r hnewton
  refine ⟨y, ?_⟩
  have hy' : y ^ 2 - (b : ℤ_[7]) = 0 := by simpa [F] using hy
  exact sub_eq_zero.mp hy'

/-- Milne, Exercise 7-3, integer part: the complete classification of
solutions to `7 X^2 = a` in `ℤ_[7]`. -/
theorem padicInt (a : ℤ) :
    (∃ x : ℤ_[7], 7 * x ^ 2 = a) ↔
      a = 0 ∨
        ∃ m : ℕ, ∃ b : ℤ,
          a = 7 ^ (2 * m + 1) * b ∧
            ¬(7 : ℤ) ∣ b ∧
              IsSquare (b : ZMod 7) := by
  constructor
  · rintro ⟨x, hx⟩
    by_cases hx0 : x = 0
    · left
      subst x
      simpa using hx.symm
    right
    let m := x.valuation
    have ha0 : a ≠ 0 := by
      intro ha
      rw [ha, Int.cast_zero] at hx
      exact hx0 (by simpa using (mul_eq_zero.mp hx).resolve_left (by norm_num))
    have hval : padicValInt 7 a = 2 * m + 1 := by
      have hv := congrArg (fun z : ℤ_[7] ↦ (z : ℚ_[7]).valuation) hx
      have hseven : (7 : ℤ_[7]).valuation = 1 := by
        change ((7 : ℕ) : ℤ_[7]).valuation = 1
        exact PadicInt.valuation_p
      simp only [PadicInt.coe_mul, PadicInt.coe_pow, ne_eq, PadicInt.coe_eq_zero,
        OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff, hx0, Padic.valuation_mul, PadicInt.valuation_coe,
          Padic.valuation_pow,
        Nat.cast_ofNat, PadicInt.coe_intCast, Padic.valuation_intCast] at hv
      rw [hseven] at hv
      have hv' : (1 : ℤ) + 2 * (m : ℤ) = (padicValInt 7 a : ℤ) := by
        simpa [m] using hv
      have hv'' : padicValInt 7 a = 1 + 2 * m := by exact_mod_cast hv'.symm
      omega
    have hdvd : (7 : ℤ) ^ (2 * m + 1) ∣ a := by
      exact (padicValInt_dvd_iff (p := 7) (2 * m + 1) a).2 (Or.inr hval.ge)
    obtain ⟨b, hab⟩ := hdvd
    refine ⟨m, b, ?_, ?_, ?_⟩
    · exact hab
    · intro h7b
      have hmore : (7 : ℤ) ^ (2 * m + 2) ∣ a := by
        obtain ⟨c, rfl⟩ := h7b
        refine ⟨c, ?_⟩
        rw [hab]
        ring
      have hm := (padicValInt_dvd_iff (p := 7) (2 * m + 2) a).1 hmore
      rcases hm with hzero | hle
      · exact ha0 hzero
      · omega
    · have hunit :
          ((b : ℤ_[7])) = (PadicInt.unitCoeff hx0 : ℤ_[7]) ^ 2 := by
        have hfactor := PadicInt.unitCoeff_spec hx0
        let u : ℤ_[7] := PadicInt.unitCoeff hx0
        have hfactor' : x = u * (7 : ℤ_[7]) ^ m := by simpa [u, m] using hfactor
        have hcast := congrArg (fun z : ℤ ↦ (z : ℤ_[7])) hab
        have hpow_ne : (7 : ℤ_[7]) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        apply mul_left_cancel₀ hpow_ne
        calc
          (7 : ℤ_[7]) ^ (2 * m + 1) * b = (a : ℤ_[7]) := by
            simpa using hcast.symm
          _ = 7 * x ^ 2 := hx.symm
          _ = (7 : ℤ_[7]) ^ (2 * m + 1) *
                (PadicInt.unitCoeff hx0 : ℤ_[7]) ^ 2 := by
            change 7 * x ^ 2 = (7 : ℤ_[7]) ^ (2 * m + 1) * u ^ 2
            rw [hfactor']
            ring
      have hsquare : IsSquare (b : ZMod 7) := by
        refine ⟨PadicInt.toZMod (PadicInt.unitCoeff hx0 : ℤ_[7]), ?_⟩
        simpa [pow_two] using congrArg PadicInt.toZMod hunit
      exact hsquare
  · rintro (rfl | ⟨m, b, rfl, h7b, hb⟩)
    · exact ⟨0, by simp⟩
    obtain ⟨y, hy⟩ := padic_sq_seven h7b hb
    refine ⟨(7 : ℤ_[7]) ^ m * y, ?_⟩
    rw [mul_pow, hy]
    push_cast
    ring

/-- The valuation half of Milne's rational classification: a nonzero rational
represented by `7 X²` in `ℚ_[7]` has odd `7`-adic valuation. -/
theorem padic_valuation (a : ℚ)
    (h : ∃ x : ℚ_[7], 7 * x ^ 2 = a) :
    a = 0 ∨ Odd (padicValRat 7 a) := by
  obtain ⟨x, hx⟩ := h
  by_cases hx0 : x = 0
  · left
    subst x
    simpa using hx.symm
  right
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, Rat.cast_zero] at hx
    exact hx0 (by simpa using (mul_eq_zero.mp hx).resolve_left (by norm_num))
  have hv := congrArg Padic.valuation hx
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, hx0,
    Padic.valuation_mul,
    Padic.valuation_ofNat, Nat.one_lt_ofNat, padicValNat_base, Nat.cast_one, Padic.valuation_pow,
      Nat.cast_ofNat,
    Padic.valuation_ratCast] at hv
  refine ⟨x.valuation, ?_⟩
  omega

/-- Milne, Exercise 7-3, rational part.  Clearing the square of the denominator
reduces the question to the integral classification above. -/
theorem sevenAdicSquarespadic (a : ℚ) :
    (∃ x : ℚ_[7], 7 * x ^ 2 = a) ↔
      a = 0 ∨
        ∃ m : ℕ, ∃ b : ℤ,
          a.num * (a.den : ℤ) = 7 ^ (2 * m + 1) * b ∧
            ¬(7 : ℤ) ∣ b ∧
              IsSquare (b : ZMod 7) := by
  constructor
  · rintro ⟨x, hx⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    let y : ℚ_[7] := (a.den : ℚ_[7]) * x
    have hden : (a.den : ℚ_[7]) ≠ 0 := by
      exact_mod_cast a.den_nz
    have hnum : a.num ≠ 0 := Rat.num_ne_zero.mpr ha
    have ha_repr : (a : ℚ_[7]) = (a.num : ℚ_[7]) / (a.den : ℚ_[7]) := by
      norm_cast
      change a = Rat.divInt a.num (a.den : ℤ)
      exact (Rat.num_divInt_den a).symm
    have hy : 7 * y ^ 2 = ((a.num * (a.den : ℤ) : ℤ) : ℚ_[7]) := by
      calc
        7 * y ^ 2 = (a.den : ℚ_[7]) ^ 2 * (7 * x ^ 2) := by
          dsimp [y]
          ring
        _ = (a.den : ℚ_[7]) ^ 2 * (a : ℚ_[7]) := by rw [hx]
        _ = ((a.num * (a.den : ℤ) : ℤ) : ℚ_[7]) := by
          rw [ha_repr]
          field_simp [hden]
          push_cast
          ring
    have hy0 : y ≠ 0 := by
      exact mul_ne_zero hden (by
        intro hx0
        apply ha
        rw [hx0, pow_two, mul_zero] at hx
        exact_mod_cast hx.symm)
    have hyv : 0 ≤ y.valuation := by
      have hv : 0 ≤ Padic.valuation
          (((a.num * (a.den : ℤ) : ℤ) : ℚ_[7])) := by
        rw [Padic.valuation_intCast]
        exact_mod_cast (Nat.zero_le (padicValInt 7 (a.num * (a.den : ℤ))))
      rw [← hy] at hv
      simp [Padic.valuation_mul, Padic.valuation_pow, hy0] at hv
      omega
    let z : ℤ_[7] := ⟨y, (Padic.norm_le_one_iff_val_nonneg y).2 hyv⟩
    have hz : 7 * z ^ 2 = (a.num * (a.den : ℤ) : ℤ) := by
      apply Subtype.ext
      simpa [z] using hy
    exact (padicInt (a.num * (a.den : ℤ))).1 ⟨z, hz⟩ |>.resolve_left
      (mul_ne_zero hnum (by exact_mod_cast a.den_nz))
  · rintro (rfl | ⟨m, b, hab, h7b, hb⟩)
    · exact ⟨0, by simp⟩
    have ha0 : a ≠ 0 := by
      intro ha
      subst a
      simp only [Rat.num_ofNat, Rat.den_ofNat, Nat.cast_one, mul_one, zero_eq_mul, ne_eq,
        Nat.add_eq_zero_iff,
        mul_eq_zero, OfNat.ofNat_ne_zero, false_or, one_ne_zero, and_false, not_false_eq_true,
          pow_eq_zero_iff] at hab
      exact h7b (by simp [hab])
    obtain ⟨z, hz⟩ := (padicInt (a.num * (a.den : ℤ))).2
      (Or.inr ⟨m, b, hab, h7b, hb⟩)
    refine ⟨(z : ℚ_[7]) / (a.den : ℚ_[7]), ?_⟩
    have hden : (a.den : ℚ_[7]) ≠ 0 := by
      exact_mod_cast a.den_nz
    rw [show (a : ℚ_[7]) = (a.num : ℚ_[7]) / (a.den : ℚ_[7]) by
      norm_cast
      change a = Rat.divInt a.num (a.den : ℤ)
      exact (Rat.num_divInt_den a).symm]
    have hz' : 7 * (z : ℚ_[7]) ^ 2 =
        ((a.num * (a.den : ℤ) : ℤ) : ℚ_[7]) := by
      have := congrArg (fun w : ℤ_[7] ↦ (w : ℚ_[7])) hz
      simpa using this
    field_simp [hden]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hz'

end

end Submission.NumberTheory.Milne

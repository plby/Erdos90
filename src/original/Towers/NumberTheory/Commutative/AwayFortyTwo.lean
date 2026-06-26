import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Localization.Ideal

/-!
# Milne, Algebraic Number Theory, Example 1.13(b): prime ideals of `Z_42`

Here `Z_42` means `Z[1/42]`. Its prime ideals are zero and the extensions of `(p)` for
rational primes `p` not dividing `42`.
-/

namespace Towers.NumberTheory.Milne

open Ideal

abbrev IntegersAwayForty := Localization.Away (42 : ℤ)

private instance : IsDomain IntegersAwayForty :=
  IsLocalization.isDomain_of_le_nonZeroDivisors IntegersAwayForty
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (by norm_num : (42 : ℤ) ≠ 0))

private lemma disjoint_powers_forty {p : ℕ}
    (hp : p.Prime) (hp42 : ¬p ∣ 42) :
    Disjoint (Submonoid.powers (42 : ℤ) : Set ℤ)
      (Ideal.span ({(p : ℤ)} : Set ℤ) : Set ℤ) := by
  rw [Set.disjoint_left]
  intro x hxPowers hxSpan
  obtain ⟨n, rfl⟩ :=
    (Submonoid.mem_powers_iff x (42 : ℤ)).mp hxPowers
  have hpPow : (p : ℤ) ∣ (42 : ℤ) ^ n :=
    Ideal.mem_span_singleton.mp hxSpan
  have hpDvdFortyTwoInt : (p : ℤ) ∣ (42 : ℤ) :=
    Int.Prime.dvd_pow' hp hpPow
  exact hp42 (Int.natCast_dvd_natCast.mp hpDvdFortyTwoInt)

/-- The prime ideals of `Z[1/42]` are `(0)` and `(p)` for primes not dividing `42`. -/
theorem integers_away_forty
    (P : Ideal IntegersAwayForty) :
    P.IsPrime ↔
      P = ⊥ ∨
        ∃ p : ℕ, p.Prime ∧ ¬p ∣ 42 ∧
          P = Ideal.map (algebraMap ℤ IntegersAwayForty)
            (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  constructor
  · intro hP
    have hcontract :=
      (IsLocalization.isPrime_iff_isPrime_disjoint
        (Submonoid.powers (42 : ℤ)) IntegersAwayForty P).mp hP
    have hmapComap :
        Ideal.map (algebraMap ℤ IntegersAwayForty)
            (P.under ℤ) = P :=
      IsLocalization.map_under
        (Submonoid.powers (42 : ℤ)) IntegersAwayForty P
    rcases Ideal.isPrime_int_iff.mp hcontract.1 with hbot | ⟨p, hp, hpSpan⟩
    · left
      rw [hbot, Ideal.map_bot] at hmapComap
      exact hmapComap.symm
    · right
      refine ⟨p, hp, ?_, ?_⟩
      · intro hpDvd
        have hfortyTwoMem : (42 : ℤ) ∈
            P.under ℤ := by
          rw [hpSpan, Ideal.mem_span_singleton]
          exact_mod_cast hpDvd
        exact Set.disjoint_left.mp hcontract.2
          (Submonoid.mem_powers (42 : ℤ)) hfortyTwoMem
      · rw [← hpSpan]
        exact hmapComap.symm
  · rintro (rfl | ⟨p, hp, hp42, rfl⟩)
    · exact Ideal.isPrime_bot
    · exact IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers (42 : ℤ)) IntegersAwayForty
        (Ideal.span ({(p : ℤ)} : Set ℤ))
        (Ideal.isPrime_int_iff.mpr (Or.inr ⟨p, hp, rfl⟩))
        (disjoint_powers_forty hp hp42)

end Towers.NumberTheory.Milne

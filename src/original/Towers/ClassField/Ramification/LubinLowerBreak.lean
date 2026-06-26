import Towers.NumberTheory.Locals.RamificationGroups

/-!
# Class Field Theory, Chapter I, Example 4.2

The lower ramification breaks of the Lubin--Tate extension `K_{pi,n}/K` occur
at `q^i - 1`.  Between consecutive breaks the relevant group index is
`(q - 1)q^i`, exactly the length of that interval.  Consequently every
segment raises the Herbrand function by one, so the lower break `q^i - 1`
corresponds to upper break `i`.

The ramification-group infrastructure itself is supplied by
`Towers.NumberTheory.Locals.RamificationGroups`.
-/

namespace Towers.CField.Ramification

open scoped BigOperators

/-- The `i`th lower ramification breakpoint in Example 4.2, viewed in `ℚ`. -/
def lubinTateBreak (q i : ℕ) : ℚ :=
  (q : ℚ) ^ i - 1

/-- The index `(G₀ : Gᵤ)` on the segment from the `i`th lower break to the
next one. -/
def lubinSegmentIndex (q i : ℕ) : ℚ :=
  ((q : ℚ) - 1) * (q : ℚ) ^ i

@[simp]
theorem lubin_tate_break (q : ℕ) :
    lubinTateBreak q 0 = 0 := by
  simp [lubinTateBreak]

/-- Consecutive lower breaks differ by the group index on the intervening
segment. -/
theorem lubin_break_sub (q i : ℕ) :
    lubinTateBreak q (i + 1) - lubinTateBreak q i =
      lubinSegmentIndex q i := by
  simp only [lubinTateBreak, lubinSegmentIndex, pow_succ]
  ring

/-- The slope `1 / (G₀ : Gᵤ)` integrated across one Lubin--Tate segment has
total change one. -/
theorem lubin_segment_length (q i : ℕ) (hq : 1 < q) :
    (lubinTateBreak q (i + 1) - lubinTateBreak q i) /
        lubinSegmentIndex q i = 1 := by
  rw [lubin_break_sub]
  apply div_self
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    have : q = 1 := by exact_mod_cast h
    omega
  · exact pow_ne_zero _ (by exact_mod_cast (Nat.zero_lt_of_lt hq).ne')

/-- The cumulative upper-numbering value after `i` Lubin--Tate segments. -/
def lubinBreakValue (q i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range i,
    (lubinTateBreak q (j + 1) - lubinTateBreak q j) /
      lubinSegmentIndex q j

/-- Example 4.2: the lower break `q^i - 1` has upper number `i`. -/
theorem lubin_break_value (q i : ℕ) (hq : 1 < q) :
    lubinBreakValue q i = i := by
  simp [lubinBreakValue, lubin_segment_length q _ hq]

end Towers.CField.Ramification

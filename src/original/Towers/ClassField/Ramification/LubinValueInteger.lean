import Towers.ClassField.Ramification.UpperRamification

/-!
# Class Field Theory, Chapter I, Example 4.7

For the Lubin--Tate ramification breaks, Example 4.2 computes the Herbrand
value at the `i`th break to be `i`.  Hence every such value is integral, which
is the direct verification of the Hasse--Arf conclusion in Example 4.7.
-/

namespace Towers.CField.Ramification

/-- The Herbrand value at every Lubin--Tate breakpoint is an integer. -/
theorem lubin_break_integer
    (q i : ℕ) (hq : 1 < q) :
    ∃ z : ℤ, lubinBreakValue q i = z := by
  refine ⟨i, ?_⟩
  simpa using lubin_break_value q i hq

/-- The first `n+1` Lubin--Tate breakpoints all have integral Herbrand
values, in the form used for the finite extension `K_{π,n}`. -/
theorem break_values_up
    (q n : ℕ) (hq : 1 < q) :
    ∀ i ≤ n, ∃ z : ℤ, lubinBreakValue q i = z := by
  intro i _
  exact lubin_break_integer q i hq

end Towers.CField.Ramification

import Mathlib.NumberTheory.LSeries.Basic

/-!
# Chapter VI, Section 1: Dirichlet series

Milne writes a Dirichlet series as `sum a(n) / n^s`, starting at `n = 1`.
Mathlib's `LSeries` is the same series: its zeroth term is defined to be zero,
so that it can be indexed by all natural numbers without a separate lower
bound.
-/

namespace Towers.CField.DSeries

open LSeries

noncomputable section

/-- The Dirichlet series attached to a sequence of complex coefficients. -/
abbrev dirichletSeries (a : ℕ → ℂ) : ℂ → ℂ := LSeries a

/-- Milne's displayed summand is exactly Mathlib's `LSeries.term` away from
the artificial zeroth coefficient. -/
theorem dirichletSeries_term {a : ℕ → ℂ} {s : ℂ} {n : ℕ}
    (hn : n ≠ 0) :
    term a s n = a n / (n : ℂ) ^ s :=
  term_of_ne_zero hn a s

/-- The value of a Dirichlet series is the infinite sum of its terms. -/
theorem dirichlet_series_tsum (a : ℕ → ℂ) (s : ℂ) :
    dirichletSeries a s = ∑' n : ℕ, term a s n :=
  rfl

end

end Towers.CField.DSeries

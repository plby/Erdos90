import Towers.ClassField.LocalGlobalPowers.Counterexample
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Chapter VIII, Section 2: the Wang counterexample

Example 2.2 rules out a cyclic degree-eight extension of `ℚ` in which `2`
remains prime.  Its global input is the product formula for local Artin
symbols, and its local obstruction is the valuation formula for norms from an
unramified extension.  The current project does not yet package local Artin
maps and their norm kernels, so the two elementary conclusions of those inputs
are recorded abstractly and exactly here.

The real and rational eighth-power calculations for `16` are in Section 1.
The assertion over every odd `p`-adic field still requires the missing local
cyclotomic splitting bridge.
-/

namespace Towers.CField.GWang

open scoped BigOperators

/-- **Example 2.2(ii), product-formula core.** If a finite product of local
symbols is one and every symbol except possibly one is trivial, then the last
symbol is trivial as well. -/
theorem symbol_all_other
    {ι G : Type*} [CommGroup G] (S : Finset ι) (phi : ι → G) {v : ι}
    (hprod : ∏ w ∈ S, phi w = 1)
    (htrivial : ∀ w ∈ S, w ≠ v → phi w = 1)
    (hv : v ∈ S) :
    phi v = 1 :=
  Finset.eq_one_of_prod_eq_one hprod htrivial v hv

/-- A general valuation obstruction to being a norm.  If valuations of norms
are divisible by the extension degree, an element whose valuation is not so
divisible cannot be a norm. -/
theorem not_valuation_dvd
    {E F : Type*} (norm : E → F) (vE : E → ℤ) (vF : F → ℤ)
    (degree : ℤ) (b : F)
    (hnorm : ∀ x, vF (norm x) = degree * vE x)
    (hb : ¬degree ∣ vF b) :
    b ∉ Set.range norm := by
  rintro ⟨x, rfl⟩
  apply hb
  refine ⟨vE x, ?_⟩
  exact hnorm x

/-- **Example 2.2(iii), numerical core.** Under the normalized valuation
formula for an unramified extension of degree eight, an element of valuation
four cannot be a norm.  This is the contradiction `4 = 8 * ord(alpha)` in the
source. -/
theorem valuation_eight_range
    {E F : Type*} (norm : E → F) (vE : E → ℤ) (vF : F → ℤ) (b : F)
    (hnorm : ∀ x, vF (norm x) = 8 * vE x)
    (hb : vF b = 4) :
    b ∉ Set.range norm := by
  apply not_valuation_dvd norm vE vF 8 b hnorm
  rw [hb]
  norm_num

end Towers.CField.GWang

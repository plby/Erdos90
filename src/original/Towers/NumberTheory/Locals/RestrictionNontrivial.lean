import Towers.NumberTheory.Locals.Ostrowski
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Restricting a number-field absolute value to the rationals

The proof of Milne's Theorem 7.14 begins by restricting an absolute value on
a number field to `ℚ` and applying Ostrowski's theorem.  This file supplies
the required nontriviality statement for that restriction.
-/

namespace Towers.NumberTheory.Milne

open scoped BigOperators
open Polynomial

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A nontrivial absolute value on a number field remains nontrivial after
restriction to `ℚ`.  This is the first reduction in the proof of Milne,
Theorem 7.14.

If the restriction were trivial, the induced norm would be ultrametric.  In
the minimal-polynomial relation for `x`, a value `w x > 1` would make the
monic leading term strictly larger than every lower term, which is
impossible.  Applying the resulting bound to `x⁻¹` forces equality. -/
theorem number_restriction_nontrivial
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial) :
    (w.comp (algebraMap ℚ K).injective).IsNontrivial := by
  let v := w.comp (algebraMap ℚ K).injective
  by_contra hv
  have hv_one : ∀ q : ℚ, q ≠ 0 → v q = 1 :=
    v.not_isNontrivial_iff.mp hv
  letI : NormedField K := w.toNormedField
  have hnat (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
    change w (n : K) ≤ 1
    by_cases hn : n = 0
    · simp [hn]
    · have hvn := hv_one (n : ℚ) (by exact_mod_cast hn)
      change w (algebraMap ℚ K (n : ℚ)) = 1 at hvn
      simpa using hvn.le
  letI : IsUltrametricDist K :=
    isUltrametricDist_iff_forall_norm_natCast_le_one.mpr hnat
  have hna : IsNonarchimedean w := fun x y =>
    IsUltrametricDist.norm_add_le_max x y
  have hle (x : K) : w x ≤ 1 := by
    by_contra hx
    have hx1 : 1 < w x := lt_of_not_ge hx
    let p : ℚ[X] := minpoly ℚ x
    have hxi : IsIntegral ℚ x := Algebra.IsAlgebraic.isIntegral.isIntegral x
    have hpmonic : p.Monic := minpoly.monic hxi
    have hd : 0 < p.natDegree :=
      natDegree_pos_of_monic_of_aeval_eq_zero hpmonic (minpoly.aeval ℚ x)
    let lower : K := ∑ i ∈ Finset.range p.natDegree,
      algebraMap ℚ K (p.coeff i) * x ^ i
    have hroot : lower + x ^ p.natDegree = 0 := by
      have h := minpoly.aeval ℚ x
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range,
        Finset.sum_range_succ] at h
      simpa only [lower, p, hpmonic.coeff_natDegree, map_one, one_mul] using h
    obtain ⟨i, hi_mem, hi_sum⟩ :=
      hna.finset_image_add
        (fun i : ℕ => algebraMap ℚ K (p.coeff i) * x ^ i)
        (Finset.range p.natDegree)
    have hi : i < p.natDegree :=
      Finset.mem_range.mp (hi_mem ⟨0, Finset.mem_range.mpr hd⟩)
    have hcoeff : w (algebraMap ℚ K (p.coeff i)) ≤ 1 := by
      by_cases hc : p.coeff i = 0
      · simp [hc]
      · simpa [v] using (show v (p.coeff i) = 1 from hv_one _ hc).le
    have hterm :
        w (algebraMap ℚ K (p.coeff i) * x ^ i) <
          w (x ^ p.natDegree) := by
      rw [w.map_mul, w.map_pow, w.map_pow]
      calc
        w (algebraMap ℚ K (p.coeff i)) * w x ^ i ≤ 1 * w x ^ i := by
          gcongr
        _ = w x ^ i := one_mul _
        _ < w x ^ p.natDegree := pow_lt_pow_right₀ hx1 hi
    have hlower : w lower < w (x ^ p.natDegree) := hi_sum.trans_lt hterm
    have hz := hna.add_eq_right_of_lt hlower
    rw [hroot, w.map_zero] at hz
    have hx0 : x ≠ 0 := w.ne_zero_iff.mp (zero_lt_one.trans hx1).ne'
    exact (w.pos (pow_ne_zero _ hx0)).ne' hz.symm
  obtain ⟨x, hx0, hx1⟩ := hw
  have hxle := hle x
  have hxinvle := hle x⁻¹
  have hxpos : 0 < w x := w.pos hx0
  have hone : w x * w x⁻¹ = 1 := by
    rw [← w.map_mul, mul_inv_cancel₀ hx0, w.map_one]
  have hxge : 1 ≤ w x := by
    nlinarith [w.nonneg x⁻¹]
  exact hx1 (le_antisymm hxle hxge)

end

end Towers.NumberTheory.Milne

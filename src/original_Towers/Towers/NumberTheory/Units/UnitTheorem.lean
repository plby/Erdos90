import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Milne, Algebraic Number Theory, Theorem 5.1 and Lemma 5.2

The Dirichlet unit theorem and the norm criterion for units, stated in Milne's notation.
-/

namespace Towers.NumberTheory.Milne

open NumberField NumberField.InfinitePlace
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Milne, Theorem 5.1 (finite generation).** The unit group of a number field is
finitely generated. -/
theorem unit_finitely_generated : Monoid.FG (𝓞 K)ˣ := by
  infer_instance

/-- **Milne, Theorem 5.1 (rank formula).** The unit rank is `r + s - 1`, where `r` and
`s` are the numbers of real and complex infinite places. -/
theorem real_places_complex :
    NumberField.Units.rank K = nrRealPlaces K + nrComplexPlaces K - 1 := by
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- The roots of unity, equivalently the torsion subgroup of the unit group, form a finite
group. -/
theorem unitTorsion_finite : Finite (NumberField.Units.torsion K) := by
  infer_instance

/-- **Milne, Theorem 5.1 (fundamental units).** Every unit has a unique expression as a
root of unity times integral powers of a fixed family of `r + s - 1` fundamental units. -/
theorem torsion_fundamental_unique (x : (𝓞 K)ˣ) :
    ∃! ζe : NumberField.Units.torsion K ×
        (Fin (NumberField.Units.rank K) → ℤ),
      x = ζe.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ (ζe.2 i) :=
  NumberField.Units.exist_unique_eq_mul_prod K x

/-- **Milne, Lemma 5.2.** An algebraic integer is a unit exactly when its field norm is
`1` or `-1`. -/
theorem integers_or_neg (x : 𝓞 K) :
    IsUnit x ↔ Algebra.norm ℚ (x : K) = 1 ∨ Algebra.norm ℚ (x : K) = -1 := by
  rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, ← abs_one, abs_eq_abs]
  simp

/-- **Milne, Lemma 5.2**, in its literal field-level form. An element of `K` comes from
a unit of the ring of integers exactly when it is integral and has field norm `1` or `-1`. -/
theorem element_integers_unit (x : K) :
    (∃ u : (𝓞 K)ˣ, (u : K) = x) ↔
      IsIntegral ℤ x ∧
        (Algebra.norm ℚ x = 1 ∨ Algebra.norm ℚ x = -1) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.isIntegral_coe,
      (integers_or_neg K u.val).mp u.isUnit⟩
  · rintro ⟨hx, hnorm⟩
    obtain ⟨xO, hxO⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hx
    have hxUnit : IsUnit xO :=
      (integers_or_neg K xO).mpr (by
        simpa [hxO] using hnorm)
    obtain ⟨u, hu⟩ := hxUnit
    refine ⟨u, ?_⟩
    rw [← hxO]
    exact congrArg (algebraMap (𝓞 K) K) hu

end Towers.NumberTheory.Milne

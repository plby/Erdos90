import Submission.ClassField.LocalBrauer.DivisionAlgebraRamification

/-!
# Chapter IV, Section 4: the ramification index

This file packages the positive generator of the division-algebra value group
chosen in `DivisionAlgebraRamification` as Milne's ramification index `e`.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [Module.Finite K D]

/-- Milne's ramification index: the positive denominator of the normalized
value group of `D`. -/
noncomputable def ramificationIndex : ℕ :=
  (ramification_value_group K D).choose

theorem ramificationIndex_pos : 0 < ramificationIndex K D :=
  (ramification_value_group K D).choose_spec.1

theorem ramification_dvd_degree :
    ramificationIndex K D ∣ Nat.sqrt (Module.finrank K D) :=
  (ramification_value_group K D).choose_spec.2.1

theorem ramification_index_degree :
    ramificationIndex K D ≤ Nat.sqrt (Module.finrank K D) :=
  (ramification_value_group K D).choose_spec.2.2.1

/-- The normalized order has value group exactly `(1/e)ℤ`. -/
theorem division_algebra_range (q : ℚ) :
    q ∈ (divisionUnitOrder K D).range ↔
      ∃ z : ℤ, q = (z : ℚ) / (ramificationIndex K D : ℚ) :=
  (ramification_value_group K D).choose_spec.2.2.2 q

/-- There is a division-algebra unit of order exactly `1/e`. -/
theorem inv_ramification_index :
    ∃ x : Additive Dˣ,
      divisionUnitOrder K D x =
        1 / (ramificationIndex K D : ℚ) := by
  apply (division_algebra_range K D _).2
  exact ⟨1, by simp⟩

/-- The elementary arithmetic step used after the degree formula: if
`e * f = n²` and both `e` and `f` are at most `n`, then both equal `n`. -/
theorem ramification_residue_sq
    {e f n : ℕ} (he : e ≤ n) (hf : f ≤ n) (hprod : e * f = n ^ 2) :
    e = n ∧ f = n := by
  have hnleef : n ^ 2 ≤ e * f := hprod.ge
  have heq : e = n := by
    by_contra hne
    have helt : e < n := lt_of_le_of_ne he hne
    have hnpos : 0 < n := (Nat.zero_le e).trans_lt helt
    have hlt : e * f < n * n := calc
      e * f ≤ e * n := Nat.mul_le_mul_left e hf
      _ < n * n := Nat.mul_lt_mul_of_pos_right helt hnpos
    exact (ne_of_lt hlt) (by simpa [pow_two] using hprod)
  subst e
  have hnpos_or_zero : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
  rcases hnpos_or_zero with rfl | hnpos
  · exact ⟨rfl, Nat.eq_zero_of_le_zero hf⟩
  · have hfEq : f = n := Nat.eq_of_mul_eq_mul_left hnpos (by
      simpa [pow_two] using hprod)
    exact ⟨rfl, hfEq⟩

end

end Submission.CField.LBrauer

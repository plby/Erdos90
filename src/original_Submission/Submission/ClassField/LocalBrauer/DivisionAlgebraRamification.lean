import Submission.ClassField.LocalBrauer.DivisionOrderDenominator

/-!
# Chapter IV, Section 4: the ramification index of a division algebra

For a central division algebra `D` of degree `n` over a nonarchimedean local
field, the values of the normalized order form a subgroup of `(1 / n) * Z`
which contains `Z`.  Multiplying by `n` therefore identifies this value group
with a subgroup of `Z` containing `n * Z`.  Its positive generator gives the
ramification index `e`; in particular `e` divides `n` and the value group is
exactly `(1 / e) * Z`.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [Module.Finite K D]

/-- The embedding `z |-> z / n`, where `n` is the degree of the central
division algebra. -/
def divisionNumeratorEmbedding : ℤ →+ ℚ where
  toFun z := (z : ℚ) / (Nat.sqrt (Module.finrank K D) : ℚ)
  map_zero' := by simp
  map_add' x y := by
    push_cast
    ring

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra.IsCentral K D] [Module.Finite K D] in
@[simp]
theorem division_numerator_embedding (z : ℤ) :
    divisionNumeratorEmbedding K D z =
      (z : ℚ) / (Nat.sqrt (Module.finrank K D) : ℚ) :=
  rfl

/-- Integral numerators of values of the normalized order on `D^times`. -/
def divisionAlgebraNumerators : AddSubgroup ℤ :=
  (divisionUnitOrder K D).range.comap
    (divisionNumeratorEmbedding K D)

omit [Algebra.IsCentral K D] [Module.Finite K D] in
theorem division_algebra_numerators (z : ℤ) :
    z ∈ divisionAlgebraNumerators K D ↔
      ∃ x : Additive Dˣ,
        divisionUnitOrder K D x =
          (z : ℚ) / (Nat.sqrt (Module.finrank K D) : ℚ) := by
  rfl

/-- The ramification index of a central division algebra exists: it is a
positive divisor of the degree `n`, and the value group of the normalized
order is exactly `(1 / e) * ℤ`. -/
theorem ramification_value_group :
    ∃ e : ℕ,
      0 < e ∧
      e ∣ Nat.sqrt (Module.finrank K D) ∧
      e ≤ Nat.sqrt (Module.finrank K D) ∧
      ∀ q : ℚ,
        q ∈ (divisionUnitOrder K D).range ↔
          ∃ z : ℤ, q = (z : ℚ) / (e : ℚ) := by
  let n := Nat.sqrt (Module.finrank K D)
  have hnpos : 0 < n := Nat.sqrt_pos.2 Module.finrank_pos
  have hn0 : n ≠ 0 := hnpos.ne'
  let H := divisionAlgebraNumerators K D
  have hnmem : (n : ℤ) ∈ H := by
    rw [show H = divisionAlgebraNumerators K D from rfl,
      division_algebra_numerators]
    obtain ⟨x, hx⟩ := local_order_surjective K (1 : ℤ)
    let y : Additive Dˣ :=
      Additive.ofMul (Units.map (algebraMap K D).toMonoidHom x.toMul)
    refine ⟨y, ?_⟩
    rw [show y = Additive.ofMul
      (Units.map (algebraMap K D).toMonoidHom x.toMul) from rfl,
      division_algebra_order, hx]
    change (1 : ℚ) = (n : ℚ) / (n : ℚ)
    exact (div_self (Nat.cast_ne_zero.mpr hn0)).symm
  obtain ⟨a, ha⟩ :=
    (H.isAddCyclic_iff_exists_zmultiples_eq_top).mp inferInstance
  have hadvdn : a ∣ (n : ℤ) := by
    rw [← Int.mem_zmultiples_iff, ha]
    exact hnmem
  let d := a.natAbs
  have hddvdn : d ∣ n := by
    simpa [d] using Int.natAbs_dvd_natAbs.mpr hadvdn
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp only [zero_dvd_iff] at hadvdn
    exact hn0 (Int.ofNat_inj.mp hadvdn)
  have hdpos : 0 < d := Int.natAbs_pos.mpr ha0
  let e := n / d
  have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hnpos hddvdn) hdpos
  have hde : d * e = n := by
    exact Nat.mul_div_cancel' hddvdn
  have hedvdn : e ∣ n := ⟨d, by rw [mul_comm, hde]⟩
  have helen : e ≤ n := Nat.le_of_dvd hnpos hedvdn
  refine ⟨e, hepos, hedvdn, helen, ?_⟩
  intro q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := division_div_sqrt K D x
    have hzH : z ∈ H := by
      rw [show H = divisionAlgebraNumerators K D from rfl,
        division_algebra_numerators]
      exact ⟨x, hz⟩
    have haz : a ∣ z := by
      rw [← Int.mem_zmultiples_iff, ha]
      exact hzH
    have hdz : (d : ℤ) ∣ z := Int.natAbs_dvd.mpr haz
    obtain ⟨k, rfl⟩ := hdz
    refine ⟨k, ?_⟩
    rw [hz]
    push_cast
    change
      ((d : ℚ) * (k : ℚ)) / (n : ℚ) =
        (k : ℚ) / (e : ℚ)
    rw [← hde]
    push_cast
    field_simp [hdpos.ne', hepos.ne']
  · rintro ⟨z, rfl⟩
    have had : a ∣ (d : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
    have hdzH : (d : ℤ) * z ∈ H := by
      rw [← ha, Int.mem_zmultiples_iff]
      exact had.trans (dvd_mul_right _ _)
    rw [show H = divisionAlgebraNumerators K D from rfl,
      division_algebra_numerators] at hdzH
    obtain ⟨x, hx⟩ := hdzH
    refine ⟨x, ?_⟩
    rw [hx]
    push_cast
    change
      ((d : ℚ) * (z : ℚ)) / (n : ℚ) =
        (z : ℚ) / (e : ℚ)
    rw [← hde]
    push_cast
    field_simp [hdpos.ne', hepos.ne']

end

end Submission.CField.LBrauer

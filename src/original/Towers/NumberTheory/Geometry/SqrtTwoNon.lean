import Towers.NumberTheory.Geometry.LatticeCriteria
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

/-!
# Milne, Algebraic Number Theory, Nonexample 4.13

The additive subgroup `ℤ + ℤ √2` of `ℝ` is free on two generators over `ℤ`, but it is dense in
`ℝ`.  In particular it is not discrete and hence is not a lattice in Milne's sense.
-/

namespace Towers.NumberTheory.Milne

open Module Submodule

/-- The additive subgroup `ℤ √2 + ℤ` of `ℝ`. -/
def sqrtAddSubgroup : AddSubgroup ℝ := AddSubgroup.closure {√2, 1}

/-- The same subgroup regarded as a `ℤ`-submodule. -/
def sqrtIntSpan : Submodule ℤ ℝ := sqrtAddSubgroup.toIntSubmodule

/-- The subgroup is the integer span of `√2` and `1`. -/
theorem sqrt_int_span :
    sqrtIntSpan = span ℤ {√2, 1} := by
  exact AddSubgroup.toIntSubmodule_closure {√2, 1}

/-- The generators `1` and `√2` are linearly independent over `ℤ`, which records the
free-abelian rank-two assertion in Nonexample 4.13. -/
theorem sqrt_linear_independent : LinearIndependent ℤ ![(1 : ℝ), √2] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  norm_num at h
  by_cases ht : t = 0
  · subst t
    norm_num at h ⊢
    exact h
  · have hsqrt : √2 = ((-s : ℤ) : ℝ) / (t : ℝ) := by
      apply (eq_div_iff (by exact_mod_cast ht)).2
      rw [mul_comm]
      push_cast
      linarith
    have hrat : √2 = (((-s : ℤ) : ℚ) / (t : ℚ) : ℚ) := by
      exact hsqrt.trans (by norm_num)
    exfalso
    exact (irrational_sqrt_two.ne_rat (((-s : ℤ) : ℚ) / (t : ℚ))) hrat

/-- Irrational rotation implies that `ℤ √2 + ℤ` is dense in `ℝ`. -/
theorem sqrt_two_dense : Dense (sqrtAddSubgroup : Set ℝ) := by
  rw [sqrtAddSubgroup, dense_addSubgroupClosure_pair_iff]
  simpa using irrational_sqrt_two

/-- Nonexample 4.13: the subgroup `ℤ + ℤ √2` is not discrete in `ℝ`. -/
theorem sqrt_not_discrete : ¬ DiscreteTopology sqrtIntSpan := by
  change ¬ DiscreteTopology sqrtAddSubgroup
  intro hdisc
  have hcyc : IsAddCyclic sqrtAddSubgroup :=
    AddSubgroup.discrete_iff_addCyclic.mpr hdisc
  obtain ⟨g, hg⟩ := isAddCyclic_iff_exists_zmultiples_eq_top.mp hcyc
  have hgen : sqrtAddSubgroup = AddSubgroup.zmultiples (g : ℝ) := by
    ext x
    constructor
    · intro hx
      have hx' : (⟨x, hx⟩ : sqrtAddSubgroup) ∈ AddSubgroup.zmultiples g := by
        rw [hg]
        trivial
      rcases hx' with ⟨n, hn⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    · rintro ⟨n, rfl⟩
      exact sqrtAddSubgroup.zsmul_mem g.2 n
  exact (AddSubgroup.dense_iff_ne_zmultiples.mp sqrt_two_dense (g : ℝ)) hgen

/-- Therefore `ℤ + ℤ √2` is not a lattice in Milne's sense. -/
theorem sqrt_not_lattice : ¬ IsLattice sqrtIntSpan :=
  fun h ↦ sqrt_not_discrete h.discreteTopology

end Towers.NumberTheory.Milne

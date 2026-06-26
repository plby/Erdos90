import Submission.NumberTheory.Locals.AbsoluteValueRing
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

/-!
# Discrete absolute values and principal valuation rings

This file records the discreteness clause of Milne's Proposition 7.6 in the
value-group formulation used by Mathlib.
-/

namespace Submission.NumberTheory.Milne

section

variable {K : Type*} [Field K]

private abbrev absoluteUnitsRange (v : AbsoluteValue K ℝ) :=
  Set.range fun x : Kˣ ↦ v (x : K)

private theorem absolute_range_pos (v : AbsoluteValue K ℝ)
    (x : absoluteUnitsRange v) : 0 < (x : ℝ) := by
  obtain ⟨u, hu⟩ := x.property
  rw [← hu]
  exact v.pos u.ne_zero

/-- Taking negative logarithms identifies the nonzero value range of an
absolute value with its additive logarithmic value group. -/
private noncomputable def absoluteHomeomorphLog
    (v : AbsoluteValue K ℝ) :
    absoluteUnitsRange v ≃ₜ negativeLogRange v where
  toFun x := ⟨-Real.log x.1, by
    obtain ⟨u, hu⟩ := x.property
    exact ⟨Additive.ofMul u, by simp [negative_log_hom, hu]⟩⟩
  invFun y := ⟨Real.exp (-y.1), by
    obtain ⟨u, hu⟩ := y.property
    refine ⟨u.toMul, ?_⟩
    rw [← hu]
    simp [negative_log_hom, Real.exp_log (v.pos u.toMul.ne_zero)]⟩
  left_inv x := by
    apply Subtype.ext
    simp [Real.exp_log (absolute_range_pos v x)]
  right_inv y := by
    apply Subtype.ext
    simp
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (((Real.continuousAt_log
      (absolute_range_pos v x).ne').comp continuousAt_subtype_val).neg).codRestrict _
  continuous_invFun := by fun_prop

/-- The same logarithm map reverses order, hence is order preserving after
passing to the order dual. -/
private noncomputable def absoluteIsoLog
    (v : AbsoluteValue K ℝ) :
    absoluteUnitsRange v ≃o (negativeLogRange v)ᵒᵈ where
  __ := (absoluteHomeomorphLog v).toEquiv
  map_rel_iff' := by
    intro x y
    change -Real.log y.1 ≤ -Real.log x.1 ↔ x.1 ≤ y.1
    rw [neg_le_neg_iff, Real.log_le_log_iff
      (absolute_range_pos v x) (absolute_range_pos v y)]

/-- For a nontrivial absolute value, density of the full valuation range is
equivalent to density after deleting zero. -/
private theorem densely_absolute_range
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial)
    (hva : IsNonarchimedean v) :
    DenselyOrdered (absoluteUnitsRange v) ↔
      DenselyOrdered (Set.range (absoluteValueValuation v hva)) := by
  let w := absoluteValueValuation v hva
  constructor
  · intro h
    letI : DenselyOrdered (absoluteUnitsRange v) := h
    constructor
    intro a b hab
    by_cases ha : (a : NNReal) = 0
    · obtain ⟨c, hc, hc1⟩ := hv.exists_abv_lt_one
      obtain ⟨z, hz⟩ := b.property
      have hbPos : 0 < (b : NNReal) := by
        change (a : NNReal) < (b : NNReal) at hab
        rwa [ha] at hab
      have hz0 : z ≠ 0 := by
        intro hz0
        apply hbPos.ne'
        rw [← hz, hz0, map_zero]
      let d : Set.range w := ⟨w (z * c), ⟨z * c, rfl⟩⟩
      refine ⟨d, ?_, ?_⟩
      · rw [Subtype.mk_lt_mk, ha]
        rw [w.map_mul]
        exact mul_pos (by exact_mod_cast v.pos hz0) (by exact_mod_cast v.pos hc)
      · rw [Subtype.mk_lt_mk, w.map_mul, hz]
        exact mul_lt_of_lt_one_right
          hbPos (by exact_mod_cast hc1)
    · have haPos : 0 < (a : NNReal) := pos_iff_ne_zero.mpr ha
      have hb0 : (b : NNReal) ≠ 0 := ne_of_gt (haPos.trans hab)
      obtain ⟨x, hx⟩ := a.property
      obtain ⟨y, hy⟩ := b.property
      have hx0 : x ≠ 0 := by
        intro hx0
        apply ha
        rw [← hx, hx0, map_zero]
      have hy0 : y ≠ 0 := by
        intro hy0
        apply hb0
        rw [← hy, hy0, map_zero]
      let a' : absoluteUnitsRange v := ⟨v x, ⟨Units.mk0 x hx0, rfl⟩⟩
      let b' : absoluteUnitsRange v := ⟨v y, ⟨Units.mk0 y hy0, rfl⟩⟩
      have hab' : a' < b' := by
        change v x < v y
        have hxy : w x < w y := by
          change (absoluteValueValuation v hva) x <
            (absoluteValueValuation v hva) y
          rw [hx, hy]
          exact hab
        exact_mod_cast hxy
      obtain ⟨d, had, hdb⟩ := exists_between hab'
      obtain ⟨u, hu⟩ := d.property
      refine ⟨⟨w (u : K), ⟨(u : K), rfl⟩⟩, ?_, ?_⟩
      · rw [Subtype.mk_lt_mk, ← hx]
        have hxu : v x < v (u : K) := by simpa [hu] using had
        exact_mod_cast hxu
      · rw [Subtype.mk_lt_mk, ← hy]
        have huy : v (u : K) < v y := by simpa [hu] using hdb
        exact_mod_cast huy
  · intro h
    letI : DenselyOrdered (Set.range w) := h
    constructor
    intro a b hab
    obtain ⟨x, hx⟩ := a.property
    obtain ⟨y, hy⟩ := b.property
    let a' : Set.range w := ⟨w (x : K), ⟨(x : K), rfl⟩⟩
    let b' : Set.range w := ⟨w (y : K), ⟨(y : K), rfl⟩⟩
    have hab' : a' < b' := by
      change w (x : K) < w (y : K)
      have hxy : v (x : K) < v (y : K) := by simpa [hx, hy] using hab
      exact_mod_cast hxy
    obtain ⟨d, had, hdb⟩ := exists_between hab'
    obtain ⟨z, hz⟩ := d.property
    have hz0 : z ≠ 0 := by
      intro hz0
      let zeroR : Set.range w := ⟨w 0, ⟨0, rfl⟩⟩
      have ha'Pos : zeroR < a' := by
        change w 0 < w (x : K)
        rw [map_zero]
        exact_mod_cast v.pos x.ne_zero
      have hdPos : zeroR < d := ha'Pos.trans had
      have hdPos' : (0 : NNReal) < (d : NNReal) := by
        calc
          (0 : NNReal) = (zeroR : NNReal) := by simp [zeroR]
          _ < (d : NNReal) := hdPos
      have : (d : NNReal) = 0 := by rw [← hz, hz0, map_zero]
      exact hdPos'.ne' this
    let u : Kˣ := Units.mk0 z hz0
    refine ⟨⟨v z, ⟨u, rfl⟩⟩, ?_, ?_⟩
    · change a.1 < v z
      rw [← hx]
      have hxz : w (x : K) < w z := by simpa [hz] using had
      exact_mod_cast hxz
    · change v z < b.1
      rw [← hy]
      have hzy : w z < w (y : K) := by simpa [hz] using hdb
      exact_mod_cast hzy

/-- For a nontrivial absolute value, topological discreteness of the nonzero
value group is exactly nondensity of the valuation range with zero adjoined. -/
private theorem discrete_topology_densely
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial)
    (hva : IsNonarchimedean v) :
    DiscreteTopology (absoluteUnitsRange v) ↔
      ¬ DenselyOrdered (Set.range (absoluteValueValuation v hva)) := by
  obtain ⟨x, hx0, hx1⟩ := hv
  let xRange : absoluteUnitsRange v :=
    ⟨v x, ⟨Units.mk0 x hx0, rfl⟩⟩
  let oneRange : absoluteUnitsRange v := ⟨1, ⟨1, by simp⟩⟩
  have hxRange : xRange ≠ oneRange := by
    intro h
    apply hx1
    exact congrArg Subtype.val h
  let e := absoluteHomeomorphLog v
  letI : Nontrivial (negativeLogRange v) :=
    ⟨e xRange, e oneRange, e.injective.ne hxRange⟩
  letI : IsOrderedAddMonoid (negativeLogRange v) :=
    Function.Injective.isOrderedAddMonoid
      (fun y : negativeLogRange v ↦ (y : ℝ)) (fun _ _ ↦ rfl)
        (fun {_ _ : negativeLogRange v} ↦ Iff.rfl)
  letI : Archimedean (negativeLogRange v) :=
    Archimedean.comap (negativeLogRange v).subtype.toAddMonoidHom
      (fun _ _ h ↦ h)
  have horder :
      DenselyOrdered (absoluteUnitsRange v) ↔
        DenselyOrdered (negativeLogRange v) :=
    (denselyOrdered_iff_of_orderIsoClass
      (absoluteIsoLog v)).trans
        denselyOrdered_orderDual
  calc
    DiscreteTopology (absoluteUnitsRange v) ↔
        DiscreteTopology (negativeLogRange v) := e.discreteTopology_iff
    _ ↔ IsAddCyclic (negativeLogRange v) :=
      (AddSubgroup.discrete_iff_addCyclic
        (H := (negativeLogRange v).toAddSubgroup)).symm
    _ ↔ ¬ DenselyOrdered (negativeLogRange v) :=
      LinearOrderedAddCommGroup.isAddCyclic_iff_not_denselyOrdered
    _ ↔ ¬ DenselyOrdered (absoluteUnitsRange v) :=
      not_congr horder.symm
    _ ↔ ¬ DenselyOrdered
        (Set.range (absoluteValueValuation v hva)) :=
      not_congr (densely_absolute_range v
        ⟨x, hx0, hx1⟩ hva)

/-- For a real-valued nonarchimedean absolute value, its valuation ring is a
principal ideal ring exactly when the value group is not densely ordered.  For
a nontrivial subgroup of the positive reals, this is the standard algebraic
form of discreteness. -/
theorem absolute_principal_densely
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    IsPrincipalIdealRing (absoluteValueRing v hv) ↔
      ¬ DenselyOrdered (Set.range (absoluteValueValuation v hv)) := by
  letI : MulArchimedean (MonoidHom.mrange (absoluteValueValuation v hv)) :=
    MulArchimedean.comap
      (MonoidHom.mrange (absoluteValueValuation v hv)).subtype
      fun _ _ h ↦ h
  simpa [absoluteValueRing] using
    (Valuation.Integers.isPrincipalIdealRing_iff_not_denselyOrdered
      (Valuation.valuationSubring.integers (absoluteValueValuation v hv)))

/-- In particular, a nondense value group makes the unique maximal ideal
principal. -/
theorem absolute_densely_ordered
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hdiscrete : ¬ DenselyOrdered (Set.range (absoluteValueValuation v hv))) :
    (IsLocalRing.maximalIdeal (absoluteValueRing v hv)).IsPrincipal := by
  letI : IsPrincipalIdealRing (absoluteValueRing v hv) :=
    (absolute_principal_densely v hv).2 hdiscrete
  exact IsPrincipalIdealRing.principal _

/-- Milne, Proposition 7.6, in the maximal-ideal formulation: the value group
is nondense exactly when the unique maximal ideal of the valuation ring is
principal.  For a subgroup of the positive reals, nondensity is the algebraic
form of discreteness used by Mathlib. -/
theorem absolute_maximal_densely
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    (IsLocalRing.maximalIdeal (absoluteValueRing v hv)).IsPrincipal ↔
      ¬ DenselyOrdered (Set.range (absoluteValueValuation v hv)) := by
  refine ⟨?_, absolute_densely_ordered v hv⟩
  intro hprincipal hdense
  let w := absoluteValueValuation v hv
  have hprincipal' :
      (IsLocalRing.maximalIdeal w.valuationSubring).IsPrincipal := by
    simpa [w, absoluteValueRing] using hprincipal
  have hIntegers : Valuation.Integers w w.valuationSubring :=
    Valuation.valuationSubring.integers w
  obtain ⟨x, hxmem, hxmax⟩ :=
    (hIntegers.isPrincipal_iff_exists_isGreatest.mp hprincipal')
  obtain ⟨a, ha, rfl⟩ := hxmem
  have ha_lt : w (algebraMap w.valuationSubring K a) < 1 := by
    simpa using (Valuation.mem_maximalIdeal_iff K w).mp ha
  obtain ⟨y, hay, hy1⟩ :
      ∃ y : K, w (algebraMap w.valuationSubring K a) < w y ∧ w y < 1 := by
    simpa only [Subtype.exists, Subtype.mk_lt_mk, Set.exists_range_iff,
      exists_prop] using
      hdense.dense
        ⟨w (algebraMap w.valuationSubring K a), Set.mem_range_self _⟩
        ⟨1, 1, w.map_one⟩ ha_lt
  obtain ⟨b, hb⟩ := hIntegers.exists_of_le_one hy1.le
  have hbmax : b ∈ IsLocalRing.maximalIdeal w.valuationSubring := by
    apply (Valuation.mem_maximalIdeal_iff K w).mpr
    change w (algebraMap w.valuationSubring K b) < 1
    rw [hb]
    exact hy1
  have hy_le := hxmax
    (Set.mem_image_of_mem (w ∘ algebraMap w.valuationSubring K) hbmax)
  simp only [Function.comp_apply, hb] at hy_le
  exact hay.not_ge hy_le

/-- **Milne, Proposition 7.6, discreteness clause.** The maximal ideal of the
valuation ring is principal exactly when the nonzero value group has the
discrete topology.  This statement also includes the trivial absolute value:
then the value group is a singleton and the maximal ideal is zero. -/
theorem absolute_maximal_discrete
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    (IsLocalRing.maximalIdeal (absoluteValueRing v hv)).IsPrincipal ↔
      DiscreteTopology (Set.range fun x : Kˣ ↦ v (x : K)) := by
  by_cases hnt : v.IsNontrivial
  · rw [absolute_maximal_densely,
      ← discrete_topology_densely v hnt hv]
  · letI : Subsingleton (absoluteUnitsRange v) := ⟨fun a b ↦ by
      apply Subtype.ext
      obtain ⟨x, hx⟩ := a.property
      obtain ⟨y, hy⟩ := b.property
      calc
        a.1 = v (x : K) := hx.symm
        _ = 1 := v.not_isNontrivial_apply hnt x.ne_zero
        _ = v (y : K) := (v.not_isNontrivial_apply hnt y.ne_zero).symm
        _ = b.1 := hy⟩
    have hdiscrete : DiscreteTopology (absoluteUnitsRange v) :=
      Subsingleton.discreteTopology
    have hnondense :
        ¬ DenselyOrdered (Set.range (absoluteValueValuation v hv)) := by
      intro hdense
      let w := absoluteValueValuation v hv
      letI : DenselyOrdered (Set.range w) := hdense
      let zeroRange : Set.range w := ⟨w 0, ⟨0, rfl⟩⟩
      let oneRange : Set.range w := ⟨w 1, ⟨1, rfl⟩⟩
      have hzeroOne : zeroRange < oneRange := by
        change w 0 < w 1
        simp
      obtain ⟨c, hzeroC, hcOne⟩ := exists_between hzeroOne
      obtain ⟨z, hz⟩ := c.property
      by_cases hz0 : z = 0
      · have hc0 : c = zeroRange := by
          apply Subtype.ext
          rw [← hz, hz0]
        exact hzeroC.ne (hc0.symm)
      · have hwz : w z = w 1 := by
          apply NNReal.eq
          change v z = v 1
          rw [v.not_isNontrivial_apply hnt hz0, map_one]
        have hc1 : c = oneRange := by
          apply Subtype.ext
          exact hz.symm.trans hwz
        exact hcOne.ne hc1
    exact ⟨fun _ ↦ hdiscrete,
      fun _ ↦ absolute_densely_ordered
        v hv hnondense⟩

/-- For a nontrivial absolute value, Milne's discrete valuation ring conclusion
is equivalent to discreteness of the nonzero value group.  Nontriviality is
necessary here because Mathlib's `IsDiscreteValuationRing` excludes fields. -/
theorem absolute_discrete_valuation
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hnt : v.IsNontrivial) :
    IsDiscreteValuationRing (absoluteValueRing v hv) ↔
      DiscreteTopology (Set.range fun x : Kˣ ↦ v (x : K)) := by
  constructor
  · intro hDVR
    letI : IsDiscreteValuationRing (absoluteValueRing v hv) := hDVR
    exact (absolute_maximal_discrete v hv).1
      (IsPrincipalIdealRing.principal _)
  · intro hdiscrete
    have hnondense :=
      (discrete_topology_densely v hnt hv).1
        hdiscrete
    letI : IsPrincipalIdealRing (absoluteValueRing v hv) :=
      (absolute_principal_densely v hv).2
        hnondense
    refine {
      toIsPrincipalIdealRing := inferInstance
      toIsLocalRing := inferInstance
      not_a_field' := ?_ }
    obtain ⟨c, hc0, hc1⟩ := hnt.exists_abv_lt_one
    let cA : absoluteValueRing v hv :=
      ⟨c, (absolute_ring v hv c).2 hc1.le⟩
    intro hbot
    have hcMem : cA ∈ IsLocalRing.maximalIdeal (absoluteValueRing v hv) :=
      (absolute_maximal_ideal v hv cA).2 hc1
    rw [hbot, Ideal.mem_bot] at hcMem
    exact hc0 (congrArg Subtype.val hcMem)

end

end Submission.NumberTheory.Milne

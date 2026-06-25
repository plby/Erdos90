import Submission.NumberTheory.ClassNumberBound


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

/-- The ambient complex vector space `ℂ^d`. -/
abbrev ComplexSpace (d : ℕ) : Type :=
  Fin d → ℂ

/-- A concrete boundedness predicate for subsets of `ℂ^d`. -/
def IsBoundedSet {d : ℕ} (Ω : Set (ComplexSpace d)) : Prop :=
  ∃ R : ℝ, ∀ z ∈ Ω, ‖z‖ ≤ R

/-- The translate `t + Ω` of a subset of `ℂ^d`. -/
def translateSet {d : ℕ} (t : ComplexSpace d) (Ω : Set (ComplexSpace d)) :
    Set (ComplexSpace d) :=
  {z | z - t ∈ Ω}

/-- The Lebesgue volume of a measurable subset of `ℂ^d`, viewed as a real number. -/
def setVolume {d : ℕ} (Ω : Set (ComplexSpace d)) : ℝ :=
  (MeasureTheory.volume Ω).toReal

/--
A lattice in `ℂ^d`, modeled as a countable additive subgroup together with a
chosen measurable fundamental domain of positive volume.
-/
structure CLattic (d : ℕ) where
  subgroup : AddSubgroup (ComplexSpace d)
  countable_subgroup : Countable subgroup
  discrete_subgroup : DiscreteTopology subgroup
  fundamentalDomain : Set (ComplexSpace d)
  isFundamentalDomain :
    MeasureTheory.IsAddFundamentalDomain subgroup fundamentalDomain MeasureTheory.volume
  positive_covolume : 0 < setVolume fundamentalDomain

/-- The covolume of a lattice, defined as the volume of a chosen fundamental domain. -/
def CLattic.covolume {d : ℕ} (Λ : CLattic d) : ℝ :=
  setVolume Λ.fundamentalDomain

/-- The set of lattice points of `Λ` that lie inside `Ω`. -/
def latticePointSet {d : ℕ} (Λ : CLattic d) (Ω : Set (ComplexSpace d)) :
    Set Λ.subgroup :=
  {x | ((x : Λ.subgroup) : ComplexSpace d) ∈ Ω}

/-- The number of lattice points of `Λ` inside `Ω`, viewed in `ℝ`. -/
def latticePointCount {d : ℕ} (Λ : CLattic d) (Ω : Set (ComplexSpace d)) : ℝ :=
  ((((latticePointSet Λ Ω).encard).toNat : ℕ) : ℝ)

/--
A bounded subset of `ℂ^d` meets a discrete lattice in only finitely many points.

This is the finiteness input needed to turn the overlap-counting `tsum` in the
averaging argument into an honest lattice-point count.
-/
lemma lattice_point_bounded
    {d : ℕ} (Λ : CLattic d) (Ω : Set (ComplexSpace d))
    (hΩ_bounded : IsBoundedSet Ω) :
    (latticePointSet Λ Ω).Finite := by
  letI : DiscreteTopology Λ.subgroup := Λ.discrete_subgroup
  rcases hΩ_bounded with ⟨R, hR⟩
  let K : Set Λ.subgroup :=
    ((↑) : Λ.subgroup → ComplexSpace d) ⁻¹' Metric.closedBall (0 : ComplexSpace d) R
  have hK_compact : IsCompact K := by
    have hclosed : IsClosed ((Λ.subgroup : AddSubgroup (ComplexSpace d)) : Set (ComplexSpace d)) :=
      AddSubgroup.isClosed_of_discrete
    exact hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall (0 : ComplexSpace d) R)
  have hK_finite : K.Finite := hK_compact.finite_of_discrete
  refine hK_finite.subset ?_
  intro x hx
  change ((x : Λ.subgroup) : ComplexSpace d) ∈ Metric.closedBall (0 : ComplexSpace d) R
  have hxR : ‖((x : Λ.subgroup) : ComplexSpace d)‖ ≤ R :=
    hR ((x : Λ.subgroup) : ComplexSpace d) hx
  simpa [Metric.mem_closedBall, dist_eq_norm] using hxR

/-- A bounded set stays bounded after translation. -/
lemma bounded_set_translate
    {d : ℕ} {t : ComplexSpace d} {Ω : Set (ComplexSpace d)}
    (hΩ : IsBoundedSet Ω) : IsBoundedSet (translateSet t Ω) := by
  rcases hΩ with ⟨R, hR⟩
  refine ⟨R + ‖t‖, ?_⟩
  intro z hz
  have hz' : ‖z - t‖ ≤ R := hR (z - t) hz
  have htri : ‖z‖ ≤ ‖z - t‖ + ‖t‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le (z - t) t
  exact le_trans htri (add_le_add hz' (le_rfl : ‖t‖ ≤ ‖t‖))

/-- A bounded set stays bounded under negation. -/
lemma bounded_set_neg {d : ℕ} {Ω : Set (ComplexSpace d)} (hΩ : IsBoundedSet Ω) :
    IsBoundedSet (-Ω) := by
  rcases hΩ with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  intro z hz
  simpa using hR (-z) (by simpa using hz)

/-- A measurable set stays measurable under negation. -/
lemma measurableSet_neg {d : ℕ} {Ω : Set (ComplexSpace d)} (hΩ : MeasurableSet Ω) :
    MeasurableSet (-Ω) := by
  change MeasurableSet ((fun z : ComplexSpace d => -z) ⁻¹' Ω)
  exact hΩ.preimage measurable_neg

/-- Negation preserves Lebesgue volume on `ℂ^d`. -/
lemma volume_neg {d : ℕ} {Ω : Set (ComplexSpace d)} (hΩ : MeasurableSet Ω) :
    MeasureTheory.volume (-Ω) = MeasureTheory.volume Ω := by
  rw [← MeasureTheory.Measure.map_neg_eq_self
    (MeasureTheory.volume : MeasureTheory.Measure (ComplexSpace d))]
  rw [MeasureTheory.Measure.map_apply measurable_neg hΩ]
  congr 1
  ext z
  simp

/--
The overlap-counting function that appears in the lattice averaging argument.
For a point `x`, it counts how many lattice translates of `-Ω` contain `x`,
while also restricting to the chosen fundamental domain.
-/
def overlapFun {d : ℕ} (Λ : CLattic d) (Ω : Set (ComplexSpace d))
    (x : ComplexSpace d) : ENNReal :=
  ∑' g : Λ.subgroup,
    Set.indicator (Λ.fundamentalDomain ∩ (g +ᵥ (-Ω))) (fun _ => (1 : ENNReal)) x

/--
On the fundamental domain, the overlap-counting `tsum` is exactly the lattice
point count of the corresponding translate of `Ω`.
-/
lemma overlap_count_nat
    {d : ℕ} (Λ : CLattic d) (Ω : Set (ComplexSpace d))
    (hΩ_bounded : IsBoundedSet Ω) (x : ComplexSpace d) (hx : x ∈ Λ.fundamentalDomain) :
    overlapFun Λ Ω x = (((latticePointSet Λ (translateSet x Ω)).encard).toNat : ENNReal) := by
  let S : Set Λ.subgroup := latticePointSet Λ (translateSet x Ω)
  let T : Set Λ.subgroup := {g | x ∈ g +ᵥ (-Ω)}
  have hST : S = T := by
    ext g
    change (((g : Λ.subgroup) : ComplexSpace d) - x ∈ Ω ↔ x ∈ g +ᵥ (-Ω))
    constructor
    · intro hg
      refine ⟨x - g, ?_, ?_⟩
      · simpa [Set.mem_neg] using hg
      · ext i
        change (((g : ComplexSpace d) + (x - g)) i = x i)
        simp [Pi.add_apply, sub_eq_add_neg]
    · intro hxg
      rcases hxg with ⟨y, hy, hxy⟩
      have hy' : -y ∈ Ω := by
        simpa [Set.mem_neg] using hy
      have hdiff : ((g : Λ.subgroup) : ComplexSpace d) - x = -y := by
        ext i
        have hxyi : ((g : ComplexSpace d) i + y i) = x i := by
          simpa [Pi.add_apply] using congrFun hxy i
        simp only [Pi.sub_apply, Pi.neg_apply]
        rw [← hxyi]
        ring_nf
      exact hdiff ▸ hy'
  have hS_finite : S.Finite :=
    lattice_point_bounded Λ (translateSet x Ω)
      (bounded_set_translate hΩ_bounded)
  have hT_finite : T.Finite := by
    rw [← hST]
    exact hS_finite
  have hsumT :
      (∑' g : Λ.subgroup, Set.indicator T (fun _ => (1 : ENNReal)) g) =
        (((T.encard).toNat : ℕ) : ENNReal) := by
    calc
      ∑' g : Λ.subgroup, Set.indicator T (fun _ => (1 : ENNReal)) g =
          ∑' g : T, (1 : ENNReal) := by
        symm
        exact tsum_subtype T (fun _ : Λ.subgroup => (1 : ENNReal))
      _ = (T.encard : ENNReal) := by
        simp
      _ = (((T.encard).toNat : ℕ) : ENNReal) := by
        rw [hT_finite.encard_eq_coe_toFinset_card]
        simp
  have hterm : ∀ g : Λ.subgroup,
      Set.indicator (Λ.fundamentalDomain ∩ (g +ᵥ (-Ω))) (fun _ => (1 : ENNReal)) x =
        Set.indicator T (fun _ => (1 : ENNReal)) g := by
    intro g
    by_cases hg : x ∈ g +ᵥ (-Ω)
    · simp [T, hg, hx]
    · simp [T, hg, hx]
  have hencard : T.encard = (latticePointSet Λ (translateSet x Ω)).encard := by
    rw [← hST]
  unfold overlapFun
  rw [show
      (∑' g : Λ.subgroup,
        Set.indicator (Λ.fundamentalDomain ∩ (g +ᵥ (-Ω))) (fun _ => (1 : ENNReal)) x) =
      (∑' g : Λ.subgroup, Set.indicator T (fun _ => (1 : ENNReal)) g) by
        apply tsum_congr hterm]
  simpa [hencard] using hsumT

/-- Bounded subsets of `ℂ^d` have finite Lebesgue volume. -/
lemma volume_top_set {d : ℕ} {Ω : Set (ComplexSpace d)}
    (hΩ_bounded : IsBoundedSet Ω) : MeasureTheory.volume Ω < ⊤ := by
  rcases hΩ_bounded with ⟨R, hR⟩
  have hsubset : Ω ⊆ Metric.closedBall (0 : ComplexSpace d) R := by
    intro z hz
    have hz' : ‖z‖ ≤ R := hR z hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  exact lt_of_le_of_lt (MeasureTheory.measure_mono hsubset)
    (MeasureTheory.measure_closedBall_lt_top (x := (0 : ComplexSpace d)) (r := R))

/--
Averaging over a lattice: some translate of a bounded measurable set contains
at least the average number of lattice points.
-/
lemma averaging_lattice
    {d : ℕ} (Λ : CLattic d) (Ω : Set (ComplexSpace d))
    (hΩ_bounded : IsBoundedSet Ω) (hΩ_measurable : MeasurableSet Ω) :
    ∃ t : ComplexSpace d,
      latticePointCount Λ (translateSet t Ω) ≥ setVolume Ω / Λ.covolume := by
  by_contra h
  push Not at h
  letI : Countable Λ.subgroup := Λ.countable_subgroup
  let r : ℝ := setVolume Ω / Λ.covolume
  let m : ℕ := Nat.ceil r
  have hr_pos : 0 < r := by
    have h0 := h 0
    have hcount_nonneg : 0 ≤ latticePointCount Λ (translateSet (0 : ComplexSpace d) Ω) := by
      unfold latticePointCount
      positivity
    linarith
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hFD_null : MeasureTheory.NullMeasurableSet Λ.fundamentalDomain MeasureTheory.volume :=
    Λ.isFundamentalDomain.nullMeasurableSet
  have hFD_toReal_pos : 0 < (MeasureTheory.volume Λ.fundamentalDomain).toReal := by
    simpa [CLattic.covolume, setVolume] using Λ.positive_covolume
  have hFD_lt_top : MeasureTheory.volume Λ.fundamentalDomain < ⊤ :=
    (ENNReal.toReal_pos_iff.mp hFD_toReal_pos).2
  have hΩ_lt_top : MeasureTheory.volume Ω < ⊤ := volume_top_set hΩ_bounded
  have hRHS_ne_top :
      (((m - 1 : ℕ) : ENNReal) * MeasureTheory.volume Λ.fundamentalDomain) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hFD_lt_top.ne
  have h_inter_null :
      ∀ g : Λ.subgroup,
        MeasureTheory.NullMeasurableSet
          (Λ.fundamentalDomain ∩ (g +ᵥ (-Ω))) MeasureTheory.volume := by
    intro g
    exact hFD_null.inter ((measurableSet_neg hΩ_measurable).nullMeasurableSet.vadd g)
  have hoverlap_integral :
      ∫⁻ x, overlapFun Λ Ω x ∂MeasureTheory.volume = MeasureTheory.volume (-Ω) := by
    unfold overlapFun
    rw [MeasureTheory.lintegral_tsum]
    · calc
        ∑' g : Λ.subgroup,
            ∫⁻ x,
              Set.indicator
                (Λ.fundamentalDomain ∩ (g +ᵥ (-Ω)))
                (fun _ => (1 : ENNReal)) x
              ∂MeasureTheory.volume
            =
              ∑' g : Λ.subgroup,
                ∫⁻ x in Λ.fundamentalDomain ∩ (g +ᵥ (-Ω)), 1 ∂MeasureTheory.volume := by
              apply tsum_congr
              intro g
              rw [MeasureTheory.lintegral_indicator₀ (h_inter_null g)]
        _ =
            ∑' g : Λ.subgroup,
              MeasureTheory.volume ((g +ᵥ (-Ω)) ∩ Λ.fundamentalDomain) := by
              apply tsum_congr
              intro g
              rw [MeasureTheory.setLIntegral_one]
              simp [Set.inter_comm]
        _ = MeasureTheory.volume (-Ω) := by
              simpa [Set.inter_comm] using (Λ.isFundamentalDomain.measure_eq_tsum (-Ω)).symm
    · intro g
      exact aemeasurable_const.indicator₀ (h_inter_null g)
  have hpointwise : ∀ x : ComplexSpace d,
      overlapFun Λ Ω x ≤
        Set.indicator Λ.fundamentalDomain (fun _ => (((m - 1 : ℕ) : ENNReal))) x := by
    intro x
    by_cases hx : x ∈ Λ.fundamentalDomain
    · have hcount_lt : latticePointCount Λ (translateSet x Ω) < r := h x
      have hnat_lt :
          ((((latticePointSet Λ (translateSet x Ω)).encard).toNat : ℕ) : ℝ) < r := by
        simpa [latticePointCount] using hcount_lt
      have hnat_le : ((latticePointSet Λ (translateSet x Ω)).encard).toNat ≤ m - 1 := by
        exact Nat.le_pred_of_lt (Nat.lt_ceil.2 hnat_lt)
      have hoverlap_le : overlapFun Λ Ω x ≤ (((m - 1 : ℕ) : ENNReal)) := by
        rw [overlap_count_nat Λ Ω hΩ_bounded x hx]
        exact_mod_cast hnat_le
      simpa [hx] using hoverlap_le
    · have hoverlap_zero : overlapFun Λ Ω x = 0 := by
        unfold overlapFun
        simp [hx]
      simp [hx, hoverlap_zero]
  have hupper_enn : MeasureTheory.volume Ω ≤
      ((((m - 1 : ℕ) : ENNReal)) * MeasureTheory.volume Λ.fundamentalDomain) := by
    calc
      MeasureTheory.volume Ω = MeasureTheory.volume (-Ω) := (volume_neg hΩ_measurable).symm
      _ = ∫⁻ x, overlapFun Λ Ω x ∂MeasureTheory.volume := hoverlap_integral.symm
      _ ≤ ∫⁻ x, Set.indicator Λ.fundamentalDomain (fun _ => (((m - 1 : ℕ) : ENNReal))) x
            ∂MeasureTheory.volume := MeasureTheory.lintegral_mono hpointwise
      _ = ((((m - 1 : ℕ) : ENNReal)) * MeasureTheory.volume Λ.fundamentalDomain) := by
        rw [MeasureTheory.lintegral_indicator₀ hFD_null, MeasureTheory.setLIntegral_const]
  have hm_pos : 0 < m := Nat.ceil_pos.2 hr_pos
  have hsub_toReal : ((↑m - 1 : ENNReal)).toReal = (m : ℝ) - 1 := by
    have hcast : ((↑m - 1 : ENNReal)) = ((m - 1 : ℕ) : ENNReal) := by
      simp
    rw [hcast, ENNReal.toReal_natCast, Nat.cast_sub (Nat.succ_le_of_lt hm_pos), Nat.cast_one]
  have hupper_real : setVolume Ω ≤ (((m : ℝ) - 1) * Λ.covolume) := by
    have htoReal := (ENNReal.toReal_le_toReal hΩ_lt_top.ne hRHS_ne_top).2 hupper_enn
    simpa [setVolume, CLattic.covolume, ENNReal.toReal_mul, hsub_toReal] using htoReal
  have hm1 : ((m : ℝ)) < r + 1 := by
    simpa [m] using Nat.ceil_lt_add_one hr_nonneg
  have hm_lt : ((m : ℝ) - 1) < r := by
    linarith
  have hstrict : (((m : ℝ) - 1) * Λ.covolume) < setVolume Ω := by
    exact (lt_div_iff₀ Λ.positive_covolume).1 hm_lt
  linarith

end Submission

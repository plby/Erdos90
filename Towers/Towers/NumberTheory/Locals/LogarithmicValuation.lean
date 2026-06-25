import Towers.NumberTheory.Geometry.LatticeCriteria
import Towers.NumberTheory.Locals.NonarchimedeanCriterion
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# From multiplicative absolute values to additive valuations

This file formalizes Milne's Proposition 7.5.  The logarithm of a nonarchimedean absolute
value is additive on the multiplicative group, satisfies the minimum inequality, and a
nontrivial discrete logarithmic value group is a real multiple of `ℤ`.
-/

namespace Towers.NumberTheory.Milne

open Module Submodule

section

variable {K : Type*} [Field K]

/-- The additive homomorphism `x ↦ -log |x|` on the multiplicative group of a field. -/
noncomputable def negativeLogHom (v : AbsoluteValue K ℝ) : Additive Kˣ →+ ℝ where
  toFun x := -Real.log (v x.toMul)
  map_zero' := by simp
  map_add' x y := by
    change -Real.log (v (x.toMul * y.toMul)) =
      -Real.log (v x.toMul) + -Real.log (v y.toMul)
    rw [map_mul, Real.log_mul (v.ne_zero x.toMul.ne_zero) (v.ne_zero y.toMul.ne_zero)]
    ring

@[simp]
theorem negative_log_hom (v : AbsoluteValue K ℝ) (x : Additive Kˣ) :
    negativeLogHom v x = -Real.log (v x.toMul) :=
  rfl

/-- Proposition 7.5(a): logarithmic values turn products into sums. -/
theorem negativeLog_mul (v : AbsoluteValue K ℝ) (x y : Kˣ) :
    -Real.log (v (x * y : Kˣ)) = -Real.log (v x) + -Real.log (v y) := by
  simpa using (negativeLogHom v).map_add (Additive.ofMul x) (Additive.ofMul y)

/-- Proposition 7.5(b): a nonarchimedean absolute value gives the minimum inequality after
applying `-log`. -/
theorem negative_log_min (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (-Real.log (v x)) (-Real.log (v y)) ≤ -Real.log (v (x + y)) := by
  have hsum := hv x y
  by_cases hle : v x ≤ v y
  · rw [max_eq_right hle] at hsum
    have hlogSum : Real.log (v (x + y)) ≤ Real.log (v y) :=
      Real.log_le_log (v.pos hxy) hsum
    have hlogXY : Real.log (v x) ≤ Real.log (v y) :=
      Real.log_le_log (v.pos hx) hle
    rw [min_eq_right (by linarith : -Real.log (v y) ≤ -Real.log (v x))]
    linarith
  · have hyx : v y ≤ v x := le_of_not_ge hle
    rw [max_eq_left hyx] at hsum
    have hlogSum : Real.log (v (x + y)) ≤ Real.log (v x) :=
      Real.log_le_log (v.pos hxy) hsum
    have hlogYX : Real.log (v y) ≤ Real.log (v x) :=
      Real.log_le_log (v.pos hy) hyx
    rw [min_eq_left (by linarith : -Real.log (v x) ≤ -Real.log (v y))]
    linarith

/-- The logarithmic value group, viewed as a `ℤ`-submodule of `ℝ`. -/
noncomputable def negativeLogRange (v : AbsoluteValue K ℝ) : Submodule ℤ ℝ :=
  LinearMap.range (negativeLogHom v).toIntLinearMap

@[simp]
theorem negative_log_range (v : AbsoluteValue K ℝ) (r : ℝ) :
    r ∈ negativeLogRange v ↔ ∃ x : Additive Kˣ, negativeLogHom v x = r :=
  Iff.rfl

/-- The final assertion of Proposition 7.5.  If the logarithmic value group is discrete and
the absolute value is nontrivial, then `-log |x| = c · ord(x)` for a nonzero real `c` and a
surjective additive homomorphism `ord : Kˣ → ℤ`. -/
theorem discrete_negative_log
    (v : AbsoluteValue K ℝ) (hnontrivial : ∃ x : Kˣ, v x ≠ 1)
    (hdiscrete : DiscreteTopology (negativeLogRange v)) :
    ∃ c : ℝ, c ≠ 0 ∧ ∃ ord : Additive Kˣ →+ ℤ,
      Function.Surjective ord ∧ ∀ x, negativeLogHom v x = c * (ord x : ℝ) := by
  let L := negativeLogRange v
  have hLattice : IsLattice L := discrete_topology L hdiscrete
  obtain ⟨s, hsfinite, hslinear, hspan⟩ := hLattice
  obtain ⟨x, hx⟩ := hnontrivial
  have hxlog : negativeLogHom v (Additive.ofMul x) ≠ 0 := by
    intro hzero
    have hlog : Real.log (v x) = 0 := by simpa using neg_eq_zero.mp hzero
    exact hx (Real.eq_one_of_pos_of_log_eq_zero (v.pos x.ne_zero) hlog)
  have hLne : L ≠ ⊥ := by
    intro hbot
    have hxmem : negativeLogHom v (Additive.ofMul x) ∈ L :=
      ⟨Additive.ofMul x, rfl⟩
    rw [hbot, Submodule.mem_bot] at hxmem
    exact hxlog hxmem
  have hsnonempty : s.Nonempty := by
    by_contra hempty
    have hsempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    apply hLne
    rw [← hspan, hsempty]
    simp
  let t := hsfinite.toFinset
  have htlinear : LinearIndepOn ℝ id (t : Set ℝ) := by
    simpa [t] using hslinear
  have hcard : t.card ≤ 1 := by
    have hle : finrank ℝ (span ℝ (t : Set ℝ)) ≤ finrank ℝ ℝ :=
      Submodule.finrank_le _
    rw [finrank_span_finset_eq_card htlinear] at hle
    simpa using hle
  have hssubsingleton : s.Subsingleton := by
    have ht := Finset.card_le_one_iff_subsingleton.mp hcard
    simpa [t] using ht
  obtain ⟨c, hc⟩ := hsnonempty
  have hseq : s = {c} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (hssubsingleton hy hc)
    · intro hy
      simp only [Set.mem_singleton_iff] at hy
      simpa [hy] using hc
  have hc0 : c ≠ 0 := hslinear.ne_zero hc
  have hspanC : span ℤ ({c} : Set ℝ) = L := by simpa [hseq] using hspan
  let g : L := ⟨c, by
    rw [← hspanC]
    exact Submodule.subset_span (Set.mem_singleton c)⟩
  have hg : AddSubgroup.zmultiples g = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : ℝ) ∈ span ℤ ({c} : Set ℝ) := by
      rw [hspanC]
      exact y.property
    obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hy
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa [g] using hn
  letI : Infinite L := Infinite.of_injective (fun n : ℤ ↦ n • g) (by
    intro m n hmn
    have hmn' := congrArg Subtype.val hmn
    change ((m • g : L) : ℝ) = ((n • g : L) : ℝ) at hmn'
    have hmul : (m : ℝ) * c = (n : ℝ) * c := by
      simpa [g, zsmul_eq_mul] using hmn'
    have hcast : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ hc0 hmul
    exact Int.cast_injective hcast)
  let e : ℤ ≃+ L := intEquivOfZMultiplesEqTop g hg
  let f : Additive Kˣ →+ L :=
    (negativeLogHom v).codRestrict L fun z ↦ ⟨z, rfl⟩
  have hf : Function.Surjective f := by
    intro y
    rcases y.property with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz
  let ord : Additive Kˣ →+ ℤ := e.symm.toAddMonoidHom.comp f
  refine ⟨c, hc0, ord, e.symm.surjective.comp hf, ?_⟩
  intro z
  have heq := congrArg Subtype.val (e.apply_symm_apply (f z))
  change ((e (ord z) : L) : ℝ) = negativeLogHom v z at heq
  have heval : ((e (ord z) : L) : ℝ) = (ord z : ℤ) • c := by
    change ((intEquivOfZMultiplesEqTop g hg (ord z) : L) : ℝ) = _
    simp [g]
  rw [heval] at heq
  simpa [zsmul_eq_mul, mul_comm] using heq.symm

end

end Towers.NumberTheory.Milne

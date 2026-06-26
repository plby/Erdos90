import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.IsOpenUnits


/-!
# Completion of a field at an absolute value

This file records the existence, density, and universal property in Milne's
Theorem 7.23 for Mathlib's completion `AbsoluteValue.Completion`.
-/

namespace Towers.NumberTheory.Milne

open AbsoluteValue UniformSpace

noncomputable section

section

variable {K : Type*} [Field K]

/-- The canonical homomorphism from a valued field to its completion. -/
def completionEmbedding (v : AbsoluteValue K ℝ) :
    K →+* v.Completion :=
  Completion.coeRingHom.comp (WithAbs.equiv v).symm.toRingHom

@[simp]
theorem completionEmbedding_apply (v : AbsoluteValue K ℝ) (x : K) :
    completionEmbedding v x = (WithAbs.equiv v).symm x :=
  rfl

/-- The canonical embedding preserves the given absolute value. -/
theorem norm_completionEmbedding (v : AbsoluteValue K ℝ) (x : K) :
    ‖completionEmbedding v x‖ = v x := by
  rw [completionEmbedding_apply, Completion.norm_coe]
  exact WithAbs.norm_toAbs_eq v x

/-- The image of the original field is dense in its completion. -/
theorem dense_range_embedding (v : AbsoluteValue K ℝ) :
    DenseRange (completionEmbedding v) :=
  Completion.denseRange_coe.comp
    (WithAbs.equiv v).symm.surjective.denseRange
    (Completion.continuous_coe _)

private theorem range_absolute_closed
    (v : AbsoluteValue K ℝ) (hclosed : IsClosed (Set.range v)) :
    Set.range (fun x : v.Completion => ‖x‖) = Set.range v := by
  apply Set.Subset.antisymm
  · rintro r ⟨x, rfl⟩
    have hx : x ∈ closure (Set.range (completionEmbedding v)) := by
      rw [(denseRange_iff_closure_range.mp (dense_range_embedding v))]
      exact Set.mem_univ x
    have hmaps : Set.MapsTo (fun y : v.Completion => ‖y‖)
        (Set.range (completionEmbedding v)) (Set.range v) := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, (norm_completionEmbedding v y).symm⟩
    exact (hmaps.closure_left continuous_norm hclosed) hx
  · rintro r ⟨x, rfl⟩
    exact ⟨completionEmbedding v x, norm_completionEmbedding v x⟩

/-- The full value range of an absolute value is closed when its nonzero value
group has the discrete topology.  The point `0` is included in the full range,
so it also contains the only possible boundary point lost on passing from
`ℝˣ` to `ℝ`. -/
theorem closed_absolute_discrete
    (v : AbsoluteValue K ℝ)
    (hdiscrete : DiscreteTopology
      (Set.range fun x : Kˣ => v (x : K))) :
    IsClosed (Set.range v) := by
  classical
  let w : Kˣ →* ℝˣ := Units.map v.toMonoidHom
  let H : Subgroup ℝˣ := MonoidHom.range w
  let f : H → ℝ := fun x => (x.1 : ℝ)
  have hf : Topology.IsEmbedding f := by
    exact IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.comp
      Topology.IsEmbedding.subtypeVal
  have hfrange : Set.range f = Set.range (fun x : Kˣ => v (x : K)) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, hu⟩ := x.property
      refine ⟨u, ?_⟩
      simpa [f, H, w] using congrArg Units.val hu
    · rintro ⟨u, rfl⟩
      let y : H := ⟨w u, ⟨u, rfl⟩⟩
      exact ⟨y, by simp [f, y, w]⟩
  let e : H ≃ₜ Set.range (fun x : Kˣ => v (x : K)) :=
    hf.toHomeomorph.trans (Homeomorph.setCongr hfrange)
  letI : DiscreteTopology H := e.discreteTopology_iff.mpr hdiscrete
  have hHclosed : IsClosed (H : Set ℝˣ) := Subgroup.isClosed_of_discrete
  rw [← closure_subset_iff_isClosed]
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, map_zero v⟩
  · let xu : ℝˣ := Units.mk0 x hx0
    have hxu : xu ∈ closure (H : Set ℝˣ) := by
      have hpre : xu ∈ Units.val ⁻¹' closure (Set.range v) := hx
      have hopen : IsOpenMap (Units.val : ℝˣ → ℝ) :=
        IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap
      rw [hopen.preimage_closure_eq_closure_preimage
        Units.continuous_val (Set.range v)] at hpre
      have hpreimage : Units.val ⁻¹' Set.range v = (H : Set ℝˣ) := by
        ext y
        constructor
        · rintro ⟨z, hz⟩
          have hz0 : z ≠ 0 := by
            intro hz0
            subst z
            exact y.ne_zero (by simpa using hz.symm)
          let zu : Kˣ := Units.mk0 z hz0
          refine ⟨zu, ?_⟩
          apply Units.ext
          simpa [w, zu] using hz
        · rintro ⟨z, hz⟩
          refine ⟨(z : K), ?_⟩
          simpa [w] using congrArg Units.val hz
      rwa [hpreimage] at hpre
    rw [hHclosed.closure_eq] at hxu
    obtain ⟨u, hu⟩ := hxu
    refine ⟨(u : K), ?_⟩
    simpa [w, xu] using congrArg Units.val hu

/-- In the discrete nonarchimedean setup following Milne's Remark 7.24,
completion introduces no new absolute values: `|K̂| = |K|`. -/
theorem range_absolute_value
    (v : AbsoluteValue K ℝ)
    (hdiscrete : DiscreteTopology
      (Set.range fun x : Kˣ => v (x : K))) :
    Set.range (fun x : v.Completion => ‖x‖) = Set.range v :=
  range_absolute_closed v
    (closed_absolute_discrete v hdiscrete)

/-- Milne, Theorem 7.23: every absolute-value-preserving homomorphism from
`K` to a complete normed field extends uniquely to the completion, among
absolute-value-preserving extensions. -/
theorem completion_universal
    (v : AbsoluteValue K ℝ) {L : Type*} [NormedField L] [CompleteSpace L]
    (f : K →+* L) (hf : ∀ x, ‖f x‖ = v x) :
    ∃! F : v.Completion →+* L,
      Isometry F ∧ F.comp (completionEmbedding v) = f := by
  let fAbs : WithAbs v →+* L := f.comp (WithAbs.equiv v).toRingHom
  have hfAbs : ∀ x, ‖fAbs x‖ = ‖x‖ := by
    intro x
    rw [show fAbs x = f ((WithAbs.equiv v) x) by rfl, hf]
    exact (WithAbs.norm_toAbs_eq v ((WithAbs.equiv v) x)).symm
  let hfIso : Isometry fAbs :=
    AddMonoidHomClass.isometry_of_norm fAbs hfAbs
  let F : v.Completion →+* L :=
    hfIso.extensionHom
  refine ⟨F, ?_, ?_⟩
  · constructor
    · exact hfIso.completion_extension
    · ext x
      change F (x : v.Completion) = f x
      rw [show F (x : v.Completion) = fAbs ((WithAbs.equiv v).symm x) by
        exact hfIso.extensionHom_coe ((WithAbs.equiv v).symm x)]
      rfl
  · intro G hG
    have hfun : (G : v.Completion → L) = F :=
      Completion.denseRange_coe.equalizer
      hG.1.continuous
      hfIso.completion_extension.continuous
      (funext fun x ↦ by
        change G (↑x : v.Completion) = F (↑x : v.Completion)
        have hF : F (↑x : v.Completion) = fAbs x := by
          exact hfIso.extensionHom_coe x
        rw [hF]
        have hcomp := RingHom.congr_fun hG.2 x.ofAbs
        simpa [completionEmbedding, fAbs] using hcomp)
    exact DFunLike.ext G F (congrFun hfun)

/-- Milne, Remark 7.24(a): any complete normed field containing a dense,
absolute-value-preserving copy of `K` is uniquely isometrically isomorphic to
the canonical completion, compatibly with the embeddings of `K`. -/
theorem completion_unique_equiv
    (v : AbsoluteValue K ℝ) {L : Type*} [NormedField L] [CompleteSpace L]
    (f : K →+* L) (hf : ∀ x, ‖f x‖ = v x) (hfdense : DenseRange f) :
    ∃! e : v.Completion ≃+* L,
      Isometry e ∧ e.toRingHom.comp (completionEmbedding v) = f := by
  obtain ⟨F, hF, hFunique⟩ := completion_universal v f hf
  have hrange : Set.range f ⊆ Set.range F := by
    rintro y ⟨x, rfl⟩
    refine ⟨completionEmbedding v x, ?_⟩
    exact RingHom.congr_fun hF.2 x
  have hFdense : DenseRange F := Dense.mono hrange hfdense
  have hFclosed : IsClosed (Set.range F) := hF.1.isClosedEmbedding.isClosed_range
  have hFrange : Set.range F = Set.univ := by
    rw [← hFclosed.closure_eq]
    exact dense_iff_closure_eq.mp hFdense
  have hFsurjective : Function.Surjective F := Set.range_eq_univ.mp hFrange
  let e : v.Completion ≃+* L :=
    RingEquiv.ofBijective F ⟨hF.1.injective, hFsurjective⟩
  refine ⟨e, ?_, ?_⟩
  · simpa [e] using hF
  · intro e' he'
    apply RingEquiv.ext
    have hhom := hFunique e'.toRingHom he'
    exact RingHom.congr_fun hhom

end

end

end Towers.NumberTheory.Milne

import Submission.NumberTheory.Locals.Ostrowski
import Submission.NumberTheory.Locals.RestrictionNontrivial
import Submission.NumberTheory.Completions.TensorDecomposition
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Archimedean absolute values on a number field

This file proves the archimedean half of Milne's Theorem 7.14 for an
arbitrary nontrivial real-valued absolute value.  The restriction to `ℚ` is
equivalent to the usual absolute value.  This equivalence identifies the two
completions topologically.  Chapter 8's scalar-extension argument then makes
the completion of the number field a finite algebraic extension of `ℝ`, hence
isomorphic to `ℝ` or `ℂ`.
-/

namespace Submission.NumberTheory.Milne

noncomputable section

open NumberField
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Equivalent absolute values have isomorphic completed rings. -/
def completionRing
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v.IsEquiv u) : v.Completion ≃+* u.Completion := by
  exact UniformSpace.Completion.mapRingEquiv
    (WithAbs.congr v u (.refl F))
    ((AbsoluteValue.isEquiv_iff_isHomeomorph v u).1 h).continuous
    ((AbsoluteValue.isEquiv_iff_isHomeomorph u v).1 h.symm).continuous

set_option backward.isDefEq.respectTransparency false in
theorem continuous_ring_equiv
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v.IsEquiv u) : Continuous (completionRing h) := by
  unfold completionRing
  change Continuous (UniformSpace.Completion.map
    (WithAbs.congr v u (.refl F)))
  exact UniformSpace.Completion.continuous_map

set_option backward.isDefEq.respectTransparency false in
theorem continuous_completion_symm
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v.IsEquiv u) : Continuous (completionRing h).symm := by
  unfold completionRing
  change Continuous (UniformSpace.Completion.map
    (WithAbs.congr u v (.refl F)))
  exact UniformSpace.Completion.continuous_map

theorem rat_absolute_real :
    Rat.infinitePlace.1 = Rat.AbsoluteValue.real := by
  ext x
  rw [← InfinitePlace.coe_apply Rat.infinitePlace x,
    Rat.infinitePlace_apply, Rat.AbsoluteValue.real_eq_abs]

/-- Equal absolute values have canonically isomorphic completions. -/
def completionEquiv
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ} (h : v = u) :
    v.Completion ≃+* u.Completion := by
  subst u
  exact RingEquiv.refl _

theorem continuous_completion_equiv
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ} (h : v = u) :
    Continuous (completionEquiv h) := by
  subst u
  exact continuous_id

theorem continuous_completion_ring
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ} (h : v = u) :
    Continuous (completionEquiv h).symm := by
  subst u
  exact continuous_id

/-- The usual rational absolute value has completion `ℝ`. -/
def rationalRealCompletion :
    Rat.AbsoluteValue.real.Completion ≃+* ℝ :=
  (completionEquiv rat_absolute_real.symm).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)

theorem continuous_rational_real :
    Continuous rationalRealCompletion := by
  unfold rationalRealCompletion
  rw [RingEquiv.coe_trans]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).continuous.comp
      (continuous_completion_equiv
        rat_absolute_real.symm)

theorem continuous_real_symm :
    Continuous rationalRealCompletion.symm := by
  unfold rationalRealCompletion
  rw [show ((completionEquiv
      rat_absolute_real.symm).trans
      (InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace)).symm =
      (InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace).symm.trans
      (completionEquiv
        rat_absolute_real.symm).symm by rfl,
    RingEquiv.coe_trans]
  exact (continuous_completion_ring
    rat_absolute_real.symm).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal
        Rat.isReal_infinitePlace).symm.isometry.continuous

/-- The completion of an archimedean absolute value on `ℚ` is topologically
and algebraically the real field. -/
def archimedeanRatReal
    (v : AbsoluteValue ℚ ℝ) (h : v.IsEquiv Rat.AbsoluteValue.real) :
    v.Completion ≃+* ℝ :=
  (completionRing h).trans
    rationalRealCompletion

theorem archimedean_rat_real
    (v : AbsoluteValue ℚ ℝ) (h : v.IsEquiv Rat.AbsoluteValue.real) :
    Continuous (archimedeanRatReal v h) := by
  unfold archimedeanRatReal
  rw [RingEquiv.coe_trans]
  exact continuous_rational_real.comp
    (continuous_ring_equiv h)

theorem continuous_archimedean_rat
    (v : AbsoluteValue ℚ ℝ) (h : v.IsEquiv Rat.AbsoluteValue.real) :
    Continuous (archimedeanRatReal v h).symm := by
  unfold archimedeanRatReal
  rw [show ((completionRing h).trans
      rationalRealCompletion).symm =
      rationalRealCompletion.symm.trans
        (completionRing h).symm by rfl,
    RingEquiv.coe_trans]
  apply Continuous.comp
  · exact continuous_completion_symm h
  · exact continuous_real_symm

set_option maxHeartbeats 2000000 in
-- Tensor-product instance synthesis and both finite-dimensional topology branches are expensive.
set_option backward.isDefEq.respectTransparency false in
private theorem archimedean_real_complex
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (v : AbsoluteValue ℚ ℝ) (w : AbsoluteValue K ℝ)
    (hv : v.IsNontrivial) (hwv : AbsoluteValue.LiesOver w v)
    (hreal : v.IsEquiv Rat.AbsoluteValue.real) :
    (∃ e : w.Completion ≃+* ℝ, IsHomeomorph e) ∨
      ∃ e : w.Completion ≃+* ℂ, IsHomeomorph e := by
  let r : v.Completion ≃+* ℝ :=
    archimedeanRatReal v hreal
  let ι : v.Completion →+* w.Completion :=
    completionLies v w hwv
  letI : Fact v.IsNontrivial := ⟨hv⟩
  letI : NontriviallyNormedField v.Completion :=
    NontriviallyNormedField.ofNormNeOne <| by
      rcases hv with ⟨x, hx0, hx1⟩
      refine ⟨completionEmbedding v x, ?_, ?_⟩
      · intro hx
        apply hx0
        apply RingHom.injective (completionEmbedding v)
        simpa using hx
      · rwa [norm_completionEmbedding]
  letI : Algebra v.Completion w.Completion := ι.toAlgebra
  letI : NormedSpace v.Completion w.Completion :=
    { norm_smul_le := fun a x => by
        change ‖ι a * x‖ ≤ ‖a‖ * ‖x‖
        have ha : ‖ι a‖ = ‖a‖ := by
          simpa only [dist_zero_right, map_zero] using
            (completion_lies_isometry v w hwv).dist_eq a 0
        calc
          ‖ι a * x‖ ≤ ‖ι a‖ * ‖x‖ := norm_mul_le _ _
          _ = ‖a‖ * ‖x‖ := by rw [ha] }
  letI : Algebra ℚ v.Completion :=
    UniformSpace.Completion.algebra (WithAbs v) ℚ
  letI : SMul ℚ v.Completion := Algebra.toSMul
  letI : Module ℚ v.Completion := Algebra.toModule
  letI : Algebra ℚ w.Completion :=
    UniformSpace.Completion.algebra (WithAbs w) ℚ
  letI : SMul ℚ w.Completion := Algebra.toSMul
  letI : Module ℚ w.Completion := Algebra.toModule
  letI : IsScalarTower ℚ v.Completion w.Completion :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa using (completion_lies_comp v w hwv).symm)
  letI : Module v.Completion (K ⊗[ℚ] v.Completion) := Algebra.toModule
  letI : Module.Finite v.Completion (v.Completion ⊗[ℚ] K) :=
    Module.Finite.base_change ℚ v.Completion K
  letI : Module.Finite v.Completion (K ⊗[ℚ] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight ℚ v.Completion K).toLinearEquiv
  let j : K →ₐ[ℚ] w.Completion :=
    { toRingHom := completionEmbedding w
      commutes' := fun _ => rfl }
  let φAlg : (K ⊗[ℚ] v.Completion) →ₐ[v.Completion] w.Completion :=
    (j.liftEquiv ℚ v.Completion K w.Completion).comp
      (Algebra.TensorProduct.commRight ℚ v.Completion K).symm.toAlgHom
  let φ : (K ⊗[ℚ] v.Completion) →ₗ[v.Completion] w.Completion :=
    φAlg.toLinearMap
  have hφdense : DenseRange φ := by
    apply (dense_range_embedding w).mono
    rintro _ ⟨x, rfl⟩
    refine ⟨x ⊗ₜ[ℚ] (1 : v.Completion), ?_⟩
    change ι 1 * completionEmbedding w x = completionEmbedding w x
    rw [map_one, one_mul]
  have hφ : Function.Surjective φ := by
    letI : Module.Finite v.Completion φ.range := Module.Finite.range φ
    rw [← Set.range_eq_univ, ← φ.coe_range,
      ← φ.range.closed_of_finiteDimensional.closure_eq]
    exact hφdense.closure_range
  letI : Module.Finite v.Completion w.Completion :=
    Module.Finite.of_surjective φ hφ
  letI : Algebra ℝ v.Completion := r.symm.toRingHom.toAlgebra
  letI : Algebra ℝ w.Completion := (ι.comp r.symm.toRingHom).toAlgebra
  letI : IsScalarTower ℝ v.Completion w.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  let re : v.Completion ≃ₐ[ℝ] ℝ :=
    { toRingEquiv := r
      commutes' := fun x => r.apply_symm_apply x }
  letI : Algebra.IsAlgebraic ℝ v.Completion := re.symm.isAlgebraic
  letI : Algebra.IsAlgebraic v.Completion w.Completion :=
    Algebra.IsAlgebraic.of_finite v.Completion w.Completion
  letI : Algebra.IsAlgebraic ℝ w.Completion :=
    Algebra.IsAlgebraic.trans ℝ v.Completion w.Completion
  rcases Real.nonempty_algEquiv_or w.Completion with he | he
  · let e : w.Completion ≃ₐ[ℝ] ℝ := he.some
    letI : Algebra v.Completion ℝ := r.toRingHom.toAlgebra
    letI : ContinuousSMul v.Completion ℝ :=
      ⟨by
        change Continuous fun p : v.Completion × ℝ => r p.1 * p.2
        exact ((archimedean_rat_real v hreal).comp
          continuous_fst).mul continuous_snd⟩
    let le : w.Completion ≃ₗ[v.Completion] ℝ :=
      { toEquiv := e.toEquiv
        map_add' := e.map_add
        map_smul' := fun a x => by
          change e (ι a * x) = r a * e x
          rw [map_mul]
          congr 1
          calc
            e (ι a) = e (algebraMap ℝ w.Completion (r a)) := by
              rw [show algebraMap ℝ w.Completion (r a) = ι a by
                change ι (r.symm (r a)) = ι a
                rw [r.symm_apply_apply]]
            _ = r a := e.commutes (r a) }
    have hcont : Continuous e :=
      le.toLinearMap.continuous_of_finiteDimensional
    letI : FiniteDimensional v.Completion ℝ := le.finiteDimensional
    have hcontInv : Continuous e.symm :=
      le.symm.toLinearMap.continuous_of_finiteDimensional
    let eh : w.Completion ≃ₜ ℝ :=
      { toEquiv := e.toEquiv
        continuous_toFun := hcont
        continuous_invFun := hcontInv }
    exact Or.inl ⟨e.toRingEquiv, eh.isHomeomorph⟩
  · let e : w.Completion ≃ₐ[ℝ] ℂ := he.some
    letI : Algebra v.Completion ℂ :=
      ((algebraMap ℝ ℂ).comp r.toRingHom).toAlgebra
    letI : ContinuousSMul v.Completion ℂ :=
      ⟨by
        change Continuous fun p : v.Completion × ℂ =>
          ((r p.1 : ℝ) : ℂ) * p.2
        exact (((Complex.continuous_ofReal.comp
          (archimedean_rat_real v hreal)).comp
            continuous_fst).mul continuous_snd)⟩
    let le : w.Completion ≃ₗ[v.Completion] ℂ :=
      { toEquiv := e.toEquiv
        map_add' := e.map_add
        map_smul' := fun a x => by
          change e (ι a * x) = (r a : ℂ) * e x
          rw [map_mul]
          congr 1
          calc
            e (ι a) = e (algebraMap ℝ w.Completion (r a)) := by
              rw [show algebraMap ℝ w.Completion (r a) = ι a by
                change ι (r.symm (r a)) = ι a
                rw [r.symm_apply_apply]]
            _ = (r a : ℂ) := e.commutes (r a) }
    have hcont : Continuous e :=
      le.toLinearMap.continuous_of_finiteDimensional
    letI : FiniteDimensional v.Completion ℂ := le.finiteDimensional
    have hcontInv : Continuous e.symm :=
      le.symm.toLinearMap.continuous_of_finiteDimensional
    let eh : w.Completion ≃ₜ ℂ :=
      { toEquiv := e.toEquiv
        continuous_toFun := hcont
        continuous_invFun := hcontInv }
    exact Or.inr ⟨e.toRingEquiv, eh.isHomeomorph⟩

set_option maxHeartbeats 1000000 in
-- Comparing the two induced topologies unfolds nested completion maps and ring equivalences.
set_option backward.isDefEq.respectTransparency false in
/-- Milne, Theorem 7.14(b,c), arbitrary-value form: every nontrivial
archimedean absolute value on a number field is equivalent to an infinite
place. -/
theorem infinite_not_nonarchimedean
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (harch : ¬ IsNonarchimedean w) :
    ∃ p : InfinitePlace K, w.IsEquiv p.1 := by
  let v : AbsoluteValue ℚ ℝ :=
    w.comp (algebraMap ℚ K).injective
  have hv : v.IsNontrivial :=
    number_restriction_nontrivial w hw
  have hvarch : ¬ IsNonarchimedean v := by
    intro hvna
    apply harch
    rw [nonarchimedean_nat_cast]
    intro n
    have hn := (nonarchimedean_nat_cast v).1 hvna n
    change w (algebraMap ℚ K (n : ℚ)) ≤ 1 at hn
    simpa using hn
  have hreal : v.IsEquiv Rat.AbsoluteValue.real :=
    ostrowski_archimedean v hv hvarch
  let hwv : AbsoluteValue.LiesOver w v := ⟨rfl⟩
  rcases archimedean_real_complex
      v w hv hwv hreal with ⟨e, he⟩ | ⟨e, he⟩
  · let eh : w.Completion ≃ₜ ℝ :=
      e.toEquiv.toHomeomorphOfContinuousOpen he.continuous he.isOpenMap
    let φ : K →+* ℂ :=
      (algebraMap ℝ ℂ).comp (e.toRingHom.comp (completionEmbedding w))
    let p : InfinitePlace K := InfinitePlace.mk φ
    let g : WithAbs p.1 →+* ℂ :=
      φ.comp (WithAbs.equiv p.1).toRingHom
    have hg : Isometry g := by
      apply AddMonoidHomClass.isometry_of_norm
      intro x
      change ‖φ x.ofAbs‖ = p.1 x.ofAbs
      exact (InfinitePlace.apply φ x.ofAbs).symm
    let f : WithAbs w ≃+* WithAbs p.1 :=
      WithAbs.congr w p.1 (.refl K)
    have hf : Continuous f := by
      apply hg.isEmbedding.continuous_iff.mpr
      have hc : Continuous fun x : WithAbs w =>
          ((e (x : w.Completion) : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp
          (eh.continuous.comp (UniformSpace.Completion.continuous_coe _))
      convert hc using 1
    have hfinv : Continuous f.symm := by
      apply UniformSpace.Completion.coe_isometry.isEmbedding.continuous_iff.mpr
      have hc : Continuous fun x : WithAbs p.1 =>
          e.symm (Complex.re (g x)) :=
        eh.symm.continuous.comp (Complex.continuous_re.comp hg.continuous)
      convert hc using 1
      funext x
      change (WithAbs.toAbs w x.ofAbs : w.Completion) =
        e.symm (Complex.re (φ x.ofAbs))
      change (WithAbs.toAbs w x.ofAbs : w.Completion) =
        e.symm (((e (WithAbs.toAbs w x.ofAbs : w.Completion) : ℝ) : ℂ).re)
      rw [Complex.ofReal_re]
      exact (e.symm_apply_apply
        (WithAbs.toAbs w x.ofAbs : w.Completion)).symm
    let fh : WithAbs w ≃ₜ WithAbs p.1 :=
      { toEquiv := f.toEquiv
        continuous_toFun := hf
        continuous_invFun := hfinv }
    refine ⟨p, (AbsoluteValue.isEquiv_iff_isHomeomorph w p.1).2 ?_⟩
    simpa [f] using fh.isHomeomorph
  · let eh : w.Completion ≃ₜ ℂ :=
      e.toEquiv.toHomeomorphOfContinuousOpen he.continuous he.isOpenMap
    let φ : K →+* ℂ := e.toRingHom.comp (completionEmbedding w)
    let p : InfinitePlace K := InfinitePlace.mk φ
    let g : WithAbs p.1 →+* ℂ :=
      φ.comp (WithAbs.equiv p.1).toRingHom
    have hg : Isometry g := by
      apply AddMonoidHomClass.isometry_of_norm
      intro x
      change ‖φ x.ofAbs‖ = p.1 x.ofAbs
      exact (InfinitePlace.apply φ x.ofAbs).symm
    let f : WithAbs w ≃+* WithAbs p.1 :=
      WithAbs.congr w p.1 (.refl K)
    have hf : Continuous f := by
      apply hg.isEmbedding.continuous_iff.mpr
      have hc : Continuous fun x : WithAbs w => e (x : w.Completion) :=
        eh.continuous.comp (UniformSpace.Completion.continuous_coe _)
      convert hc using 1
    have hfinv : Continuous f.symm := by
      apply UniformSpace.Completion.coe_isometry.isEmbedding.continuous_iff.mpr
      have hc : Continuous fun x : WithAbs p.1 => e.symm (g x) :=
        eh.symm.continuous.comp hg.continuous
      convert hc using 1
      funext x
      change (WithAbs.toAbs w x.ofAbs : w.Completion) =
        e.symm (φ x.ofAbs)
      change (WithAbs.toAbs w x.ofAbs : w.Completion) =
        e.symm (e (WithAbs.toAbs w x.ofAbs : w.Completion))
      exact (e.symm_apply_apply
        (WithAbs.toAbs w x.ofAbs : w.Completion)).symm
    let fh : WithAbs w ≃ₜ WithAbs p.1 :=
      { toEquiv := f.toEquiv
        continuous_toFun := hf
        continuous_invFun := hfinv }
    refine ⟨p, (AbsoluteValue.isEquiv_iff_isHomeomorph w p.1).2 ?_⟩
    simpa [f] using fh.isHomeomorph

end

end Submission.NumberTheory.Milne

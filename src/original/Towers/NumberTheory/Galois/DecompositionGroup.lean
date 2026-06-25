import Towers.NumberTheory.Completions.TensorDecomposition
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois


/-!
# Milne, Chapter 8, Proposition 8.10: decomposition groups

For an extension `w` of an absolute value `v`, this file defines the
decomposition group as the subgroup of `Gal(L/K)` preserving `w`.  It then
constructs Milne's homomorphism from this group to `Gal(L_w/K_v)`, and
proves that it is an isomorphism for finite normal extensions at every
place.  The inverse restricts a local automorphism to the embedded normal
global field.  At infinite places, norm preservation follows from the
classification of continuous ring automorphisms of `ℝ` and `ℂ`.

The ideal-theoretic ramification API also gives the degree consequence of
Proposition 8.10: the order of the decomposition group is `e * f`.
-/

namespace Towers.NumberTheory.Milne

open AbsoluteValue UniformSpace
open Module
open scoped Pointwise TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

section Completion

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)

/-- The decomposition group of `w` in `Gal(L/K)`: the automorphisms that
preserve the absolute value `w`. -/
def absoluteValueDecomposition
    (_v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) :
    Subgroup Gal(L/K) where
  carrier := { σ | ∀ x, w (σ x) = w x }
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ x
    simp only [AlgEquiv.mul_apply]
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ x
    simpa using (hσ (σ⁻¹ x)).symm

/-- The isometric ring endomorphism of `L_w` extending a
decomposition-group element. -/
private def decompositionRingHom
    (σ : absoluteValueDecomposition v w) :
    w.Completion →+* w.Completion :=
  Classical.choose (completion_universal w
    ((completionEmbedding w).comp (σ.1 : L ≃ₐ[K] L).toRingEquiv.toRingHom)
    (fun x ↦ by
      change ‖completionEmbedding w (σ.1 x)‖ = w x
      rw [norm_completionEmbedding]
      exact σ.2 x))

private theorem decomposition_ring_isometry
    (σ : absoluteValueDecomposition v w) :
    Isometry (decompositionRingHom v w σ) :=
  (Classical.choose_spec (completion_universal w
    ((completionEmbedding w).comp (σ.1 : L ≃ₐ[K] L).toRingEquiv.toRingHom)
    (fun x ↦ by
      change ‖completionEmbedding w (σ.1 x)‖ = w x
      rw [norm_completionEmbedding]
      exact σ.2 x))).1.1

private theorem decomposition_completion_coe
    (σ : absoluteValueDecomposition v w) (x : L) :
    decompositionRingHom v w σ (completionEmbedding w x) =
      completionEmbedding w (σ.1 x) := by
  have hcomp := (Classical.choose_spec (completion_universal w
    ((completionEmbedding w).comp (σ.1 : L ≃ₐ[K] L).toRingEquiv.toRingHom)
    (fun x ↦ by
      change ‖completionEmbedding w (σ.1 x)‖ = w x
      rw [norm_completionEmbedding]
      exact σ.2 x))).1.2
  exact RingHom.congr_fun hcomp x

private theorem decomposition_ring_inv
    (σ : absoluteValueDecomposition v w) :
    (decompositionRingHom v w σ).comp
        (decompositionRingHom v w σ⁻¹) = RingHom.id _ := by
  have hfun :
      (fun x ↦ decompositionRingHom v w σ
        (decompositionRingHom v w σ⁻¹ x)) = id :=
    UniformSpace.Completion.denseRange_coe.equalizer
      ((decomposition_ring_isometry v w σ).continuous.comp
        (decomposition_ring_isometry v w σ⁻¹).continuous)
      continuous_id
      (funext fun x ↦ by
        change decompositionRingHom v w σ
            (decompositionRingHom v w σ⁻¹
              (completionEmbedding w x.ofAbs)) =
          completionEmbedding w x.ofAbs
        rw [decomposition_completion_coe, decomposition_completion_coe]
        simp)
  exact DFunLike.ext _ _ (congrFun hfun)

private theorem decomposition_inv_mul
    (σ : absoluteValueDecomposition v w) :
    (decompositionRingHom v w σ⁻¹).comp
        (decompositionRingHom v w σ) = RingHom.id _ := by
  have hfun :
      (fun x ↦ decompositionRingHom v w σ⁻¹
        (decompositionRingHom v w σ x)) = id :=
    UniformSpace.Completion.denseRange_coe.equalizer
      ((decomposition_ring_isometry v w σ⁻¹).continuous.comp
        (decomposition_ring_isometry v w σ).continuous)
      continuous_id
      (funext fun x ↦ by
        change decompositionRingHom v w σ⁻¹
            (decompositionRingHom v w σ
              (completionEmbedding w x.ofAbs)) =
          completionEmbedding w x.ofAbs
        rw [decomposition_completion_coe, decomposition_completion_coe]
        simp)
  exact DFunLike.ext _ _ (congrFun hfun)

/-- The ring automorphism of `L_w` extending a decomposition-group element. -/
private def decompositionCompletionRing
    (σ : absoluteValueDecomposition v w) :
    w.Completion ≃+* w.Completion :=
  RingEquiv.ofRingHom
    (decompositionRingHom v w σ)
    (decompositionRingHom v w σ⁻¹)
    (decomposition_ring_inv v w σ)
    (decomposition_inv_mul v w σ)

private theorem decomposition_ring_coe
    (σ : absoluteValueDecomposition v w) (x : L) :
    decompositionCompletionRing v w σ (completionEmbedding w x) =
      completionEmbedding w (σ.1 x) :=
  decomposition_completion_coe v w σ x

variable [hwv : Fact (AbsoluteValue.LiesOver w v)]

private noncomputable local instance decompositionCompletionNontriviallyNormedField
    [Fact v.IsNontrivial] : NontriviallyNormedField v.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases (Fact.out : v.IsNontrivial) with ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding v x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding v)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

set_option backward.isDefEq.respectTransparency false in
local instance decompositionCompletionBaseAlgebra :
    Algebra v.Completion w.Completion :=
  (completionLies v w hwv.out).toAlgebra

local instance decompositionCompletionBaseSMul :
    SMul v.Completion w.Completion :=
  (decompositionCompletionBaseAlgebra v w).toSMul

local instance decompositionCompletionBaseModule :
    Module v.Completion w.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance decompositionGlobalBaseCompletionAlgebra : Algebra K v.Completion :=
  UniformSpace.Completion.algebra (WithAbs v) K

local instance decompositionGlobalBaseCompletionSMul : SMul K v.Completion :=
  (decompositionGlobalBaseCompletionAlgebra v).toSMul

local instance decompositionGlobalBaseCompletionModule : Module K v.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance decompositionGlobalTopCompletionAlgebra : Algebra L w.Completion :=
  UniformSpace.Completion.algebra (WithAbs w) L

local instance decompositionGlobalTopCompletionSMul : SMul L w.Completion :=
  (decompositionGlobalTopCompletionAlgebra w).toSMul

local instance decompositionGlobalTopCompletionModule : Module L w.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance decompositionGlobalBaseTopCompletionAlgebra : Algebra K w.Completion :=
  UniformSpace.Completion.algebra (WithAbs w) K

local instance decompositionGlobalBaseTopCompletionSMul : SMul K w.Completion :=
  (decompositionGlobalBaseTopCompletionAlgebra w).toSMul

local instance decompositionGlobalBaseTopCompletionModule : Module K w.Completion :=
  Algebra.toModule

local instance decompositionGlobalCompletionTower : IsScalarTower K L w.Completion :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance decompositionLocalCompletionTower :
    IsScalarTower K v.Completion w.Completion :=
  IsScalarTower.of_algebraMap_eq' (by
    simpa using (completion_lies_comp v w hwv.out).symm)

private theorem decomposition_ring_commutes
    (σ : absoluteValueDecomposition v w) (x : v.Completion) :
    decompositionCompletionRing v w σ
        (algebraMap v.Completion w.Completion x) =
      algebraMap v.Completion w.Completion x := by
  have hfun :
      (fun y ↦ decompositionCompletionRing v w σ
        (completionLies v w hwv.out y)) =
        (fun y ↦ completionLies v w hwv.out y) :=
    (dense_range_embedding v).equalizer
      ((decomposition_ring_isometry v w σ).continuous.comp
        (completion_lies_isometry v w hwv.out).continuous)
      (completion_lies_isometry v w hwv.out).continuous
      (funext fun k ↦ by
        change decompositionCompletionRing v w σ
            (completionLies v w hwv.out (completionEmbedding v k)) =
          completionLies v w hwv.out (completionEmbedding v k)
        have hk : completionLies v w hwv.out (completionEmbedding v k) =
            completionEmbedding w (algebraMap K L k) := by
          simpa only [RingHom.comp_apply] using
            RingHom.congr_fun (completion_lies_comp v w hwv.out) k
        rw [hk]
        rw [decomposition_ring_coe]
        rw [(σ.1 : L ≃ₐ[K] L).commutes])
  exact congrFun hfun x

/-- A decomposition-group element extends to a `K_v`-algebra automorphism
of `L_w`. -/
def decompositionCompletionEquiv
    (σ : absoluteValueDecomposition v w) :
    w.Completion ≃ₐ[v.Completion] w.Completion :=
  AlgEquiv.ofRingEquiv
    (f := decompositionCompletionRing v w σ)
    (decomposition_ring_commutes v w σ)

private theorem decomposition_alg_isometry
    (σ : absoluteValueDecomposition v w) :
    Isometry (decompositionCompletionEquiv v w σ) :=
  decomposition_ring_isometry v w σ

/-- The extension agrees with the original automorphism on the dense copy
of `L` in its completion. -/
@[simp]
theorem decomposition_alg_embedding
    (σ : absoluteValueDecomposition v w) (x : L) :
    decompositionCompletionEquiv v w σ (completionEmbedding w x) =
      completionEmbedding w (σ.1 x) :=
  decomposition_ring_coe v w σ x

/-- The extension of a decomposition-group element is continuous. -/
theorem decomposition_alg_continuous
    (σ : absoluteValueDecomposition v w) :
    Continuous (decompositionCompletionEquiv v w σ) :=
  (decomposition_alg_isometry v w σ).continuous

/-- The continuous extension of a decomposition-group element to `L_w` is
unique. -/
theorem decomposition_alg_unique
    (σ : absoluteValueDecomposition v w)
    (F : w.Completion ≃ₐ[v.Completion] w.Completion)
    (hF : Continuous F)
    (hext : ∀ x : L,
      F (completionEmbedding w x) = completionEmbedding w (σ.1 x)) :
    F = decompositionCompletionEquiv v w σ := by
  apply AlgEquiv.ext
  have hfun : (fun y ↦ F y) =
      (fun y ↦ decompositionCompletionEquiv v w σ y) :=
    (dense_range_embedding w).equalizer hF
      (decomposition_alg_continuous v w σ)
      (funext fun x ↦ by
        change F (completionEmbedding w x) =
          decompositionCompletionEquiv v w σ (completionEmbedding w x)
        rw [decomposition_alg_embedding]
        exact hext x)
  exact congrFun hfun

/-- Milne's homomorphism `G_w → Gal(L_w/K_v)`. -/
def decompositionCompletionHom :
    absoluteValueDecomposition v w →* Gal(w.Completion/v.Completion) where
  toFun := decompositionCompletionEquiv v w
  map_one' := by
    apply AlgEquiv.ext
    have hfun : (decompositionCompletionEquiv v w 1 :
        w.Completion → w.Completion) = id :=
      UniformSpace.Completion.denseRange_coe.equalizer
        (decomposition_alg_isometry v w 1).continuous
        continuous_id
        (funext fun x ↦ by
          change decompositionCompletionEquiv v w 1
              (completionEmbedding w x.ofAbs) = completionEmbedding w x.ofAbs
          rw [decomposition_alg_embedding]
          simp)
    exact congrFun hfun
  map_mul' := by
    intro σ τ
    apply AlgEquiv.ext
    have hfun : (decompositionCompletionEquiv v w (σ * τ) :
        w.Completion → w.Completion) =
        fun x ↦ decompositionCompletionEquiv v w σ
          (decompositionCompletionEquiv v w τ x) :=
      UniformSpace.Completion.denseRange_coe.equalizer
        (decomposition_alg_isometry v w (σ * τ)).continuous
        ((decomposition_alg_isometry v w σ).continuous.comp
          (decomposition_alg_isometry v w τ).continuous)
        (funext fun x ↦ by
          change decompositionCompletionEquiv v w (σ * τ)
              (completionEmbedding w x.ofAbs) =
            decompositionCompletionEquiv v w σ
              (decompositionCompletionEquiv v w τ
                (completionEmbedding w x.ofAbs))
          rw [decomposition_alg_embedding]
          rw [decomposition_alg_embedding]
          rw [decomposition_alg_embedding]
          rfl)
    exact congrFun hfun

/-- Distinct decomposition-group elements induce distinct automorphisms of
the completion. -/
theorem decomposition_alg_injective :
    Function.Injective (decompositionCompletionEquiv v w) := by
  intro σ τ h
  ext x
  apply (completionEmbedding w).injective
  have hx := DFunLike.congr_fun h (completionEmbedding w x)
  rw [decomposition_alg_embedding,
    decomposition_alg_embedding] at hx
  exact hx

/-- The homomorphism `G_w → Gal(L_w/K_v)` is injective, the first half of
Milne's Proposition 8.10. -/
theorem decomp_compl_injec :
    Function.Injective (decompositionCompletionHom v w) :=
  decomposition_alg_injective v w

private theorem norm_completion_alg
    [Fact v.IsNontrivial]
    [FiniteDimensional v.Completion w.Completion]
    [IsUltrametricDist v.Completion]
    (φ : w.Completion ≃ₐ[v.Completion] w.Completion) (x : w.Completion) :
    ‖φ x‖ = ‖x‖ := by
  letI : Algebra.IsAlgebraic v.Completion w.Completion :=
    Algebra.IsAlgebraic.of_finite v.Completion w.Completion
  have hnorm : NormedField.toAbsoluteValue w.Completion =
      completeAbsoluteValue v.Completion w.Completion :=
    complete_absolute_unique v.Completion w.Completion
      (NormedField.toAbsoluteValue w.Completion) (fun y => by
        change ‖algebraMap v.Completion w.Completion y‖ = ‖y‖
        simpa only [dist_zero_right, map_zero] using
          (completion_lies_isometry v w hwv.out).dist_eq y 0)
  change NormedField.toAbsoluteValue w.Completion (φ x) =
    NormedField.toAbsoluteValue w.Completion x
  rw [hnorm]
  exact (spectralNorm_eq_of_equiv φ x).symm

private theorem isometry_completion_alg
    [Fact v.IsNontrivial]
    [FiniteDimensional v.Completion w.Completion]
    [IsUltrametricDist v.Completion]
    (φ : w.Completion ≃ₐ[v.Completion] w.Completion) : Isometry φ := by
  apply AddMonoidHomClass.isometry_of_norm
  exact norm_completion_alg v w φ

/-- Restriction of a local automorphism to the embedded normal global
field.  Normality ensures that the image of `L` is again `L`. -/
def restrictCompletionAlg
    [Normal K L]
    (φ : w.Completion ≃ₐ[v.Completion] w.Completion) : Gal(L/K) :=
  (φ.restrictScalars K).toAlgHom.restrictNormal' L

@[simp]
theorem embedding_restrict_alg
    [Normal K L]
    (φ : w.Completion ≃ₐ[v.Completion] w.Completion) (x : L) :
    completionEmbedding w (restrictCompletionAlg v w φ x) =
      φ (completionEmbedding w x) :=
  AlgHom.restrictNormal_commutes (φ.restrictScalars K).toAlgHom L x

/-- A local automorphism restricts to an element of the decomposition
group because local automorphisms preserve the unique extended norm. -/
def restrictAlgDecomposition
    [Normal K L] [Fact v.IsNontrivial]
    [FiniteDimensional v.Completion w.Completion]
    [IsUltrametricDist v.Completion]
    (φ : w.Completion ≃ₐ[v.Completion] w.Completion) :
    absoluteValueDecomposition v w := by
  refine ⟨restrictCompletionAlg v w φ, ?_⟩
  intro x
  rw [← norm_completionEmbedding w]
  rw [embedding_restrict_alg v w]
  rw [norm_completion_alg v w]
  exact norm_completionEmbedding w x

private theorem decompositionCompletion_restrict
    [Normal K L] [Fact v.IsNontrivial]
    [FiniteDimensional v.Completion w.Completion]
    [IsUltrametricDist v.Completion]
    (φ : w.Completion ≃ₐ[v.Completion] w.Completion) :
    decompositionCompletionEquiv v w
        (restrictAlgDecomposition v w φ) = φ := by
  apply AlgEquiv.ext
  have hfun : (fun y ↦ decompositionCompletionEquiv v w
      (restrictAlgDecomposition v w φ) y) =
        (fun y ↦ φ y) :=
    (dense_range_embedding w).equalizer
      (decomposition_alg_continuous v w _)
      (isometry_completion_alg v w φ).continuous
      (funext fun x ↦ by
        change decompositionCompletionEquiv v w
            (restrictAlgDecomposition v w φ)
              (completionEmbedding w x) = φ (completionEmbedding w x)
        rw [decomposition_alg_embedding]
        exact embedding_restrict_alg v w φ x)
  exact congrFun hfun

/-- The homomorphism `G_w → Gal(L_w/K_v)` is surjective for a finite
completed normal extension. -/
theorem decomp_compl_surje
    [Normal K L] [Fact v.IsNontrivial]
    [FiniteDimensional v.Completion w.Completion]
    [IsUltrametricDist v.Completion] :
    Function.Surjective (decompositionCompletionHom v w) := by
  intro φ
  refine ⟨restrictAlgDecomposition v w φ, ?_⟩
  exact decompositionCompletion_restrict v w φ

/-- Milne, Proposition 8.10: the decomposition group at `w` is the Galois
group of the corresponding extension of completions. -/
def decompositionGroupCompletion
    [Normal K L] [Fact v.IsNontrivial]
    [FiniteDimensional v.Completion w.Completion]
    [IsUltrametricDist v.Completion] :
    absoluteValueDecomposition v w ≃*
      Gal(w.Completion/v.Completion) :=
  MulEquiv.ofBijective (decompositionCompletionHom v w)
    ⟨decomp_compl_injec v w,
      decomp_compl_surje v w⟩

/-- Proposition 8.10 for a finite normal global extension at a
nonarchimedean absolute value.  Finiteness of `L_w/K_v` follows from the
completed tensor-product decomposition of Proposition 8.2. -/
def decompositionCompletionExtension
    [Normal K L] [FiniteDimensional K L] [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] :
    absoluteValueDecomposition v w ≃*
      Gal(w.Completion/v.Completion) := by
  let W := {u : AbsoluteValue L ℝ // AbsoluteValue.LiesOver u v}
  let u : W := ⟨w, hwv.out⟩
  letI : Module.Finite v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  letI : Module.Finite v.Completion (L ⊗[K] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  letI : Module.Finite v.Completion w.Completion :=
    Module.Finite.of_surjective
      (completionTensorPlace v u).toLinearMap
      (completions_component_surjective v u)
  exact decompositionGroupCompletion v w

end Completion

section InfiniteCompletion

open NumberField

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L] [FiniteDimensional K L]
  (v : InfinitePlace K) (w : InfinitePlace L)
  [hwv : Fact (AbsoluteValue.LiesOver w.1 v.1)]

private local instance decompositionInfiniteBaseNontrivial :
    Fact v.1.IsNontrivial :=
  ⟨infinite_place_nontrivial v⟩

private local instance decompositionInfiniteAbsoluteLiesOver :
    AbsoluteValue.LiesOver w.1 v.1 :=
  hwv.out

set_option backward.isDefEq.respectTransparency false in
local instance decompositionInfiniteCompletionAlgebra :
    Algebra v.1.Completion w.1.Completion :=
  (completionLies v.1 w.1 hwv.out).toAlgebra

local instance decompositionInfiniteCompletionSMul :
    SMul v.1.Completion w.1.Completion :=
  (decompositionInfiniteCompletionAlgebra v w).toSMul

local instance decompositionInfiniteCompletionModule :
    Module v.1.Completion w.1.Completion :=
  Algebra.toModule

local instance decompositionInfiniteCompletionNormedSpace :
    NormedSpace v.1.Completion w.1.Completion where
  norm_smul_le r x := by
    change ‖algebraMap v.1.Completion w.1.Completion r * x‖ ≤ ‖r‖ * ‖x‖
    have hr : ‖algebraMap v.1.Completion w.1.Completion r‖ = ‖r‖ := by
      simpa only [dist_zero_right, map_zero] using
        (completion_lies_isometry v.1 w.1 hwv.out).dist_eq r 0
    calc
      ‖algebraMap v.1.Completion w.1.Completion r * x‖ ≤
          ‖algebraMap v.1.Completion w.1.Completion r‖ * ‖x‖ :=
        norm_mul_le _ _
      _ = ‖r‖ * ‖x‖ := by rw [hr]

set_option backward.isDefEq.respectTransparency false in
local instance decompositionInfiniteGlobalBaseCompletionAlgebra :
    Algebra K v.1.Completion :=
  UniformSpace.Completion.algebra (WithAbs v.1) K

local instance decompositionInfiniteGlobalBaseCompletionSMul :
    SMul K v.1.Completion :=
  (decompositionInfiniteGlobalBaseCompletionAlgebra v).toSMul

local instance decompositionInfiniteGlobalBaseCompletionModule :
    Module K v.1.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance decompositionInfiniteGlobalTopCompletionAlgebra :
    Algebra L w.1.Completion :=
  UniformSpace.Completion.algebra (WithAbs w.1) L

local instance decompositionInfiniteGlobalTopCompletionSMul :
    SMul L w.1.Completion :=
  (decompositionInfiniteGlobalTopCompletionAlgebra w).toSMul

local instance decompositionInfiniteGlobalTopCompletionModule :
    Module L w.1.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance decompositionInfiniteGlobalBaseTopCompletionAlgebra :
    Algebra K w.1.Completion :=
  UniformSpace.Completion.algebra (WithAbs w.1) K

local instance decompositionInfiniteGlobalBaseTopCompletionSMul :
    SMul K w.1.Completion :=
  (decompositionInfiniteGlobalBaseTopCompletionAlgebra w).toSMul

local instance decompositionInfiniteGlobalBaseTopCompletionModule :
    Module K w.1.Completion :=
  Algebra.toModule

local instance decompositionInfiniteGlobalCompletionTower :
    IsScalarTower K L w.1.Completion :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance decompositionInfiniteLocalCompletionTower :
    IsScalarTower K v.1.Completion w.1.Completion :=
  IsScalarTower.of_algebraMap_eq' (by
    simpa using (completion_lies_comp v.1 w.1 hwv.out).symm)

set_option maxHeartbeats 1000000 in
-- The complex-base case unfolds several completion equivalences.
omit [Algebra.IsSeparable K L] [FiniteDimensional K L] in
/-- Every automorphism of an archimedean completion over the completed base
field is an isometry.  After identifying the completions with `ℝ` or `ℂ`,
the automorphism is respectively the identity, the identity or conjugation,
or the identity over a complex base. -/
theorem infinite_alg_isometry
    (φ : w.1.Completion ≃ₐ[v.1.Completion] w.1.Completion) :
    Isometry φ := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rcases w.isReal_or_isComplex with hw | hw
  · let ew := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let Ew := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let f : ℝ ≃+* ℝ :=
      ew.symm.trans (φ.toRingEquiv.trans ew)
    have hf : f.toRingHom = RingHom.id ℝ := Subsingleton.elim _ _
    have hf_ew (y : w.1.Completion) : f (ew y) = ew (φ y) := by
      dsimp [f]
      rw [ew.symm_apply_apply]
    have hfx : ew (φ x) = ew x := by
      have h := RingHom.congr_fun hf (ew x)
      change f (ew x) = ew x at h
      rw [hf_ew] at h
      exact h
    have hew_norm (y : w.1.Completion) : ‖ew y‖ = ‖y‖ := by
      have h := Ew.isometry_toFun.dist_eq y 0
      change dist (ew y) (ew 0) = dist y 0 at h
      have hzero : ew (0 : w.1.Completion) = 0 := ew.map_zero
      calc
        ‖ew y‖ = dist (ew y) 0 := (dist_zero_right (ew y)).symm
        _ = dist (ew y) (ew 0) :=
          congrArg (fun z : ℝ => dist (ew y) z) hzero.symm
        _ = dist y 0 := h
        _ = ‖y‖ := dist_zero_right y
    rw [← hew_norm (φ x), hfx, hew_norm]
  · rcases v.isReal_or_isComplex with hv | hv
    · let ev := InfinitePlace.Completion.ringEquivRealOfIsReal hv
      let ew := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      let Ew := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
      have hlie :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
      have he :
          (algebraMap ℝ ℂ).comp ev.toRingHom =
            ew.toRingHom.comp
              (algebraMap v.1.Completion w.1.Completion) := by
        ext y
        simp [ev, ew, InfinitePlace.Completion.ringEquivRealOfIsReal,
          InfinitePlace.Completion.ringEquivComplexOfIsComplex,
          InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      let f : ℂ ≃+* ℂ :=
        ew.symm.trans (φ.toRingEquiv.trans ew)
      have hf_ew (y : w.1.Completion) : f (ew y) = ew (φ y) := by
        dsimp [f]
        rw [ew.symm_apply_apply]
      have hfReal (r : ℝ) :
          f (algebraMap ℝ ℂ r) = algebraMap ℝ ℂ r := by
        have hpre :
            ew.symm (algebraMap ℝ ℂ r) =
              algebraMap v.1.Completion w.1.Completion
                (ev.symm r) := by
          apply ew.injective
          rw [ew.apply_symm_apply]
          have h := RingHom.congr_fun he (ev.symm r)
          change (algebraMap ℝ ℂ) (ev (ev.symm r)) =
            ew (algebraMap v.1.Completion w.1.Completion (ev.symm r)) at h
          rw [ev.apply_symm_apply] at h
          exact h
        change ew (φ (ew.symm (algebraMap ℝ ℂ r))) =
          algebraMap ℝ ℂ r
        rw [hpre, φ.commutes]
        have h := RingHom.congr_fun he (ev.symm r)
        change (algebraMap ℝ ℂ) (ev (ev.symm r)) =
          ew (algebraMap v.1.Completion w.1.Completion (ev.symm r)) at h
        rw [ev.apply_symm_apply] at h
        exact h.symm
      let fa : ℂ ≃ₐ[ℝ] ℂ := AlgEquiv.ofRingEquiv (f := f) hfReal
      have hnormf (z : ℂ) : ‖f z‖ = ‖z‖ := by
        rcases Complex.real_algHom_eq_id_or_conj fa.toAlgHom with h | h
        · have hz := DFunLike.congr_fun h z
          change f z = z at hz
          rw [hz]
        · have hz := DFunLike.congr_fun h z
          change f z = starRingEnd ℂ z at hz
          rw [hz, Complex.norm_conj]
      have hew_norm (y : w.1.Completion) : ‖ew y‖ = ‖y‖ := by
        have h := Ew.isometry_toFun.dist_eq y 0
        change dist (ew y) (ew 0) = dist y 0 at h
        have hzero : ew (0 : w.1.Completion) = 0 := ew.map_zero
        calc
          ‖ew y‖ = dist (ew y) 0 := (dist_zero_right (ew y)).symm
          _ = dist (ew y) (ew 0) :=
            congrArg (fun z : ℂ => dist (ew y) z) hzero.symm
          _ = dist y 0 := h
          _ = ‖y‖ := dist_zero_right y
      calc
        ‖φ x‖ = ‖ew (φ x)‖ := (hew_norm (φ x)).symm
        _ = ‖f (ew x)‖ := congrArg norm (hf_ew x).symm
        _ = ‖ew x‖ := hnormf _
        _ = ‖x‖ := hew_norm x
    · let ev := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
      let ew := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      let Ew := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
      let f : ℂ ≃+* ℂ :=
        ew.symm.trans (φ.toRingEquiv.trans ew)
      have hf_ew (y : w.1.Completion) : f (ew y) = ew (φ y) := by
        dsimp [f]
        rw [ew.symm_apply_apply]
      have hf : f = RingEquiv.refl ℂ := by
        ext z
        rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
            w v with h | h
        · letI : NumberField.ComplexEmbedding.LiesOver
              w.embedding v.embedding := ⟨h⟩
          have hlie :=
            InfinitePlace.Completion.liesOver_extensionEmbedding (v := v) w
          let y : v.1.Completion := ev.symm z
          have hy : ew (algebraMap v.1.Completion w.1.Completion y) = z := by
            change InfinitePlace.Completion.extensionEmbedding w
                (algebraMap v.1.Completion w.1.Completion y) = z
            calc
              _ = InfinitePlace.Completion.extensionEmbedding v y :=
                RingHom.congr_fun hlie.over y
              _ = z := ev.apply_symm_apply z
          change ew (φ (ew.symm z)) = z
          rw [show ew.symm z =
              algebraMap v.1.Completion w.1.Completion y by
            apply ew.injective
            simp [hy]]
          rw [φ.commutes, hy]
        · letI : NumberField.ComplexEmbedding.LiesOver
              (NumberField.ComplexEmbedding.conjugate w.embedding) v.embedding :=
            ⟨h⟩
          have hlie :=
            InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding (v := v) w
          let y : v.1.Completion :=
            ev.symm (starRingEnd ℂ z)
          have hy : ew (algebraMap v.1.Completion w.1.Completion y) = z := by
            have hc := RingHom.congr_fun hlie.over y
            change starRingEnd ℂ
                (ew (algebraMap v.1.Completion w.1.Completion y)) = ev y at hc
            rw [show ev y = starRingEnd ℂ z by simp [y]] at hc
            exact star_injective hc
          change ew (φ (ew.symm z)) = z
          rw [show ew.symm z =
              algebraMap v.1.Completion w.1.Completion y by
            apply ew.injective
            simp [hy]]
          rw [φ.commutes, hy]
      have hfx : ew (φ x) = ew x := by
        have h := DFunLike.congr_fun hf (ew x)
        change f (ew x) = ew x at h
        rw [hf_ew] at h
        exact h
      have hew_norm (y : w.1.Completion) : ‖ew y‖ = ‖y‖ := by
        have h := Ew.isometry_toFun.dist_eq y 0
        change dist (ew y) (ew 0) = dist y 0 at h
        have hzero : ew (0 : w.1.Completion) = 0 := ew.map_zero
        calc
          ‖ew y‖ = dist (ew y) 0 := (dist_zero_right (ew y)).symm
          _ = dist (ew y) (ew 0) :=
            congrArg (fun z : ℂ => dist (ew y) z) hzero.symm
          _ = dist y 0 := h
          _ = ‖y‖ := dist_zero_right y
      rw [← hew_norm (φ x), hfx, hew_norm]

/-- Restriction of an automorphism of an archimedean completion to the global
field, regarded as an element of the decomposition group. -/
def restrictInfiniteDecomposition
    [Normal K L]
    (φ : w.1.Completion ≃ₐ[v.1.Completion] w.1.Completion) :
    absoluteValueDecomposition v.1 w.1 := by
  refine ⟨restrictCompletionAlg v.1 w.1 φ, ?_⟩
  intro x
  rw [← norm_completionEmbedding w.1]
  rw [embedding_restrict_alg v.1 w.1]
  have hnorm : ‖φ (completionEmbedding w.1 x)‖ =
      ‖completionEmbedding w.1 x‖ := by
    have h := (infinite_alg_isometry v w φ).dist_eq
      (completionEmbedding w.1 x) 0
    change dist (φ (completionEmbedding w.1 x)) (φ 0) =
      dist (completionEmbedding w.1 x) 0 at h
    have hzero : φ (0 : w.1.Completion) = 0 := φ.map_zero
    calc
      ‖φ (completionEmbedding w.1 x)‖ =
          dist (φ (completionEmbedding w.1 x)) 0 :=
        (dist_zero_right (φ (completionEmbedding w.1 x))).symm
      _ = dist (φ (completionEmbedding w.1 x)) (φ 0) :=
        congrArg (fun z : w.1.Completion =>
          dist (φ (completionEmbedding w.1 x)) z) hzero.symm
      _ = dist (completionEmbedding w.1 x) 0 := h
      _ = ‖completionEmbedding w.1 x‖ := dist_zero_right _
  rw [hnorm]
  exact norm_completionEmbedding w.1 x

omit [Algebra.IsSeparable K L] [FiniteDimensional K L] in
private theorem decomposition_infinite_restrict
    [Normal K L]
    (φ : w.1.Completion ≃ₐ[v.1.Completion] w.1.Completion) :
    decompositionCompletionEquiv v.1 w.1
        (restrictInfiniteDecomposition v w φ) = φ := by
  apply AlgEquiv.ext
  have hfun : (fun y ↦ decompositionCompletionEquiv v.1 w.1
      (restrictInfiniteDecomposition v w φ) y) =
        (fun y ↦ φ y) :=
    (dense_range_embedding w.1).equalizer
      (decomposition_alg_continuous v.1 w.1 _)
      (infinite_alg_isometry v w φ).continuous
      (funext fun x ↦ by
        change decompositionCompletionEquiv v.1 w.1
            (restrictInfiniteDecomposition v w φ)
              (completionEmbedding w.1 x) =
          φ (completionEmbedding w.1 x)
        rw [decomposition_alg_embedding]
        exact embedding_restrict_alg v.1 w.1 φ x)
  exact congrFun hfun

omit [Algebra.IsSeparable K L] [FiniteDimensional K L] in
/-- The decomposition-group homomorphism is surjective at an infinite place. -/
theorem infinite_decomposition_completion
    [Normal K L] :
    Function.Surjective (decompositionCompletionHom v.1 w.1) := by
  intro φ
  exact ⟨restrictInfiniteDecomposition v w φ,
    decomposition_infinite_restrict v w φ⟩

/-- The archimedean half of Milne, Proposition 8.10: the decomposition group
of an infinite place is the Galois group of the corresponding extension of
completions. -/
def infiniteDecompositionGroup
    [Normal K L] :
    absoluteValueDecomposition v.1 w.1 ≃*
      Gal(w.1.Completion/v.1.Completion) :=
  MulEquiv.ofBijective (decompositionCompletionHom v.1 w.1)
    ⟨decomp_compl_injec v.1 w.1,
      infinite_decomposition_completion v w⟩

end InfiniteCompletion

section Residue

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]

/-- The residue-field row in Milne's diagram after Proposition 8.10:
the decomposition group modulo inertia is the Galois group of the residue
field extension. -/
noncomputable def decompositionInertiaGalois
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    MulAction.stabilizer G P ⧸
        (P.inertia G).subgroupOf (MulAction.stabilizer G P) ≃*
      Gal((B ⧸ P)/(A ⧸ p)) :=
  Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P

end Residue

section Cardinality

variable {R S G : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [IsTorsionFree R S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

/-- The degree formula contained in Milne's Proposition 8.10: the order of
the decomposition group at `P` equals `e(P/p) f(P/p)`. -/
theorem decomposition_inertia_deg
    (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S)
    [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) =
      p.ramificationIdxIn S * p.inertiaDegIn S :=
  Ideal.card_stabilizer_eq p hp P

end Cardinality

end

end Towers.NumberTheory.Milne

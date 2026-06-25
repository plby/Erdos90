import Mathlib.RingTheory.DedekindDomain.Different
import Towers.NumberTheory.Completions.CompletionNormTrace
import Towers.NumberTheory.Completions.CompletedValuationExtension
import Towers.NumberTheory.Completions.NormTraceProduct


/-!
# Trace duals under completion base change and finite products

These are the linear-algebraic parts of compatibility of the different with
completion.  The trace form remains nondegenerate after extending the base
field, dual bases extend coefficientwise, and the trace dual of a product
lattice is the product of the trace duals of its factors.
-/

namespace Towers.NumberTheory.Milne

open Module Polynomial
open scoped BigOperators TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

section IntegralClosureProducts

/-- An element of a finite product is integral exactly when each coordinate
is integral. -/
theorem integral_pi
    {R ι : Type*} {B : ι → Type*}
    [CommRing R] [Finite ι]
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    {x : ∀ i, B i} :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  constructor
  · intro hx i
    exact hx.map (Pi.evalAlgHom R B i)
  · intro hx
    classical
    letI := Fintype.ofFinite ι
    choose p hp_monic hp_zero using hx
    refine ⟨∏ i, p i,
      monic_prod_of_monic Finset.univ p (by simpa using hp_monic), ?_⟩
    rw [← aeval_def]
    ext i
    rw [Polynomial.aeval_pi_apply₂]
    simp only [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by simpa [aeval_def] using hp_zero i)

/-- A finite product of integral closures is the integral closure of the
diagonal base ring in the product algebra. -/
theorem integral_closure_pi
    {R ι : Type*} {O B : ι → Type*}
    [CommRing R] [Finite ι]
    [∀ i, CommRing (O i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra R (B i)] [∀ i, Algebra (O i) (B i)]
    [∀ i, IsIntegralClosure (O i) R (B i)] :
    IsIntegralClosure (∀ i, O i) R (∀ i, B i) where
  algebraMap_injective := by
    intro x y hxy
    funext i
    apply IsIntegralClosure.algebraMap_injective (O i) R (B i)
    exact congrFun hxy i
  isIntegral_iff := by
    intro x
    rw [integral_pi]
    constructor
    · intro hx
      choose y hy using fun i ↦
        (IsIntegralClosure.isIntegral_iff
          (A := O i) (R := R) (B := B i)).mp (hx i)
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩ i
      exact (IsIntegralClosure.isIntegral_iff
        (A := O i) (R := R) (B := B i)).mpr ⟨y i, rfl⟩

end IntegralClosureProducts

section CompletionFactors

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) [IsUltrametricDist v.Completion]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The completion and tensor-product algebra structures require controlled unfolding.
omit [IsUltrametricDist v.Completion] in
/-- Every completion belonging to an extension place is finite over the
completed base field. -/
theorem completion_field_module
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.Finite v.Completion w.1.Completion := by
  let completionBaseAlgebra : Algebra K v.Completion :=
    UniformSpace.Completion.algebra (WithAbs v) K
  letI : Algebra K v.Completion := completionBaseAlgebra
  letI : SMul K v.Completion := completionBaseAlgebra.toSMul
  letI : Module K v.Completion := Algebra.toModule
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Module.Finite v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  letI : Module.Finite v.Completion (L ⊗[K] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  exact Module.Finite.of_surjective
    (completionTensorPlace v w).toLinearMap
    (completions_component_surjective v w)

end CompletionFactors

section ProductCompletionIntegers

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) [IsUltrametricDist v.Completion]

local instance completionExtensionsFinite
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial] :
    Finite {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} :=
  absolute_extensions_separable v

private local instance completionExtensionNontrivial
    [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Fact w.1.IsNontrivial := ⟨by
  rcases (Fact.out : v.IsNontrivial) with ⟨x, hx0, hx1⟩
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · intro hx
    apply hx0
    apply (algebraMap K L).injective
    simpa using hx
  change (w.1.comp (algebraMap K L).injective) x ≠ 1
  rw [w.2.comp_eq]
  exact hx1⟩

set_option backward.isDefEq.respectTransparency false in
private local instance completionProductNormedAlgebra
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    NormedAlgebra v.Completion w.1.Completion where
  toAlgebra := (completionLies v w.1 w.2).toAlgebra
  norm_smul_le r x := by
    change ‖completionLies v w.1 w.2 r * x‖ ≤ ‖r‖ * ‖x‖
    calc
      ‖completionLies v w.1 w.2 r * x‖ ≤
          ‖completionLies v w.1 w.2 r‖ * ‖x‖ := norm_mul_le _ _
      _ = ‖r‖ * ‖x‖ := by
        congr 1
        simpa only [dist_zero_right, map_zero] using
          (completion_lies_isometry v w.1 w.2).dist_eq r 0

private local instance completionProductUpperUltrametric
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    IsUltrametricDist w.1.Completion :=
  IsUltrametricDist.of_normedAlgebra v.Completion

private local instance completionProductFieldFinite
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Module.Finite v.Completion w.1.Completion :=
  completion_field_module v w

private local instance completionProductFieldAlgebraic
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra.IsAlgebraic v.Completion w.1.Completion :=
  Algebra.IsAlgebraic.of_finite v.Completion w.1.Completion

private local instance completionProductUpperIntegerAlgebra
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra (completionIntegerRing w.1) w.1.Completion :=
  (completionIntegerRing w.1).subtype.toAlgebra

private local instance completionProductBaseIntegerAlgebra
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra (completionIntegerRing v) w.1.Completion :=
  ((completionLies v w.1 w.2).comp
    (completionIntegerRing v).subtype).toAlgebra

private local instance completionProductIntegerAlgebra
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra (completionIntegerRing v) (completionIntegerRing w.1) :=
  completionIntegerLies v w.1 w.2

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product reconstructs a compatible algebra tower at every place.
set_option maxHeartbeats 1000000 in
/-- The product of the valuation integer rings in all completions above `v`
is the integral closure of the base valuation integer ring in the product of
the completed fields. -/
theorem integer_rings_pi
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial] :
    IsIntegralClosure
      (∀ w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v},
        completionIntegerRing w.1)
      (completionIntegerRing v)
      (∀ w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v},
        w.1.Completion) := by
  let W := {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}
  letI (w : W) : IsIntegralClosure (completionIntegerRing w.1)
      (completionIntegerRing v) w.1.Completion :=
    completion_integer_closure v w.1 w.2
      (completionProductFieldAlgebraic v w)
  exact integral_closure_pi

end ProductCompletionIntegers

section BaseChange

variable (K F L : Type u) [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- The trace form remains nondegenerate after arbitrary extension of the
base field, even when the scalar extension is a product rather than a field. -/
theorem form_tensor_nondegenerate :
    (Algebra.traceForm F (F ⊗[K] L)).Nondegenerate := by
  let b := Module.finBasis K L
  let bF := Algebra.TensorProduct.basis F b
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero
    (Algebra.traceForm F (F ⊗[K] L)) bF
  have hmatrix :
      (Algebra.traceForm F (F ⊗[K] L)).toMatrix bF =
        ((Algebra.traceForm K L).toMatrix b).map (algebraMap K F) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply,
      Algebra.traceForm_apply, Matrix.map_apply]
    rw [show bF i = (1 : F) ⊗ₜ[K] b i by simp [bF],
      show bF j = (1 : F) ⊗ₜ[K] b j by simp [bF]]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_base_change K F L (b i * b j)
  rw [hmatrix]
  change ((algebraMap K F).mapMatrix
    ((Algebra.traceForm K L).toMatrix b)).det ≠ 0
  rw [← RingHom.map_det]
  simpa using (FaithfulSMul.algebraMap_injective K F).ne
    (det_traceForm_ne_zero b)

/-- Under scalar extension, the trace-dual basis is the scalar extension of
the original trace-dual basis. -/
theorem form_dual_basis
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    (Algebra.traceForm F (F ⊗[K] L)).dualBasis
        (form_tensor_nondegenerate K F L)
        (Algebra.TensorProduct.basis F b) =
      Algebra.TensorProduct.basis F b.traceDual := by
  apply DFunLike.coe_injective
  rw [LinearMap.BilinForm.dualBasis_eq_iff]
  intro i j
  simp only [Algebra.TensorProduct.basis_apply, Algebra.traceForm_apply]
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    tmul_base_change]
  rw [mul_comm, b.trace_mul_traceDual]
  split <;> simp_all

/-- Consequently, the trace dual of a scalar-extended lattice presented by
a basis is spanned by the scalar extensions of the original dual basis. -/
theorem dual_submodule_basis
    {C : Type u} [CommRing C] [Algebra C F]
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    (Algebra.traceForm F (F ⊗[K] L)).dualSubmodule
        (Submodule.span C
          (Set.range (Algebra.TensorProduct.basis F b))) =
      Submodule.span C
        (Set.range (Algebra.TensorProduct.basis F b.traceDual)) := by
  rw [(Algebra.traceForm F (F ⊗[K] L)).dualSubmodule_span_of_basis
    (form_tensor_nondegenerate K F L)]
  congr 1
  exact congrArg Set.range
    (congrArg DFunLike.coe
      (form_dual_basis K F L b))

end BaseChange

section Product

universe v

variable {A K ι : Type*} [CommRing A] [Field K] [Finite ι]
variable (L : ι → Type*) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
variable [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]
variable [Algebra A K] [∀ i, Module A (L i)] [∀ i, IsScalarTower A K (L i)]

noncomputable local instance : Fintype ι := Fintype.ofFinite ι
noncomputable local instance : DecidableEq ι := Classical.decEq ι

private theorem form_pi_single
    (x : ∀ i, L i) (i : ι) (y : L i) :
    Algebra.traceForm K (∀ i, L i) x (Pi.single i y) =
      Algebra.traceForm K (L i) (x i) y := by
  classical
  rw [Algebra.traceForm_apply, algebraTrace_pi L,
    Algebra.traceForm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- A finite product of finite separable field extensions has nondegenerate
trace form. -/
theorem trace_pi_nondegenerate
    [∀ i, Algebra.IsSeparable K (L i)] :
    (Algebra.traceForm K (∀ i, L i)).Nondegenerate := by
  classical
  constructor
  · intro x hx
    funext i
    apply (traceForm_nondegenerate K (L i)).1
    intro y
    have h := hx (Pi.single i y)
    rw [form_pi_single L x i y] at h
    exact h
  · intro y hy
    funext i
    apply (traceForm_nondegenerate K (L i)).2
    intro x
    have h := hy (Pi.single i x)
    rw [show Algebra.traceForm K (∀ i, L i) (Pi.single i x) y =
        Algebra.traceForm K (∀ i, L i) y (Pi.single i x) by
          simp only [Algebra.traceForm_apply, mul_comm]] at h
    rw [form_pi_single L y i x,
      Algebra.traceForm_apply, mul_comm] at h
    exact h

/-- The trace dual of a product lattice is the product of the trace duals
of its factors. -/
theorem dual_submodule_pi
    (O : ∀ i, Submodule A (L i)) :
    (Algebra.traceForm K (∀ i, L i)).dualSubmodule
        (Submodule.pi Set.univ O) =
      Submodule.pi Set.univ
        (fun i => (Algebra.traceForm K (L i)).dualSubmodule (O i)) := by
  classical
  ext x
  rw [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_pi]
  constructor
  · intro hx i _
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    let z : ∀ j, L j := Pi.single i y
    have hz : z ∈ Submodule.pi Set.univ O := by
      rw [Submodule.mem_pi]
      intro j _
      by_cases hji : j = i
      · subst j
        simpa [z] using hy
      · simp [z, Pi.single_eq_of_ne hji]
    have hglobal := hx z hz
    change Algebra.traceForm K (∀ i, L i) x (Pi.single i y) ∈ 1 at hglobal
    rw [form_pi_single L x i y] at hglobal
    exact hglobal
  · intro hx y hy
    rw [Algebra.traceForm_apply, algebraTrace_pi L]
    have hcomp : ∀ i,
        Algebra.trace K (L i) (x i * y i) ∈ (1 : Submodule A K) := by
      intro i
      have hxi := hx i (Set.mem_univ i)
      rw [LinearMap.BilinForm.mem_dualSubmodule] at hxi
      have hi := hxi (y i) ((Submodule.mem_pi.mp hy) i (Set.mem_univ i))
      simpa only [Algebra.traceForm_apply] using hi
    simp only [Pi.mul_apply]
    exact Submodule.sum_mem _ fun i _ => hcomp i

end Product

end


end Towers.NumberTheory.Milne

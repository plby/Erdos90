import Towers.NumberTheory.Completions.TensorDecomposition
import Towers.NumberTheory.Completions.NormTraceProduct


/-!
# Milne, Chapter 8, Corollary 8.4: norm and trace over completions

The canonical decomposition from Proposition 8.2 identifies the scalar
extension of `L` to the completion at `v` with the product of all completions
of `L` above `v`.  Transporting norm and trace through this equivalence gives
the product and sum formulas of Corollary 8.4.
-/

namespace Towers.NumberTheory.Milne

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

/-- Norm commutes with extension of scalars on a pure tensor. -/
theorem algebra_tmul_change
    (R S L : Type u) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] [Module.Free R L] [Module.Finite R L]
    (x : L) :
    Algebra.norm S ((1 : S) ⊗ₜ[R] x : S ⊗[R] L) =
      algebraMap R S (Algebra.norm R x) := by
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul x,
    LinearMap.det_baseChange, Algebra.norm_apply]

/-- Trace commutes with extension of scalars on a pure tensor. -/
theorem tmul_base_change
    (R S L : Type u) [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] [Module.Free R L] [Module.Finite R L]
    (x : L) :
    Algebra.trace S (S ⊗[R] L) ((1 : S) ⊗ₜ[R] x) =
      algebraMap R S (Algebra.trace R L x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul x,
    LinearMap.trace_baseChange, Algebra.trace_apply]

section Nonarchimedean

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) [IsUltrametricDist v.Completion]

private noncomputable local instance completionNontriviallyNormedField
    [Fact v.IsNontrivial] :
    NontriviallyNormedField v.Completion :=
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
local instance cor84CompletionBaseAlgebra : Algebra K v.Completion :=
  UniformSpace.Completion.algebra (WithAbs v) K

local instance cor84CompletionBaseSMul : SMul K v.Completion :=
  (cor84CompletionBaseAlgebra v).toSMul

local instance cor84CompletionBaseModule : Module K v.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance cor84CompletionPlaceAlgebra
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra v.Completion w.1.Completion :=
  (completionLies v w.1 w.2).toAlgebra

local instance cor84CompletionPlaceSMul
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    SMul v.Completion w.1.Completion :=
  (cor84CompletionPlaceAlgebra v w).toSMul

local instance cor84CompletionPlaceModule
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Module v.Completion w.1.Completion :=
  Algebra.toModule

local instance cor84CompletionPlaceFree
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Module.Free v.Completion w.1.Completion :=
  Module.Free.of_divisionRing v.Completion w.1.Completion

local instance cor84ExtensionsFinite
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial] :
    Finite {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} :=
  absolute_extensions_separable v

noncomputable local instance cor84ExtensionsFintype
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial] :
    Fintype {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} :=
  Fintype.ofFinite _

local instance cor84CompletionTensorFinite [FiniteDimensional K L] :
    Module.Finite v.Completion (L ⊗[K] v.Completion) := by
  letI : Module.Finite v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  exact Module.Finite.equiv
    (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv

local instance cor84CompletionTensorFree :
    Module.Free v.Completion (L ⊗[K] v.Completion) :=
  Module.Free.of_divisionRing v.Completion (L ⊗[K] v.Completion)

local instance cor84CompletionPlaceFinite
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Module.Finite v.Completion w.1.Completion :=
  Module.Finite.of_surjective
    (completionTensorPlace v w).toLinearMap
    (completions_component_surjective v w)

set_option maxHeartbeats 800000 in
-- The dependent product of completion modules requires substantial instance synthesis.
/-- Milne's Corollary 8.4: after embedding into the completion at `v`, the
global norm and trace are respectively the product and sum of the local norms
and traces over all extensions of `v` to `L`. -/
theorem completion_norm_trace
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial]
    (x : L) :
    algebraMap K v.Completion (Algebra.norm K x) =
        ∏ w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v},
          Algebra.norm v.Completion (completionEmbedding w.1 x) ∧
      algebraMap K v.Completion (Algebra.trace K L x) =
        ∑ w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v},
          Algebra.trace v.Completion w.1.Completion (completionEmbedding w.1 x) := by
  let y : L ⊗[K] v.Completion := x ⊗ₜ[K] (1 : v.Completion)
  let e := completionTensorCompletions (K := K) (L := L) v
  have hy (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
      e y w = completionEmbedding w.1 x := by
    change completionTensorPlace v w
      (x ⊗ₜ[K] (1 : v.Completion)) = completionEmbedding w.1 x
    rw [tensor_place_tmul, map_one]
    exact mul_one _
  have hsplit := norm_alg_pi
    (A := fun w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} ↦
      w.1.Completion) e y
  have hnorm_base :
      Algebra.norm v.Completion y =
        algebraMap K v.Completion (Algebra.norm K x) := by
    let c := Algebra.TensorProduct.commRight K v.Completion L
    calc
      Algebra.norm v.Completion y =
          Algebra.norm v.Completion ((1 : v.Completion) ⊗ₜ[K] x) := by
        exact Algebra.norm_eq_of_algEquiv c ((1 : v.Completion) ⊗ₜ[K] x)
      _ = algebraMap K v.Completion (Algebra.norm K x) :=
        algebra_tmul_change K v.Completion L x
  have htrace_base :
      Algebra.trace v.Completion (L ⊗[K] v.Completion) y =
        algebraMap K v.Completion (Algebra.trace K L x) := by
    let c := Algebra.TensorProduct.commRight K v.Completion L
    calc
      Algebra.trace v.Completion (L ⊗[K] v.Completion) y =
          Algebra.trace v.Completion (v.Completion ⊗[K] L)
            ((1 : v.Completion) ⊗ₜ[K] x) := by
        exact Algebra.trace_eq_of_algEquiv c ((1 : v.Completion) ⊗ₜ[K] x)
      _ = algebraMap K v.Completion (Algebra.trace K L x) :=
        tmul_base_change K v.Completion L x
  constructor
  · rw [← hnorm_base]
    simpa only [hy] using hsplit.1
  · rw [← htrace_base]
    simpa only [hy] using hsplit.2

/-- Taking absolute values in the norm identity of Corollary 8.4 expresses
the value of the global norm as the product of the values of the local
norms.  This is the norm-theoretic step in Milne's Proposition 8.7. -/
theorem prod_value_global
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial]
    (x : L) :
    (∏ w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v},
        ‖Algebra.norm v.Completion (completionEmbedding w.1 x)‖) =
      v (Algebra.norm K x) := by
  have hnorm := (completion_norm_trace (K := K) (L := L) v x).1
  have hnorm' := congrArg norm hnorm
  change ‖completionEmbedding v (Algebra.norm K x)‖ =
    ‖∏ w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v},
      Algebra.norm v.Completion (completionEmbedding w.1 x)‖ at hnorm'
  rw [← norm_completionEmbedding v (Algebra.norm K x)]
  rw [norm_prod] at hnorm'
  exact hnorm'.symm

end Nonarchimedean

section Archimedean

open NumberField

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

private noncomputable local instance infiniteCompletionNontriviallyNormedField
    (v : InfinitePlace K) : NontriviallyNormedField v.1.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases infinite_place_nontrivial v with ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding v.1 x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding v.1)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

set_option backward.isDefEq.respectTransparency false in
local instance infiniteCor84CompletionBaseAlgebra (v : InfinitePlace K) :
    Algebra K v.1.Completion :=
  UniformSpace.Completion.algebra (WithAbs v.1) K

local instance infiniteCor84CompletionBaseSMul (v : InfinitePlace K) :
    SMul K v.1.Completion :=
  (infiniteCor84CompletionBaseAlgebra v).toSMul

local instance infiniteCor84CompletionBaseModule (v : InfinitePlace K) :
    Module K v.1.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance infiniteCor84CompletionPlaceAlgebra
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Algebra v.1.Completion w.1.1.Completion :=
  (completionLies v.1 w.1.1
    (infinite_lies_comap v w.1 w.2)).toAlgebra

local instance infiniteCor84CompletionPlaceSMul
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    SMul v.1.Completion w.1.1.Completion :=
  (infiniteCor84CompletionPlaceAlgebra v w).toSMul

local instance infiniteCor84CompletionPlaceModule
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Module v.1.Completion w.1.1.Completion :=
  Algebra.toModule

local instance infiniteCor84CompletionPlaceFree
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Module.Free v.1.Completion w.1.1.Completion :=
  Module.Free.of_divisionRing v.1.Completion w.1.1.Completion

local instance infiniteCor84ExtensionsFinite
    [FiniteDimensional K L] (v : InfinitePlace K) :
    Finite {w : InfinitePlace L // w.comap (algebraMap K L) = v} := by
  let alpha := (Field.exists_primitive_element K L).choose
  letI : Finite (CompletedMinpolyFactor v.1 alpha) :=
    completed_minpoly_factor v.1 alpha
  let halphaIF := (Field.exists_primitive_element K L).choose_spec
  have halpha : Algebra.adjoin K {alpha} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic alpha)]
    exact congrArg IntermediateField.toSubalgebra halphaIF
  exact Finite.of_equiv (CompletedMinpolyFactor v.1 alpha)
    (infinitePlacesMinpoly
      v alpha halpha).symm

noncomputable local instance infiniteCor84ExtensionsFintype
    [FiniteDimensional K L] (v : InfinitePlace K) :
    Fintype {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
  Fintype.ofFinite _

local instance infiniteCor84CompletionTensorFinite
    [FiniteDimensional K L] (v : InfinitePlace K) :
    Module.Finite v.1.Completion (L ⊗[K] v.1.Completion) := by
  letI : Module.Finite v.1.Completion (v.1.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.1.Completion L
  exact Module.Finite.equiv
    (Algebra.TensorProduct.commRight K v.1.Completion L).toLinearEquiv

local instance infiniteCor84CompletionTensorFree (v : InfinitePlace K) :
    Module.Free v.1.Completion (L ⊗[K] v.1.Completion) :=
  Module.Free.of_divisionRing v.1.Completion (L ⊗[K] v.1.Completion)

local instance infiniteCor84CompletionPlaceFinite
    [FiniteDimensional K L] (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Module.Finite v.1.Completion w.1.1.Completion :=
  Module.Finite.of_surjective
    (infiniteTensorPlace v w).toLinearMap
    (infinite_tensor_surjective v w)

set_option maxHeartbeats 800000 in
-- The dependent product of archimedean completion modules requires
-- substantial instance synthesis.
omit [Algebra.IsSeparable K L] in
/-- Milne's Corollary 8.4 at an infinite place: after embedding into the
completion at `v`, the global norm and trace are respectively the product and
sum of the norms and traces in all completions above `v`. -/
theorem infinite_completion_trace
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : InfinitePlace K) (x : L) :
    algebraMap K v.1.Completion (Algebra.norm K x) =
        ∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v},
          Algebra.norm v.1.Completion (completionEmbedding w.1.1 x) ∧
      algebraMap K v.1.Completion (Algebra.trace K L x) =
        ∑ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v},
          Algebra.trace v.1.Completion w.1.1.Completion
            (completionEmbedding w.1.1 x) := by
  let y : L ⊗[K] v.1.Completion :=
    x ⊗ₜ[K] (1 : v.1.Completion)
  let e := infiniteTensorCompletions
    (K := K) (L := L) v
  have hy
      (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
      e y w = completionEmbedding w.1.1 x := by
    rw [infinite_completions_tmul, map_one]
    exact mul_one _
  have hsplit := norm_alg_pi
    (A := fun w : {w : InfinitePlace L // w.comap (algebraMap K L) = v} ↦
      w.1.1.Completion) e y
  have hnorm_base :
      Algebra.norm v.1.Completion y =
        algebraMap K v.1.Completion (Algebra.norm K x) := by
    let c := Algebra.TensorProduct.commRight K v.1.Completion L
    calc
      Algebra.norm v.1.Completion y =
          Algebra.norm v.1.Completion
            ((1 : v.1.Completion) ⊗ₜ[K] x) := by
        exact Algebra.norm_eq_of_algEquiv c
          ((1 : v.1.Completion) ⊗ₜ[K] x)
      _ = algebraMap K v.1.Completion (Algebra.norm K x) :=
        algebra_tmul_change K v.1.Completion L x
  have htrace_base :
      Algebra.trace v.1.Completion (L ⊗[K] v.1.Completion) y =
        algebraMap K v.1.Completion (Algebra.trace K L x) := by
    let c := Algebra.TensorProduct.commRight K v.1.Completion L
    calc
      Algebra.trace v.1.Completion (L ⊗[K] v.1.Completion) y =
          Algebra.trace v.1.Completion (v.1.Completion ⊗[K] L)
            ((1 : v.1.Completion) ⊗ₜ[K] x) := by
        exact Algebra.trace_eq_of_algEquiv c
          ((1 : v.1.Completion) ⊗ₜ[K] x)
      _ = algebraMap K v.1.Completion (Algebra.trace K L x) :=
        tmul_base_change K v.1.Completion L x
  constructor
  · rw [← hnorm_base]
    simpa only [hy] using hsplit.1
  · rw [← htrace_base]
    simpa only [hy] using hsplit.2

end Archimedean

end

end Towers.NumberTheory.Milne

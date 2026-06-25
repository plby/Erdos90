import Submission.NumberTheory.FieldExtensions.SeparableTensorProduct
import Submission.NumberTheory.Completions.CompletionFactorization
import Submission.NumberTheory.Completions.PlaceFactorCorrespondence
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Topology.Algebra.Module.FiniteDimension


/-!
# Milne, Chapter 8, Proposition 8.2: scalar-extension decomposition

For a finite separable extension `L / K` and any field extension `Khat / K`,
the scalar extension `L ⊗[K] Khat` is a finite product of finite separable
field extensions of `Khat`.  Taking `Khat` to be the completion of `K` gives
the algebraic decomposition in Proposition 8.2.

For both nonarchimedean absolute values and infinite places, this file also
constructs the canonical map from the tensor product to the product of the
actual place completions and proves Milne's formula on pure tensors.  The
completed-factor product and a finite-dimensional rank calculation then
identify that canonical map as an algebra equivalence.
-/

namespace Submission.NumberTheory.Milne

open Polynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u v

/-- Milne, Proposition 8.2, algebraic decomposition after extending scalars
to the completed base field.  The theorem is stated for an arbitrary field
extension `Khat / K`, and hence applies in particular to a completion. -/
theorem completion_tensor_pi
    (K L Khat : Type u) [Field K] [Field L] [Field Khat]
    [Algebra K L] [Algebra K Khat] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    ∃ (ι : Type u) (_ : Finite ι) (Li : ι → Type u)
      (_ : ∀ i, Field (Li i)) (_ : ∀ i, Algebra Khat (Li i))
      (_ : (L ⊗[K] Khat) ≃ₐ[Khat] ((i : ι) → Li i)),
      ∀ i, Module.Finite Khat (Li i) ∧ Algebra.IsSeparable Khat (Li i) :=
  tensor_pi_separable K L Khat

/-- If `α` is a primitive element for `L / K`, its image generates every
field factor in the scalar-extension decomposition. -/
theorem tensor_pi_primitive
    (K L Khat : Type u) [Field K] [Field L] [Field Khat]
    [Algebra K L] [Algebra K Khat] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    ∃ (ι : Type u) (_ : Finite ι) (Li : ι → Type u)
      (_ : ∀ i, Field (Li i)) (_ : ∀ i, Algebra Khat (Li i))
      (e : (Khat ⊗[K] L) ≃ₐ[Khat] ((i : ι) → Li i)),
      (∀ i, Algebra.adjoin Khat {e ((1 : Khat) ⊗ₜ[K] α) i} = ⊤) ∧
        ∀ i, Module.Finite Khat (Li i) ∧ Algebra.IsSeparable Khat (Li i) :=
  pi_primitive_element K L Khat α hα

section Nonarchimedean

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
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
/-- The natural `K`-algebra structure on its `v`-completion.  Naming this
instance before the tensor-product declarations avoids an elaboration loop. -/
local instance completionBaseAlgebra : Algebra K v.Completion :=
  UniformSpace.Completion.algebra (WithAbs v) K

local instance completionBaseSMul : SMul K v.Completion :=
  (completionBaseAlgebra v).toSMul

local instance completionBaseModule : Module K v.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
/-- The completed embedding associated with `w | v` supplies the scalar
action of the completed base field on the completed extension. -/
local instance completionPlaceAlgebra
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra v.Completion w.1.Completion :=
  (completionLies v w.1 w.2).toAlgebra

local instance completionPlaceSMul
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    SMul v.Completion w.1.Completion :=
  (completionPlaceAlgebra v w).toSMul

local instance completionPlaceModule
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Module v.Completion w.1.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance completionPlaceBaseAlgebra
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Algebra K w.1.Completion :=
  UniformSpace.Completion.algebra (WithAbs w.1) K

local instance completionPlaceBaseSMul
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    SMul K w.1.Completion :=
  (completionPlaceBaseAlgebra v w).toSMul

local instance completionPlaceBaseModule
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    Module K w.1.Completion :=
  Algebra.toModule

set_option backward.isDefEq.respectTransparency false in
local instance completionPlaceTower
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    IsScalarTower K v.Completion w.1.Completion :=
  IsScalarTower.of_algebraMap_eq' (by
    simpa using (completion_lies_comp v w.1 w.2).symm)

/-- The component of Milne's canonical scalar-extension map belonging to one
extension `w` of `v`. -/
def completionTensorPlace
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    (L ⊗[K] v.Completion) →ₐ[v.Completion] w.1.Completion := by
  let j : L →ₐ[K] w.1.Completion :=
    { toRingHom := completionEmbedding w.1
      commutes' := fun _ => rfl }
  exact (j.liftEquiv K v.Completion L w.1.Completion).comp
    (Algebra.TensorProduct.commRight K v.Completion L).symm.toAlgHom

/-- The canonical scalar-extension map in Milne's Proposition 8.2, indexed
by the absolute values on `L` extending `v`. -/
def tensorPlaceCompletions :
    (L ⊗[K] v.Completion) →ₐ[v.Completion]
      ((w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) →
        w.1.Completion) := by
  exact Pi.algHom v.Completion
    (fun w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} => w.1.Completion)
    (fun w => completionTensorPlace v w)

set_option maxHeartbeats 800000 in
-- Unfolding the tensor commutativity map and the lifted algebra hom is expensive.
omit [IsUltrametricDist v.Completion] in
/-- The component map has Milne's expected formula on pure tensors. -/
@[simp]
theorem tensor_place_tmul
    (a : L) (b : v.Completion)
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    completionTensorPlace v w (a ⊗ₜ[K] b) =
      completionEmbedding w.1 a * completionLies v w.1 w.2 b := by
  simp only [completionEmbedding_apply, WithAbs.equiv_symm_apply]
  change completionLies v w.1 w.2 b * completionEmbedding w.1 a =
    completionEmbedding w.1 a * completionLies v w.1 w.2 b
  exact mul_comm _ _

set_option maxHeartbeats 800000 in
-- The closed-range argument unfolds several scalar-extension module structures.
omit [IsUltrametricDist v.Completion] in
/-- Every component of the canonical map has dense, finite-dimensional range
and is therefore surjective.  This is the topological step in Milne's proof
that the completion belonging to `w` is generated over the completed base by
the image of `L`. -/
theorem completions_component_surjective
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Function.Surjective (completionTensorPlace v w) := by
  let ι : v.Completion →+* w.1.Completion :=
    completionLies v w.1 w.2
  letI : NormedSpace v.Completion w.1.Completion :=
    { norm_smul_le := fun r x => by
        change ‖ι r * x‖ ≤ ‖r‖ * ‖x‖
        have hr : ‖ι r‖ = ‖r‖ := by
          simpa only [dist_zero_right, map_zero] using
            (completion_lies_isometry v w.1 w.2).dist_eq r 0
        calc
          ‖ι r * x‖ ≤ ‖ι r‖ * ‖x‖ := norm_mul_le _ _
          _ = ‖r‖ * ‖x‖ := by rw [hr] }
  letI : Module v.Completion (L ⊗[K] v.Completion) := Algebra.toModule
  letI : Module.Finite v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  letI : Module.Finite v.Completion (L ⊗[K] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  let j : L →ₐ[K] w.1.Completion :=
    { toRingHom := completionEmbedding w.1
      commutes' := fun _ => rfl }
  let φ : (L ⊗[K] v.Completion) →ₐ[v.Completion] w.1.Completion :=
    (j.liftEquiv K v.Completion L w.1.Completion).comp
      (Algebra.TensorProduct.commRight K v.Completion L).symm.toAlgHom
  let Φ : (L ⊗[K] v.Completion) →ₗ[v.Completion] w.1.Completion :=
    φ.toLinearMap
  have h_dense : DenseRange Φ := by
    apply (dense_range_embedding w.1).mono
    rintro _ ⟨l, rfl⟩
    refine ⟨l ⊗ₜ[K] (1 : v.Completion), ?_⟩
    change completionLies v w.1 w.2 1 * completionEmbedding w.1 l =
      completionEmbedding w.1 l
    rw [map_one]
    exact one_mul _
  have hsurj : Function.Surjective Φ := by
    letI : Module.Finite v.Completion Φ.range := Module.Finite.range Φ
    rw [← Set.range_eq_univ, ← Φ.coe_range,
      ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range
  change Function.Surjective Φ
  exact hsurj

set_option maxHeartbeats 800000 in
-- This proof transports surjectivity through tensor commutativity and adjoin.
omit [IsUltrametricDist v.Completion] in
/-- If `α` is primitive for `L / K`, then its image generates the completion
belonging to `w` over the completed base field. -/
theorem adjoin_embedding_top
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤)
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Algebra.adjoin v.Completion {completionEmbedding w.1 α} = ⊤ := by
  let j : L →ₐ[K] w.1.Completion :=
    { toRingHom := completionEmbedding w.1
      commutes' := fun _ => rfl }
  let φ : (v.Completion ⊗[K] L) →ₐ[v.Completion] w.1.Completion :=
    j.liftEquiv K v.Completion L w.1.Completion
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ :=
      completions_component_surjective v w y
    refine ⟨(Algebra.TensorProduct.commRight K v.Completion L).symm x, ?_⟩
    change φ ((Algebra.TensorProduct.commRight K v.Completion L).symm x) = y at hx
    exact hx
  have hgen : Algebra.adjoin v.Completion
      ({(1 : v.Completion) ⊗ₜ[K] α} : Set (v.Completion ⊗[K] L)) = ⊤ := by
    simpa using Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (A := v.Completion) ({α} : Set L) hα
  have hφα : φ ((1 : v.Completion) ⊗ₜ[K] α) = completionEmbedding w.1 α := by
    change completionLies v w.1 w.2 1 * completionEmbedding w.1 α =
      completionEmbedding w.1 α
    rw [map_one]
    exact one_mul _
  calc
    Algebra.adjoin v.Completion {completionEmbedding w.1 α} =
        Algebra.adjoin v.Completion {φ ((1 : v.Completion) ⊗ₜ[K] α)} := by
          rw [hφα]
    _ = (Algebra.adjoin v.Completion
          ({(1 : v.Completion) ⊗ₜ[K] α} : Set (v.Completion ⊗[K] L))).map φ := by
          rw [AlgHom.map_adjoin]
          simp
    _ = (⊤ : Subalgebra v.Completion (v.Completion ⊗[K] L)).map φ := by
          rw [hgen]
    _ = ⊤ := by
      rw [Algebra.map_top, (AlgHom.range_eq_top φ).2 hφ]

omit [IsUltrametricDist v.Completion] in
/-- The completion belonging to `w` is canonically the factor field defined
by the minimal polynomial of the completed image of a primitive element. -/
def completionAdjoinMinpoly
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤)
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    AdjoinRoot (minpoly v.Completion (completionEmbedding w.1 α)) ≃ₐ[v.Completion]
      w.1.Completion := by
  let hgen := adjoin_embedding_top v α hα w
  exact (((Subalgebra.topEquiv (R := v.Completion) (A := w.1.Completion)).symm.trans
    (Subalgebra.equivOfEq ⊤ (Algebra.adjoin v.Completion {completionEmbedding w.1 α})
      hgen.symm)).trans
    (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly v.Completion
      (completionEmbedding w.1 α))).symm

omit [IsUltrametricDist v.Completion] in
/-- The completion-factor equivalence sends the adjoined root to the image
of the primitive element. -/
@[simp]
theorem completion_adjoin_minpoly
    [FiniteDimensional K L] [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤)
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    completionAdjoinMinpoly v α hα w
      (AdjoinRoot.root (minpoly v.Completion (completionEmbedding w.1 α))) =
        completionEmbedding w.1 α := by
  change ((↑(AdjoinRoot.Minpoly.toAdjoin v.Completion
    (completionEmbedding w.1 α) (AdjoinRoot.root
      (minpoly v.Completion (completionEmbedding w.1 α)))) : w.1.Completion)) = _
  rw [AdjoinRoot.root, AdjoinRoot.Minpoly.coe_toAdjoin_mk_X]

local instance completedMinpolyFactorFinite [FiniteDimensional K L] (α : L) :
    Finite (CompletedMinpolyFactor v α) :=
  completed_minpoly_factor v α

noncomputable local instance completedMinpolyFactorFintype
    [FiniteDimensional K L] (α : L) :
    Fintype (CompletedMinpolyFactor v α) :=
  Fintype.ofFinite _

omit [IsUltrametricDist v.Completion] in
/-- The mapped minimal polynomial is the product of all of its distinct monic
irreducible completed factors. -/
theorem mapped_minpoly_completed
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (α : L) :
    (minpoly K α).map (completionEmbedding v) =
      ∏ G : CompletedMinpolyFactor v α, (G.1 : v.Completion[X]) := by
  classical
  let p : v.Completion[X] := (minpoly K α).map (completionEmbedding v)
  have hpmonic : p.Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral α)).map (completionEmbedding v)
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  have hpsep : p.Separable := by
    simpa [p] using Polynomial.Separable.map
      (Algebra.IsSeparable.isSeparable K α : (minpoly K α).Separable)
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors p).Nodup :=
    UniqueFactorizationMonoid.normalizedFactors_nodup hpsep.squarefree.isRadical
  let factors : Finset v.Completion[X] :=
    ⟨UniqueFactorizationMonoid.normalizedFactors p, hnodup⟩
  let FactorMember :=
    {g : v.Completion[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors p}
  letI : Fintype FactorMember := Fintype.ofFinset factors (fun _ => Iff.rfl)
  let e : CompletedMinpolyFactor v α ≃ FactorMember :=
    { toFun := fun g => ⟨g.1,
          (Polynomial.mem_normalizedFactors_iff hp0).2 g.2⟩
      invFun := fun g => ⟨g.1,
          (Polynomial.mem_normalizedFactors_iff hp0).1 g.2⟩
      left_inv := fun g => Subtype.ext rfl
      right_inv := fun g => Subtype.ext rfl }
  change p = _
  rw [← (Polynomial.normalize_eq_self_iff_monic hp0).2 hpmonic]
  rw [← UniqueFactorizationMonoid.prod_normalizedFactors_eq hp0]
  calc
    (UniqueFactorizationMonoid.normalizedFactors p).prod =
        ∏ g : FactorMember, g.1 := by
      change (UniqueFactorizationMonoid.normalizedFactors p).prod =
        ∏ g : factors, g.1
      rw [Finset.prod_coe_sort factors (fun x : v.Completion[X] => x)]
      change (UniqueFactorizationMonoid.normalizedFactors p).prod = factors.prod id
      change (UniqueFactorizationMonoid.normalizedFactors p).prod =
        (⟨UniqueFactorizationMonoid.normalizedFactors p, hnodup⟩ :
          Finset v.Completion[X]).prod id
      rw [Finset.prod_mk, Multiset.map_id]
    _ = ∏ G : CompletedMinpolyFactor v α, G.1 := by
      exact (Fintype.prod_equiv e (fun G => G.1) (fun g => g.1)
        (fun _ => rfl)).symm

set_option maxHeartbeats 3000000 in
-- Power-basis reduction unfolds the canonical maps at every completed factor.
/-- The canonical map to the product of place completions is injective. -/
theorem tensor_completions_injective
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    Function.Injective (tensorPlaceCompletions v :
      (L ⊗[K] v.Completion) →
        ((w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) →
          w.1.Completion)) := by
  classical
  let W := {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}
  let I := CompletedMinpolyFactor v α
  let P : v.Completion[X] := (minpoly K α).map (completionEmbedding v)
  letI : Finite W := absolute_value_extensions v α hα
  letI : Fintype W := Fintype.ofFinite W
  let A := v.Completion ⊗[K] L
  letI : Nontrivial A :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      K v.Completion L (algebraMap K v.Completion).injective
        (algebraMap K L).injective
  let x : A := (1 : v.Completion) ⊗ₜ[K] α
  letI : Module.Finite v.Completion A := Module.Finite.base_change K v.Completion L
  letI : Module.Finite v.Completion (L ⊗[K] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  have hxgen : Algebra.adjoin v.Completion {x} = ⊤ := by
    simpa [x] using Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (A := v.Completion) ({α} : Set L) hα
  let pb : PowerBasis v.Completion A :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral x) hxgen
  let ψ : A →ₐ[v.Completion] (w : W) → w.1.Completion :=
    (tensorPlaceCompletions (K := K) (L := L) v).comp
      (Algebra.TensorProduct.commRight K v.Completion L).toAlgHom
  have hψx (w : W) : ψ x w = completionEmbedding w.1 α := by
    change completionTensorPlace v w
      ((Algebra.TensorProduct.commRight K v.Completion L) x) = _
    rw [show (Algebra.TensorProduct.commRight K v.Completion L) x =
      α ⊗ₜ[K] (1 : v.Completion) by rfl]
    rw [tensor_place_tmul, map_one]
    exact mul_one _
  have hprod : (∏ G : I, (G.1 : v.Completion[X])) = P := by
    exact (mapped_minpoly_completed v α).symm
  have hPdegree : P.natDegree = pb.dim := by
    calc
      P.natDegree = (minpoly K α).natDegree :=
        (minpoly.monic (Algebra.IsIntegral.isIntegral α)).natDegree_map _
      _ = Module.finrank K L := by
        let pbK : PowerBasis K L :=
          PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral α) hα
        calc
          (minpoly K α).natDegree = pbK.dim := by
            rw [show α = pbK.gen by rfl]
            exact pbK.natDegree_minpoly
          _ = Module.finrank K L := pbK.finrank.symm
      _ = Module.finrank v.Completion A := Module.finrank_baseChange.symm
      _ = pb.dim := pb.finrank
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply sub_eq_zero.mp
    let z := a - b
    have hz : ψ z = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨q, hqdeg, hzq⟩ := pb.exists_eq_aeval z
    have hGdvd (G : I) : (G.1 : v.Completion[X]) ∣ q := by
      let w : W := completedMinpolyExtension v α hα G
      have hwzero : ψ z w = 0 := congrFun hz w
      have heval : aeval (completionEmbedding w.1 α) q = 0 := by
        rw [hzq, ← Polynomial.aeval_algHom_apply] at hwzero
        rw [Polynomial.aeval_pi_apply₂] at hwzero
        simpa [show pb.gen = x by rfl, hψx] using hwzero
      have hmin : minpoly v.Completion (completionEmbedding w.1 α) ∣ q :=
        minpoly.dvd v.Completion _ heval
      have hround := congrArg Subtype.val
        (minpoly_place_roundtrip v α hα G)
      change minpoly v.Completion (completionEmbedding w.1 α) = G.1 at hround
      rwa [hround] at hmin
    have hall : (∏ G : I, (G.1 : v.Completion[X])) ∣ q := by
      apply Fintype.prod_dvd_of_coprime
      · exact pairwise_monic_irreducible
          (fun G : I => G.1) (fun G => G.2.2.1) (fun G => G.2.1)
          (fun _ _ h => Subtype.ext h)
      · exact hGdvd
    have hPq : P ∣ q := by
      rwa [hprod] at hall
    have hqzero : q = 0 := by
      by_contra hq
      exact (not_lt_of_ge (natDegree_le_of_dvd hPq hq))
        (hPdegree ▸ hqdeg)
    rw [hqzero, map_zero] at hzq
    exact hzq
  intro a b hab
  apply (Algebra.TensorProduct.commRight K v.Completion L).symm.injective
  apply hψ
  simpa [ψ] using hab

set_option synthInstance.maxHeartbeats 500000 in
-- The rank comparison unfolds each completion through its adjoin-root model.
set_option maxHeartbeats 2000000 in
/-- The canonical map in Proposition 8.2, for a chosen primitive element,
is an algebra equivalence. -/
def tensorCompletionsPrimitive
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    (L ⊗[K] v.Completion) ≃ₐ[v.Completion]
      ((w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) →
        w.1.Completion) := by
  classical
  let W := {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}
  letI : Finite W := absolute_value_extensions v α hα
  letI : Fintype W := Fintype.ofFinite W
  let g : W → v.Completion[X] := fun w =>
    (absoluteCompletedMinpoly v α w).1
  let e := completedMinpolyExtensions v α hα
  have hp_prod : (minpoly K α).map (completionEmbedding v) = ∏ w : W, g w := by
    rw [mapped_minpoly_completed v α]
    exact Fintype.prod_equiv e (fun G => G.1) g (fun G => by
      exact congrArg Subtype.val (e.left_inv G).symm)
  letI : Module.Finite v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  letI : Module.Finite v.Completion (L ⊗[K] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  letI (w : W) : Module.Finite v.Completion w.1.Completion := by
    exact Module.Finite.of_surjective
      (completionTensorPlace v w).toLinearMap
      (completions_component_surjective v w)
  have hcoord (w : W) :
      Module.finrank v.Completion w.1.Completion = (g w).natDegree := by
    let G := absoluteMinpolyFactor v α w.1 w.2
    let ew := completionAdjoinMinpoly v α hα w
    calc
      Module.finrank v.Completion w.1.Completion =
          Module.finrank v.Completion
            (AdjoinRoot (minpoly v.Completion (completionEmbedding w.1 α))) :=
        ew.toLinearEquiv.finrank_eq.symm
      _ = (minpoly v.Completion (completionEmbedding w.1 α)).natDegree := by
        let pbw := AdjoinRoot.powerBasis (show
          minpoly v.Completion (completionEmbedding w.1 α) ≠ 0 by
            exact G.2.1.ne_zero)
        rw [pbw.finrank, AdjoinRoot.powerBasis_dim]
      _ = (g w).natDegree := rfl
  have hpdeg : ((minpoly K α).map (completionEmbedding v)).natDegree =
      Module.finrank K L := by
    rw [(minpoly.monic (Algebra.IsIntegral.isIntegral α)).natDegree_map]
    have hα' : IntermediateField.adjoin K {α} = ⊤ := by
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => IsAlgebraic.of_finite K x), IntermediateField.top_toSubalgebra]
      exact hα
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα'
  have hsum : (∑ w : W, (g w).natDegree) = Module.finrank K L := by
    rw [← hpdeg, hp_prod]
    exact (Polynomial.natDegree_prod_of_monic (s := Finset.univ)
      (f := g) (fun w _ =>
        (absoluteCompletedMinpoly v α w).2.2.1)).symm
  have hdim : Module.finrank v.Completion (L ⊗[K] v.Completion) =
      Module.finrank v.Completion (∀ w : W, w.1.Completion) := by
    calc
      Module.finrank v.Completion (L ⊗[K] v.Completion) =
          Module.finrank v.Completion (v.Completion ⊗[K] L) :=
        (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K L := Module.finrank_baseChange
      _ = ∑ w : W, (g w).natDegree := hsum.symm
      _ = ∑ w : W, Module.finrank v.Completion w.1.Completion := by
        simp_rw [hcoord]
      _ = Module.finrank v.Completion (∀ w : W, w.1.Completion) := by
        rw [Module.finrank_pi_fintype]
  let φ := tensorPlaceCompletions (K := K) (L := L) v
  have hinj : Function.Injective φ :=
    tensor_completions_injective (K := K) (L := L) v α hα
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) hdim).mp hinj
  exact AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

set_option maxHeartbeats 800000 in
-- Choosing a primitive element unfolds the dependent product of all place completions.
/-- Milne, Proposition 8.2: scalar extension to the completion is canonically
the product of the completions belonging to the places above `v`. -/
def completionTensorCompletions
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial] :
    (L ⊗[K] v.Completion) ≃ₐ[v.Completion]
      ((w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) →
        w.1.Completion) := by
  let α := (Field.exists_primitive_element K L).choose
  let hα := (Field.exists_primitive_element K L).choose_spec
  have hα' : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)]
    exact congrArg IntermediateField.toSubalgebra hα
  exact tensorCompletionsPrimitive v α hα'

set_option maxHeartbeats 800000 in
-- The forward map is definitionally the canonical algebra hom.
@[simp]
theorem completion_tensor_completions
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fact v.IsNontrivial]
    (x : L ⊗[K] v.Completion) :
    completionTensorCompletions (K := K) (L := L) v x =
      tensorPlaceCompletions (K := K) (L := L) v x :=
  rfl

end Nonarchimedean

section Archimedean

open NumberField

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The absolute value underlying an infinite place is nontrivial. -/
theorem infinite_place_nontrivial (v : InfinitePlace K) :
    v.1.IsNontrivial := by
  letI : CharZero K :=
    ⟨fun m n h => by
      have h' : (m : ℂ) = (n : ℂ) := by
        simpa using congrArg v.embedding h
      exact Nat.cast_injective h'⟩
  refine ⟨(2 : K), by norm_num, ?_⟩
  rw [show v.1 (2 : K) = ‖v.embedding (2 : K)‖ by
    exact (v.norm_embedding_eq 2).symm]
  rw [map_ofNat]
  norm_num

private noncomputable local instance infinitePlaceNontrivialFact
    (v : InfinitePlace K) : Fact v.1.IsNontrivial :=
  ⟨infinite_place_nontrivial v⟩

set_option backward.isDefEq.respectTransparency false in
local instance infiniteCompletionPlaceAlgebra
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Algebra v.1.Completion w.1.1.Completion :=
  (completionLies v.1 w.1.1
    (infinite_lies_comap v w.1 w.2)).toAlgebra

local instance infiniteCompletionPlaceSMul
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    SMul v.1.Completion w.1.1.Completion :=
  (infiniteCompletionPlaceAlgebra v w).toSMul

local instance infiniteCompletionPlaceModule
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Module v.1.Completion w.1.1.Completion :=
  Algebra.toModule

/-- The component of Milne's canonical tensor map belonging to an infinite
place `w` above `v`. -/
def infiniteTensorPlace
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    (L ⊗[K] v.1.Completion) →ₐ[v.1.Completion] w.1.1.Completion :=
  completionTensorPlace v.1
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

/-- The archimedean canonical map in Milne's Proposition 8.2, indexed by the
infinite places of `L` above `v`. -/
def infinitePlaceCompletions
    (v : InfinitePlace K) :
    (L ⊗[K] v.1.Completion) →ₐ[v.1.Completion]
      ((w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) →
        w.1.1.Completion) := by
  exact Pi.algHom v.1.Completion
    (fun w : {w : InfinitePlace L // w.comap (algebraMap K L) = v} =>
      w.1.1.Completion)
    (fun w => infiniteTensorPlace v w)

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- Milne's explicit formula `a ⊗ b ↦ a_i b` for an infinite component. -/
@[simp]
theorem infinite_tensor_tmul
    (v : InfinitePlace K) (a : L) (b : v.1.Completion)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    infiniteTensorPlace v w (a ⊗ₜ[K] b) =
      completionEmbedding w.1.1 a *
        completionLies v.1 w.1.1
          (infinite_lies_comap v w.1 w.2) b := by
  exact tensor_place_tmul v.1 a b
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- Each archimedean component of the canonical tensor map is surjective. -/
theorem infinite_tensor_surjective
    [FiniteDimensional K L]
    (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Function.Surjective (infiniteTensorPlace v w) := by
  exact completions_component_surjective v.1
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- A primitive element generates every archimedean completion over the
completed base field. -/
theorem infinite_adjoin_top
    [FiniteDimensional K L]
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Algebra.adjoin v.1.Completion {completionEmbedding w.1.1 alpha} = ⊤ := by
  exact adjoin_embedding_top v.1 alpha halpha
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

/-- The completion at an infinite place is the field defined by the minimal
polynomial of the completed primitive element. -/
def infiniteAdjoinMinpoly
    [FiniteDimensional K L]
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    AdjoinRoot (minpoly v.1.Completion (completionEmbedding w.1.1 alpha))
      ≃ₐ[v.1.Completion] w.1.1.Completion :=
  completionAdjoinMinpoly v.1 alpha halpha
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The preceding equivalence sends the adjoined root to the image of the
primitive element in the completion. -/
@[simp]
theorem infinite_adjoin_minpoly
    [FiniteDimensional K L]
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    infiniteAdjoinMinpoly v alpha halpha w
        (AdjoinRoot.root
          (minpoly v.1.Completion (completionEmbedding w.1.1 alpha))) =
      completionEmbedding w.1.1 alpha := by
  exact completion_adjoin_minpoly v.1 alpha halpha
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩

local instance infinitePlacesAboveFinite
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
    (placesAboveMinpoly v alpha halpha).symm

noncomputable local instance infinitePlacesAboveFintype
    [FiniteDimensional K L] (v : InfinitePlace K) :
    Fintype {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
  Fintype.ofFinite _

local instance infiniteCompletionPlaceFinite
    [FiniteDimensional K L] (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Module.Finite v.1.Completion w.1.1.Completion := by
  letI : Module.Finite v.1.Completion (v.1.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.1.Completion L
  letI : Module.Finite v.1.Completion (L ⊗[K] v.1.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.1.Completion L).toLinearEquiv
  exact Module.Finite.of_surjective
    (infiniteTensorPlace v w).toLinearMap
    (infinite_tensor_surjective v w)

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The local degree at an infinite place is the degree of the completed
minimal polynomial attached to that place. -/
theorem finrank_infinite_minpoly
    [FiniteDimensional K L]
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    Module.finrank v.1.Completion w.1.1.Completion =
      (minpoly v.1.Completion
        (completionEmbedding w.1.1 alpha)).natDegree := by
  let e := infiniteAdjoinMinpoly v alpha halpha w
  calc
    Module.finrank v.1.Completion w.1.1.Completion =
        Module.finrank v.1.Completion
          (AdjoinRoot (minpoly v.1.Completion
            (completionEmbedding w.1.1 alpha))) :=
      e.toLinearEquiv.finrank_eq.symm
    _ = (minpoly v.1.Completion
          (completionEmbedding w.1.1 alpha)).natDegree := by
      let G := infiniteCompletedMinpoly v alpha w
      let pb := AdjoinRoot.powerBasis (show
        minpoly v.1.Completion (completionEmbedding w.1.1 alpha) ≠ 0 by
          exact G.2.1.ne_zero)
      rw [pb.finrank, AdjoinRoot.powerBasis_dim]

set_option maxHeartbeats 3000000 in
-- Power-basis reduction unfolds the canonical maps at every infinite place.
omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The archimedean canonical map to the product of place completions is
injective. -/
theorem infinite_completions_injective
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    Function.Injective (infinitePlaceCompletions v :
      (L ⊗[K] v.1.Completion) →
        ((w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) →
          w.1.1.Completion)) := by
  classical
  let W := {w : InfinitePlace L // w.comap (algebraMap K L) = v}
  let I := CompletedMinpolyFactor v.1 alpha
  let P : v.1.Completion[X] :=
    (minpoly K alpha).map (completionEmbedding v.1)
  letI : Finite I := completed_minpoly_factor v.1 alpha
  letI : Fintype I := Fintype.ofFinite I
  let A := v.1.Completion ⊗[K] L
  letI : Nontrivial A :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      K v.1.Completion L (algebraMap K v.1.Completion).injective
        (algebraMap K L).injective
  letI : Nontrivial A :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      K v.1.Completion L (RingHom.injective _) (RingHom.injective _)
  let x : A := (1 : v.1.Completion) ⊗ₜ[K] alpha
  letI : Module.Finite v.1.Completion A :=
    Module.Finite.base_change K v.1.Completion L
  letI : Module.Finite v.1.Completion (L ⊗[K] v.1.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.1.Completion L).toLinearEquiv
  have hxgen : Algebra.adjoin v.1.Completion {x} = ⊤ := by
    simpa [x] using Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (A := v.1.Completion) ({alpha} : Set L) halpha
  let pb : PowerBasis v.1.Completion A :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral x) hxgen
  let psi : A →ₐ[v.1.Completion] (w : W) → w.1.1.Completion :=
    (infinitePlaceCompletions (K := K) (L := L) v).comp
      (Algebra.TensorProduct.commRight K v.1.Completion L).toAlgHom
  have hpsix (w : W) : psi x w = completionEmbedding w.1.1 alpha := by
    change infiniteTensorPlace v w
      ((Algebra.TensorProduct.commRight K v.1.Completion L) x) = _
    rw [show (Algebra.TensorProduct.commRight K v.1.Completion L) x =
      alpha ⊗ₜ[K] (1 : v.1.Completion) by rfl]
    rw [infinite_tensor_tmul, map_one]
    exact mul_one _
  have hprod : (∏ G : I, (G.1 : v.1.Completion[X])) = P := by
    exact (mapped_minpoly_completed v.1 alpha).symm
  have hPdegree : P.natDegree = pb.dim := by
    calc
      P.natDegree = (minpoly K alpha).natDegree :=
        (minpoly.monic (Algebra.IsIntegral.isIntegral alpha)).natDegree_map _
      _ = Module.finrank K L := by
        let pbK : PowerBasis K L :=
          PowerBasis.ofAdjoinEqTop
            (Algebra.IsIntegral.isIntegral alpha) halpha
        calc
          (minpoly K alpha).natDegree = pbK.dim := by
            rw [show alpha = pbK.gen by rfl]
            exact pbK.natDegree_minpoly
          _ = Module.finrank K L := pbK.finrank.symm
      _ = Module.finrank v.1.Completion A := Module.finrank_baseChange.symm
      _ = pb.dim := pb.finrank
  have hpsi : Function.Injective psi := by
    intro a b hab
    apply sub_eq_zero.mp
    let z := a - b
    have hz : psi z = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨q, hqdeg, hzq⟩ := pb.exists_eq_aeval z
    have hGdvd (G : I) : (G.1 : v.1.Completion[X]) ∣ q := by
      let w : W :=
        completedMinpolyPlace v alpha halpha G
      have hwzero : psi z w = 0 := congrFun hz w
      have heval : aeval (completionEmbedding w.1.1 alpha) q = 0 := by
        rw [hzq, ← Polynomial.aeval_algHom_apply] at hwzero
        rw [Polynomial.aeval_pi_apply₂] at hwzero
        simpa [show pb.gen = x by rfl, hpsix] using hwzero
      have hmin :
          minpoly v.1.Completion (completionEmbedding w.1.1 alpha) ∣ q :=
        minpoly.dvd v.1.Completion _ heval
      have hround := congrArg Subtype.val
        (completed_minpoly_roundtrip
          v alpha halpha G)
      change minpoly v.1.Completion
        (completionEmbedding w.1.1 alpha) = G.1 at hround
      rwa [hround] at hmin
    have hall : (∏ G : I, (G.1 : v.1.Completion[X])) ∣ q := by
      apply Fintype.prod_dvd_of_coprime
      · exact pairwise_monic_irreducible
          (fun G : I => G.1) (fun G => G.2.2.1) (fun G => G.2.1)
          (fun _ _ h => Subtype.ext h)
      · exact hGdvd
    have hPq : P ∣ q := by
      rwa [hprod] at hall
    have hqzero : q = 0 := by
      by_contra hq
      exact (not_lt_of_ge (natDegree_le_of_dvd hPq hq))
        (hPdegree ▸ hqdeg)
    rw [hqzero, map_zero] at hzq
    exact hzq
  intro a b hab
  apply (Algebra.TensorProduct.commRight K v.1.Completion L).symm.injective
  apply hpsi
  simpa [psi] using hab

set_option maxHeartbeats 2000000 in
-- The rank comparison unfolds each completion through its adjoin-root model.
/-- The archimedean canonical map in Proposition 8.2, for a chosen primitive
element, is an algebra equivalence. -/
def infiniteCompletionsPrimitive
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    (L ⊗[K] v.1.Completion) ≃ₐ[v.1.Completion]
      ((w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) →
        w.1.1.Completion) := by
  classical
  let W := {w : InfinitePlace L // w.comap (algebraMap K L) = v}
  let I := CompletedMinpolyFactor v.1 alpha
  let g : W → v.1.Completion[X] := fun w =>
    (infiniteCompletedMinpoly v alpha w).1
  let e : W ≃ I :=
    infinitePlacesMinpoly
      v alpha halpha
  letI : Finite I := completed_minpoly_factor v.1 alpha
  letI : Fintype I := Fintype.ofFinite I
  have hp_prod :
      (minpoly K alpha).map (completionEmbedding v.1) = ∏ w : W, g w := by
    rw [mapped_minpoly_completed v.1 alpha]
    exact (Fintype.prod_equiv e g (fun G : I => G.1)
      (fun _ => rfl)).symm
  letI : Module.Finite v.1.Completion (v.1.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.1.Completion L
  letI : Module.Finite v.1.Completion (L ⊗[K] v.1.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.1.Completion L).toLinearEquiv
  have hcoord (w : W) :
      Module.finrank v.1.Completion w.1.1.Completion =
        (g w).natDegree := by
    exact finrank_infinite_minpoly
      v alpha halpha w
  have hpdeg :
      ((minpoly K alpha).map (completionEmbedding v.1)).natDegree =
        Module.finrank K L := by
    rw [(minpoly.monic
      (Algebra.IsIntegral.isIntegral alpha)).natDegree_map]
    have halpha' : IntermediateField.adjoin K {alpha} = ⊤ := by
      apply IntermediateField.toSubalgebra_injective
      rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => IsAlgebraic.of_finite K x),
        IntermediateField.top_toSubalgebra]
      exact halpha
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K alpha).mp
      halpha'
  have hsum : (∑ w : W, (g w).natDegree) = Module.finrank K L := by
    rw [← hpdeg, hp_prod]
    exact (Polynomial.natDegree_prod_of_monic (s := Finset.univ)
      (f := g) (fun w _ =>
        (infiniteCompletedMinpoly v alpha w).2.2.1)).symm
  have hdim : Module.finrank v.1.Completion
        (L ⊗[K] v.1.Completion) =
      Module.finrank v.1.Completion (∀ w : W, w.1.1.Completion) := by
    calc
      Module.finrank v.1.Completion (L ⊗[K] v.1.Completion) =
          Module.finrank v.1.Completion (v.1.Completion ⊗[K] L) :=
        (Algebra.TensorProduct.commRight K v.1.Completion L).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K L := Module.finrank_baseChange
      _ = ∑ w : W, (g w).natDegree := hsum.symm
      _ = ∑ w : W, Module.finrank v.1.Completion w.1.1.Completion := by
        simp_rw [hcoord]
      _ = Module.finrank v.1.Completion (∀ w : W, w.1.1.Completion) := by
        rw [Module.finrank_pi_fintype]
  let phi := infinitePlaceCompletions
    (K := K) (L := L) v
  have hinj : Function.Injective phi :=
    infinite_completions_injective
      v alpha halpha
  have hsurj : Function.Surjective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := phi.toLinearMap) hdim).mp hinj
  exact AlgEquiv.ofBijective phi ⟨hinj, hsurj⟩

set_option maxHeartbeats 800000 in
-- Choosing a primitive element unfolds the dependent product of completions.
/-- The archimedean half of Milne, Proposition 8.2: scalar extension to the
completion is canonically the product of the completions at infinite places
above `v`. -/
def infiniteTensorCompletions
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : InfinitePlace K) :
    (L ⊗[K] v.1.Completion) ≃ₐ[v.1.Completion]
      ((w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) →
        w.1.1.Completion) := by
  let alpha := (Field.exists_primitive_element K L).choose
  let halphaIF := (Field.exists_primitive_element K L).choose_spec
  have halpha : Algebra.adjoin K {alpha} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic alpha)]
    exact congrArg IntermediateField.toSubalgebra halphaIF
  exact infiniteCompletionsPrimitive
    v alpha halpha

set_option maxHeartbeats 3000000 in
-- Unfolding the canonical archimedean equivalence is expensive.
omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The forward map of the archimedean equivalence is the canonical tensor
map. -/
@[simp]
theorem infinite_tensor_completions
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : InfinitePlace K) (x : L ⊗[K] v.1.Completion) :
    infiniteTensorCompletions v x =
      infinitePlaceCompletions v x :=
  rfl

set_option maxHeartbeats 3000000 in
-- Unfolding the canonical equivalence and its component maps is expensive.
omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- Milne's canonical formula `a ⊗ b ↦ (a_i b)_i` for the
archimedean equivalence in Proposition 8.2. -/
@[simp]
theorem infinite_completions_tmul
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : InfinitePlace K) (a : L) (b : v.1.Completion)
    (w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}) :
    infiniteTensorCompletions v (a ⊗ₜ[K] b) w =
      completionEmbedding w.1.1 a *
        completionLies v.1 w.1.1
          (infinite_lies_comap v w.1 w.2) b := by
  rw [infinite_tensor_completions]
  exact infinite_tensor_tmul v a b w

end Archimedean

end

end Submission.NumberTheory.Milne

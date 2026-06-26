import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Central.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Submission.ClassField.BrauerGroups.BasisSupport


/-!
# Chapter IV, Lemma 2.7

For a division algebra `D` central over `k`, every two-sided ideal of
`D ⊗[k] A` is generated as a left `D`-module by its intersection with
`1 ⊗ A`.  This is Milne's lemma after commuting the two tensor factors.
-/

namespace Submission.CField.BGroups

open Module
open scoped TensorProduct

variable {k D A ι : Type*} [Field k] [DivisionRing D] [Ring A]
  [Algebra k D] [Algebra k A] [Algebra.IsCentral k D]

abbrev CentralTensor (k D A : Type*) [Field k] [DivisionRing D] [Ring A]
    [Algebra k D] [Algebra k A] := D ⊗[k] A

omit [Algebra.IsCentral k D] in
private theorem include_left_smul (d : D) (x : CentralTensor k D A) :
    (d ⊗ₜ[k] 1) * x = d • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d' a => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [mul_add, smul_add, hx, hy]

/-- A two-sided ideal of `D ⊗ A`, regarded as a left `D`-submodule. -/
def twoSidedSubmodule (I : TwoSidedIdeal (CentralTensor k D A)) :
    Submodule D (CentralTensor k D A) where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' d x hx := by
    rw [← include_left_smul]
    exact I.mul_mem_left _ _ hx

/-- Right multiplication by `δ ⊗ 1` is left `D`-linear. -/
def tensorRightMul (δ : D) :
    CentralTensor k D A →ₗ[D] CentralTensor k D A where
  toFun x := x * Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A) δ
  map_add' x y := add_mul x y _
  map_smul' d x := by
    change (d • x) * (δ ⊗ₜ[k] 1) = d • (x * (δ ⊗ₜ[k] 1))
    exact smul_mul_assoc d x (δ ⊗ₜ[k] 1)

omit [Algebra.IsCentral k D] in
@[simp]
theorem tensor_right_mul (δ : D) (x : CentralTensor k D A) :
    tensorRightMul (k := k) (A := A) δ x =
      x * Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A) δ :=
  rfl

section Coordinates

variable (b : Basis ι k A)

noncomputable abbrev tensorBasis : Basis ι D (CentralTensor k D A) :=
  Algebra.TensorProduct.basis D b

omit [Algebra.IsCentral k D] in
/-- Right multiplication by `δ ⊗ 1` right-multiplies every `D`-coordinate by `δ`. -/
theorem tensor_basis_repr (δ : D) (x : CentralTensor k D A) (i : ι) :
    (tensorBasis (D := D) b).repr (tensorRightMul (k := k) (A := A) δ x) i =
      (tensorBasis (D := D) b).repr x i * δ := by
  let lhs : CentralTensor k D A →ₗ[D] D :=
    (Finsupp.lapply i).comp
      ((tensorBasis (D := D) b).repr.toLinearMap.comp
        (tensorRightMul (k := k) (A := A) δ))
  let rhs : CentralTensor k D A →ₗ[D] D :=
    (LinearMap.mulRight D δ).comp
      ((Finsupp.lapply i).comp (tensorBasis (D := D) b).repr.toLinearMap)
  have hlr : lhs = rhs := by
    apply (tensorBasis (D := D) b).ext
    intro j
    classical
    by_cases hij : i = j
    · subst j
      simp [lhs, rhs, tensorBasis, tensorRightMul, Algebra.TensorProduct.basis_apply,
        Finsupp.lapply]
    · simp [lhs, rhs, tensorBasis, tensorRightMul, Algebra.TensorProduct.basis_apply,
        Finsupp.lapply, hij]
  exact DFunLike.congr_fun hlr x

omit [Algebra.IsCentral k D] in
theorem basis_support_tensor (b : Basis ι k A) {δ : D} (hδ : δ ≠ 0)
    (x : CentralTensor k D A) :
    basisSupport (tensorBasis (D := D) b) (tensorRightMul (k := k) (A := A) δ x) =
      basisSupport (tensorBasis (D := D) b) x := by
  classical
  ext i
  simp only [basisSupport, Finsupp.mem_support_iff]
  rw [tensor_basis_repr]
  exact mul_ne_zero_iff_right hδ

end Coordinates

omit [Algebra.IsCentral k D] in
theorem tensor_ne_zero {δ : D} (hδ : δ ≠ 0) {x : CentralTensor k D A}
    (hx : x ≠ 0) : tensorRightMul (k := k) (A := A) δ x ≠ 0 := by
  intro hzero
  apply hx
  have h := congrArg (fun y ↦ tensorRightMul (k := k) (A := A) δ⁻¹ y) hzero
  simpa [tensorRightMul, mul_assoc, hδ, ← Algebra.TensorProduct.one_def] using h

/-- Every primordial element of a two-sided ideal lies in `1 ⊗ A`. -/
theorem primordial_include_right (b : Basis ι k A)
    (I : TwoSidedIdeal (CentralTensor k D A)) {x : CentralTensor k D A}
    (hx : IsPrimordial (tensorBasis (D := D) b) (twoSidedSubmodule I) x) :
    x ∈ (Algebra.TensorProduct.includeRight :
      A →ₐ[k] CentralTensor k D A).range := by
  have hcomm : x ∈ Subalgebra.centralizer k
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A) :
        D →ₐ[k] CentralTensor k D A).range := by
    rw [Subalgebra.mem_centralizer_iff]
    intro y hy
    obtain ⟨δ, rfl⟩ := hy
    by_cases hδ : δ = 0
    · subst δ
      simp
    · let z := tensorRightMul (k := k) (A := A) δ x
      have hzI : z ∈ twoSidedSubmodule I := by
        exact I.mul_mem_right _ _ hx.1.1
      have hz0 : z ≠ 0 := tensor_ne_zero hδ hx.1.2.1
      have hzsupp : basisSupport (tensorBasis (D := D) b) z ⊆
          basisSupport (tensorBasis (D := D) b) x := by
        exact (basis_support_tensor b hδ x).le
      obtain ⟨c, hc, hzc⟩ :=
        (support_minimal_smul (tensorBasis (D := D) b)
          (twoSidedSubmodule I) hx.1 hzI hz0).mp hzsupp
      obtain ⟨j, hxj⟩ := hx.2
      have hcδ : c = δ := by
        have hcoord := congrArg (fun w ↦ (tensorBasis (D := D) b).repr w j) hzc
        change (tensorBasis (D := D) b).repr
          (tensorRightMul (k := k) (A := A) δ x) j =
            (tensorBasis (D := D) b).repr (c • x) j at hcoord
        rw [tensor_basis_repr, LinearEquiv.map_smul] at hcoord
        have hδc : δ = c := by simpa [hxj] using hcoord
        exact hδc.symm
      calc
        Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A) δ * x =
            δ • x := include_left_smul δ x
        _ = c • x := by rw [hcδ]
        _ = z := hzc.symm
        _ = x * Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A) δ := rfl
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct k D A,
    Algebra.IsCentral.center_eq_bot] at hcomm
  have hleft :
      (Algebra.TensorProduct.includeLeft.comp (⊥ : Subalgebra k D).val).range ≤
        (Algebra.TensorProduct.includeRight : A →ₐ[k] CentralTensor k D A).range := by
    intro y hy
    obtain ⟨d, rfl⟩ := hy
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp d.2
    refine ⟨algebraMap k A r, ?_⟩
    simp [← hr]
  have hmap :
      (Algebra.TensorProduct.map (⊥ : Subalgebra k D).val (AlgHom.id k A)).range ≤
        (Algebra.TensorProduct.includeRight : A →ₐ[k] CentralTensor k D A).range := by
    rw [Algebra.TensorProduct.map_range]
    exact sup_le hleft le_rfl
  exact hmap hcomm

/-- Milne's Lemma IV.2.7, with the tensor factors commuted: a two-sided ideal of
`D ⊗[k] A` is generated as a left `D`-module by its intersection with `1 ⊗ A`. -/
theorem sided_submodule_intersection (b : Basis ι k A)
    (I : TwoSidedIdeal (CentralTensor k D A)) :
    twoSidedSubmodule I =
      Submodule.span D {x : CentralTensor k D A |
        x ∈ I ∧ x ∈ (Algebra.TensorProduct.includeRight :
          A →ₐ[k] CentralTensor k D A).range} := by
  apply le_antisymm
  · rw [← span_primordial_eq (tensorBasis (D := D) b) (twoSidedSubmodule I)]
    apply Submodule.span_mono
    intro x hx
    exact ⟨hx.1.1, primordial_include_right b I hx⟩
  · apply Submodule.span_le.2
    intro x hx
    exact hx.1

/-- The division-algebra case at the heart of Proposition IV.2.6: tensoring a
simple algebra with a central division algebra preserves simplicity. -/
theorem division_simple_ring [IsSimpleRing A] :
    IsSimpleRing (CentralTensor k D A) := by
  letI : Nontrivial (CentralTensor k D A) :=
    (Algebra.TensorProduct.includeRight_injective (A := D) (B := A)
      (FaithfulSMul.algebraMap_injective k D)).nontrivial
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    let b := Module.Free.chooseBasis k A
    let S : Set (CentralTensor k D A) := {x |
      x ∈ I ∧ x ∈ (Algebra.TensorProduct.includeRight :
        A →ₐ[k] CentralTensor k D A).range}
    have hsub_ne : twoSidedSubmodule I ≠ ⊥ := by
      intro hsub
      apply hI
      ext x
      constructor
      · intro hxI
        have hx : x ∈ twoSidedSubmodule I := hxI
        rw [hsub] at hx
        simpa using hx
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        simp [hx0]
    have hspan_ne : Submodule.span D S ≠ ⊥ := by
      rw [← sided_submodule_intersection b I]
      exact hsub_ne
    have hex : ∃ x : CentralTensor k D A, x ∈ S ∧ x ≠ 0 := by
      by_contra h
      apply hspan_ne
      rw [Submodule.span_eq_bot]
      intro x hx
      by_contra hx0
      exact h ⟨x, hx, hx0⟩
    obtain ⟨x, ⟨hxI, hxR⟩, hx0⟩ := hex
    obtain ⟨a, rfl⟩ := hxR
    have ha0 : a ≠ 0 := by
      intro ha
      subst a
      simp at hx0
    let J : TwoSidedIdeal A :=
      I.comap (Algebra.TensorProduct.includeRight (R := k) (A := D) :
        A →ₐ[k] CentralTensor k D A).toRingHom
    have haJ : a ∈ J := by
      rw [TwoSidedIdeal.mem_comap]
      exact hxI
    have h1J : (1 : A) ∈ J := IsSimpleRing.one_mem_of_ne_zero_mem J ha0 haJ
    have h1I : (1 : CentralTensor k D A) ∈ I := by
      rw [TwoSidedIdeal.mem_comap] at h1J
      simpa using h1J
    exact TwoSidedIdeal.eq_top I h1I

end Submission.CField.BGroups

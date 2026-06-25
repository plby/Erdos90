import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Chapter IV, Proposition 2.3

The centralizer of a tensor product of subalgebras is the tensor product of
their centralizers.  The proof follows Milne's two-stage argument, first
centralizing the left factor and then the right factor.
-/

namespace Towers.CField.BGroups

open Algebra.TensorProduct

variable (k A A' : Type*) [Field k]
variable [Ring A] [Ring A'] [Algebra k A] [Algebra k A']

private theorem centralizer_inf_centralizers
    (B : Subalgebra k A) (B' : Subalgebra k A') :
    (Algebra.TensorProduct.map
          (Subalgebra.centralizer k (B : Set A)).val (AlgHom.id k A')).range ⊓
        Subalgebra.centralizer k
          (B'.map (Algebra.TensorProduct.includeRight (R := k) (A := A))) ≤
      (Algebra.TensorProduct.map
        (Subalgebra.centralizer k (B : Set A)).val
        (Subalgebra.centralizer k (B' : Set A')).val).range := by
  classical
  let C := Subalgebra.centralizer k (B : Set A)
  let C' := Subalgebra.centralizer k (B' : Set A')
  letI : Module.Free k A' := Module.Free.of_divisionRing k A'
  letI : Module.Free k C := Module.Free.of_divisionRing k C
  letI : Module.Flat k C := Module.Flat.of_free
  letI : Module.Flat k A' := Module.Flat.of_free
  let f : TensorProduct k (↑C) A' →ₐ[k] TensorProduct k A A' :=
    Algebra.TensorProduct.map C.val (AlgHom.id k A')
  have hf : Function.Injective f := by
    simpa [f] using
      (TensorProduct.map_injective_of_flat_flat'
        C.val.toLinearMap (LinearMap.id (R := k) (M := A'))
        Subtype.val_injective (Function.injective_id : Function.Injective (id : A' → A')))
  rintro x ⟨⟨y, rfl⟩, hxright⟩
  change f y ∈ Subalgebra.centralizer k
    (B'.map (Algebra.TensorProduct.includeRight (R := k) (A := A))) at hxright
  have hxright' := Iff.mp (Subalgebra.mem_centralizer_iff k) hxright
  have hycentral :
      y ∈ Subalgebra.centralizer k
        (B'.map (Algebra.TensorProduct.includeRight (R := k) (A := C))) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro z ⟨b, hb, rfl⟩
    apply hf
    simp only [map_mul]
    have hcomm := hxright'
      (Algebra.TensorProduct.includeRight b)
      ⟨b, hb, rfl⟩
    simpa [f] using hcomm
  rw [Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct
    k C A' B'] at hycentral
  rcases hycentral with ⟨z, rfl⟩
  refine ⟨z, ?_⟩
  change Algebra.TensorProduct.map C.val C'.val z =
    f (Algebra.TensorProduct.map (AlgHom.id k C) C'.val z)
  simpa [f] using congrArg
    (fun g : TensorProduct k C C' →ₐ[k] TensorProduct k A A' => g z)
    (Algebra.TensorProduct.map_comp C.val (AlgHom.id k C) (AlgHom.id k A') C'.val)

private theorem centralizers_centralizer_inf
    (B : Subalgebra k A) (B' : Subalgebra k A') :
    (Algebra.TensorProduct.map
        (Subalgebra.centralizer k (B : Set A)).val
        (Subalgebra.centralizer k (B' : Set A')).val).range ≤
      (Algebra.TensorProduct.map
          (Subalgebra.centralizer k (B : Set A)).val (AlgHom.id k A')).range ⊓
        Subalgebra.centralizer k
          (B'.map (Algebra.TensorProduct.includeRight (R := k) (A := A))) := by
  classical
  let C := Subalgebra.centralizer k (B : Set A)
  let C' := Subalgebra.centralizer k (B' : Set A')
  rintro x ⟨y, rfl⟩
  constructor
  · refine ⟨Algebra.TensorProduct.map (AlgHom.id k C) C'.val y, ?_⟩
    change
      Algebra.TensorProduct.map C.val (AlgHom.id k A')
          (Algebra.TensorProduct.map (AlgHom.id k C) C'.val y) =
        Algebra.TensorProduct.map C.val C'.val y
    simpa using congrArg
      (fun g : TensorProduct k C C' →ₐ[k] TensorProduct k A A' => g y)
      (Algebra.TensorProduct.map_comp C.val (AlgHom.id k C) (AlgHom.id k A') C'.val).symm
  · apply Iff.mpr (Subalgebra.mem_centralizer_iff k)
    rintro _ ⟨b, hb, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c c' =>
        change
          (1 ⊗ₜ[k] b) * ((c : A) ⊗ₜ[k] (c' : A')) =
            ((c : A) ⊗ₜ[k] (c' : A')) * (1 ⊗ₜ[k] b)
        simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [Iff.mp (Subalgebra.mem_centralizer_iff k) c'.2 b hb]
    | add y z hy hz => simpa [map_add, mul_add, add_mul] using congrArg₂ (· + ·) hy hz

/-- Milne, Proposition IV.2.3: the centralizer of `B ⊗ B'` in `A ⊗ A'`
is the image of `C_A(B) ⊗ C_A'(B')`. -/
theorem centralizer_tensorProduct (B : Subalgebra k A) (B' : Subalgebra k A') :
    Subalgebra.centralizer k
        (Algebra.TensorProduct.map B.val B'.val).range =
      (Algebra.TensorProduct.map
        (Subalgebra.centralizer k (B : Set A)).val
        (Subalgebra.centralizer k (B' : Set A')).val).range := by
  letI : Module.Free k A := Module.Free.of_divisionRing k A
  letI : Module.Free k A' := Module.Free.of_divisionRing k A'
  rw [Algebra.TensorProduct.map_range, Subalgebra.centralizer_coe_sup]
  have hleft :
      ((Algebra.TensorProduct.includeLeft (R := k) (B := A')).comp B.val).range =
        B.map (Algebra.TensorProduct.includeLeft (R := k) (B := A')) := by
    ext x
    simp
  have hright :
      ((Algebra.TensorProduct.includeRight (R := k) (A := A)).comp B'.val).range =
        B'.map (Algebra.TensorProduct.includeRight (R := k) (A := A)) := by
    ext x
    simp
  rw [hleft, hright]
  rw [Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct k A A' B]
  exact le_antisymm
    (centralizer_inf_centralizers k A A' B B')
    (centralizers_centralizer_inf k A A' B B')

/-- The consequence following Proposition IV.2.3: the centre of a tensor
product is the image of the tensor product of the two centres. -/
theorem center_tensorProduct :
    Subalgebra.center k (TensorProduct k A A') =
      (Algebra.TensorProduct.map
        (Subalgebra.center k A).val (Subalgebra.center k A').val).range := by
  let f := Algebra.TensorProduct.map
    (⊤ : Subalgebra k A).val (⊤ : Subalgebra k A').val
  have hf : Function.Surjective f := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero f⟩
    | tmul a a' =>
        exact ⟨⟨a, by simp⟩ ⊗ₜ[k] ⟨a', by simp⟩, by simp [f]⟩
    | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add f x' y'⟩
  have hftop : f.range = ⊤ := (AlgHom.range_eq_top f).mpr hf
  have h := centralizer_tensorProduct k A A'
    (⊤ : Subalgebra k A) (⊤ : Subalgebra k A')
  change Subalgebra.centralizer k (f.range : Set (TensorProduct k A A')) = _ at h
  rw [hftop] at h
  simp only [Algebra.coe_top] at h
  rw [Subalgebra.centralizer_univ] at h
  let C := Subalgebra.centralizer k (Set.univ : Set A)
  let C' := Subalgebra.centralizer k (Set.univ : Set A')
  let Z := Subalgebra.center k A
  let Z' := Subalgebra.center k A'
  have hCZ : C ≤ Z := by
    change Subalgebra.centralizer k Set.univ ≤ Subalgebra.center k A
    rw [Subalgebra.centralizer_univ]
  have hZC : Z ≤ C := by
    change Subalgebra.center k A ≤ Subalgebra.centralizer k Set.univ
    rw [Subalgebra.centralizer_univ]
  have hC'Z' : C' ≤ Z' := by
    change Subalgebra.centralizer k Set.univ ≤ Subalgebra.center k A'
    rw [Subalgebra.centralizer_univ]
  have hZ'C' : Z' ≤ C' := by
    change Subalgebra.center k A' ≤ Subalgebra.centralizer k Set.univ
    rw [Subalgebra.centralizer_univ]
  let toZ : C →ₐ[k] Z := Subalgebra.inclusion hCZ
  let toZ' : C' →ₐ[k] Z' := Subalgebra.inclusion hC'Z'
  let toC : Z →ₐ[k] C := Subalgebra.inclusion hZC
  let toC' : Z' →ₐ[k] C' := Subalgebra.inclusion hZ'C'
  have hrange :
      (Algebra.TensorProduct.map C.val C'.val).range =
        (Algebra.TensorProduct.map Z.val Z'.val).range := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      refine ⟨Algebra.TensorProduct.map toZ toZ' y, ?_⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c c' => rfl
      | add y z hy hz =>
          simpa [map_add] using congrArg₂ (fun a b => a + b) hy hz
    · rintro _ ⟨y, rfl⟩
      refine ⟨Algebra.TensorProduct.map toC toC' y, ?_⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul z z' => rfl
      | add y z hy hz =>
          simpa [map_add] using congrArg₂ (fun a b => a + b) hy hz
  exact h.trans hrange

end Towers.CField.BGroups

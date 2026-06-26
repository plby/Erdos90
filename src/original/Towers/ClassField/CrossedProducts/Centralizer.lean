import Mathlib.LinearAlgebra.Dimension.Constructions
import Towers.ClassField.BrauerGroups.TensorProductCentral
import Towers.ClassField.CrossedProducts.EndRestrictScalars

/-!
# Chapter IV, Corollary 3.3

The centralizer of a central simple subalgebra is central simple, and tensor
multiplication identifies the two factors with the ambient algebra.
-/

namespace Towers.CField.CProduca

open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

variable (B : Subalgebra k A) [IsSimpleRing B] [Algebra.IsCentral k B]

private abbrev Centralizer := Subalgebra.centralizer k (B : Set A)

/-- In Theorem IV.3.1, a central subalgebra has central centralizer. -/
theorem centralizer_isCentral : Algebra.IsCentral k (Centralizer k A B) := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  have hzdouble : (z : A) ∈
      Subalgebra.centralizer k (Centralizer k A B : Set A) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro c hc
    exact congrArg Subtype.val (hz ⟨c, hc⟩)
  have hzB : (z : A) ∈ B := by
    rw [centralizer_centralizer_eq k A B] at hzdouble
    exact hzdouble
  let zB : B := ⟨z, hzB⟩
  have hzBcenter : zB ∈ Subalgebra.center k B := by
    rw [Subalgebra.mem_center_iff]
    intro b
    apply Subtype.ext
    exact z.2 b b.2
  have hzBbot := Algebra.IsCentral.out hzBcenter
  rw [Algebra.mem_bot] at hzBbot ⊢
  obtain ⟨c, hc⟩ := hzBbot
  refine ⟨c, ?_⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val hc

/-- The canonical multiplication homomorphism `B ⊗ C_A(B) → A`. -/
noncomputable def centralizerMul :
    B ⊗[k] Centralizer k A B →ₐ[k] A :=
  Algebra.TensorProduct.lift B.val (Centralizer k A B).val fun b c =>
    c.2 b b.2

/-- Milne, Corollary IV.3.3: if `B` is central, tensor multiplication is an
isomorphism `B ⊗ C_A(B) ≃ A`. -/
noncomputable def tensorCentralizerEquiv :
    B ⊗[k] Centralizer k A B ≃ₐ[k] A := by
  let C := Centralizer k A B
  letI : Module.Finite k B :=
    Module.Finite.of_injective B.val.toLinearMap B.val.injective
  letI : Module.Finite k C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  letI : IsSimpleRing C := centralizer_simple_ring k A B
  letI : Algebra.IsCentral k C := centralizer_isCentral k A B
  letI : IsSimpleRing (B ⊗[k] C) :=
    BGroups.tensor_simple_ring k B C
  let f : B ⊗[k] C →ₐ[k] A := centralizerMul k A B
  have hinj : Function.Injective f := f.toRingHom.injective
  have hfinrank : Module.finrank k (B ⊗[k] C) = Module.finrank k A := by
    rw [Module.finrank_tensorProduct]
    exact finrank_mul_centralizer k A B
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hinj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

end Towers.CField.CProduca

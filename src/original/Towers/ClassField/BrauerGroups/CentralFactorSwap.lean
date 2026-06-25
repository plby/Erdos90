import Mathlib.Algebra.Module.TransferInstance
import Towers.ClassField.BrauerGroups.CentralTensor

/-!
# Milne, Class Field Theory, Lemma IV.2.7

The existing theorem proves the result after commuting the tensor factors,
for `D ⊗[k] A`, and exposes the basis used by the primordial-element
argument.  The source statement is for `A ⊗[k] D`, with the left `D`-action

`d • (a ⊗ d') = a ⊗ (d * d')`,

and has no chosen basis among its hypotheses.  We transport that action and
the proved span equality across tensor-factor swap, choosing a basis of `A`
internally.
-/

namespace Towers.CField.BGroups

open Module
open scoped TensorProduct

noncomputable section

variable {k D A : Type*} [Field k] [DivisionRing D] [Ring A]
  [Algebra k D] [Algebra k A] [Algebra.IsCentral k D]

/-- The tensor product in Milne's literal factor order. -/
abbrev SourceCentralTensor (k A D : Type*) [Field k] [Ring A]
    [DivisionRing D] [Algebra k A] [Algebra k D] := A ⊗[k] D

/-- Tensor-factor swap from Milne's order to the order used by `Lemma27`. -/
noncomputable def sourceTensorSwap :
    SourceCentralTensor k A D ≃ₐ[k] CentralTensor k D A :=
  Algebra.TensorProduct.comm k A D

omit [Algebra.IsCentral k D] in
/-- Under the transported left `D`-module structure, `D` acts on the second
tensor factor by left multiplication, exactly as in Milne's proof. -/
theorem tensor_smul_tmul (d d' : D) (a : A) :
    letI : Module D (SourceCentralTensor k A D) :=
      (sourceTensorSwap (k := k) (A := A) (D := D)).toAddEquiv.module D
    d • (a ⊗ₜ[k] d') = a ⊗ₜ[k] (d * d') := by
  let e := sourceTensorSwap (k := k) (A := A) (D := D)
  letI : Module D (SourceCentralTensor k A D) := e.toAddEquiv.module D
  apply e.injective
  simp [e, sourceTensorSwap, Equiv.smul_def,
    TensorProduct.smul_tmul']

/-- **Lemma IV.2.7.**  Every two-sided ideal of `A ⊗[k] D` is generated,
as a left `D`-module, by its intersection with `A ⊗ 1`.  The equality of
carrier sets below is the literal meaning of that generation statement. -/
theorem sided_intersection_order
    (I : TwoSidedIdeal (SourceCentralTensor k A D)) :
    letI : Module D (SourceCentralTensor k A D) :=
      (sourceTensorSwap (k := k) (A := A) (D := D)).toAddEquiv.module D
    (I : Set (SourceCentralTensor k A D)) =
      (Submodule.span D {x : SourceCentralTensor k A D |
        x ∈ I ∧ x ∈ (Algebra.TensorProduct.includeLeft :
          A →ₐ[k] SourceCentralTensor k A D).range} :
        Set (SourceCentralTensor k A D)) := by
  let eAlg := sourceTensorSwap (k := k) (A := A) (D := D)
  letI : Module D (SourceCentralTensor k A D) := eAlg.toAddEquiv.module D
  let e : SourceCentralTensor k A D ≃ₗ[D] CentralTensor k D A :=
    eAlg.toAddEquiv.linearEquiv D
  let J : TwoSidedIdeal (CentralTensor k D A) :=
    eAlg.toRingEquiv.mapTwoSidedIdeal I
  let S : Set (SourceCentralTensor k A D) := {x |
    x ∈ I ∧ x ∈ (Algebra.TensorProduct.includeLeft :
      A →ₐ[k] SourceCentralTensor k A D).range}
  let T : Set (CentralTensor k D A) := {x |
    x ∈ J ∧ x ∈ (Algebra.TensorProduct.includeRight :
      A →ₐ[k] CentralTensor k D A).range}
  have himage : e '' S = T := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxI, hxA⟩, rfl⟩
      constructor
      · change eAlg x ∈ eAlg.toRingEquiv.mapTwoSidedIdeal I
        rw [RingEquiv.mapTwoSidedIdeal_apply, TwoSidedIdeal.mem_comap]
        change eAlg.symm (eAlg x) ∈ I
        rw [eAlg.symm_apply_apply]
        exact hxI
      · obtain ⟨a, rfl⟩ := hxA
        refine ⟨a, ?_⟩
        change (1 ⊗ₜ[k] a) = eAlg (a ⊗ₜ[k] 1)
        rfl
    · rintro ⟨hyJ, hyA⟩
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      constructor
      · change eAlg.symm y ∈ I
        change y ∈ I.comap eAlg.symm at hyJ
        rwa [TwoSidedIdeal.mem_comap] at hyJ
      · obtain ⟨a, ha⟩ := hyA
        refine ⟨a, ?_⟩
        rw [← ha]
        rfl
  let b := Module.Free.chooseBasis k A
  have htarget := sided_submodule_intersection
    (D := D) b J
  ext x
  change (x ∈ I) ↔ x ∈ Submodule.span D S
  calc
    x ∈ I ↔ e x ∈ J := by
      change x ∈ I ↔ eAlg x ∈ I.comap eAlg.symm
      simp [TwoSidedIdeal.mem_comap]
    _ ↔ e x ∈ twoSidedSubmodule J := Iff.rfl
    _ ↔ e x ∈ Submodule.span D T := by rw [htarget]
    _ ↔ e x ∈ Submodule.span D (e '' S) := by rw [himage]
    _ ↔ x ∈ Submodule.span D S :=
      Submodule.apply_mem_span_image_iff_mem_span e.injective

end

end Towers.CField.BGroups

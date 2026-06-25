import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.SimpleRing.Matrix
import Submission.ClassField.BrauerGroups.SimpleSubalgebraInner
import Submission.ClassField.BrauerGroups.TensorProductCentral
import Submission.ClassField.BrauerGroups.CentralizerInfCentralizers

/-!
# Chapter IV, Theorem 3.1

The double-centralizer theorem for a simple subalgebra of a
finite-dimensional central simple algebra.
-/

namespace Submission.CField.CProduca

open scoped TensorProduct

universe u

private noncomputable def endRestrictScalars (k B : Type u)
    [Field k] [Ring B] [Algebra k B] :
    Module.End B B →ₐ[k] Module.End k B where
  toFun f := f.restrictScalars k
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    ext x
    simp [Algebra.smul_def]

private noncomputable def rightRegular (k B : Type u)
    [Field k] [Ring B] [Algebra k B] :
    Bᵐᵒᵖ →ₐ[k] Module.End k B :=
  (endRestrictScalars k B).comp (AlgEquiv.moduleEndSelf k (A := B)).toAlgHom

private theorem right_regular_one (k B : Type u)
    [Field k] [Ring B] [Algebra k B] (b : Bᵐᵒᵖ) :
    rightRegular k B b 1 = MulOpposite.unop b := by
  change (AlgEquiv.moduleEndSelf k (A := B) b) 1 = MulOpposite.unop b
  simp [AlgEquiv.moduleEndSelf, RingEquiv.moduleEndSelf_apply,
    DistribSMul.toLinearMap_apply]

private theorem right_regular_centralizer (k B : Type u)
    [Field k] [Ring B] [Algebra k B] (b : Bᵐᵒᵖ) :
    rightRegular k B b ∈ Subalgebra.centralizer k
      ((Algebra.lsmul k (A := B) k B).range : Set (Module.End k B)) := by
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  ext x
  simp [rightRegular, endRestrictScalars, AlgEquiv.moduleEndSelf,
    Algebra.lsmul_coe, mul_assoc]

private noncomputable def rightRegularCentralizer (k B : Type u)
    [Field k] [Ring B] [Algebra k B] :
    Bᵐᵒᵖ →ₐ[k] Subalgebra.centralizer k
      ((Algebra.lsmul k (A := B) k B).range : Set (Module.End k B)) :=
  (rightRegular k B).codRestrict _ (right_regular_centralizer k B)

private theorem regular_centralizer_bijective (k B : Type u)
    [Field k] [Ring B] [Algebra k B] :
    Function.Bijective (rightRegularCentralizer k B) := by
  constructor
  · intro x y hxy
    apply MulOpposite.unop_injective
    have hxy' : rightRegular k B x = rightRegular k B y := by
      exact congrArg Subtype.val hxy
    have h := congrArg (fun f : Module.End k B => f 1) hxy'
    simpa only [right_regular_one] using h
  · intro f
    refine ⟨MulOpposite.op ((f : Module.End k B) 1), ?_⟩
    apply Subtype.ext
    ext x
    change x * (f : Module.End k B) 1 = (f : Module.End k B) x
    have h := f.2 ((Algebra.lsmul k (A := B) k B) x) ⟨x, rfl⟩
    have h1 := DFunLike.congr_fun h (1 : B)
    simpa [Module.End.mul_apply, Algebra.lsmul_coe, rightRegularCentralizer,
      rightRegular, endRestrictScalars, AlgEquiv.moduleEndSelf] using h1

/-- The centralizer of the left regular representation of `B` is `Bᵐᵒᵖ`. -/
private noncomputable def regularCentralizerEquiv (k B : Type u)
    [Field k] [Ring B] [Algebra k B] :
    Bᵐᵒᵖ ≃ₐ[k] Subalgebra.centralizer k
      ((Algebra.lsmul k (A := B) k B).range : Set (Module.End k B)) :=
  AlgEquiv.ofBijective (rightRegularCentralizer k B)
    (regular_centralizer_bijective k B)

private noncomputable def centralizerEquivMap (k T : Type u)
    [Field k] [Ring T] [Algebra k T]
    (e : T ≃ₐ[k] T) (S : Subalgebra k T) :
    Subalgebra.centralizer k (S : Set T) ≃ₐ[k]
      Subalgebra.centralizer k (S.map e.toAlgHom : Set T) where
  toFun x := ⟨e x, by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    simpa only [map_mul] using congrArg e (x.2 s hs)⟩
  invFun x := ⟨e.symm x, by
    rw [Subalgebra.mem_centralizer_iff]
    intro s hs
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      x.2 (e s) ⟨s, hs, rfl⟩⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (e.map_add x y)
  map_mul' x y := Subtype.ext (e.map_mul x y)
  commutes' r := Subtype.ext (e.commutes r)

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

variable (B : Subalgebra k A) [IsSimpleRing B]

private abbrev Centralizer := Subalgebra.centralizer k (B : Set A)

set_option maxHeartbeats 800000 in
-- Skolem--Noether plus the two tensor-centralizer identifications is elaboration-heavy.
private noncomputable def centralizerTensorEquiv :
    Centralizer k A B ⊗[k] Module.End k B ≃ₐ[k] A ⊗[k] Bᵐᵒᵖ := by
  let C := Centralizer k A B
  let E := Module.End k B
  let T := A ⊗[k] E
  letI : Module.Finite k B :=
    Module.Finite.of_injective B.val.toLinearMap B.val.injective
  let eE : E ≃ₐ[k]
      Matrix (Fin (Module.finrank k B)) (Fin (Module.finrank k B)) k :=
    algEquivMatrix (Module.finBasis k B)
  letI : Nonempty (Fin (Module.finrank k B)) :=
    Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := k) (M := B))
  letI : IsSimpleRing E :=
    IsSimpleRing.of_ringEquiv eE.symm.toRingEquiv inferInstance
  letI : Algebra.IsCentral k E :=
    Algebra.IsCentral.of_algEquiv k _ _ eE.symm
  letI : Module.Finite k E := inferInstance
  letI : IsSimpleRing T :=
    BGroups.tensor_simple_ring k A E
  letI : Algebra.IsCentral k T := BGroups.tensor_product_central k A E
  letI : Module.Finite k T := inferInstance
  letI : Module.Free k A := Module.Free.of_divisionRing k A
  letI : Module.Free k C := Module.Free.of_divisionRing k C
  letI : Module.Free k E := Module.Free.of_divisionRing k E
  letI : Module.Flat k A := Module.Flat.of_free
  letI : Module.Flat k C := Module.Flat.of_free
  letI : Module.Flat k E := Module.Flat.of_free
  let phi : B →ₐ[k] T :=
    (Algebra.TensorProduct.includeLeft (R := k) (B := E)).comp B.val
  let psi : B →ₐ[k] T :=
    (Algebra.TensorProduct.includeRight (R := k) (A := A)).comp
      (Algebra.lsmul k (A := B) k B)
  let hex := BGroups.skolemNoether k B T phi psi
  let v : Tˣ := Classical.choose hex
  have hv : ∀ b : B, phi b = (v : T) * psi b * (v⁻¹ : Tˣ) :=
    Classical.choose_spec hex
  letI : SMulCommClass T k T :=
    ⟨fun x r y => Algebra.mul_smul_comm r x y⟩
  let inner : T ≃ₐ[k] T :=
    MulSemiringAction.toAlgEquiv k T (ConjAct.toConjAct v)
  have hrange : phi.range = psi.range.map inner.toAlgHom := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨psi b, ⟨b, rfl⟩, ?_⟩
      simpa [inner, ConjAct.toConjAct_smul] using (hv b).symm
    · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
      refine ⟨b, ?_⟩
      simpa [inner, ConjAct.toConjAct_smul] using hv b
  let fleft : C ⊗[k] E →ₐ[k] T :=
    Algebra.TensorProduct.map C.val (AlgHom.id k E)
  have hfleft : Function.Injective fleft := by
    simpa [fleft] using
      (TensorProduct.map_injective_of_flat_flat'
        C.val.toLinearMap (LinearMap.id (R := k) (M := E))
        Subtype.val_injective (Function.injective_id : Function.Injective (id : E → E)))
  have hleft : fleft.range = Subalgebra.centralizer k (phi.range : Set T) := by
    rw [show phi.range = B.map
      (Algebra.TensorProduct.includeLeft (R := k) (B := E)) by
        exact Subalgebra.range_comp_val B _]
    exact (Subalgebra.centralizer_coe_map_includeLeft_eq_center_tensorProduct
      k A E B).symm
  let R := Subalgebra.centralizer k
    ((Algebra.lsmul k (A := B) k B).range : Set E)
  let fright : A ⊗[k] R →ₐ[k] T :=
    Algebra.TensorProduct.map (AlgHom.id k A) R.val
  have hfright : Function.Injective fright := by
    simpa [fright] using
      (TensorProduct.map_injective_of_flat_flat'
        (LinearMap.id (R := k) (M := A)) R.val.toLinearMap
        (Function.injective_id : Function.Injective (id : A → A))
        Subtype.val_injective)
  have hright : fright.range = Subalgebra.centralizer k (psi.range : Set T) := by
    rw [show psi.range =
      (Algebra.lsmul k (A := B) k B).range.map
        (Algebra.TensorProduct.includeRight (R := k) (A := A)) by
          simpa [psi] using AlgHom.range_comp
            (Algebra.lsmul k (A := B) k B)
            (Algebra.TensorProduct.includeRight (R := k) (A := A))]
    exact (Subalgebra.centralizer_coe_map_includeRight_eq_center_tensorProduct
      k A E (Algebra.lsmul k (A := B) k B).range).symm
  let eleft : C ⊗[k] E ≃ₐ[k] Subalgebra.centralizer k (phi.range : Set T) :=
    (AlgEquiv.ofInjective fleft hfleft).trans
      (Subalgebra.equivOfEq fleft.range _ hleft)
  let eright : A ⊗[k] Bᵐᵒᵖ ≃ₐ[k]
      Subalgebra.centralizer k (psi.range : Set T) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl (regularCentralizerEquiv k B)).trans <|
      (AlgEquiv.ofInjective fright hfright).trans
        (Subalgebra.equivOfEq fright.range _ hright)
  let econj : Subalgebra.centralizer k (phi.range : Set T) ≃ₐ[k]
      Subalgebra.centralizer k (psi.range : Set T) :=
    (Subalgebra.equivOfEq _ _ (congrArg (Subalgebra.centralizer k)
      (congrArg SetLike.coe hrange))).trans
        (centralizerEquivMap k T inner psi.range).symm
  exact eleft.trans (econj.trans eright.symm)

/-- The centralizer of a simple subalgebra in a finite-dimensional central
simple algebra is simple. -/
theorem centralizer_simple_ring : IsSimpleRing (Centralizer k A B) := by
  let C := Centralizer k A B
  let E := Module.End k B
  letI : Module.Finite k B :=
    Module.Finite.of_injective B.val.toLinearMap B.val.injective
  letI : Nonempty (Fin (Module.finrank k B)) :=
    Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := k) (M := B))
  letI : IsSimpleRing (A ⊗[k] Bᵐᵒᵖ) :=
    BGroups.tensor_simple_ring k A Bᵐᵒᵖ
  let hCE : IsSimpleRing (C ⊗[k] E) :=
    IsSimpleRing.of_ringEquiv
      (centralizerTensorEquiv k A B).symm.toRingEquiv inferInstance
  let eE : E ≃ₐ[k]
      Matrix (Fin (Module.finrank k B)) (Fin (Module.finrank k B)) k :=
    algEquivMatrix (Module.finBasis k B)
  let eMatrix : C ⊗[k] E ≃ₐ[k]
      Matrix (Fin (Module.finrank k B)) (Fin (Module.finrank k B)) C :=
    (Algebra.TensorProduct.congr AlgEquiv.refl eE).trans
      (matrixEquivTensor (Fin (Module.finrank k B)) k C).symm
  letI : IsSimpleRing
      (Matrix (Fin (Module.finrank k B)) (Fin (Module.finrank k B)) C) :=
    IsSimpleRing.of_ringEquiv eMatrix.toRingEquiv hCE
  exact ⟨(TwoSidedIdeal.orderIsoMatrix
    (R := C) (n := Fin (Module.finrank k B))).isSimpleOrder⟩

/-- The dimensions of a simple subalgebra and its centralizer multiply to the
dimension of the ambient central simple algebra. -/
theorem finrank_mul_centralizer :
    Module.finrank k B * Module.finrank k (Centralizer k A B) =
      Module.finrank k A := by
  letI : Module.Finite k B :=
    Module.Finite.of_injective B.val.toLinearMap B.val.injective
  let C := Centralizer k A B
  have hdim := (centralizerTensorEquiv k A B).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct,
    Module.finrank_linearMap, MulOpposite.finrank] at hdim
  apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := k) (M := B))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hdim

/-- Milne, Theorem IV.3.1: taking the centralizer twice recovers the original
simple subalgebra. -/
theorem centralizer_centralizer_eq :
    Subalgebra.centralizer k
        (Centralizer k A B : Set A) = B := by
  let C := Centralizer k A B
  let D := Subalgebra.centralizer k (C : Set A)
  letI : Module.Finite k B :=
    Module.Finite.of_injective B.val.toLinearMap B.val.injective
  letI : Module.Finite k C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  letI : Module.Finite k D :=
    Module.Finite.of_injective D.val.toLinearMap Subtype.val_injective
  letI : IsSimpleRing C := centralizer_simple_ring k A B
  have hBC := finrank_mul_centralizer k A B
  have hCD := finrank_mul_centralizer k A C
  have hdim : Module.finrank k B = Module.finrank k D := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := C))
    calc
      Module.finrank k C * Module.finrank k B =
          Module.finrank k B * Module.finrank k C := Nat.mul_comm _ _
      _ = Module.finrank k A := hBC
      _ = Module.finrank k C * Module.finrank k D := hCD.symm
  have hle : B ≤ D := by
    intro b hb
    rw [Subalgebra.mem_centralizer_iff]
    intro c hc
    exact (Iff.mp (Subalgebra.mem_centralizer_iff k) hc b hb).symm
  exact (Subalgebra.eq_of_le_of_finrank_eq hle hdim).symm

end Submission.CField.CProduca

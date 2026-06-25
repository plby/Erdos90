import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.RingTheory.SimpleRing.Field
import Submission.ClassField.SimpleAlgebras.NaturalRightMul
import Submission.ClassField.BrauerGroups.BrauerGroup
import Submission.ClassField.BrauerGroups.MulLeftBijective
import Submission.ClassField.BrauerGroups.ScalarExtensionCentral
import Submission.ClassField.BrauerGroups.IsSplitBy
import Submission.ClassField.CrossedProducts.Centralizer
import Submission.ClassField.CrossedProducts.SubalgebraField

/-!
# Chapter IV, Corollary 3.6

Splitting fields are characterized by embeddings as maximal subfields of
central simple algebras in the same Brauer class.  The final clause follows:
a subfield of the square-root degree inside a central simple algebra splits
it.
-/

namespace Submission.CField.CProduca

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private noncomputable def tensorRightCongr
    (k L A B : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (e : A ≃ₐ[k] B) : A ⊗[k] L ≃ₐ[L] B ⊗[k] L :=
  { Algebra.TensorProduct.congr e AlgEquiv.refl with
    commutes' := by
      intro l
      rw [Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.right_algebraMap_apply]
      simp }

private noncomputable def tensorMatrixAlg
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] (n : ℕ) :
    L ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[L]
      Matrix (Fin n) (Fin n) (L ⊗[k] A) :=
  { BGroups.tensorMatrixEquiv (k := k) (A := L) (D := A) (Fin n) with
    commutes' := by
      intro l
      change BGroups.tensorMatrixEquiv
        (k := k) (A := L) (D := A) (Fin n) (l ⊗ₜ[k] 1) = _
      simp only [BGroups.tensorMatrixEquiv, AlgEquiv.trans_apply,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
        Algebra.TensorProduct.one_def, Algebra.TensorProduct.assoc_symm_tmul,
        matrixEquivTensor_apply_symm]
      ext i j
      simp [Matrix.one_apply, Matrix.algebraMap_matrix_apply,
        Algebra.TensorProduct.algebraMap_apply] }

private noncomputable def scalarMatrixEquiv
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] (n : ℕ) :
    Matrix (Fin n) (Fin n) A ⊗[k] L ≃ₐ[L]
      Matrix (Fin n) (Fin n) (A ⊗[k] L) :=
  (Algebra.TensorProduct.commRight k L (Matrix (Fin n) (Fin n) A)).symm |>.trans
    (tensorMatrixAlg k L A n) |>.trans
      (AlgEquiv.mapMatrix (Algebra.TensorProduct.commRight k L A))

private noncomputable def scalarExtendMatrix
    (k L A B : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (n m : ℕ) (e : Matrix (Fin n) (Fin n) A ≃ₐ[k]
      Matrix (Fin m) (Fin m) B) :
    Matrix (Fin n) (Fin n) (A ⊗[k] L) ≃ₐ[L]
      Matrix (Fin m) (Fin m) (B ⊗[k] L) :=
  (scalarMatrixEquiv k L A n).symm |>.trans
    (tensorRightCongr k L _ _ e) |>.trans
      (scalarMatrixEquiv k L B m)

private noncomputable def flattenSplitMatrix
    (L C : Type u) [Field L] [Ring C] [Algebra L C]
    (m r : ℕ) (e : C ≃ₐ[L] Matrix (Fin r) (Fin r) L) :
    Matrix (Fin m) (Fin m) C ≃ₐ[L]
      Matrix (Fin (m * r)) (Fin (m * r)) L :=
  e.mapMatrix |>.trans
    (Matrix.compAlgEquiv (Fin m) (Fin r) L L) |>.trans
      (Matrix.reindexAlgEquiv L L finProdFinEquiv)

private noncomputable def splitOppositeEquiv
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] (n : ℕ)
    (e : A ⊗[k] L ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Aᵐᵒᵖ ⊗[k] L ≃ₐ[L] Matrix (Fin n) (Fin n) L :=
  (Algebra.TensorProduct.commRight k L Aᵐᵒᵖ).symm |>.trans
    (Algebra.TensorProduct.congr (AlgEquiv.toOpposite L L) AlgEquiv.refl) |>.trans
      (Algebra.TensorProduct.opAlgEquiv k L L A) |>.trans
        (AlgEquiv.op (Algebra.TensorProduct.commRight k L A)) |>.trans
          (AlgEquiv.op e) |>.trans
            (Matrix.transposeAlgEquiv (Fin n) L L).symm

private noncomputable def endScalarsV
    (k L V : Type u) [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V] :
    Module.End L V →ₐ[k] Module.End k V where
  toFun f := f.restrictScalars k
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    ext x
    simp

private theorem equivalent_op_matrix
    (k A B : Type u) [Field k]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A]
    [Ring B] [Algebra k B] [IsSimpleRing B] [Algebra.IsCentral k B]
    [Module.Finite k B]
    (q : ℕ) (hq : q ≠ 0)
    (e : Aᵐᵒᵖ ⊗[k] B ≃ₐ[k] Matrix (Fin q) (Fin q) k) :
    IsBrauerEquivalent (BGroups.centralSimpleCSA k A)
      (BGroups.centralSimpleCSA k B) := by
  let d := Module.finrank k A
  let E : Matrix (Fin q) (Fin q) A ≃ₐ[k] Matrix (Fin d) (Fin d) B :=
    (matrixEquivTensor (Fin q) k A).trans <|
      (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans <|
        (Algebra.TensorProduct.assoc k k k A Aᵐᵒᵖ B).symm.trans <|
          (Algebra.TensorProduct.congr (BGroups.tensorEquivMatrix k A)
            AlgEquiv.refl).trans <|
            (Algebra.TensorProduct.comm k (Matrix (Fin d) (Fin d) k) B).trans <|
              (matrixEquivTensor (Fin d) k B).symm
  refine ⟨q, d, hq, (Module.finrank_pos (R := k) (M := A)).ne', ⟨E⟩⟩

/-- Splitting is invariant under Brauer equivalence. -/
theorem split_equivalent
    (k L A B : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A]
    [Ring B] [Algebra k B] [IsSimpleRing B] [Algebra.IsCentral k B]
    [Module.Finite k B]
    (hAB : IsBrauerEquivalent (BGroups.centralSimpleCSA k A)
      (BGroups.centralSimpleCSA k B))
    (hB : BGroups.ISBy k L B) : BGroups.ISBy k L A := by
  rcases hAB with ⟨n, m, hn, hm, ⟨eAB⟩⟩
  rcases hB with ⟨r, hr, ⟨eB⟩⟩
  let C := A ⊗[k] L
  let q := m * r
  let eMatrix : Matrix (Fin n) (Fin n) C ≃ₐ[L]
      Matrix (Fin q) (Fin q) L :=
    (scalarExtendMatrix k L A B n m eAB).trans
      (flattenSplitMatrix L (B ⊗[k] L) m r eB)
  have hCSA := BGroups.scalar_extension_simple k L A
  letI : IsSimpleRing C := hCSA.1
  letI : Algebra.IsCentral L C := hCSA.2
  letI : Module.Finite L (L ⊗[k] A) := Module.Finite.base_change k L A
  letI : Module.Finite L C :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight k L A).toLinearEquiv
  letI : IsArtinianRing C := IsArtinianRing.of_finite L C
  obtain ⟨p, hp, D, hDdiv, hDalg, hDfin, ⟨eC⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite L C
  letI : DivisionRing D := hDdiv
  letI : Algebra L D := hDalg
  letI : Module.Finite L D := hDfin
  letI : NeZero n := ⟨hn⟩
  letI : NeZero q := ⟨mul_ne_zero hm (NeZero.ne r)⟩
  let eD : Matrix (Fin n) (Fin n) C ≃ₐ[L]
      Matrix (Fin (n * p)) (Fin (n * p)) D :=
    eC.mapMatrix |>.trans
      (Matrix.compAlgEquiv (Fin n) (Fin p) D L) |>.trans
        (Matrix.reindexAlgEquiv L D finProdFinEquiv)
  obtain ⟨_, ⟨eDL⟩⟩ :=
    SAlgebr.wedderburn_presentation_unique
      L (Matrix (Fin n) (Fin n) C) D L (n * p) q eD eMatrix
  refine ⟨p, hp, ⟨eC.trans eDL.mapMatrix⟩⟩

/-- Equivalent central simple algebras have exactly the same splitting
fields. -/
theorem split_brauer_equivalent
    (k L A B : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A]
    [Ring B] [Algebra k B] [IsSimpleRing B] [Algebra.IsCentral k B]
    [Module.Finite k B]
    (hAB : IsBrauerEquivalent (BGroups.centralSimpleCSA k A)
      (BGroups.centralSimpleCSA k B)) :
    BGroups.ISBy k L A ↔ BGroups.ISBy k L B := by
  constructor
  · exact split_equivalent k L B A hAB.symm
  · exact split_equivalent k L A B hAB

private noncomputable def rightScalarHom
    (k A : Type u) [Field k] [Ring A] [Algebra k A]
    (L : Subalgebra k A) (hL : ∀ x y : L, x * y = y * x) :
    L →+* Aᵐᵒᵖ where
  toFun l := MulOpposite.op (l : A)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    apply MulOpposite.unop_injective
    change ((x * y : L) : A) = (y : A) * (x : A)
    exact congrArg Subtype.val (hL x y)

private noncomputable def rightScalarEmbedding
    (L A : Type u) [Field L] [Ring A] (i : L →+* A) : L →+* Aᵐᵒᵖ where
  toFun l := MulOpposite.op (i l)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    apply MulOpposite.unop_injective
    change i (x * y) = i y * i x
    rw [mul_comm x y, map_mul]

@[reducible] private noncomputable def rightModule
    (k A : Type u) [Field k] [Ring A] [Algebra k A]
    (L : Subalgebra k A) (hL : ∀ x y : L, x * y = y * x) : Module L A :=
  Module.compHom A (rightScalarHom k A L hL)

@[reducible] private noncomputable def rightModuleEmbedding
    (L A : Type u) [Field L] [Ring A] (i : L →+* A) : Module L A :=
  Module.compHom A (rightScalarEmbedding L A i)

/-- A commutative simple subalgebra is a field. -/
theorem simpleCommutativeSubalgebra
    (k A : Type u) [Field k] [Ring A] [Algebra k A]
    (L : Subalgebra k A) [IsSimpleRing L]
    (hL : ∀ x y : L, x * y = y * x) : IsField L := by
  letI : CommRing L := { (inferInstance : Ring L) with mul_comm := hL }
  exact (isSimpleRing_iff_isField L).mp inferInstance

/-- The field structure canonically obtained from a commutative simple
subalgebra.  It extends the inherited ring operations on the subtype. -/
@[reducible] noncomputable def fieldCommutativeSubalgebra
    (k A : Type u) [Field k] [Ring A] [Algebra k A]
    (L : Subalgebra k A) [IsSimpleRing L]
    (hL : ∀ x y : L, x * y = y * x) : Field L :=
  (simpleCommutativeSubalgebra k A L hL).toField

/-- A field embedded in a central simple algebra with square-root degree is a
splitting field.  This is the embedding form of the final clause of
Corollary IV.3.6. -/
theorem embedding_split_sq
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A] [Module.Finite k L]
    (i : L →ₐ[k] A)
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    BGroups.ISBy k L A := by
  let rM := rightModuleEmbedding L A i.toRingHom
  letI : SMul L A := rM.toSMul
  letI : Module L A := rM
  have right_smul (l : L) (a : A) : l • a = a * i l := by
    change MulOpposite.op (i l) • a = _
    rfl
  letI : IsScalarTower k L A := ⟨fun r l a => by
    simp only [Algebra.smul_def]
    rw [right_smul, right_smul]
    rw [map_mul, i.commutes, ← mul_assoc, (Algebra.commutes r a).symm, mul_assoc]⟩
  letI : SMulCommClass A L A := ⟨fun a l x => by
    change a * (x * i l) = (a * x) * i l
    exact (mul_assoc _ _ _).symm⟩
  letI : SMulCommClass L L A := ⟨fun l m x => by
    rw [right_smul, right_smul, right_smul, right_smul]
    rw [mul_assoc, mul_assoc]
    have himul : i l * i m = i m * i l := by
      calc
        i l * i m = i (l * m) := (map_mul i l m).symm
        _ = i (m * l) := congrArg i (mul_comm l m)
        _ = i m * i l := map_mul i m l
    exact congrArg (x * ·) himul.symm⟩
  letI : IsScalarTower L L A := ⟨fun l m x => by
    simp only [Algebra.smul_def]
    rw [right_smul, right_smul]
    change x * i (l * m) = (x * i m) * i l
    rw [map_mul, mul_assoc]
    have himul : i l * i m = i m * i l := by
      calc
        i l * i m = i (l * m) := (map_mul i l m).symm
        _ = i (m * l) := congrArg i (mul_comm l m)
        _ = i m * i l := map_mul i m l
    exact congrArg (x * ·) himul⟩
  letI : Module.Finite L A := Module.Finite.of_restrictScalars_finite k L A
  letI : Module.Free L A := Module.Free.of_divisionRing L A
  let g : A →ₐ[k] Module.End L A := Algebra.lsmul k L A
  let f : L ⊗[k] A →ₐ[L] Module.End L A :=
    (AlgHom.liftEquiv k L A (Module.End L A)) g
  letI : IsSimpleRing (L ⊗[k] A) :=
    BGroups.tensor_simple_right (k := k) (A := L) (B := A)
  have hinj : Function.Injective f := f.toRingHom.injective
  have htower : Module.finrank k L * Module.finrank L A = Module.finrank k A :=
    Module.finrank_mul_finrank k L A
  have hLA : Module.finrank L A = Module.finrank k L := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := L))
    calc
      Module.finrank k L * Module.finrank L A = Module.finrank k A := htower
      _ = (Module.finrank k L) ^ 2 := hdim
      _ = Module.finrank k L * Module.finrank k L := by rw [pow_two]
  have hfinrank : Module.finrank L (L ⊗[k] A) =
      Module.finrank L (Module.End L A) := by
    rw [Module.finrank_baseChange, Module.finrank_linearMap]
    calc
      Module.finrank k A = (Module.finrank k L) ^ 2 := hdim
      _ = (Module.finrank L A) ^ 2 := by rw [hLA]
      _ = Module.finrank L A * Module.finrank L A := by rw [pow_two]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hinj
  let eEnd : L ⊗[k] A ≃ₐ[L] Module.End L A :=
    AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  let n := Module.finrank L A
  letI : NeZero n := ⟨Nat.ne_of_gt (Module.finrank_pos (R := L) (M := A))⟩
  refine ⟨n, inferInstance, ?_⟩
  exact ⟨(Algebra.TensorProduct.commRight k L A).symm.trans <|
    eEnd.trans (algEquivMatrix (Module.finBasis L A))⟩

/-- The converse implication in Milne, Corollary IV.3.6: a square-dimensional
central simple algebra in the Brauer class of `A` containing `L` makes `L` a
splitting field of `A`. -/
theorem similar_containing
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A]
    (h : ∃ (B : CSA.{u, u} k) (i : L →ₐ[k] B),
      Function.Injective i ∧
      Module.finrank k B = (Module.finrank k L) ^ 2 ∧
      IsBrauerEquivalent (BGroups.centralSimpleCSA k A) B) :
    BGroups.ISBy k L A := by
  obtain ⟨B, i, _, hdim, hAB⟩ := h
  have hB : BGroups.ISBy k L B :=
    embedding_split_sq k L B i hdim
  exact split_equivalent k L A B hAB hB

/-- The forward implication in Milne, Corollary IV.3.6.  From a splitting of
`A` over `L`, take the centralizer of the induced representation of
`Aᵐᵒᵖ` on an `L`-vector space. -/
theorem similar_containing_split
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A]
    (hsplit : BGroups.ISBy k L A) :
    ∃ (B : CSA.{u, u} k) (i : L →ₐ[k] B),
      Function.Injective i ∧
      Module.finrank k B = (Module.finrank k L) ^ 2 ∧
      IsBrauerEquivalent (BGroups.centralSimpleCSA k A) B := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hsplit
  letI : NeZero n := hn
  let V := Fin n → L
  letI : Module.Finite k V := inferInstance
  letI : Module.Free k V := Module.Free.of_divisionRing k V
  let q := Module.finrank k V
  letI : NeZero q := ⟨(Module.finrank_pos (R := k) (M := V)).ne'⟩
  let E := Module.End k V
  let eEV : E ≃ₐ[k] Matrix (Fin q) (Fin q) k :=
    algEquivMatrix (Module.finBasis k V)
  letI : IsSimpleRing E :=
    IsSimpleRing.of_ringEquiv eEV.symm.toRingEquiv inferInstance
  letI : Algebra.IsCentral k E :=
    Algebra.IsCentral.of_algEquiv k (Matrix (Fin q) (Fin q) k) E eEV.symm
  letI : Module.Finite k E := inferInstance
  let eOpp : Aᵐᵒᵖ ⊗[k] L ≃ₐ[L] Matrix (Fin n) (Fin n) L :=
    splitOppositeEquiv k L A n e
  let eEnd : Aᵐᵒᵖ ⊗[k] L ≃ₐ[L] Module.End L V :=
    eOpp.trans Matrix.toLinAlgEquiv'
  let rhoL : Aᵐᵒᵖ →ₐ[k] Module.End L V :=
    (eEnd.restrictScalars k).toAlgHom.comp Algebra.TensorProduct.includeLeft
  let rho : Aᵐᵒᵖ →ₐ[k] Module.End k V :=
    (endScalarsV k L V).comp rhoL
  have hrho : Function.Injective rho := rho.toRingHom.injective
  let S : Subalgebra k (Module.End k V) := rho.range
  let eS : Aᵐᵒᵖ ≃ₐ[k] S :=
    AlgEquiv.ofBijective rho.rangeRestrict
      ⟨fun x y hxy => hrho (congrArg Subtype.val hxy),
        rho.rangeRestrict_surjective⟩
  letI : Module.Finite k S :=
    Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective
  letI : IsSimpleRing S := IsSimpleRing.of_ringEquiv eS.toRingEquiv inferInstance
  letI : Algebra.IsCentral k S :=
    Algebra.IsCentral.of_algEquiv k Aᵐᵒᵖ S eS
  let Bsub := Subalgebra.centralizer k (S : Set E)
  letI : Module.Finite k Bsub :=
    Module.Finite.of_injective Bsub.val.toLinearMap Subtype.val_injective
  letI : IsSimpleRing Bsub := centralizer_simple_ring k E S
  letI : Algebra.IsCentral k Bsub := centralizer_isCentral k E S
  let Bpack : CSA.{u, u} k := BGroups.centralSimpleCSA k Bsub
  let lsmul : L →ₐ[k] E := Algebra.lsmul k (A := L) k V
  have hlsmul (l : L) : lsmul l ∈ Bsub := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    apply LinearMap.ext
    intro v
    change rhoL a (l • v) = l • (rhoL a v)
    exact (rhoL a).map_smul l v
  let iSub : L →ₐ[k] Bsub := lsmul.codRestrict Bsub hlsmul
  let i : L →ₐ[k] Bpack := iSub
  have hi : Function.Injective i := i.toRingHom.injective
  have hA : Module.finrank k A = n ^ 2 := by
    calc
      Module.finrank k A = Module.finrank L (A ⊗[k] L) :=
        ((Algebra.TensorProduct.commRight k L A).toLinearEquiv.finrank_eq.symm.trans
          Module.finrank_baseChange).symm
      _ = Module.finrank L (Matrix (Fin n) (Fin n) L) :=
        e.toLinearEquiv.finrank_eq
      _ = n ^ 2 := by simp [Module.finrank_matrix, pow_two]
  have hS : Module.finrank k S = n ^ 2 := by
    rw [← hA]
    exact eS.toLinearEquiv.finrank_eq.symm.trans MulOpposite.finrank
  have hV : Module.finrank k V = n * Module.finrank k L := by
    rw [Module.finrank_pi_fintype]
    simp
  have hcentral := finrank_mul_centralizer k E S
  have hE : Module.finrank k E = (n * Module.finrank k L) ^ 2 := by
    rw [Module.finrank_linearMap, hV, pow_two]
  have hBdim : Module.finrank k Bsub = (Module.finrank k L) ^ 2 := by
    change Module.finrank k S * Module.finrank k Bsub = Module.finrank k E at hcentral
    rw [hS, hE, pow_two, pow_two] at hcentral
    rw [pow_two]
    apply Nat.eq_of_mul_eq_mul_left (mul_pos (NeZero.pos n) (NeZero.pos n))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcentral
  let eTensor : Aᵐᵒᵖ ⊗[k] Bsub ≃ₐ[k] E :=
    (Algebra.TensorProduct.congr eS AlgEquiv.refl).trans
      (tensorCentralizerEquiv k E S)
  let eMatrix : Aᵐᵒᵖ ⊗[k] Bsub ≃ₐ[k] Matrix (Fin q) (Fin q) k :=
    eTensor.trans (algEquivMatrix (Module.finBasis k V))
  have hBrauer : IsBrauerEquivalent (BGroups.centralSimpleCSA k A)
      (BGroups.centralSimpleCSA k Bsub) :=
    equivalent_op_matrix k A Bsub q (NeZero.ne q) eMatrix
  exact ⟨Bpack, i, hi, hBdim, hBrauer⟩

/-- Milne, Corollary IV.3.6: a finite extension splits `A` exactly when it
embeds as a maximal subfield of a central simple algebra in the Brauer class
of `A`. -/
theorem split_similar_containing
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L]
    [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
    [Module.Finite k A] :
    BGroups.ISBy k L A ↔
      ∃ (B : CSA.{u, u} k) (i : L →ₐ[k] B),
        Function.Injective i ∧
        Module.finrank k B = (Module.finrank k L) ^ 2 ∧
        IsBrauerEquivalent (BGroups.centralSimpleCSA k A) B := by
  constructor
  · exact similar_containing_split k L A
  · exact similar_containing k L A

/-- Splitting by a subalgebra, using the compatible field structure supplied
by `fieldCommutativeSubalgebra`. -/
def SplitSubalgebra
    (k A : Type u) [Field k] [Ring A] [Algebra k A]
    (L : Subalgebra k A) [IsSimpleRing L]
    (hL : ∀ x y : L, x * y = y * x) : Prop :=
  @BGroups.ISBy k L A inferInstance
    (fieldCommutativeSubalgebra k A L hL)
    inferInstance inferInstance inferInstance

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]
variable (L : Subalgebra k A) [IsSimpleRing L]
  (hL : ∀ x y : L, x * y = y * x)

/-- The final assertion of Milne, Corollary IV.3.6: a subfield whose degree is
the square root of the dimension of `A` splits `A`. -/
theorem subfield_split_sq
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    SplitSubalgebra k A L hL := by
  let hfield := simpleCommutativeSubalgebra k A L hL
  letI : Field L := hfield.toField
  let rM := rightModule k A L hL
  letI : SMul L A := rM.toSMul
  letI : Module L A := rM
  have right_smul (l : L) (a : A) : l • a = a * (l : A) := by
    change MulOpposite.op (l : A) • a = _
    rfl
  letI : IsScalarTower k L A := ⟨fun r l a => by
    simp only [Algebra.smul_def]
    rw [right_smul, right_smul]
    change a * ((algebraMap k A r) * (l : A)) =
      (algebraMap k A r) * (a * (l : A))
    rw [← mul_assoc, (Algebra.commutes r a).symm, mul_assoc]⟩
  letI : SMulCommClass A L A := ⟨fun a l x => by
    change a * (x * (l : A)) = (a * x) * (l : A)
    exact (mul_assoc _ _ _).symm⟩
  letI : SMulCommClass L L A := ⟨fun l m x => by
    rw [right_smul, right_smul, right_smul, right_smul]
    rw [mul_assoc, mul_assoc]
    exact congrArg (x * ·) (congrArg Subtype.val (hfield.mul_comm m l))⟩
  letI : IsScalarTower L L A := ⟨fun l m x => by
    simp only [Algebra.smul_def]
    rw [right_smul, right_smul]
    change x * ((l * m : L) : A) = (x * (m : A)) * (l : A)
    rw [mul_assoc]
    exact congrArg (x * ·) (congrArg Subtype.val (hfield.mul_comm l m))⟩
  letI : Module.Finite L A := Module.Finite.of_restrictScalars_finite k L A
  letI : Module.Free L A := Module.Free.of_divisionRing L A
  let g : A →ₐ[k] Module.End L A := Algebra.lsmul k L A
  let f : L ⊗[k] A →ₐ[L] Module.End L A :=
    (AlgHom.liftEquiv k L A (Module.End L A)) g
  letI : IsSimpleRing (L ⊗[k] A) :=
    BGroups.tensor_simple_right (k := k) (A := L) (B := A)
  have hinj : Function.Injective f := f.toRingHom.injective
  have htower : Module.finrank k L * Module.finrank L A = Module.finrank k A :=
    Module.finrank_mul_finrank k L A
  have hLA : Module.finrank L A = Module.finrank k L := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := L))
    calc
      Module.finrank k L * Module.finrank L A = Module.finrank k A := htower
      _ = (Module.finrank k L) ^ 2 := hdim
      _ = Module.finrank k L * Module.finrank k L := by rw [pow_two]
  have hfinrank : Module.finrank L (L ⊗[k] A) =
      Module.finrank L (Module.End L A) := by
    rw [Module.finrank_baseChange, Module.finrank_linearMap]
    calc
      Module.finrank k A = (Module.finrank k L) ^ 2 := hdim
      _ = (Module.finrank L A) ^ 2 := by rw [hLA]
      _ = Module.finrank L A * Module.finrank L A := by rw [pow_two]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hinj
  let eEnd : L ⊗[k] A ≃ₐ[L] Module.End L A :=
    AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  let n := Module.finrank L A
  letI : NeZero n := ⟨Nat.ne_of_gt (Module.finrank_pos (R := L) (M := A))⟩
  refine ⟨n, inferInstance, ?_⟩
  exact ⟨(Algebra.TensorProduct.commRight k L A).symm.trans <|
    eEnd.trans (algEquivMatrix (Module.finBasis L A))⟩

end Submission.CField.CProduca

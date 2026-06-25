import Submission.ClassField.SimpleAlgebras.NaturalMatrixModule
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Chapter IV, Corollary 1.22

The division algebra in an Artin--Wedderburn presentation is recovered from the
endomorphism algebra of a simple module.  This file records the two elementary
ingredients in that uniqueness argument: the commutant of the natural module of
a full matrix algebra and the finrank cancellation which recovers the matrix size.
-/

namespace Submission.CField.SAlgebr

open scoped Matrix.Module

section NaturalModuleCommutant

variable (k D ι : Type*) [Field k] [DivisionRing D] [Algebra k D]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Right multiplication by `d` is linear for the left action of the full matrix algebra. -/
noncomputable def naturalModuleMul (d : Dᵐᵒᵖ) :
    Module.End (Matrix ι ι D) (ι → D) where
  toFun v i := v i * MulOpposite.unop d
  map_add' x y := by
    ext i
    exact add_mul (x i) (y i) _
  map_smul' A v := by
    ext i
    simp only [Matrix.Module.smul_apply, RingHom.id_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change (A i j * v j) * MulOpposite.unop d =
      A i j * (v j * MulOpposite.unop d)
    exact mul_assoc _ _ _

omit [Nonempty ι] in
@[simp]
theorem natural_module_mul (d : Dᵐᵒᵖ) (v : ι → D) (i : ι) :
    naturalModuleMul D ι d v i = v i * MulOpposite.unop d :=
  rfl

/-- The right scalar action identifies `Dᵐᵒᵖ` with the commutant of the natural
`M_ι(D)`-module. -/
noncomputable def naturalModuleAlg :
    Dᵐᵒᵖ →ₐ[k] Module.End (Matrix ι ι D) (ι → D) where
  toFun := naturalModuleMul D ι
  map_one' := by
    ext v i
    simp
  map_mul' x y := by
    ext v i
    simp [Module.End.mul_apply, mul_assoc]
  map_zero' := by
    ext v i
    simp
  map_add' x y := by
    ext v i
    simp [mul_add]
  commutes' r := by
    ext v i
    simp only [naturalModuleMul, Module.algebraMap_end_apply, Pi.smul_apply,
      MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    simpa only [Algebra.smul_def] using (Algebra.commutes r (v i)).symm

omit [Nonempty ι] in
@[simp]
theorem natural_module_alg (d : Dᵐᵒᵖ) (v : ι → D) (i : ι) :
    naturalModuleAlg k D ι d v i = v i * MulOpposite.unop d :=
  rfl

theorem natural_module_injective :
    Function.Injective (naturalModuleAlg k D ι) := by
  classical
  intro x y hxy
  let i := Classical.choice (inferInstance : Nonempty ι)
  apply MulOpposite.unop_injective
  have h := congrFun (DFunLike.congr_fun hxy (Pi.single i 1)) i
  simpa using h

theorem natural_module_surjective :
    Function.Surjective (naturalModuleAlg k D ι) := by
  classical
  intro f
  let j := Classical.choice (inferInstance : Nonempty ι)
  let e : ι → D := Pi.single j 1
  let d : D := f e j
  refine ⟨MulOpposite.op d, ?_⟩
  ext v i
  let A : Matrix ι ι D := fun r c ↦ if c = j then v r else 0
  have hAe : A • e = v := by
    ext r
    simp [A, e, Matrix.Module.smul_apply]
  let P : Matrix ι ι D := fun r c ↦ if r = j ∧ c = j then 1 else 0
  have hPe : P • e = e := by
    ext r
    by_cases hr : r = j
    · subst r
      simp [P, e, Matrix.Module.smul_apply]
    · simp [P, e, Matrix.Module.smul_apply, hr]
  have hfP : f e = P • f e := by
    calc
      f e = f (P • e) := congrArg f hPe.symm
      _ = P • f e := LinearMap.map_smul f P e
  have hfi (r : ι) : f e r = if r = j then d else 0 := by
    rw [hfP]
    by_cases hr : r = j
    · subst r
      simp [P, d, Matrix.Module.smul_apply]
    · simp [P, Matrix.Module.smul_apply, hr]
  change v i * d = f v i
  rw [← hAe, LinearMap.map_smul]
  symm
  rw [Matrix.Module.smul_apply, Finset.sum_eq_single j]
  · rw [show A i j = v i by simp [A], show (A • e) i = v i from congrFun hAe i]
    change v i * f e j = v i * d
    rw [hfi j, if_pos rfl]
  · intro b _ hb
    change (if b = j then v i else 0) * f e b = 0
    rw [if_neg hb, zero_mul]
  · simp

/-- The endomorphism algebra of the natural simple `M_ι(D)`-module is `Dᵐᵒᵖ`. -/
noncomputable def naturalModuleEnd :
    Dᵐᵒᵖ ≃ₐ[k] Module.End (Matrix ι ι D) (ι → D) :=
  AlgEquiv.ofBijective (naturalModuleAlg k D ι)
    ⟨natural_module_injective k D ι,
      natural_module_surjective k D ι⟩

end NaturalModuleCommutant

section TransportEndomorphisms

variable (k : Type*) {A B M : Type*} [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B] [AddCommGroup M] [Module k M]
  [Module A M] [Module B M] [IsScalarTower k A M] [IsScalarTower k B M]

/-- Transporting the scalar ring across an algebra equivalence does not change the
endomorphism algebra of a module. -/
noncomputable def moduleEndTransport (e : A ≃ₐ[k] B)
    (hsmul : ∀ (a : A) (x : M), a • x = e a • x) :
    Module.End B M ≃ₐ[k] Module.End A M := by
  let f : Module.End B M →ₐ[k] Module.End A M :=
    { toFun := fun g ↦
        { toFun := g
          map_add' := g.map_add
          map_smul' := fun a x ↦ by
            change g (a • x) = a • g x
            rw [hsmul a x, g.map_smul, ← hsmul a (g x)] }
      map_one' := by ext; rfl
      map_mul' := by intro g h; ext; rfl
      map_zero' := by ext; rfl
      map_add' := by intro g h; ext; rfl
      commutes' := by intro r; ext x; simp }
  apply AlgEquiv.ofBijective f
  constructor
  · intro g h hgh
    ext x
    exact DFunLike.congr_fun hgh x
  · intro g
    let h : Module.End B M :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun b x ↦ by
          change g (b • x) = b • g x
          rw [← e.apply_symm_apply b, ← hsmul (e.symm b) x,
            g.map_smul, hsmul (e.symm b) (g x)] }
    exact ⟨h, by ext; rfl⟩

end TransportEndomorphisms

section SimpleModules

variable (k A : Type*) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [IsArtinianRing A]

/-- Any two simple modules over an Artinian simple algebra are linearly equivalent. -/
theorem nonempty_simple_modules
    (S T : Type*) [AddCommGroup S] [AddCommGroup T] [Module A S] [Module A T]
    [IsSimpleModule A S] [IsSimpleModule A T] : Nonempty (S ≃ₗ[A] T) := by
  obtain ⟨I, ⟨eS⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A S
  obtain ⟨J, ⟨eT⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A T
  letI : IsSimpleModule A I := (eS.isSimpleModule_iff).mp inferInstance
  letI : IsSimpleModule A J := (eT.isSimpleModule_iff).mp inferInstance
  obtain ⟨eIJ⟩ := (IsSimpleRing.isIsotypic A A I) J
  exact ⟨eS.trans (eIJ.symm.trans eT.symm)⟩

/-- The opposite endomorphism division algebra attached to a simple module is independent
of the chosen simple module. -/
theorem nonempty_simple_end
    (D E S T : Type*) [DivisionRing D] [DivisionRing E] [Algebra k D] [Algebra k E]
    [AddCommGroup S] [AddCommGroup T] [Module A S] [Module A T]
    [Module k S] [Module k T] [IsScalarTower k A S] [IsScalarTower k A T]
    [IsSimpleModule A S] [IsSimpleModule A T]
    (hD : Dᵐᵒᵖ ≃ₐ[k] Module.End A S) (hE : Eᵐᵒᵖ ≃ₐ[k] Module.End A T) :
    Nonempty (D ≃ₐ[k] E) := by
  obtain ⟨e⟩ := nonempty_simple_modules (A := A) S T
  let q : Dᵐᵒᵖ ≃ₐ[k] Eᵐᵒᵖ := hD.trans ((e.conjAlgEquiv k).trans hE.symm)
  exact ⟨(AlgEquiv.opOp k D).trans (q.op.trans (AlgEquiv.opOp k E).symm)⟩

end SimpleModules

section MatrixSize

variable (k D E : Type*) [Field k] [DivisionRing D] [DivisionRing E]
  [Algebra k D] [Algebra k E] [FiniteDimensional k D]

/-- Once the coefficient division algebras are known to be isomorphic, equality of the
finranks of two full matrix algebras forces equality of their matrix sizes. -/
theorem matrix_size_finrank (n m : ℕ) (hDE : Nonempty (D ≃ₐ[k] E))
    (hfin : Module.finrank k (Matrix (Fin n) (Fin n) D) =
      Module.finrank k (Matrix (Fin m) (Fin m) E)) : n = m := by
  obtain ⟨e⟩ := hDE
  have hDpos : 0 < Module.finrank k D := Module.finrank_pos
  have hedim : Module.finrank k D = Module.finrank k E := e.toLinearEquiv.finrank_eq
  have hdim : n * n * Module.finrank k D = m * m * Module.finrank k D := by
    rw [Module.finrank_matrix, Module.finrank_matrix,
      Fintype.card_fin, Fintype.card_fin, ← hedim] at hfin
    exact hfin
  have hsquare : n * n = m * m := Nat.eq_of_mul_eq_mul_right hDpos hdim
  exact (mul_self_inj (Nat.zero_le n) (Nat.zero_le m)).mp hsquare

end MatrixSize

section PresentationUniqueness

variable (k A D E : Type*) [Field k] [Ring A] [Algebra k A]
  [IsSimpleRing A] [IsArtinianRing A]
  [DivisionRing D] [DivisionRing E] [Algebra k D] [Algebra k E]
  [FiniteDimensional k D]

/-- Milne's Corollary IV.1.22: in two finite Artin--Wedderburn presentations of the
same simple algebra, the matrix size is equal and the division algebra is unique up to
`k`-algebra isomorphism. -/
theorem wedderburn_presentation_unique (n m : ℕ) [NeZero n] [NeZero m]
    (eD : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (eE : A ≃ₐ[k] Matrix (Fin m) (Fin m) E) :
    n = m ∧ Nonempty (D ≃ₐ[k] E) := by
  classical
  letI moduleD : Module A (Fin n → D) := Module.compHom _ eD.toRingHom
  letI : RingHomSurjective eD.toRingEquiv.toRingHom := ⟨eD.surjective⟩
  letI towerD : IsScalarTower k A (Fin n → D) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change eD (algebraMap k A r) • x = r • x
      rw [eD.commutes]
      exact IsScalarTower.algebraMap_smul (A := Matrix (Fin n) (Fin n) D) r x
  let semilinearD : (Fin n → D) →ₛₗ[eD.toRingEquiv.toRingHom] (Fin n → D) :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  letI simpleD : IsSimpleModule A (Fin n → D) :=
    (semilinearD.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      natural_matrix_simple
  have hsmulD (a : A) (x : Fin n → D) : a • x = eD a • x := rfl
  let endD : Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) ≃ₐ[k]
      Module.End A (Fin n → D) :=
    moduleEndTransport k eD hsmulD
  let recoverD : Dᵐᵒᵖ ≃ₐ[k] Module.End A (Fin n → D) :=
    (naturalModuleEnd k D (Fin n)).trans endD
  letI moduleE : Module A (Fin m → E) := Module.compHom _ eE.toRingHom
  letI : RingHomSurjective eE.toRingEquiv.toRingHom := ⟨eE.surjective⟩
  letI towerE : IsScalarTower k A (Fin m → E) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change eE (algebraMap k A r) • x = r • x
      rw [eE.commutes]
      exact IsScalarTower.algebraMap_smul (A := Matrix (Fin m) (Fin m) E) r x
  let semilinearE : (Fin m → E) →ₛₗ[eE.toRingEquiv.toRingHom] (Fin m → E) :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  letI simpleE : IsSimpleModule A (Fin m → E) :=
    (semilinearE.isSimpleModule_iff_of_bijective Function.bijective_id).mpr
      natural_matrix_simple
  have hsmulE (a : A) (x : Fin m → E) : a • x = eE a • x := rfl
  let endE : Module.End (Matrix (Fin m) (Fin m) E) (Fin m → E) ≃ₐ[k]
      Module.End A (Fin m → E) :=
    moduleEndTransport k eE hsmulE
  let recoverE : Eᵐᵒᵖ ≃ₐ[k] Module.End A (Fin m → E) :=
    (naturalModuleEnd k E (Fin m)).trans endE
  have hDE : Nonempty (D ≃ₐ[k] E) :=
    nonempty_simple_end (k := k) (A := A)
      D E (Fin n → D) (Fin m → E) recoverD recoverE
  have hfin : Module.finrank k (Matrix (Fin n) (Fin n) D) =
      Module.finrank k (Matrix (Fin m) (Fin m) E) :=
    eD.toLinearEquiv.finrank_eq.symm.trans eE.toLinearEquiv.finrank_eq
  exact ⟨matrix_size_finrank k D E n m hDE hfin, hDE⟩

omit [IsArtinianRing A] in
/-- **Corollary IV.1.22, finite-dimensional form.** The matrix size and the
coefficient division algebra in a Wedderburn--Artin presentation are uniquely
determined by the original finite-dimensional simple algebra. -/
theorem wedderburn_presentation_dimensional
    [Module.Finite k A] (n m : ℕ) [NeZero n] [NeZero m]
    (eD : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (eE : A ≃ₐ[k] Matrix (Fin m) (Fin m) E) :
    n = m ∧ Nonempty (D ≃ₐ[k] E) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact wedderburn_presentation_unique k A D E n m eD eE

end PresentationUniqueness

end Submission.CField.SAlgebr

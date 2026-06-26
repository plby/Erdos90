import Towers.NumberTheory.Dedekind.DeterminantLattice
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Milne, Algebraic Number Theory, stable cancellation over Dedekind domains

We prove the determinant-lattice argument underlying the necessary direction of
Theorem 3.31(b): if `A^n × I` and `A^n × J` are linearly equivalent, then the
nonzero fractional ideals `I` and `J` represent the same ideal class.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum nonZeroDivisors
open TensorProduct

noncomputable def fractionalFractionRing
    (A : Type*) [CommRing A] [IsDomain A]
    (I : FractionalIdeal A⁰ (FractionRing A)) :
    I →ₗ[A] FractionRing A where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' a x := by
    simp [Algebra.smul_def]

theorem fractional_localized_module
    (A : Type*) [CommRing A] [IsDomain A]
    (I : FractionalIdeal A⁰ (FractionRing A)) (hI : I ≠ 0) :
    IsLocalizedModule A⁰ (fractionalFractionRing A I) where
  map_units s :=
    IsLocalizedModule.map_units (Algebra.linearMap A (FractionRing A)) s
  surj y := by
    obtain ⟨z, hzI, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj A⁰
      (y / (z : FractionRing A))
    let x : I := ⟨a • z, I.val.smul_mem a hzI⟩
    refine ⟨⟨x, s⟩, ?_⟩
    dsimp [fractionalFractionRing]
    rw [Submonoid.smul_def, Algebra.smul_def]
    have hz' : (z : FractionRing A) ≠ 0 := hz
    calc
      algebraMap A (FractionRing A) s.1 * y =
          ((y / (z : FractionRing A)) *
            algebraMap A (FractionRing A) s.1) * (z : FractionRing A) := by
              field_simp
      _ = algebraMap A (FractionRing A) a * (z : FractionRing A) := by rw [has]
      _ = x.1 := by simp [x, Algebra.smul_def]
  exists_of_eq h := by
    refine ⟨1, ?_⟩
    simp only [one_smul]
    exact Subtype.ext h

noncomputable def freeProdPi
    (K : Type*) [CommRing K] (n : ℕ) :
    ((Fin n → K) × K) ≃ₗ[K] (Fin (n + 1) → K) where
  toFun x := Fin.lastCases x.2 x.1
  invFun y := (fun i ↦ y i.castSucc, y (Fin.last n))
  left_inv x := by
    apply Prod.ext
    · ext i
      simp
    · simp
  right_inv y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

@[simp] theorem pi_cast_succ
    (K : Type*) [CommRing K] (n : ℕ) (x : (Fin n → K) × K) (i : Fin n) :
    freeProdPi K n x i.castSucc = x.1 i := by
  simp [freeProdPi]

@[simp] theorem free_pi_last
    (K : Type*) [CommRing K] (n : ℕ) (x : (Fin n → K) × K) :
    freeProdPi K n x (Fin.last n) = x.2 := by
  simp [freeProdPi]

noncomputable def freeFractionRing
    (A : Type*) [CommRing A] [IsDomain A] (n : ℕ) :
    (Fin n → A) →ₗ[A] (Fin n → FractionRing A) :=
  (Algebra.linearMap A (FractionRing A)).compLeft (Fin n)

theorem free_fraction_change
    (A : Type*) [CommRing A] [IsDomain A] (n : ℕ) :
    IsBaseChange (FractionRing A) (freeFractionRing A n) := by
  exact IsBaseChange.finitePow (Fin n)
    (IsBaseChange.linearMap A (FractionRing A))

theorem fractional_base_change
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ) (I : FractionalIdeal A⁰ (FractionRing A)) (hI : I ≠ 0) :
    IsBaseChange (FractionRing A) (fractionalLatticeMap A n I) := by
  let hfree := free_fraction_change A n
  let hideal : IsBaseChange (FractionRing A) (fractionalFractionRing A I) :=
    (isLocalizedModule_iff_isBaseChange A⁰ (FractionRing A)
      (fractionalFractionRing A I)).mp
        (fractional_localized_module A I hI)
  apply IsBaseChange.of_equiv
    (TensorProduct.prodRight A (FractionRing A) (FractionRing A) (Fin n → A) I ≪≫ₗ
      hfree.equiv.prodCongr hideal.equiv ≪≫ₗ
      freeProdPi (FractionRing A) n)
  intro x
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [fractionalLatticeMap, fractionalFractionRing]
  · simp [fractionalLatticeMap, freeFractionRing]

noncomputable def fractionalLatticeChange
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ)
    (I J : FractionalIdeal A⁰ (FractionRing A))
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (e : ((Fin n → A) × I) ≃ₗ[A] ((Fin n → A) × J)) :
    (Fin (n + 1) → FractionRing A) ≃ₗ[FractionRing A]
      (Fin (n + 1) → FractionRing A) :=
  let bI := fractional_base_change A n I hI
  let bJ := fractional_base_change A n J hJ
  bI.equiv.symm ≪≫ₗ
    e.baseChange A (FractionRing A) ((Fin n → A) × I) ((Fin n → A) × J) ≪≫ₗ
    bJ.equiv

@[simp] theorem fractional_lattice_change
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ)
    (I J : FractionalIdeal A⁰ (FractionRing A))
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (e : ((Fin n → A) × I) ≃ₗ[A] ((Fin n → A) × J))
    (x : (Fin n → A) × I) :
    fractionalLatticeChange A n I J hI hJ e
        (fractionalLatticeMap A n I x) =
      fractionalLatticeMap A n J (e x) := by
  simp [fractionalLatticeChange,
    IsBaseChange.equiv_symm_apply, IsBaseChange.equiv_tmul]

noncomputable def fractionalLatticeDet
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ) (I : FractionalIdeal A⁰ (FractionRing A)) (x : I) :
    Fin (n + 1) → ((Fin n → A) × I) :=
  Fin.lastCases (0, x) (fun i ↦ (Pi.single i 1, 0))

theorem fractional_det
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ) (I : FractionalIdeal A⁰ (FractionRing A)) (x : I) :
    (Pi.basisFun (FractionRing A) (Fin (n + 1))).det
        (fractionalLatticeMap A n I ∘ fractionalLatticeDet A n I x) = x := by
  classical
  let b := Pi.basisFun (FractionRing A) (Fin (n + 1))
  have hv :
      fractionalLatticeMap A n I ∘ fractionalLatticeDet A n I x =
        Function.update b (Fin.last n) ((x : FractionRing A) • b (Fin.last n)) := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · ext k
      refine Fin.lastCases ?_ (fun l ↦ ?_) k
      · simp [fractionalLatticeDet, b, Pi.basisFun_apply]
      · simp [fractionalLatticeDet, b, Pi.basisFun_apply,
          Fin.castSucc_ne_last]
    · ext k
      refine Fin.lastCases ?_ (fun l ↦ ?_) k
      · simp [fractionalLatticeDet, b, Pi.basisFun_apply,
          Fin.castSucc_ne_last]
      · by_cases h : j = l <;>
          simp [fractionalLatticeDet, b, Pi.basisFun_apply, h]
  change b.det _ = x
  rw [hv, AlternatingMap.map_update_smul, Function.update_eq_self, b.det_self]
  simp

theorem free_prod_linear
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (n : ℕ)
    {I J : (FractionalIdeal A⁰ (FractionRing A))ˣ}
    (e : ((Fin n → A) × (I : FractionalIdeal A⁰ (FractionRing A))) ≃ₗ[A]
      ((Fin n → A) × (J : FractionalIdeal A⁰ (FractionRing A)))) :
    ClassGroup.mk (FractionRing A) I = ClassGroup.mk (FractionRing A) J := by
  let E := fractionalLatticeChange A n
    (I : FractionalIdeal A⁰ (FractionRing A))
    (J : FractionalIdeal A⁰ (FractionRing A)) I.ne_zero J.ne_zero e
  let d : FractionRing A := LinearMap.det E.toLinearMap
  let d' : FractionRing A := LinearMap.det E.symm.toLinearMap
  have hmul (x : (I : FractionalIdeal A⁰ (FractionRing A))) :
      d * (x : FractionRing A) ∈
        (J : FractionalIdeal A⁰ (FractionRing A)) := by
    let v := fractionalLatticeDet A n
      (I : FractionalIdeal A⁰ (FractionRing A)) x
    have hmem := fractional_lattice_det A n
      (J : FractionalIdeal A⁰ (FractionRing A)) (e ∘ v)
    have hfun :
        fractionalLatticeMap A n (J : FractionalIdeal A⁰ (FractionRing A)) ∘ (e ∘ v) =
          E ∘ (fractionalLatticeMap A n
            (I : FractionalIdeal A⁰ (FractionRing A)) ∘ v) := by
      funext i
      simp [E]
    rw [hfun] at hmem
    change (Pi.basisFun (FractionRing A) (Fin (n + 1))).det
      (E.toLinearMap ∘
        (fractionalLatticeMap A n
          (I : FractionalIdeal A⁰ (FractionRing A)) ∘ v)) ∈
        (J : FractionalIdeal A⁰ (FractionRing A)) at hmem
    rw [Module.Basis.det_comp] at hmem
    rw [fractional_det] at hmem
    simpa [d] using hmem
  have hmul' (y : (J : FractionalIdeal A⁰ (FractionRing A))) :
      d' * (y : FractionRing A) ∈
        (I : FractionalIdeal A⁰ (FractionRing A)) := by
    let v := fractionalLatticeDet A n
      (J : FractionalIdeal A⁰ (FractionRing A)) y
    have hmem := fractional_lattice_det A n
      (I : FractionalIdeal A⁰ (FractionRing A)) (e.symm ∘ v)
    have hfun :
        fractionalLatticeMap A n (I : FractionalIdeal A⁰ (FractionRing A)) ∘
            (e.symm ∘ v) =
          E.symm ∘ (fractionalLatticeMap A n
            (J : FractionalIdeal A⁰ (FractionRing A)) ∘ v) := by
      funext i
      apply E.injective
      simp [E]
    rw [hfun] at hmem
    change (Pi.basisFun (FractionRing A) (Fin (n + 1))).det
      (E.symm.toLinearMap ∘
        (fractionalLatticeMap A n
          (J : FractionalIdeal A⁰ (FractionRing A)) ∘ v)) ∈
        (I : FractionalIdeal A⁰ (FractionRing A)) at hmem
    rw [Module.Basis.det_comp] at hmem
    rw [fractional_det] at hmem
    simpa [d'] using hmem
  apply ClassGroup.mk_eq_mk.mpr
  refine ⟨LinearEquiv.det E, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, coe_toPrincipalIdeal, LinearEquiv.coe_det]
  change (I : FractionalIdeal A⁰ (FractionRing A)) *
      FractionalIdeal.spanSingleton A⁰ d =
    (J : FractionalIdeal A⁰ (FractionRing A))
  rw [mul_comm]
  apply le_antisymm
  · intro y hy
    rcases FractionalIdeal.mem_singleton_mul.mp hy with ⟨x, hx, rfl⟩
    exact hmul ⟨x, hx⟩
  · intro y hy
    apply FractionalIdeal.mem_singleton_mul.mpr
    refine ⟨d' * y, hmul' ⟨y, hy⟩, ?_⟩
    change y = d * (d' * y)
    rw [← mul_assoc]
    change y =
      LinearMap.det E.toLinearMap * LinearMap.det E.symm.toLinearMap * y
    rw [LinearEquiv.det_mul_det_symm, one_mul]

/-- The same-rank form of Theorem 3.31(b): two finite sums of nonzero ideals are
equivalent exactly when the products of the ideals represent the same ideal class. -/
theorem ideals_direct_class
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (n : ℕ) (I J : Fin (n + 1) → Ideal A)
    (hI : ∀ i, I i ≠ ⊥) (hJ : ∀ i, J i ≠ ⊥) :
    Nonempty ((⨁ i, I i) ≃ₗ[A] (⨁ i, J i)) ↔
      ClassGroup.mk0 ⟨∏ i, I i, mem_nonZeroDivisors_iff_ne_zero.mpr
          (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hI i)⟩ =
        ClassGroup.mk0 ⟨∏ i, J i, mem_nonZeroDivisors_iff_ne_zero.mpr
          (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hJ i)⟩ := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨eI⟩ := ideals_direct_prod A n I hI
    obtain ⟨eJ⟩ := ideals_direct_prod A n J hJ
    let pI : (Ideal A)⁰ :=
      ⟨∏ i, I i, mem_nonZeroDivisors_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hI i)⟩
    let pJ : (Ideal A)⁰ :=
      ⟨∏ i, J i, mem_nonZeroDivisors_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hJ i)⟩
    let uI : (FractionalIdeal A⁰ (FractionRing A))ˣ :=
      FractionalIdeal.mk0 (FractionRing A) pI
    let uJ : (FractionalIdeal A⁰ (FractionRing A))ˣ :=
      FractionalIdeal.mk0 (FractionRing A) pJ
    let freeEquiv : (⨁ (_ : Fin n), A) ≃ₗ[A] (Fin n → A) :=
      DirectSum.linearEquivFunOnFintype A (Fin n) (fun _ ↦ A)
    let idealEquivI :
        (uI : FractionalIdeal A⁰ (FractionRing A)) ≃ₗ[A] ↑(∏ i, I i) :=
      (LinearEquiv.ofEq _ _ (by simp [uI, pI])).symm ≪≫ₗ
        (idealCoeFractional A (∏ i, I i)).symm
    let idealEquivJ :
        ↑(∏ i, J i) ≃ₗ[A]
          (uJ : FractionalIdeal A⁰ (FractionRing A)) :=
      idealCoeFractional A (∏ i, J i) ≪≫ₗ
        LinearEquiv.ofEq _ _ (by simp [uJ, pJ])
    let eStable :
        ((Fin n → A) × (uI : FractionalIdeal A⁰ (FractionRing A))) ≃ₗ[A]
          ((Fin n → A) × (uJ : FractionalIdeal A⁰ (FractionRing A))) :=
      (freeEquiv.symm.prodCongr idealEquivI) ≪≫ₗ
        eI.symm ≪≫ₗ e ≪≫ₗ eJ ≪≫ₗ
        (freeEquiv.prodCongr idealEquivJ)
    simpa [uI, uJ, pI, pJ] using
      free_prod_linear A n eStable
  · exact ideals_direct_linear A n I J hI hJ

/-- Theorem 3.31(b): two nonempty finite direct sums of nonzero ideals are equivalent
exactly when they have the same number of summands and the products of their ideals
represent the same ideal class. -/
theorem ideals_direct_nonempty
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (m n : ℕ) (I : Fin (m + 1) → Ideal A) (J : Fin (n + 1) → Ideal A)
    (hI : ∀ i, I i ≠ ⊥) (hJ : ∀ i, J i ≠ ⊥) :
    Nonempty ((⨁ i, I i) ≃ₗ[A] (⨁ i, J i)) ↔
      m = n ∧
        ClassGroup.mk0 ⟨∏ i, I i, mem_nonZeroDivisors_iff_ne_zero.mpr
            (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hI i)⟩ =
          ClassGroup.mk0 ⟨∏ i, J i, mem_nonZeroDivisors_iff_ne_zero.mpr
            (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hJ i)⟩ := by
  constructor
  · rintro ⟨e⟩
    have hmn := ideals_direct_imp A (m + 1) (n + 1) I J hI hJ e
    have hmn' : m = n := by omega
    subst n
    refine ⟨rfl, ?_⟩
    exact (ideals_direct_class
      A m I J hI hJ).mp ⟨e⟩
  · rintro ⟨hmn, hclass⟩
    subst n
    exact (ideals_direct_class
      A m I J hI hJ).mpr hclass

/-- A nonprincipal ideal is not isomorphic to the base ring.  This is the rank-one
part of the example following Theorem 3.31. -/
theorem not_base_ne
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥)
    (hclass :
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ ≠ 1) :
    ¬ Nonempty ((I : Type _) ≃ₗ[A] A) := by
  intro he
  obtain ⟨e⟩ := he
  let pI : (Ideal A)⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let pOne : (Ideal A)⁰ :=
    ⟨⊤, mem_nonZeroDivisors_iff_ne_zero.mpr (show (⊤ : Ideal A) ≠ ⊥ by simp)⟩
  let uI : (FractionalIdeal A⁰ (FractionRing A))ˣ :=
    FractionalIdeal.mk0 (FractionRing A) pI
  let uOne : (FractionalIdeal A⁰ (FractionRing A))ˣ :=
    FractionalIdeal.mk0 (FractionRing A) pOne
  have huI :
      (uI : FractionalIdeal A⁰ (FractionRing A)) =
        (I : FractionalIdeal A⁰ (FractionRing A)) := by
    simp [uI, pI]
  have huOne :
      (uOne : FractionalIdeal A⁰ (FractionRing A)) =
        ((⊤ : Ideal A) : FractionalIdeal A⁰ (FractionRing A)) := by
    simp [uOne, pOne]
  let eI :
      (uI : FractionalIdeal A⁰ (FractionRing A)) ≃ₗ[A] I :=
    (LinearEquiv.ofEq _ _
      (congrArg FractionalIdeal.coeToSubmodule huI)).trans
        (idealCoeFractional A I).symm
  let eOne :
      A ≃ₗ[A] (uOne : FractionalIdeal A⁰ (FractionRing A)) :=
    Submodule.topEquiv.symm |>.trans
      (idealCoeFractional A ⊤) |>.trans
      (LinearEquiv.ofEq _ _
        (congrArg FractionalIdeal.coeToSubmodule huOne.symm))
  let eFrac :
      (uI : FractionalIdeal A⁰ (FractionRing A)) ≃ₗ[A]
        (uOne : FractionalIdeal A⁰ (FractionRing A)) :=
    (eI.trans e).trans eOne
  have hclasses :
      ClassGroup.mk (FractionRing A) uI = ClassGroup.mk (FractionRing A) uOne :=
    class_fractional_linear A eFrac
  have hclasses' : ClassGroup.mk0 pI = ClassGroup.mk0 pOne := by
    simpa [uI, uOne] using hclasses
  have hpOne : pOne = 1 := by
    apply Subtype.ext
    simp [pOne]
  apply hclass
  calc
    ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ =
        ClassGroup.mk0 pI := by rfl
    _ = ClassGroup.mk0 pOne := hclasses'
    _ = 1 := by rw [hpOne, map_one]

/-- If a nonzero ideal has class of order dividing two, then two copies of it are
isomorphic to a free module of rank two. -/
theorem order_direct_free
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥)
    (horder :
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ ^ 2 = 1) :
    Nonempty
      ((⨁ _ : Fin 2, I) ≃ₗ[A] (⨁ _ : Fin 2, (⊤ : Ideal A))) := by
  refine ideals_direct_linear A 1
    (fun _ ↦ I) (fun _ ↦ ⊤) (fun _ ↦ hI) (fun _ ↦ by simp) ?_
  let pI : (Ideal A)⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  calc
    _ = ClassGroup.mk0 pI ^ 2 := by
      rw [← map_pow]
      congr 1
      apply Subtype.ext
      simp [pI, pow_two]
    _ = 1 := by simpa [pI] using horder
    _ = _ := by
      symm
      rw [← map_one (ClassGroup.mk0 : (Ideal A)⁰ →* ClassGroup A)]
      congr 1
      apply Subtype.ext
      simp

/-- The example after Theorem 3.31: an ideal of nontrivial order two in the class
group is not free, although its direct sum with itself is free of rank two. -/
theorem nonfree_but_direct
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥)
    (horder :
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ ^ 2 = 1)
    (hne : ClassGroup.mk0
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ ≠ 1) :
    ¬ Nonempty ((I : Type _) ≃ₗ[A] A) ∧
      Nonempty
        ((⨁ _ : Fin 2, I) ≃ₗ[A] (⨁ _ : Fin 2, (⊤ : Ideal A))) :=
  ⟨not_base_ne A I hI hne,
    order_direct_free A I hI horder⟩

end Towers.NumberTheory.Milne

import Towers.NumberTheory.Dedekind.CyclicQuotientCoordinates
import Towers.NumberTheory.Dedekind.FactorLastStep
import Towers.NumberTheory.Dedekind.InvariantFactorPseudobasis

/-!
# Induction for simultaneous invariant-factor pseudobases

This file packages the last-coordinate splitting used to turn an exact-rank quotient
presentation into Milne's simultaneous pseudobases.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

@[simp]
theorem if_fun_symm
    (A : Type*) [Semiring A]
    (i : Type*) [Fintype i]
    (F : i → Type*) [∀ j, AddCommMonoid (F j)] [∀ j, Module A (F j)]
    (x : ∀ j, F j) (j : i) :
    (DirectSum.linearEquivFunOnFintype A i F).symm x j = x j := by
  have h := congrFun
    ((DirectSum.linearEquivFunOnFintype A i F).apply_symm_apply x) j
  simpa using h

@[simp]
theorem if_pi_congr
    (A : Type*) [Semiring A]
    {i j : Type*} (F : i → Type*)
    [∀ k, AddCommMonoid (F k)] [∀ k, Module A (F k)]
    (e : j ≃ i) (x : ∀ k, F k) (k : j) :
    (LinearEquiv.piCongrLeft A F e).symm x k = x (e k) :=
  rfl

@[simp]
theorem if_option_fst
    (A : Type*) [Semiring A]
    {i : Type*} (F : Option i → Type*)
    [∀ k, AddCommMonoid (F k)] [∀ k, Module A (F k)]
    (x : ∀ k, F k) :
    (LinearEquiv.piOptionEquivProd A x).1 = x none :=
  rfl

@[simp]
theorem if_option_snd
    (A : Type*) [Semiring A]
    {i : Type*} (F : Option i → Type*)
    [∀ k, AddCommMonoid (F k)] [∀ k, Module A (F k)]
    (x : ∀ k, F k) (k : i) :
    (LinearEquiv.piOptionEquivProd A x).2 k = x (some k) :=
  rfl

/-- The subtype of a product submodule is the product of the two submodule types. -/
def ifPSubmodule
    {A X Y : Type*} [Semiring A]
    [AddCommMonoid X] [Module A X]
    [AddCommMonoid Y] [Module A Y]
    (P : Submodule A X) (Q : Submodule A Y) :
    Submodule.prod P Q ≃ₗ[A] P × Q where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), ⟨z.1.2, z.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Inside a coprime ideal, the elements lying in `I` form the product ideal. -/
def ifComapSubtype
    {A : Type*} [CommRing A]
    (B I : Ideal A) (hcop : B ⊔ I = ⊤) :
    Submodule.comap B.subtype (I : Submodule A A) ≃ₗ[A] (B * I : Ideal A) where
  toFun y := ⟨y.1.1, by
    rw [Ideal.mul_eq_inf_of_coprime hcop]
    exact ⟨y.1.2, y.2⟩⟩
  invFun y := ⟨⟨y.1, (Ideal.mul_le_right : B * I ≤ B) y.2⟩,
    (Ideal.mul_le_left : B * I ≤ I) y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Split a finite direct sum of ideals into its prefix and final coordinate. -/
noncomputable def directSplitLast
    (A : Type*) [CommRing A]
    (n : ℕ) (a : Fin (n + 1) → Ideal A) :
    DirectSum (Fin (n + 1)) (fun i ↦ a i) ≃ₗ[A]
      DirectSum (Fin n) (fun i ↦ a i.castSucc) × a (Fin.last n) := by
  classical
  let F : Fin (n + 1) → Type _ := fun i ↦ a i
  let KIdeal : Option (Fin n) → Ideal A := fun
    | none => a (Fin.last n)
    | some i => a i.castSucc
  let reindex :
      DirectSum (Fin (n + 1)) F ≃ₗ[A]
        DirectSum (Option (Fin n)) (fun o ↦ F (finSuccEquivLast.symm o)) :=
    DirectSum.lequivCongrLeft A finSuccEquivLast
  let normalize :
      DirectSum (Option (Fin n)) (fun o ↦ F (finSuccEquivLast.symm o)) ≃ₗ[A]
        DirectSum (Option (Fin n)) (fun o ↦ KIdeal o) :=
    DFinsupp.mapRange.linearEquiv fun o ↦ by
      cases o with
      | none => exact LinearEquiv.ofEq _ _ (by simp [KIdeal])
      | some i => exact LinearEquiv.ofEq _ _ (by simp [KIdeal])
  let split :
      DirectSum (Option (Fin n)) (fun o ↦ KIdeal o) ≃ₗ[A]
        KIdeal none × DirectSum (Fin n) (fun i ↦ KIdeal (some i)) :=
    DirectSum.lequivProdDirectSum (R := A)
  simpa [F, KIdeal] using
    (reindex ≪≫ₗ normalize ≪≫ₗ split ≪≫ₗ LinearEquiv.prodComm A _ _)

@[simp]
theorem direct_split_fst
    (A : Type*) [CommRing A]
    (n : ℕ) (a : Fin (n + 1) → Ideal A)
    (x : DirectSum (Fin (n + 1)) (fun i ↦ a i)) (i : Fin n) :
    (directSplitLast A n a x).1 i = x i.castSucc := by
  apply Subtype.ext
  change (x (finSuccEquivLast.symm (some i))).1 = (x i.castSucc).1
  exact congrArg (fun j : Fin (n + 1) ↦ (x j : A))
    (finSuccEquivLast_symm_some i)

@[simp]
theorem direct_split_snd
    (A : Type*) [CommRing A]
    (n : ℕ) (a : Fin (n + 1) → Ideal A)
    (x : DirectSum (Fin (n + 1)) (fun i ↦ a i)) :
    (directSplitLast A n a x).2 = x (Fin.last n) := by
  apply Subtype.ext
  change (x (finSuccEquivLast.symm none)).1 = (x (Fin.last n)).1
  exact congrArg (fun j : Fin (n + 1) ↦ (x j : A))
    finSuccEquivLast_symm_none

/-- Splitting the last ideal coordinate commutes with the diagonal invariant-factor map. -/
theorem direct_split_diagonal
    (A : Type*) [CommRing A]
    (n : ℕ) (a b : Fin (n + 1) → Ideal A)
    (x : DirectSum (Fin (n + 1)) (fun i ↦ (a i * b i : Ideal A))) :
    directSplitLast A n a
        (invariantFactorDiagonal A a b x) =
      (invariantFactorDiagonal A
          (fun i ↦ a i.castSucc) (fun i ↦ b i.castSucc)
          (directSplitLast A n
            (fun i ↦ a i * b i) x).1,
        Submodule.inclusion Ideal.mul_le_right
          (directSplitLast A n
            (fun i ↦ a i * b i) x).2) := by
  apply Prod.ext
  · ext i
    rfl
  · apply Subtype.ext
    rfl

/-- Restricting the explicit kernel-range splitting to `N` gives the product of its kernel
part and the product ideal `range f * I`. -/
noncomputable def submodule_range_mul
    {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    (f : M →ₗ[A] A) (r : LinearMap.range f →ₗ[A] M)
    (hr : f.rangeRestrict.comp r = LinearMap.id)
    (I : Ideal A) (hcop : LinearMap.range f ⊔ I = ⊤)
    (N : Submodule A M)
    (hIM : I • (⊤ : Submodule A M) ≤ N)
    (hN : N ≤ Submodule.comap f (I : Submodule A A)) :
    N ≃ₗ[A]
      (Submodule.comap (LinearMap.ker f).subtype N) ×
        (LinearMap.range f * I : Ideal A) := by
  let e := kerRangeSection f r hr
  let P := Submodule.comap (LinearMap.ker f).subtype N
  let Q := Submodule.comap (LinearMap.range f).subtype (I : Submodule A A)
  have hmap : N.map e.toLinearMap = Submodule.prod P Q :=
    submodule_comap_subtype
      f r hr I hcop N hIM hN
  exact e.submoduleMap N ≪≫ₗ LinearEquiv.ofEq _ _ hmap ≪≫ₗ
    ifPSubmodule P Q ≪≫ₗ
      (LinearEquiv.refl A P).prodCongr
        (ifComapSubtype (LinearMap.range f) I hcop)

end Towers.NumberTheory.Milne

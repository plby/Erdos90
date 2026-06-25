import Submission.NumberTheory.Dedekind.FactorPseudobasisStep
import Submission.NumberTheory.Dedekind.RankRecursionHelpers


/-!
# Recursive construction of simultaneous invariant-factor pseudobases

This file packages the append operation and the induction that turns an exact-length cyclic
quotient presentation into Milne's simultaneous pseudobases.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

universe u

/-- Coordinatewise linear equivalences induce an equivalence of direct sums. -/
noncomputable def directCongrRight
    {A ι : Type*} [Semiring A]
    (M N : ι → Type*)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module A (N i)]
    (e : ∀ i, M i ≃ₗ[A] N i) :
    DirectSum ι M ≃ₗ[A] DirectSum ι N :=
  LinearEquiv.ofLinear
    (DirectSum.lmap fun i ↦ (e i).toLinearMap)
    (DirectSum.lmap fun i ↦ (e i).symm.toLinearMap)
    (by ext x i; simp)
    (by ext x i; simp)

@[simp]
theorem direct_congr_right
    {A ι : Type*} [Semiring A]
    (M N : ι → Type*)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module A (N i)]
    (e : ∀ i, M i ≃ₗ[A] N i) (x : DirectSum ι M) (i : ι) :
    directCongrRight M N e x i = e i (x i) :=
  rfl

@[simp]
theorem direct_congr_symm
    {A ι : Type*} [Semiring A]
    (M N : ι → Type*)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module A (N i)]
    (e : ∀ i, M i ≃ₗ[A] N i) (x : DirectSum ι N) (i : ι) :
    (directCongrRight M N e).symm x i = (e i).symm (x i) :=
  rfl

/-- Append one ideal coordinate to a simultaneous invariant-factor pseudobasis. -/
noncomputable def IFPseudo.appendLast
    {A K M : Type*} [CommRing A]
    [AddCommGroup K] [Module A K]
    [AddCommGroup M] [Module A M]
    {n : ℕ} (b : Fin (n + 1) → Ideal A)
    (N₀ : Submodule A K) (N : Submodule A M)
    (d : IFPseudo A K N₀ n (fun i ↦ b i.castSucc))
    (B : Ideal A) (hB : B ≠ ⊥)
    (eM : M ≃ₗ[A] K × B)
    (eN : N ≃ₗ[A] N₀ × (B * b (Fin.last n) : Ideal A))
    (hcomm : ∀ x : N,
      eM x.1 = ((eN x).1.1,
        Submodule.inclusion Ideal.mul_le_right (eN x).2)) :
    IFPseudo A M N (n + 1) b := by
  let a : Fin (n + 1) → Ideal A := Fin.snoc d.ambientIdeal B
  let rawSplitA := directSplitLast A n a
  let normalizeA :
      (DirectSum (Fin n) (fun i ↦ a i.castSucc) × a (Fin.last n)) ≃ₗ[A]
        (DirectSum (Fin n) (fun i ↦ d.ambientIdeal i) × B) := by
    exact (directCongrRight
      (fun i : Fin n ↦ a i.castSucc) (fun i ↦ d.ambientIdeal i) (fun i ↦
        LinearEquiv.ofEq (a i.castSucc) (d.ambientIdeal i)
          (by simp [a]))).prodCongr
        (LinearEquiv.ofEq (a (Fin.last n)) B (by simp [a]))
  let splitA :
      DirectSum (Fin (n + 1)) (fun i ↦ a i) ≃ₗ[A]
        DirectSum (Fin n) (fun i ↦ d.ambientIdeal i) × B :=
    rawSplitA ≪≫ₗ normalizeA
  let rawSplitAB :=
    directSplitLast A n (fun i ↦ a i * b i)
  let normalizeAB :
      (DirectSum (Fin n) (fun i ↦ (a i.castSucc * b i.castSucc : Ideal A)) ×
          (a (Fin.last n) * b (Fin.last n) : Ideal A)) ≃ₗ[A]
        (DirectSum (Fin n)
            (fun i ↦ (d.ambientIdeal i * b i.castSucc : Ideal A)) ×
          (B * b (Fin.last n) : Ideal A)) := by
    exact (directCongrRight
      (fun i : Fin n ↦ (a i.castSucc * b i.castSucc : Ideal A))
      (fun i ↦ (d.ambientIdeal i * b i.castSucc : Ideal A)) (fun i ↦
        LinearEquiv.ofEq (a i.castSucc * b i.castSucc)
          (d.ambientIdeal i * b i.castSucc) (by simp [a]))).prodCongr
        (LinearEquiv.ofEq (a (Fin.last n) * b (Fin.last n))
          (B * b (Fin.last n)) (by simp [a]))
  let splitAB :
      DirectSum (Fin (n + 1)) (fun i ↦ (a i * b i : Ideal A)) ≃ₗ[A]
        DirectSum (Fin n)
            (fun i ↦ (d.ambientIdeal i * b i.castSucc : Ideal A)) ×
          (B * b (Fin.last n) : Ideal A) :=
    rawSplitAB ≪≫ₗ normalizeAB
  let ambientEquiv :
      M ≃ₗ[A] DirectSum (Fin (n + 1)) (fun i ↦ a i) :=
    eM ≪≫ₗ
      d.ambientEquiv.prodCongr (LinearEquiv.refl A B) ≪≫ₗ splitA.symm
  let submoduleEquiv :
      N ≃ₗ[A]
        DirectSum (Fin (n + 1)) (fun i ↦ (a i * b i : Ideal A)) :=
    eN ≪≫ₗ
      d.submoduleEquiv.prodCongr
        (LinearEquiv.refl A (B * b (Fin.last n) : Ideal A)) ≪≫ₗ
      splitAB.symm
  refine
    { ambientIdeal := a
      ambient_ne_bot := ?_
      ambientEquiv := ambientEquiv
      submoduleEquiv := submoduleEquiv
      inclusion_commutes := ?_ }
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [a] using hB
    simpa only [a, Fin.snoc_castSucc] using d.ambient_ne_bot j
  · intro x
    apply splitA.injective
    change splitA
        (invariantFactorDiagonal A a b (submoduleEquiv x)) =
      splitA (splitA.symm (d.ambientEquiv (eM x.1).1, (eM x.1).2))
    rw [splitA.apply_symm_apply]
    change normalizeA (rawSplitA
        (invariantFactorDiagonal A a b
          (rawSplitAB.symm (normalizeAB.symm
            (d.submoduleEquiv (eN x).1, (eN x).2))))) =
      (d.ambientEquiv (eM x.1).1, (eM x.1).2)
    have hdiag := direct_split_diagonal A n a b
      (rawSplitAB.symm (normalizeAB.symm
        (d.submoduleEquiv (eN x).1, (eN x).2)))
    rw [hdiag, rawSplitAB.apply_symm_apply]
    apply Prod.ext
    · have hc1 := congrArg Prod.fst (hcomm x)
      rw [hc1]
      ext i
      have hd := congrArg (fun z ↦ (z i : A))
        (d.inclusion_commutes (eN x).1)
      simpa [normalizeA, normalizeAB, a,
        LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply] using hd
    · apply Subtype.ext
      have hc2 := congrArg (fun z ↦ z.2.1) (hcomm x)
      simpa [normalizeA, normalizeAB, a,
        LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply] using hc2.symm

/-- An exact-rank invariant-factor presentation of the quotient lifts recursively to simultaneous
ideal pseudobases of the ambient lattice and sublattice. -/
theorem invariant_pseudobasis_rank
    (A M : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (n : ℕ) (b : Fin n → Ideal A) (hb : Antitone b)
    (e : (M ⧸ N) ≃ₗ[A]
      DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i)))
    (hrank : Module.finrank A M = n) :
    Nonempty (IFPseudo A M N n b) := by
  induction n generalizing M with
  | zero =>
      have hfin : Module.finrank A M = 0 := hrank
      letI : Subsingleton M := Module.finrank_zero_iff.mp hfin
      have hN : N = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : x = 0 := Subsingleton.elim _ _
        simp [hx]
      exact invariant_pseudobasis_top A M N hN 0 b
        (fun i ↦ Fin.elim0 i) hrank
  | succ n ih =>
      by_cases hlast : b (Fin.last n) = ⊤
      · have hbtop : ∀ i, b i = ⊤ := by
          intro i
          apply top_unique
          simpa [hlast] using hb (Fin.le_last i)
        have htarget : ∀ y : DirectSum (Fin (n + 1))
            (fun i ↦ idealQuotientModule A (b i)), y = 0 := by
          intro y
          ext i
          letI : Unique (idealQuotientModule A (b i)) :=
            Classical.choice (Submodule.unique_quotient_iff_eq_top.mpr (hbtop i))
          exact Subsingleton.elim _ _
        have hsource : ∀ y : M ⧸ N, y = 0 := by
          intro y
          apply e.injective
          simpa using htarget (e y)
        have hN : N = ⊤ := by
          apply Submodule.Quotient.subsingleton_iff.mp
          exact ⟨fun x y ↦ (hsource x).trans (hsource y).symm⟩
        exact invariant_pseudobasis_top A M N hN (n + 1) b
          hbtop hrank
      · obtain ⟨f, r, hr, hJ, eM, eN, ePrefix, hcomm⟩ :=
          invariant_pseudobasis_step A M N n b hb e hlast
        let K := LinearMap.ker f
        let P := Submodule.comap K.subtype N
        let J := LinearMap.range f
        letI : Module.Finite A K :=
          Module.Finite.of_fg (IsNoetherian.noetherian _)
        letI : Module.Finite A J :=
          Module.Finite.of_fg (IsNoetherian.noetherian _)
        have hfinJ : Module.finrank A J = 1 := by
          apply Nat.le_antisymm
          · simpa [J] using
              LinearMap.finrank_le_finrank_of_injective (LinearMap.range f).injective_subtype
          · exact (Submodule.one_le_finrank_iff).2 hJ
        have hfinK : Module.finrank A K = n := by
          have hfinQuotient : Module.finrank A (M ⧸ K) = 1 := by
            exact f.quotKerEquivRange.finrank_eq.trans hfinJ
          have h := K.finrank_quotient_add_finrank
          rw [hfinQuotient, hrank] at h
          omega
        have hbPrefix : Antitone (fun i : Fin n ↦ b i.castSucc) := by
          intro i j hij
          exact hb (Fin.castSucc_le_castSucc_iff.mpr hij)
        obtain ⟨d⟩ := ih (M := K) P (fun i : Fin n ↦ b i.castSucc)
          hbPrefix ePrefix hfinK
        exact ⟨d.appendLast b P N J hJ eM eN hcomm⟩

end Submission.NumberTheory.Milne

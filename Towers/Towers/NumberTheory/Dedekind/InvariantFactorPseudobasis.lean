import Towers.NumberTheory.Dedekind.InvariantFactorKernel
import Towers.NumberTheory.Dedekind.PseudobasisGlobal

/-!
# Pseudobasis form of the invariant-factor theorem

The structure below records Milne's simultaneous pseudobases without choosing explicit fraction
field generators: the ambient lattice is a direct sum of nonzero ideals `a i`, the sublattice is
a direct sum of the products `a i * b i`, and the inclusion is the componentwise ideal inclusion.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

universe u

/-- The componentwise inclusion from the product-ideal pseudobasis into the ambient pseudobasis. -/
noncomputable def invariantFactorDiagonal
    (A : Type*) [CommRing A]
    {n : ℕ} (a b : Fin n → Ideal A) :
    DirectSum (Fin n) (fun i ↦ (a i * b i : Ideal A)) →ₗ[A]
      DirectSum (Fin n) (fun i ↦ a i) :=
  DirectSum.lmap fun _ ↦
    Submodule.inclusion Ideal.mul_le_right

@[simp]
theorem invariant_diagonal_coe
    (A : Type*) [CommRing A]
    {n : ℕ} (a b : Fin n → Ideal A)
    (x : DirectSum (Fin n) (fun i ↦ (a i * b i : Ideal A))) (i : Fin n) :
    (((invariantFactorDiagonal A a b x) i : a i) : A) = (x i : A) :=
  rfl

/-- A simultaneous ideal pseudobasis realizing a prescribed family of invariant factors. -/
structure IFPseudo
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (N : Submodule A M) (n : ℕ) (b : Fin n → Ideal A) where
  ambientIdeal : Fin n → Ideal A
  ambient_ne_bot : ∀ i, ambientIdeal i ≠ ⊥
  ambientEquiv : M ≃ₗ[A] DirectSum (Fin n) (fun i ↦ ambientIdeal i)
  submoduleEquiv :
    N ≃ₗ[A] DirectSum (Fin n) (fun i ↦ (ambientIdeal i * b i : Ideal A))
  inclusion_commutes : ∀ x : N,
    invariantFactorDiagonal A ambientIdeal b (submoduleEquiv x) =
      ambientEquiv x.1

/-- When every invariant factor is the unit ideal, the diagonal map is an equivalence. -/
noncomputable def invariantDiagonalTop
    (A : Type*) [CommRing A]
    {n : ℕ} (a b : Fin n → Ideal A) (hb : ∀ i, b i = ⊤) :
    DirectSum (Fin n) (fun i ↦ (a i * b i : Ideal A)) ≃ₗ[A]
      DirectSum (Fin n) (fun i ↦ a i) := by
  apply LinearEquiv.ofBijective (invariantFactorDiagonal A a b)
  constructor
  · change Function.Injective (DirectSum.lmap fun i ↦
      Submodule.inclusion (Ideal.mul_le_right : a i * b i ≤ a i))
    rw [DirectSum.lmap_injective]
    intro i
    exact (Submodule.inclusion_injective Ideal.mul_le_right)
  · change Function.Surjective (DirectSum.lmap fun i ↦
      Submodule.inclusion (Ideal.mul_le_right : a i * b i ≤ a i))
    rw [DirectSum.lmap_surjective]
    intro i y
    refine ⟨⟨y.1, ?_⟩, rfl⟩
    simp [hb i, y.2]

/-- The degenerate branch of the invariant-factor theorem: if `N = M` and all invariant ideals
are `⊤`, any ideal pseudobasis of `M` is already a simultaneous invariant-factor pseudobasis. -/
theorem invariant_pseudobasis_top
    (A M : Type u) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M) (hN : N = ⊤)
    (n : ℕ) (b : Fin n → Ideal A) (hb : ∀ i, b i = ⊤)
    (hrank : Module.finrank A M = n) :
    Nonempty (IFPseudo A M N n b) := by
  classical
  obtain ⟨m, I, hI, ⟨eM⟩⟩ :=
    direct_nonzero_ideals A M
  have hm : Module.finrank A M = m := by
    rw [eM.finrank_eq]
    exact ideals_direct_finrank A m I hI
  have hmn : m = n := hm.symm.trans hrank
  let idx : Fin m ≃ Fin n := finCongr hmn
  let a : Fin n → Ideal A := fun i ↦ I (idx.symm i)
  have ha : ∀ i, a i ≠ ⊥ := fun i ↦ hI (idx.symm i)
  let ambientEquiv : M ≃ₗ[A] DirectSum (Fin n) (fun i ↦ a i) :=
    eM ≪≫ₗ DirectSum.lequivCongrLeft A idx
  let diagonalEquiv := invariantDiagonalTop A a b hb
  let topEquiv : N ≃ₗ[A] M := LinearEquiv.ofTop N hN
  let submoduleEquiv :
      N ≃ₗ[A] DirectSum (Fin n) (fun i ↦ (a i * b i : Ideal A)) :=
    topEquiv ≪≫ₗ ambientEquiv ≪≫ₗ diagonalEquiv.symm
  refine ⟨⟨a, ha, ambientEquiv, submoduleEquiv, ?_⟩⟩
  intro x
  change invariantFactorDiagonal A a b (diagonalEquiv.symm (ambientEquiv (topEquiv x))) =
    ambientEquiv x.1
  change diagonalEquiv (diagonalEquiv.symm (ambientEquiv (topEquiv x))) =
    ambientEquiv x.1
  calc
    diagonalEquiv (diagonalEquiv.symm (ambientEquiv (topEquiv x))) =
        ambientEquiv (topEquiv x) := diagonalEquiv.apply_symm_apply _
    _ = ambientEquiv x.1 := congrArg ambientEquiv (LinearEquiv.ofTop_apply N x)

end Towers.NumberTheory.Milne

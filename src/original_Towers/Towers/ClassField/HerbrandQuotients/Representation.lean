import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Equiv

/-!
# Chapter VII, Section 3, Lemma 3.2

Descent of an isomorphism between two finite-dimensional representations
from a field extension of an infinite ground field.
-/

namespace Towers.CField.HQuotie

open scoped BigOperators TensorProduct

noncomputable section

universe u v w x y

/-- Extension of scalars of a representation, on the canonical tensor-product
model `Ω ⊗[k] M`. -/
def Representation.baseChange
    (k Ω G M : Type*) [CommSemiring k] [Semiring Ω] [Algebra k Ω]
    [Monoid G] [AddCommMonoid M] [Module k M]
    (ρ : Representation k G M) : Representation Ω G (Ω ⊗[k] M) :=
  (Module.End.baseChangeHom k Ω M).toMonoidHom.comp ρ

@[simp]
lemma Representation.baseChange_apply
    (k Ω G M : Type*) [CommSemiring k] [Semiring Ω] [Algebra k Ω]
    [Monoid G] [AddCommMonoid M] [Module k M]
    (ρ : Representation k G M) (g : G) :
    Representation.baseChange k Ω G M ρ g = (ρ g).baseChange Ω :=
  rfl

/-- Base change of an equivariant linear map is equivariant for the
base-changed representations. -/
def Representation.IntertwiningMap.change
    {k Ω G M N : Type*} [CommSemiring k] [Semiring Ω] [Algebra k Ω]
    [Monoid G] [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N]
    {ρ : Representation k G M} {σ : Representation k G N}
    (f : ρ.IntertwiningMap σ) :
    (Representation.baseChange k Ω G M ρ).IntertwiningMap
      (Representation.baseChange k Ω G N σ) where
  toLinearMap := f.toLinearMap.baseChange Ω
  isIntertwining' g := by
    rw [Representation.baseChange_apply, Representation.baseChange_apply,
      ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, f.isIntertwining']

@[simp]
lemma Representation.IntertwiningMap.ba_c_l
    {k Ω G M N : Type*} [CommSemiring k] [Semiring Ω] [Algebra k Ω]
    [Monoid G] [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N]
    {ρ : Representation k G M} {σ : Representation k G N}
    (f : ρ.IntertwiningMap σ) :
    (Representation.IntertwiningMap.change (Ω := Ω) f).toLinearMap =
      f.toLinearMap.baseChange Ω :=
  rfl

/-- The precise linear-algebra comparison used in Milne's proof: every
equivariant map after extension of scalars is an `Ω`-linear combination of
base changes of equivariant maps over `k`.

This is the only interface not currently packaged by Mathlib's representation
API. It is the kernel/base-change fact for the finite homogeneous linear
system expressing equivariance. -/
def IntertwiningSpanningBridge : Prop :=
  ∀ (k : Type u) (Ω : Type v) (G : Type w) (M : Type x) (N : Type y)
    [Field k] [Field Ω] [Algebra k Ω] [Group G] [Finite G]
    [AddCommGroup M] [Module k M] [Module.Finite k M]
    [AddCommGroup N] [Module k N] [Module.Finite k N]
    (ρ : Representation k G M) (σ : Representation k G N)
    (f : (Representation.baseChange k Ω G M ρ).IntertwiningMap
      (Representation.baseChange k Ω G N σ)),
    ∃ (n : ℕ) (a : Fin n → Ω) (g : Fin n → ρ.IntertwiningMap σ),
      f.toLinearMap = ∑ i, a i •
        (Representation.IntertwiningMap.change (Ω := Ω) (g i)).toLinearMap

private lemma matrix_baseChange
    {k Ω M : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [AddCommGroup M] [Module k M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k M) (f : M →ₗ[k] M) :
    LinearMap.toMatrix (b.baseChange Ω) (b.baseChange Ω) (f.baseChange Ω) =
      (algebraMap k Ω).mapMatrix (LinearMap.toMatrix b b f) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

/-- Milne's determinant-polynomial argument, with the one unavailable
kernel/base-change comparison supplied by the bridge above. -/
theorem representation_statement_bridge
    (hbase : IntertwiningSpanningBridge.{u, v, w, x, y}) :
    (∀ (k : Type u) (Ω : Type v) (G : Type w) (M : Type x) (N : Type y)
          [Field k] [Infinite k] [Field Ω] [Algebra k Ω]
          [Group G] [Finite G]
          [AddCommGroup M] [Module k M] [Module.Finite k M]
          [AddCommGroup N] [Module k N] [Module.Finite k N]
          (ρ : Representation k G M) (σ : Representation k G N),
          Nonempty ((Representation.baseChange k Ω G M ρ).Equiv
            (Representation.baseChange k Ω G N σ)) → Nonempty (ρ.Equiv σ)) := by
  intro k Ω G M N _ _ _ _ _ _ _ _ _ _ _ _ ρ σ ⟨φ⟩
  have hrankΩ : Module.finrank Ω (Ω ⊗[k] M) = Module.finrank Ω (Ω ⊗[k] N) :=
    φ.toLinearEquiv.finrank_eq
  have hrank : Module.finrank k M = Module.finrank k N := by
    simpa only [Module.finrank_baseChange] using hrankΩ
  let e : N ≃ₗ[k] M := LinearEquiv.ofFinrankEq N M hrank.symm
  obtain ⟨n, a, g, hφ⟩ := hbase k Ω G M N ρ σ φ.toIntertwiningMap
  let I := Module.Free.ChooseBasisIndex k M
  let b : Module.Basis I k M := Module.Free.chooseBasis k M
  let F : Fin n → M →ₗ[k] M := fun i ↦ e.toLinearMap ∘ₗ (g i).toLinearMap
  let A : Matrix I I (MvPolynomial (Fin n) k) :=
    fun r s ↦ ∑ i : Fin n, MvPolynomial.X i *
      MvPolynomial.C (LinearMap.toMatrix b b (F i) r s)
  let p : MvPolynomial (Fin n) k := A.det
  have hcomp :
      (e.baseChange k Ω N M).toLinearMap ∘ₗ φ.toLinearMap =
        ∑ i, a i • (F i).baseChange Ω := by
    rw [hφ]
    ext z
    simp [F, LinearMap.baseChange_comp]
  have hmatrixΩ :
      (MvPolynomial.eval₂Hom (algebraMap k Ω) a).mapMatrix A =
        LinearMap.toMatrix (b.baseChange Ω) (b.baseChange Ω)
          ((e.baseChange k Ω N M).toLinearMap ∘ₗ φ.toLinearMap) := by
    rw [hcomp]
    ext i j
    simp only [A, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
      RingHom.mapMatrix_apply, smul_eq_mul]
    simp [F, matrix_baseChange]
  have hp_eval : MvPolynomial.eval₂ (algebraMap k Ω) a p ≠ 0 := by
    change (MvPolynomial.eval₂Hom (algebraMap k Ω) a) A.det ≠ 0
    rw [RingHom.map_det, hmatrixΩ]
    have hu : IsUnit ((e.baseChange k Ω N M).toLinearMap ∘ₗ φ.toLinearMap) := by
      rw [Module.End.isUnit_iff]
      exact (e.baseChange k Ω N M).bijective.comp φ.toLinearEquiv.bijective
    have hd := (LinearMap.isUnit_det _ hu).ne_zero
    simpa only [LinearMap.det_toMatrix (b.baseChange Ω)] using hd
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hp_eval
  obtain ⟨c, hc⟩ : ∃ c : Fin n → k, MvPolynomial.eval c p ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply MvPolynomial.funext
    intro c
    simpa using h c
  let f : ρ.IntertwiningMap σ := ∑ i, c i • g i
  have hdet : LinearMap.det (e.toLinearMap ∘ₗ f.toLinearMap) ≠ 0 := by
    rw [← LinearMap.det_toMatrix b]
    have hcompk : e.toLinearMap ∘ₗ f.toLinearMap = ∑ i, c i • F i := by
      ext z
      change e ((∑ i, c i • g i) z) = _
      rw [show (∑ i, c i • g i) z = ∑ i, (c i • g i) z by
        exact Representation.IntertwiningMap.sum_apply ρ σ Finset.univ
          (fun i ↦ c i • g i) z]
      simp [F]
    have heval :
        (MvPolynomial.eval c).mapMatrix A =
          LinearMap.toMatrix b b (e.toLinearMap ∘ₗ f.toLinearMap) := by
      rw [hcompk]
      ext i j
      simp only [A, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply,
        RingHom.mapMatrix_apply, smul_eq_mul]
      simp [Matrix.map_apply]
    rw [← heval, ← RingHom.map_det]
    exact hc
  have hendUnit : IsUnit (e.toLinearMap ∘ₗ f.toLinearMap) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact (isUnit_iff_ne_zero).2 hdet
  have hfbij : Function.Bijective f := by
    have hcompbij : Function.Bijective (e.toLinearMap ∘ₗ f.toLinearMap) :=
      (Module.End.isUnit_iff _).1 hendUnit
    constructor
    · intro x y hxy
      apply hcompbij.injective
      exact congrArg e hxy
    · intro y
      obtain ⟨x, hx⟩ := hcompbij.surjective (e y)
      exact ⟨x, e.injective hx⟩
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap hfbij)
    f.isIntertwining'⟩

end

end Towers.CField.HQuotie

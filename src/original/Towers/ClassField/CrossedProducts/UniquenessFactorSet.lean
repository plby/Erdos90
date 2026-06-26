import Towers.ClassField.CrossedProducts.ConjugatorsIndependent

/-!
# Chapter IV, Section 3, Theorem 3.11: uniqueness from a factor set

This file formalizes the uniqueness step in Milne's proof.  An algebra with an
`L`-basis indexed by `Gal(L/k)` is determined, up to `k`-algebra isomorphism,
by equations (39) and (40).
-/

namespace Towers.CField.CProduca

noncomputable section

universe u

variable (k L A A' : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  [Ring A] [Nontrivial A] [Algebra k A]
  [Ring A'] [Nontrivial A'] [Algebra k A']

/-- Two algebras with Galois-indexed bases satisfying the same factor-set
relations are isomorphic as `k`-algebras.  This is the uniqueness assertion
used in the proof that the fibres of `gamma` in Theorem IV.3.11 are
isomorphism classes. -/
def algSameSet
    (i : L →ₐ[k] A) (i' : L →ₐ[k] A')
    (b : letI : Module L A := i.toRingHom.toModule
      Module.Basis Gal(L/k) L A)
    (b' : letI : Module L A' := i'.toRingHom.toModule
      Module.Basis Gal(L/k) L A')
    (phi : Gal(L/k) × Gal(L/k) → Lˣ)
    (hb_one : b 1 = 1) (hb'_one : b' 1 = 1)
    (hb_scalar : ∀ (sigma : Gal(L/k)) (a : L),
      b sigma * i a = i (sigma a) * b sigma)
    (hb'_scalar : ∀ (sigma : Gal(L/k)) (a : L),
      b' sigma * i' a = i' (sigma a) * b' sigma)
    (hb_mul : ∀ sigma tau : Gal(L/k),
      b sigma * b tau = i (phi (sigma, tau) : L) * b (sigma * tau))
    (hb'_mul : ∀ sigma tau : Gal(L/k),
      b' sigma * b' tau = i' (phi (sigma, tau) : L) * b' (sigma * tau)) :
    A ≃ₐ[k] A' := by
  letI : Module L A := i.toRingHom.toModule
  letI : Module L A' := i'.toRingHom.toModule
  letI : IsScalarTower k L A := ⟨fun r s x ↦ by
    change i (r • s) * x = r • (i s * x)
    rw [map_smul]
    exact Algebra.smul_mul_assoc r (i s) x⟩
  letI : IsScalarTower k L A' := ⟨fun r s x ↦ by
    change i' (r • s) * x = r • (i' s * x)
    rw [map_smul]
    exact Algebra.smul_mul_assoc r (i' s) x⟩
  let eL : A ≃ₗ[L] A' := b.equiv b' (Equiv.refl _)
  have hproduct (sigma tau : Gal(L/k)) (a c : L) :
      (a • b sigma) * (c • b tau) =
        (a * sigma c * (phi (sigma, tau) : L)) • b (sigma * tau) := by
    change (i a * b sigma) * (i c * b tau) =
      i (a * sigma c * (phi (sigma, tau) : L)) * b (sigma * tau)
    calc
      (i a * b sigma) * (i c * b tau) =
          (i a * (b sigma * i c)) * b tau := by simp only [mul_assoc]
      _ = (i a * (i (sigma c) * b sigma)) * b tau := by rw [hb_scalar]
      _ = (i a * i (sigma c)) * (b sigma * b tau) := by simp only [mul_assoc]
      _ = (i a * i (sigma c)) *
          (i (phi (sigma, tau) : L) * b (sigma * tau)) := by rw [hb_mul]
      _ = i (a * sigma c * (phi (sigma, tau) : L)) * b (sigma * tau) := by
        simp only [map_mul, mul_assoc]
  have hproduct' (sigma tau : Gal(L/k)) (a c : L) :
      (a • b' sigma) * (c • b' tau) =
        (a * sigma c * (phi (sigma, tau) : L)) • b' (sigma * tau) := by
    change (i' a * b' sigma) * (i' c * b' tau) =
      i' (a * sigma c * (phi (sigma, tau) : L)) * b' (sigma * tau)
    calc
      (i' a * b' sigma) * (i' c * b' tau) =
          (i' a * (b' sigma * i' c)) * b' tau := by simp only [mul_assoc]
      _ = (i' a * (i' (sigma c) * b' sigma)) * b' tau := by rw [hb'_scalar]
      _ = (i' a * i' (sigma c)) * (b' sigma * b' tau) := by simp only [mul_assoc]
      _ = (i' a * i' (sigma c)) *
          (i' (phi (sigma, tau) : L) * b' (sigma * tau)) := by rw [hb'_mul]
      _ = i' (a * sigma c * (phi (sigma, tau) : L)) * b' (sigma * tau) := by
        simp only [map_mul, mul_assoc]
  have hsingle (sigma tau : Gal(L/k)) (a c : L) :
      eL ((a • b sigma) * (c • b tau)) =
        eL (a • b sigma) * eL (c • b tau) := by
    rw [hproduct]
    simp only [eL.map_smul]
    simp only [eL, Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [hproduct']
  have hmul_repr (f g : Gal(L/k) →₀ L) :
      eL (b.repr.symm f * b.repr.symm g) =
        eL (b.repr.symm f) * eL (b.repr.symm g) := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ hf₁ hf₂ => simp only [map_add, add_mul, hf₁, hf₂]
    | single sigma a =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ hg₁ hg₂ => simp only [map_add, mul_add, hg₁, hg₂]
      | single tau c =>
        simpa only [Module.Basis.repr_symm_single] using hsingle sigma tau a c
  have hmul (x y : A) : eL (x * y) = eL x * eL y := by
    rw [← b.repr.symm_apply_apply x, ← b.repr.symm_apply_apply y]
    exact hmul_repr (b.repr x) (b.repr y)
  have hone : eL 1 = 1 := by
    rw [← hb_one, Module.Basis.equiv_apply, Equiv.refl_apply, hb'_one]
  exact AlgEquiv.ofLinearEquiv (eL.restrictScalars k) hone hmul

/-- A version of `algSameSet` for already chosen `L`-module
structures.  It is useful when scalar multiplication is propositionally, but
not definitionally, left multiplication through the specified embeddings. -/
def sameScalarActions
    [Module L A] [Module L A'] [IsScalarTower k L A] [IsScalarTower k L A']
    (i : L →ₐ[k] A) (i' : L →ₐ[k] A')
    (b : Module.Basis Gal(L/k) L A)
    (b' : Module.Basis Gal(L/k) L A')
    (phi : Gal(L/k) × Gal(L/k) → Lˣ)
    (hi : ∀ (a : L) (x : A), i a * x = a • x)
    (hi' : ∀ (a : L) (x : A'), i' a * x = a • x)
    (hb_one : b 1 = 1) (hb'_one : b' 1 = 1)
    (hb_scalar : ∀ (sigma : Gal(L/k)) (a : L),
      b sigma * i a = i (sigma a) * b sigma)
    (hb'_scalar : ∀ (sigma : Gal(L/k)) (a : L),
      b' sigma * i' a = i' (sigma a) * b' sigma)
    (hb_mul : ∀ sigma tau : Gal(L/k),
      b sigma * b tau = i (phi (sigma, tau) : L) * b (sigma * tau))
    (hb'_mul : ∀ sigma tau : Gal(L/k),
      b' sigma * b' tau = i' (phi (sigma, tau) : L) * b' (sigma * tau)) :
    A ≃ₐ[k] A' := by
  let eL : A ≃ₗ[L] A' := b.equiv b' (Equiv.refl _)
  have hproduct (sigma tau : Gal(L/k)) (a c : L) :
      (a • b sigma) * (c • b tau) =
        (a * sigma c * (phi (sigma, tau) : L)) • b (sigma * tau) := by
    rw [← hi, ← hi, ← hi]
    calc
      (i a * b sigma) * (i c * b tau) =
          (i a * (b sigma * i c)) * b tau := by simp only [mul_assoc]
      _ = (i a * (i (sigma c) * b sigma)) * b tau := by rw [hb_scalar]
      _ = (i a * i (sigma c)) * (b sigma * b tau) := by simp only [mul_assoc]
      _ = (i a * i (sigma c)) *
          (i (phi (sigma, tau) : L) * b (sigma * tau)) := by rw [hb_mul]
      _ = i (a * sigma c * (phi (sigma, tau) : L)) * b (sigma * tau) := by
        simp only [map_mul, mul_assoc]
  have hproduct' (sigma tau : Gal(L/k)) (a c : L) :
      (a • b' sigma) * (c • b' tau) =
        (a * sigma c * (phi (sigma, tau) : L)) • b' (sigma * tau) := by
    rw [← hi', ← hi', ← hi']
    calc
      (i' a * b' sigma) * (i' c * b' tau) =
          (i' a * (b' sigma * i' c)) * b' tau := by simp only [mul_assoc]
      _ = (i' a * (i' (sigma c) * b' sigma)) * b' tau := by rw [hb'_scalar]
      _ = (i' a * i' (sigma c)) * (b' sigma * b' tau) := by simp only [mul_assoc]
      _ = (i' a * i' (sigma c)) *
          (i' (phi (sigma, tau) : L) * b' (sigma * tau)) := by rw [hb'_mul]
      _ = i' (a * sigma c * (phi (sigma, tau) : L)) * b' (sigma * tau) := by
        simp only [map_mul, mul_assoc]
  have hsingle (sigma tau : Gal(L/k)) (a c : L) :
      eL ((a • b sigma) * (c • b tau)) =
        eL (a • b sigma) * eL (c • b tau) := by
    rw [hproduct]
    simp only [eL.map_smul]
    simp only [eL, Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [hproduct']
  have hmul_repr (f g : Gal(L/k) →₀ L) :
      eL (b.repr.symm f * b.repr.symm g) =
        eL (b.repr.symm f) * eL (b.repr.symm g) := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ hf₁ hf₂ => simp only [map_add, add_mul, hf₁, hf₂]
    | single sigma a =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ hg₁ hg₂ => simp only [map_add, mul_add, hg₁, hg₂]
      | single tau c =>
        simpa only [Module.Basis.repr_symm_single] using hsingle sigma tau a c
  have hmul (x y : A) : eL (x * y) = eL x * eL y := by
    rw [← b.repr.symm_apply_apply x, ← b.repr.symm_apply_apply y]
    exact hmul_repr (b.repr x) (b.repr y)
  have hone : eL 1 = 1 := by
    rw [← hb_one, Module.Basis.equiv_apply, Equiv.refl_apply, hb'_one]
  exact AlgEquiv.ofLinearEquiv (eL.restrictScalars k) hone hmul

end

end Towers.CField.CProduca

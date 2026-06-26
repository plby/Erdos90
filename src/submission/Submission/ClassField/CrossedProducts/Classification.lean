import Submission.ClassField.CrossedProducts.CrossedProductGalois
import Submission.ClassField.CrossedProducts.UniquenessFactorSet


/-!
# Chapter IV, Section 3, Theorem 3.11: crossed-product realization

Every central simple algebra of the required square dimension containing the
finite Galois extension `L/k` is isomorphic to the crossed product attached to
its normalized factor set.
-/

namespace Submission.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

variable (k L A : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  [Ring A] [Nontrivial A] [Algebra k A]
  [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]

/-- The normalized cocycle determined by the chosen Skolem--Noether
representatives in `A`. -/
def galoisNormalizedCocycle (i : L →ₐ[k] A)
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    NMCocycl₂ (G := Gal(L/k)) (M := Lˣ) where
  toFun := galoisFactor k L A i hdim
  isMulCocycle₂ := galois_factor_cocycle₂ k L A i hdim
  map_one_fst := galois_factor_left k L A i hdim
  map_one_snd := galois_factor_right k L A i hdim

/-- The crossed product of the factor set attached to `A` recovers `A` as a
`k`-algebra.  This is the constructive inverse in Theorem IV.3.11. -/
def algCrossedEmbedding
    (i : L →ₐ[k] A)
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    A ≃ₐ[k] CProduc (galoisNormalizedCocycle k L A i hdim) := by
  let c := galoisNormalizedCocycle k L A i hdim
  letI : Module L A := i.toRingHom.toModule
  letI : IsScalarTower k L A := ⟨fun r s x ↦ by
    change i (r • s) * x = r • (i s * x)
    rw [map_smul]
    exact Algebra.smul_mul_assoc r (i s) x⟩
  letI : IsScalarTower k L (CProduc c) := ⟨fun r a x ↦ by
    change (r • a) • x = algebraMap k L r • (a • x)
    rw [Algebra.smul_def]
    exact mul_smul _ _ _⟩
  let b := galoisConjugatorBasis k L A i hdim
  let b' := CProduc.basis c
  let eL : A ≃ₗ[L] CProduc c := b.equiv b' (Equiv.refl _)
  have hproduct (sigma tau : Gal(L/k)) (a d : L) :
      (a • b sigma) * (d • b tau) =
        (a * sigma d * (galoisFactor k L A i hdim (sigma, tau) : L)) •
          b (sigma * tau) := by
    simp only [b, galois_conjugator_basis]
    change (i a * (galoisConjugator k L A i sigma : A)) *
        (i d * (galoisConjugator k L A i tau : A)) =
      i (a * sigma d * (galoisFactor k L A i hdim (sigma, tau) : L)) *
        (galoisConjugator k L A i (sigma * tau) : A)
    have h := congrArg Units.val
      (galoisConjugator_mul k L A i hdim sigma tau)
    have hmul :
        (galoisConjugator k L A i sigma : A) *
            (galoisConjugator k L A i tau : A) =
          i (galoisFactor k L A i hdim (sigma, tau) : L) *
            (galoisConjugator k L A i (sigma * tau) : A) := by
      simpa [scalarUnits] using h
    change (galoisConjugator k L A i sigma : A) *
        (galoisConjugator k L A i tau : A) =
      i (galoisFactor k L A i hdim (sigma, tau) : L) *
        (galoisConjugator k L A i (sigma * tau) : A) at h
    calc
      (i a * (galoisConjugator k L A i sigma : A)) *
          (i d * (galoisConjugator k L A i tau : A)) =
          (i a * ((galoisConjugator k L A i sigma : A) * i d)) *
            (galoisConjugator k L A i tau : A) := by simp only [mul_assoc]
      _ = (i a * (i (sigma d) * (galoisConjugator k L A i sigma : A))) *
            (galoisConjugator k L A i tau : A) := by
              rw [conjugator_mul_scalar]
      _ = (i a * i (sigma d)) *
            ((galoisConjugator k L A i sigma : A) *
              (galoisConjugator k L A i tau : A)) := by simp only [mul_assoc]
      _ = (i a * i (sigma d)) *
            (i (galoisFactor k L A i hdim (sigma, tau) : L) *
              (galoisConjugator k L A i (sigma * tau) : A)) := by
                rw [hmul]
      _ = i (a * sigma d * (galoisFactor k L A i hdim (sigma, tau) : L)) *
            (galoisConjugator k L A i (sigma * tau) : A) := by
              simp only [map_mul, mul_assoc]
  have hproduct' (sigma tau : Gal(L/k)) (a d : L) :
      (a • b' sigma) * (d • b' tau) =
        (a * sigma d * (galoisFactor k L A i hdim (sigma, tau) : L)) •
          b' (sigma * tau) := by
    simp only [b', CProduc.basis_apply, CProduc.smul_single,
      CProduc.single_mul_single, mul_one]
    rfl
  have hsingle (sigma tau : Gal(L/k)) (a d : L) :
      eL ((a • b sigma) * (d • b tau)) =
        eL (a • b sigma) * eL (d • b tau) := by
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
      | single tau d =>
        simpa only [Module.Basis.repr_symm_single] using hsingle sigma tau a d
  have hmul (x y : A) : eL (x * y) = eL x * eL y := by
    rw [← b.repr.symm_apply_apply x, ← b.repr.symm_apply_apply y]
    exact hmul_repr (b.repr x) (b.repr y)
  have hone : eL 1 = 1 := by
    have hb_one : b 1 = 1 := by
      simp [b]
    rw [← hb_one, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [b', CProduc.basis_apply]
  exact AlgEquiv.ofLinearEquiv (eL.restrictScalars k) hone hmul

end

end Submission.CField.CProduca

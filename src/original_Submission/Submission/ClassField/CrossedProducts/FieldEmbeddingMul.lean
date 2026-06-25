import Mathlib.Algebra.Central.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Submission.ClassField.BrauerGroups.BasisSupport
import Submission.ClassField.CrossedProducts.CrossedProductGalois


/-!
# Chapter IV, Section 3, Lemma 3.13

The crossed-product algebra attached to a normalized cocycle over a finite
Galois extension is central simple.
-/

namespace Submission.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

open BGroups

namespace CProduc

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Left multiplication by the embedded coefficient field is the transported
`L`-module structure. -/
theorem fieldEmbedding_mul (a : L) (x : CProduc c) :
    fieldEmbedding k L c a * x = a • x := by
  change coefficientRingHom c a * x = a • x
  exact coefficient_mul c a x

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Coefficients after right multiplication by an element of the embedded
coefficient field. -/
theorem coeff_field_embedding (x : CProduc c) (a : L)
    (sigma : Gal(L/k)) :
    coeff c (x * fieldEmbedding k L c a) sigma = coeff c x sigma * sigma a := by
  classical
  induction x using induction_on c with
  | zero => simp
  | hsingle tau b =>
      by_cases h : tau = sigma
      · subst tau
        simp [fieldEmbedding, coeff_single]
      · simp [fieldEmbedding, coeff_single, h]
  | hadd x y hx hy =>
      rw [add_mul, coeff_add, coeff_add, hx, hy, add_mul]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The centralizer of the embedded copy of `L` consists of that copy itself. -/
theorem field_embedding_commutes
    (x : CProduc c)
    (hx : ∀ a : L,
      x * fieldEmbedding k L c a = fieldEmbedding k L c a * x) :
    x = fieldEmbedding k L c (coeff c x 1) := by
  classical
  apply ext_coeff c
  intro sigma
  by_cases hsigma : sigma = 1
  · subst sigma
    simp [fieldEmbedding, coeff_single]
  · have hex : ∃ a : L, sigma a ≠ a := by
      by_contra h
      push Not at h
      apply hsigma
      ext a
      simpa using h a
    obtain ⟨a, ha⟩ := hex
    have hcoeff := congrArg (fun y : CProduc c ↦ coeff c y sigma) (hx a)
    change coeff c (x * fieldEmbedding k L c a) sigma =
      coeff c (fieldEmbedding k L c a * x) sigma at hcoeff
    rw [coeff_field_embedding, fieldEmbedding_mul, coeff_smul] at hcoeff
    have hzero : coeff c x sigma = 0 := by
      by_contra hne
      apply ha
      apply mul_left_cancel₀ hne
      calc
        coeff c x sigma * sigma a = a * coeff c x sigma := hcoeff
        _ = coeff c x sigma * a := mul_comm _ _
    rw [hzero]
    have hone : (1 : Gal(L/k)) ≠ sigma := Ne.symm hsigma
    simp [fieldEmbedding, coeff_single, hone]

/-- The centre of a Galois crossed product consists of base-field scalars. -/
theorem mem_center_iff (x : CProduc c) :
    x ∈ Subalgebra.center k (CProduc c) ↔
      ∃ r : k, x = algebraMap k (CProduc c) r := by
  classical
  constructor
  · intro hx
    have hcentral : IsMulCentral x := hx
    have hxL : x = fieldEmbedding k L c (coeff c x 1) :=
      field_embedding_commutes k L c x fun a ↦ (hcentral.comm _).eq
    have hfixed : ∀ sigma : Gal(L/k), sigma (coeff c x 1) = coeff c x 1 := by
      intro sigma
      have hcomm := (hcentral.comm (basis c sigma)).eq
      rw [hxL, basis_mul_include, fieldEmbedding_mul, fieldEmbedding_mul] at hcomm
      have hcoeff := congrArg (fun y : CProduc c ↦ coeff c y sigma) hcomm
      change coeff c ((coeff c x 1) • basis c sigma) sigma =
        coeff c ((sigma (coeff c x 1)) • basis c sigma) sigma at hcoeff
      rw [coeff_smul, coeff_smul, basis_apply, coeff_single] at hcoeff
      simpa using hcoeff.symm
    obtain ⟨r, hr⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed (F := k) (E := L)
        (coeff c x 1)).2 hfixed
    refine ⟨r, ?_⟩
    rw [hxL, ← hr]
    rfl
  · rintro ⟨r, rfl⟩
    exact Subalgebra.algebraMap_mem _ r

instance : Algebra.IsCentral k (CProduc c) where
  out x hx := by
    rw [Algebra.mem_bot]
    obtain ⟨r, hr⟩ := (mem_center_iff k L c x).1 hx
    exact ⟨r, hr.symm⟩

/-- A two-sided ideal of a crossed product, regarded as an `L`-subspace. -/
def twoSidedSubmodule (I : TwoSidedIdeal (CProduc c)) :
    Submodule L (CProduc c) where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' a x hx := by
    rw [← fieldEmbedding_mul k L c]
    exact I.mul_mem_left _ _ hx

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem basis_repr_coeff (x : CProduc c) (sigma : Gal(L/k)) :
    (basis c).repr x sigma = coeff c x sigma := by
  rfl

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem coeff_neg (x : CProduc c) (sigma : Gal(L/k)) :
    coeff c (-x) sigma = -coeff c x sigma := by
  rfl

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The coefficient identity used in Milne's support-reduction argument. -/
theorem coeff_sub_embedding (x : CProduc c) (a : L)
    (tau sigma : Gal(L/k)) :
    coeff c ((tau a) • x - x * fieldEmbedding k L c a) sigma =
      coeff c x sigma * (tau a - sigma a) := by
  rw [sub_eq_add_neg, coeff_add, coeff_neg, coeff_smul,
    coeff_field_embedding]
  ring

omit [FiniteDimensional k L] [IsGalois k L] in
/-- A primordial element of a two-sided ideal has support consisting of its
normalized coordinate alone. -/
theorem primordial_eq_basis (I : TwoSidedIdeal (CProduc c))
    {x : CProduc c}
    (hx : IsPrimordial (basis c) (twoSidedSubmodule k L c I) x) :
    ∃ sigma : Gal(L/k), x = basis c sigma := by
  classical
  obtain ⟨sigma₀, hsigma₀⟩ := hx.2
  refine ⟨sigma₀, ?_⟩
  apply (basis c).repr.injective
  ext sigma
  by_cases hs : sigma = sigma₀
  · subst sigma
    change coeff c x sigma₀ = coeff c (basis c sigma₀) sigma₀
    rw [basis_apply, coeff_single]
    simpa [basis_repr_coeff] using hsigma₀
  · have hcoeff : (basis c).repr x sigma = 0 := by
      by_contra hcoeff
      have hsep : ∃ a : L, sigma a ≠ sigma₀ a := by
        by_contra h
        push Not at h
        apply hs
        ext a
        exact h a
      obtain ⟨a, ha⟩ := hsep
      let z : CProduc c := (sigma a) • x - x * fieldEmbedding k L c a
      have hzI : z ∈ twoSidedSubmodule k L c I := by
        apply Submodule.sub_mem
        · exact Submodule.smul_mem _ _ hx.1.1
        · exact I.mul_mem_right _ _ hx.1.1
      have hzcoeff (tau : Gal(L/k)) :
          (basis c).repr z tau =
            (basis c).repr x tau * (sigma a - tau a) := by
        exact coeff_sub_embedding k L c x a sigma tau
      have hzsupp : basisSupport (basis c) z ⊆ basisSupport (basis c) x := by
        intro tau htau
        by_contra htaux
        have hxtau : (basis c).repr x tau = 0 := by
          simpa [basisSupport, Finsupp.mem_support_iff] using htaux
        have hztau : (basis c).repr z tau ≠ 0 := by
          simpa [basisSupport, Finsupp.mem_support_iff] using htau
        exact hztau (by rw [hzcoeff, hxtau, zero_mul])
      have hz0 : z ≠ 0 := by
        intro hz
        have hzsigma₀ := congrArg (fun y ↦ (basis c).repr y sigma₀) hz
        change (basis c).repr z sigma₀ = 0 at hzsigma₀
        rw [hzcoeff] at hzsigma₀
        exact ha (by
          apply sub_eq_zero.mp
          apply mul_left_cancel₀ (show (1 : L) ≠ 0 by simp)
          simpa [hsigma₀] using hzsigma₀)
      have hmin := hx.1.2.2 z hzI hz0 hzsupp
      have hsigma_mem : sigma ∈ basisSupport (basis c) x := by
        simpa [basisSupport, Finsupp.mem_support_iff] using hcoeff
      have hsigma_not_mem : sigma ∉ basisSupport (basis c) z := by
        simp [basisSupport, hzcoeff]
      exact hsigma_not_mem (hmin hsigma_mem)
    change coeff c x sigma = coeff c (basis c sigma₀) sigma
    rw [basis_apply, coeff_single]
    have hxcoeff : coeff c x sigma = 0 := by
      simpa [basis_repr_coeff] using hcoeff
    rw [hxcoeff]
    simp [Ne.symm hs]

/-- Milne, Lemma IV.3.13 (simplicity half): a Galois crossed product is a
simple ring. -/
instance : IsSimpleRing (CProduc c) := by
  letI : Nontrivial (CProduc c) :=
    (fieldEmbedding_injective k L c).nontrivial
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    have hsub : twoSidedSubmodule k L c I ≠ ⊥ := by
      intro h
      apply hI
      ext x
      constructor
      · intro hxI
        have hx : x ∈ twoSidedSubmodule k L c I := hxI
        rw [h] at hx
        simpa using hx
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        simp [hx0]
    have hprim : ∃ x : CProduc c,
        IsPrimordial (basis c) (twoSidedSubmodule k L c I) x := by
      by_contra h
      push Not at h
      have hempty : {x : CProduc c |
          IsPrimordial (basis c) (twoSidedSubmodule k L c I) x} = ∅ := by
        ext x
        simp [h x]
      apply hsub
      rw [← span_primordial_eq (basis c) (twoSidedSubmodule k L c I), hempty]
      simp
    obtain ⟨x, hx⟩ := hprim
    obtain ⟨sigma, rfl⟩ := primordial_eq_basis k L c I hx
    have hbasisI : basis c sigma ∈ I := hx.1.1
    have hprodI : basis c sigma * basis c sigma⁻¹ ∈ I :=
      I.mul_mem_right _ _ hbasisI
    have hscalarI : fieldEmbedding k L c (c (sigma, sigma⁻¹) : L) ∈ I := by
      simpa using hprodI
    have honeI : (1 : CProduc c) ∈ I := by
      have hinvI := I.mul_mem_left
        (fieldEmbedding k L c ((c (sigma, sigma⁻¹) : L)⁻¹)) _ hscalarI
      simpa [← map_mul] using hinvI
    exact TwoSidedIdeal.eq_top I honeI

end CProduc

end

end Submission.CField.CProduca

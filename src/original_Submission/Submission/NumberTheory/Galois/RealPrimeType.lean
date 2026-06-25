import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Milne, Chapter 8, Remark 8.24: the cycle type at a real prime

Complex conjugation fixes the real roots of a rational polynomial and pairs
its nonreal roots.  Consequently, if there are `j` conjugate pairs of
nonreal roots, its action on all complex roots is a product of `j` disjoint
transpositions.
-/

namespace Submission.NumberTheory.Milne

open scoped Polynomial

noncomputable section

/-- Complex conjugation as an element of the polynomial Galois group of a
real-coefficient polynomial, acting on its complex roots. -/
def realConjugationPerm (p : ℝ[X]) :
    Equiv.Perm (p.rootSet ℂ) := by
  letI : Fact ((p.map (algebraMap ℝ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  exact Polynomial.Gal.galActionHom p ℂ
    (Polynomial.Gal.restrict p ℂ Complex.conjAe)

/-- Complex conjugation on the roots of a real polynomial is an involution. -/
theorem real_perm_sq (p : ℝ[X]) :
    realConjugationPerm p ^ 2 = 1 := by
  letI : Fact ((p.map (algebraMap ℝ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  simp only [realConjugationPerm, ← map_pow]
  have hconj : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) ^ 2 = 1 :=
    AlgEquiv.ext Complex.conj_conj
  calc
    (Polynomial.Gal.galActionHom p ℂ)
        ((Polynomial.Gal.restrict p ℂ) (Complex.conjAe ^ 2)) =
        (Polynomial.Gal.galActionHom p ℂ)
          ((Polynomial.Gal.restrict p ℂ) 1) :=
      congrArg _ (congrArg _ hconj)
    _ = 1 := by simp

/-- The complex roots of a real polynomial split into its real roots and the
support of complex conjugation. -/
private theorem complex_roots_support
    (p : ℝ[X]) :
    (p.rootSet ℂ).toFinset.card =
      (p.rootSet ℝ).toFinset.card +
        (realConjugationPerm p).support.card := by
  classical
  letI : Fact ((p.map (algebraMap ℝ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  by_cases hp : p = 0
  · haveI : IsEmpty (p.rootSet ℂ) := by rw [hp, Polynomial.rootSet_zero]; infer_instance
    simp_rw [(realConjugationPerm p).support.eq_empty_of_isEmpty,
      hp, Polynomial.rootSet_zero, Set.toFinset_empty, Finset.card_empty]
  let inclusion : ℝ →ₐ[ℝ] ℂ := IsScalarTower.toAlgHom ℝ ℝ ℂ
  have hinj : Function.Injective inclusion := (algebraMap ℝ ℂ).injective
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective,
    ← Finset.card_image_of_injective _ hinj]
  let a : Finset ℂ := (p.rootSet ℂ).toFinset
  let b : Finset ℂ := (p.rootSet ℝ).toFinset.image inclusion
  let c : Finset ℂ := (realConjugationPerm p).support.image
    ((↑) : p.rootSet ℂ → ℂ)
  change a.card = b.card + c.card
  have ha : ∀ z : ℂ, z ∈ a ↔ Polynomial.aeval z p = 0 := by
    intro z
    simp only [a, Set.mem_toFinset, Polynomial.mem_rootSet_of_ne hp]
  have hb : ∀ z : ℂ, z ∈ b ↔ Polynomial.aeval z p = 0 ∧ z.im = 0 := by
    intro z
    simp_rw [b, Finset.mem_image, Set.mem_toFinset,
      Polynomial.mem_rootSet_of_ne hp]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [Polynomial.aeval_algHom_apply, hw, map_zero], rfl⟩
    · rintro ⟨hz, hzIm⟩
      have hzReal : inclusion z.re = z := by
        apply Complex.ext
        · rfl
        · simpa using hzIm.symm
      exact ⟨z.re, hinj (by
        rwa [← Polynomial.aeval_algHom_apply, hzReal, map_zero]), hzReal⟩
  have hfix (w : p.rootSet ℂ) :
      realConjugationPerm p w = w ↔ w.val.im = 0 := by
    rw [Subtype.ext_iff]
    change ((Polynomial.Gal.galActionHom p ℂ)
      ((Polynomial.Gal.restrict p ℂ) Complex.conjAe) w).1 = w.1 ↔ _
    rw [Polynomial.Gal.galActionHom_restrict]
    exact Complex.conj_eq_iff_im
  have hc : ∀ z : ℂ, z ∈ c ↔ Polynomial.aeval z p = 0 ∧ z.im ≠ 0 := by
    intro z
    simp only [c, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(Polynomial.mem_rootSet.mp w.2).2,
        mt (hfix w).mpr (Equiv.Perm.mem_support.mp hw)⟩
    · rintro ⟨hz, hzIm⟩
      let w : p.rootSet ℂ :=
        ⟨z, Polynomial.mem_rootSet.mpr ⟨hp, hz⟩⟩
      exact ⟨w, Equiv.Perm.mem_support.mpr (mt (hfix w).mp hzIm), rfl⟩
  rw [← Finset.card_union_of_disjoint]
  · apply congrArg Finset.card
    ext z
    simp only [Finset.mem_union, ha, hb, hc]
    tauto
  · rw [Finset.disjoint_left]
    intro z
    rw [hb, hc]
    tauto

/-- Remark 8.24 for a real-coefficient polynomial: if it has `2 * j` more
complex roots than real roots, complex conjugation has cycle type `2^j`. -/
theorem perm_cycle_type (p : ℝ[X]) (j : ℕ)
    (hroots :
      (p.rootSet ℂ).toFinset.card =
        (p.rootSet ℝ).toFinset.card + 2 * j) :
    (realConjugationPerm p).cycleType =
      Multiset.replicate j 2 := by
  classical
  let σ := realConjugationPerm p
  have hσ : σ ^ 2 = 1 := real_perm_sq p
  have htype : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσ
  have hsupport : σ.support.card = 2 * j := by
    have hcount := complex_roots_support p
    change (p.rootSet ℂ).toFinset.card =
      (p.rootSet ℝ).toFinset.card + σ.support.card at hcount
    omega
  have hcard : σ.cycleType.card = j := by
    have hmul : σ.cycleType.card * 2 = 2 * j := by
      calc
        σ.cycleType.card * 2 =
            (Multiset.replicate σ.cycleType.card 2).sum := by simp
        _ = σ.cycleType.sum := congrArg Multiset.sum htype.symm
        _ = σ.support.card := σ.sum_cycleType
        _ = 2 * j := hsupport
    omega
  simpa [σ, hcard] using htype

/-- Remark 8.24 over `ℝ`: if exactly `j` irreducible factors are quadratic
and all remaining factors are linear, complex conjugation is a product of
`j` disjoint transpositions on the complex roots. -/
theorem cycle_type_factorization
    {ι : Type*} [Fintype ι]
    (p : ℝ[X]) (g : ι → ℝ[X]) (j : ℕ)
    (hfactor : p = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hquadratic :
      (Finset.univ.filter fun i => (g i).natDegree = 2).card = j)
    (hseparable : p.Separable) :
    (realConjugationPerm p).cycleType =
      Multiset.replicate j 2 := by
  classical
  apply perm_cycle_type p j
  have hprodne : (∏ i, g i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hirr i).ne_zero
  have hcomplex : (p.rootSet ℂ).toFinset.card = p.natDegree := by
    simpa only [Set.toFinset_card] using
      (Polynomial.card_rootSet_eq_natDegree hseparable (IsAlgClosed.splits _))
  have hreal : (p.rootSet ℝ).toFinset.card = ∑ i, (g i).roots.card := by
    rw [Set.toFinset_card]
    simp_rw [Polynomial.rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Polynomial.aroots_def]
    rw [show p.map (algebraMap ℝ ℝ) = p by simp]
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hseparable)]
    rw [hfactor, Polynomial.roots_prod g Finset.univ hprodne,
      Multiset.card_bind]
    simp
  have hdegree : p.natDegree = ∑ i, (g i).natDegree := by
    rw [hfactor]
    exact Polynomial.natDegree_prod Finset.univ g fun i _ => (hirr i).ne_zero
  have hfactorCard : ∀ i,
      (g i).natDegree = (g i).roots.card +
        (if (g i).natDegree = 2 then 2 else 0) := by
    intro i
    have hpos := (hirr i).natDegree_pos
    have hle := (hirr i).natDegree_le_two
    have hcases : (g i).natDegree = 1 ∨ (g i).natDegree = 2 := by omega
    rcases hcases with hdeg | hdeg
    · have hdegreeOne : (g i).degree = 1 :=
        (Polynomial.degree_eq_iff_natDegree_eq (hirr i).ne_zero).2 hdeg
      rw [Polynomial.roots_degree_eq_one hdegreeOne]
      simp [hdeg]
    · rw [Polynomial.roots_eq_zero_of_irreducible_of_natDegree_ne_one
        (hirr i) (by omega)]
      simp [hdeg]
  have hextra :
      (∑ i, if (g i).natDegree = 2 then 2 else 0) = 2 * j := by
    have hbool :
        (∑ i, if (g i).natDegree = 2 then 1 else 0) = j := by
      simpa only [Finset.sum_boole, Nat.cast_id] using hquadratic
    calc
      (∑ i, if (g i).natDegree = 2 then 2 else 0) =
          2 * ∑ i, if (g i).natDegree = 2 then 1 else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> simp
      _ = 2 * j := by rw [hbool]
  rw [hcomplex, hreal, hdegree]
  calc
    (∑ i, (g i).natDegree) =
        ∑ i, ((g i).roots.card +
          if (g i).natDegree = 2 then 2 else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hfactorCard i
    _ = (∑ i, (g i).roots.card) + 2 * j := by
      rw [Finset.sum_add_distrib, hextra]

/-- Milne, Remark 8.24 at an arbitrary real embedding of the coefficient
field.  Mapping the polynomial through that embedding reduces the assertion
to the real-coefficient theorem above. -/
theorem real_cycle_type
    {K ι : Type*} [Field K] [Fintype ι]
    (ψ : K →+* ℝ) (p : K[X]) (g : ι → ℝ[X]) (j : ℕ)
    (hfactor : p.map ψ = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hquadratic :
      (Finset.univ.filter fun i => (g i).natDegree = 2).card = j)
    (hseparable : p.Separable) :
    (realConjugationPerm (p.map ψ)).cycleType =
      Multiset.replicate j 2 :=
  cycle_type_factorization
    (p.map ψ) g j hfactor hirr hquadratic hseparable.map

/-- Complex conjugation, regarded as the permutation of the complex roots of
a rational polynomial supplied by its polynomial Galois group. -/
def complexConjugationPerm (p : ℚ[X]) : Equiv.Perm (p.rootSet ℂ) := by
  letI : Fact ((p.map (algebraMap ℚ ℂ)).Splits) := Polynomial.Gal.splits_ℚ_ℂ
  exact Polynomial.Gal.galActionHom p ℂ
    (Polynomial.Gal.restrict p ℂ (Complex.conjAe.restrictScalars ℚ))

/-- Complex conjugation acts as an involution on the roots. -/
theorem complex_perm_sq (p : ℚ[X]) :
    complexConjugationPerm p ^ 2 = 1 := by
  letI : Fact ((p.map (algebraMap ℚ ℂ)).Splits) := Polynomial.Gal.splits_ℚ_ℂ
  simp only [complexConjugationPerm, ← map_pow]
  rw [show (Complex.conjAe.restrictScalars ℚ) ^ 2 = 1 from
      AlgEquiv.ext Complex.conj_conj]
  simp

/-- Milne, Remark 8.24. If the complex root set has exactly `2 * j` more
elements than the real root set, complex conjugation has cycle type consisting
of `j` disjoint cycles of length two. -/
theorem complex_perm_type (p : ℚ[X]) (j : ℕ)
    (hroots :
      (p.rootSet ℂ).toFinset.card =
        (p.rootSet ℝ).toFinset.card + 2 * j) :
    (complexConjugationPerm p).cycleType = Multiset.replicate j 2 := by
  classical
  let σ := complexConjugationPerm p
  have hσ : σ ^ 2 = 1 := complex_perm_sq p
  have htype : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσ
  have hsupport : σ.support.card = 2 * j := by
    have hcount :=
      Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv p
    change
      (p.rootSet ℂ).toFinset.card =
        (p.rootSet ℝ).toFinset.card + σ.support.card at hcount
    omega
  have hcard : σ.cycleType.card = j := by
    have hmul : σ.cycleType.card * 2 = 2 * j := by
      calc
        σ.cycleType.card * 2 = (Multiset.replicate σ.cycleType.card 2).sum := by
          simp
        _ = σ.cycleType.sum := congrArg Multiset.sum htype.symm
        _ = σ.support.card := σ.sum_cycleType
        _ = 2 * j := hsupport
    omega
  simpa [σ, hcard] using htype

/-- Milne, Remark 8.24, with its stated factorization hypothesis.  If a
separable rational polynomial factors over `ℝ` into irreducibles and exactly
`j` of those factors are quadratic, complex conjugation on its complex roots
has cycle type consisting of `j` disjoint transpositions. -/
theorem complex_cycle_type
    {iota : Type*} [Fintype iota]
    (p : ℚ[X]) (g : iota → ℝ[X]) (j : ℕ)
    (hfactor : p.map (algebraMap ℚ ℝ) = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hquadratic :
      (Finset.univ.filter fun i => (g i).natDegree = 2).card = j)
    (hseparable : p.Separable) :
    (complexConjugationPerm p).cycleType = Multiset.replicate j 2 := by
  classical
  apply complex_perm_type p j
  have hprodne : (∏ i, g i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hirr i).ne_zero
  have hcomplex : (p.rootSet ℂ).toFinset.card = p.natDegree := by
    simpa only [Set.toFinset_card] using
      (Polynomial.card_rootSet_eq_natDegree hseparable (IsAlgClosed.splits _))
  have hreal :
      (p.rootSet ℝ).toFinset.card = ∑ i, (g i).roots.card := by
    rw [Set.toFinset_card]
    simp_rw [Polynomial.rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
    rw [Polynomial.aroots_def]
    rw [Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots hseparable.map)]
    rw [hfactor, Polynomial.roots_prod g Finset.univ hprodne,
      Multiset.card_bind]
    simp
  have hdegree : p.natDegree = ∑ i, (g i).natDegree := by
    rw [← Polynomial.natDegree_map (algebraMap ℚ ℝ), hfactor]
    exact Polynomial.natDegree_prod Finset.univ g fun i _ => (hirr i).ne_zero
  have hfactorCard : ∀ i,
      (g i).natDegree = (g i).roots.card +
        (if (g i).natDegree = 2 then 2 else 0) := by
    intro i
    have hpos := (hirr i).natDegree_pos
    have hle := (hirr i).natDegree_le_two
    have hcases : (g i).natDegree = 1 ∨ (g i).natDegree = 2 := by omega
    rcases hcases with hdeg | hdeg
    · have hdegreeOne : (g i).degree = 1 :=
        (Polynomial.degree_eq_iff_natDegree_eq (hirr i).ne_zero).2 hdeg
      rw [Polynomial.roots_degree_eq_one hdegreeOne]
      simp [hdeg]
    · rw [Polynomial.roots_eq_zero_of_irreducible_of_natDegree_ne_one
        (hirr i) (by omega)]
      simp [hdeg]
  have hextra :
      (∑ i, if (g i).natDegree = 2 then 2 else 0) = 2 * j := by
    have hbool :
        (∑ i, if (g i).natDegree = 2 then 1 else 0) = j := by
      simpa only [Finset.sum_boole, Nat.cast_id] using hquadratic
    calc
      (∑ i, if (g i).natDegree = 2 then 2 else 0) =
          2 * ∑ i, if (g i).natDegree = 2 then 1 else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> simp
      _ = 2 * j := by rw [hbool]
  rw [hcomplex, hreal, hdegree]
  calc
    (∑ i, (g i).natDegree) =
        ∑ i, ((g i).roots.card +
          if (g i).natDegree = 2 then 2 else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hfactorCard i
    _ = (∑ i, (g i).roots.card) + 2 * j := by
      rw [Finset.sum_add_distrib, hextra]

end

end Submission.NumberTheory.Milne

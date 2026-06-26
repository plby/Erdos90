import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.Smooth.AdicCompletion
import Towers.NumberTheory.Locals.LocalPolynomialCoprime
import Towers.NumberTheory.Locals.HenselFactorUniqueness


/-!
# Hensel factorization

This file proves the degree-one-factor case of Milne's Theorem 7.33 over a
Henselian local ring, and its general coprime-factor form over a local ring
complete for its maximal-ideal-adic topology.
-/

namespace Towers.NumberTheory.Milne

open IsLocalRing Polynomial

noncomputable section

variable {A : Type*} [CommRing A] [HenselianLocalRing A]

/-- The linear-factor case of Milne's Theorem 7.33.  If the reduction of a
monic polynomial is `(X - a₀) * h₀` and the two factors are coprime, then
this factorization lifts to monic, strictly coprime factors over the Henselian
local ring. -/
theorem hensel_lift_factorization
    (f : A[X]) (hf : f.Monic) (a₀ : ResidueField A) (h₀ : (ResidueField A)[X])
    (hfactor₀ : f.map (residue A) = (X - C a₀) * h₀)
    (hcoprime₀ : IsCoprime (X - C a₀) h₀) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.map (residue A) = X - C a₀ ∧
          h.map (residue A) = h₀ ∧ IsCoprime g h := by
  have hh₀eval : h₀.eval a₀ ≠ 0 := by
    rcases aeval_ne_zero_of_isCoprime hcoprime₀ a₀ with hlinear | hrest
    · simp at hlinear
    · simpa [aeval_def] using hrest
  have hderiv : aeval a₀ (derivative f) ≠ 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map, ← derivative_map]
    rw [hfactor₀, derivative_mul]
    simpa using hh₀eval
  have hlift :=
    ((HenselianLocalRing.TFAE A).out 0 1).mp
      (inferInstance : HenselianLocalRing A)
  obtain ⟨a, haRoot, haMap⟩ := hlift f hf a₀ (by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map, hfactor₀]
    simp) hderiv
  let g : A[X] := X - C a
  let h : A[X] := f /ₘ g
  have hg : g.Monic := by
    simpa [g] using monic_X_sub_C a
  have hmul : g * h = f := by
    simpa [g, h] using (mul_divByMonic_eq_iff_isRoot (p := f) (a := a)).2 haRoot
  have hh : h.Monic := hg.of_mul_monic_left (by rw [hmul]; exact hf)
  have hgmap : g.map (residue A) = X - C a₀ := by
    simp [g, haMap]
  have hhmap : h.map (residue A) = h₀ := by
    change (f /ₘ g).map (residue A) = h₀
    rw [map_divByMonic (residue A) hg, hgmap, hfactor₀]
    exact mul_divByMonic_cancel_left h₀ (monic_X_sub_C a₀)
  have hcoprime : IsCoprime g h := by
    apply coprime_monic_residue hg hh
    simpa [hgmap, hhmap] using hcoprime₀
  exact ⟨g, h, hg, hh, hmul.symm, hgmap, hhmap, hcoprime⟩

/-- The preceding linear-factor Hensel theorem specialized directly to a
local ring complete for its maximal-ideal-adic filtration. -/
theorem complete_hensel_factorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (f : A[X]) (hf : f.Monic) (a₀ : ResidueField A) (h₀ : (ResidueField A)[X])
    (hfactor₀ : f.map (residue A) = (X - C a₀) * h₀)
    (hcoprime₀ : IsCoprime (X - C a₀) h₀) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.map (residue A) = X - C a₀ ∧
          h.map (residue A) = h₀ ∧ IsCoprime g h := by
  letI : HenselianLocalRing A := {
    toIsLocalRing := inferInstance
    is_henselian := by
      intro p hp a ha hpa
      exact @HenselianRing.is_henselian A _ (maximalIdeal A)
        (IsAdicComplete.henselianRing A (maximalIdeal A))
        p hp a ha (hpa.map (Ideal.Quotient.mk (maximalIdeal A))) }
  exact hensel_lift_factorization f hf a₀ h₀ hfactor₀ hcoprime₀

/-- The general coprime-factor form of Hensel's factorization theorem for a
local ring complete in its maximal-ideal-adic topology.  A coprime monic
factorization over the residue field lifts to a coprime monic factorization
over the ring itself. -/
theorem adic_hensel_factorization
    {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (ResidueField A)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor₀ : f.map (residue A) = g₀ * h₀)
    (hcoprime₀ : IsCoprime g₀ h₀) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.map (residue A) = g₀ ∧ h.map (residue A) = h₀ ∧
          IsCoprime g h := by
  have hdegree : f.natDegree = g₀.natDegree + h₀.natDegree := by
    have h := congrArg Polynomial.natDegree hfactor₀
    simpa [hf.natDegree_map, hg₀.natDegree_mul hh₀] using h
  let p : MonicDegreeEq A f.natDegree := MonicDegreeEq.mk f hf rfl
  let q₁ : MonicDegreeEq (ResidueField A) g₀.natDegree :=
    MonicDegreeEq.mk g₀ hg₀ rfl
  let q₂ : MonicDegreeEq (ResidueField A) h₀.natDegree :=
    MonicDegreeEq.mk h₀ hh₀ rfl
  let U := UniversalCoprimeFactorizationRing
    g₀.natDegree h₀.natDegree hdegree p
  let q₀ : {q : MonicDegreeEq (ResidueField A) g₀.natDegree ×
      MonicDegreeEq (ResidueField A) h₀.natDegree //
      q.1.1 * q.2.1 = p.1.map (algebraMap A (ResidueField A)) ∧
        IsCoprime q.1.1 q.2.1} := by
    refine ⟨(q₁, q₂), ?_, ?_⟩
    · simpa [p, q₁, q₂, ResidueField.algebraMap_eq] using hfactor₀.symm
    · exact hcoprime₀
  let φ₀ : U →ₐ[A] ResidueField A :=
    (UniversalCoprimeFactorizationRing.homEquiv
      (ResidueField A) g₀.natDegree h₀.natDegree hdegree p).symm q₀
  obtain ⟨φ, hφ⟩ :=
    Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
      (I := maximalIdeal A) φ₀
  let q := UniversalCoprimeFactorizationRing.homEquiv
    A g₀.natDegree h₀.natDegree hdegree p φ
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, ?_, ?_, q.2.2⟩
  · simpa [p] using q.2.1.symm
  · let ρ : A →ₐ[A] ResidueField A :=
      Ideal.Quotient.mkₐ A (maximalIdeal A)
    have hcomp := UniversalCoprimeFactorizationRing.homEquiv_comp_fst
      (R := A) (S := A) (T := ResidueField A)
      (m := g₀.natDegree) (k := h₀.natDegree) (n := f.natDegree)
      (hn := hdegree) (p := p) (f := φ) (g := ρ)
    have hφρ : ρ.comp φ = φ₀ := by simpa [ρ] using hφ
    rw [hφρ] at hcomp
    have hq₀ := (UniversalCoprimeFactorizationRing.homEquiv
      (ResidueField A) g₀.natDegree h₀.natDegree hdegree p).apply_symm_apply q₀
    change (q.1.1.map ρ).1 = g₀
    rw [← hcomp]
    exact congrArg (fun z ↦ z.1.1.1) hq₀
  · let ρ : A →ₐ[A] ResidueField A :=
      Ideal.Quotient.mkₐ A (maximalIdeal A)
    have hcomp := UniversalCoprimeFactorizationRing.homEquiv_comp_snd
      (R := A) (S := A) (T := ResidueField A)
      (m := g₀.natDegree) (k := h₀.natDegree) (n := f.natDegree)
      (hn := hdegree) (p := p) (f := φ) (g := ρ)
    have hφρ : ρ.comp φ = φ₀ := by simpa [ρ] using hφ
    rw [hφρ] at hcomp
    have hq₀ := (UniversalCoprimeFactorizationRing.homEquiv
      (ResidueField A) g₀.natDegree h₀.natDegree hdegree p).apply_symm_apply q₀
    change (q.1.2.map ρ).1 = h₀
    rw [← hcomp]
    exact congrArg (fun z ↦ z.1.2.1) hq₀

/-- Milne, Theorem 7.33 in its full existence-and-uniqueness form.  A
coprime monic factorization over the residue field lifts to exactly one
monic factorization over a local ring complete in its maximal-ideal-adic
topology; the lifted factors are strictly coprime. -/
theorem adic_hensel_unique
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (f : A[X]) (hf : f.Monic)
    (g0 h0 : (ResidueField A)[X]) (hg0 : g0.Monic) (hh0 : h0.Monic)
    (hfactor0 : f.map (residue A) = g0 * h0)
    (hcoprime0 : IsCoprime g0 h0) :
    ∃! gh : A[X] × A[X],
      gh.1.Monic ∧ gh.2.Monic ∧ f = gh.1 * gh.2 ∧
        gh.1.map (residue A) = g0 ∧
          gh.2.map (residue A) = h0 ∧ IsCoprime gh.1 gh.2 := by
  obtain ⟨g, h, hg, hh, hfactor, hgmap, hhmap, hcoprime⟩ :=
    adic_hensel_factorization
      f hf g0 h0 hg0 hh0 hfactor0 hcoprime0
  refine ⟨(g, h), ⟨hg, hh, hfactor, hgmap, hhmap, hcoprime⟩, ?_⟩
  rintro ⟨g', h'⟩ ⟨hg', hh', hfactor', hgmap', hhmap', _⟩
  have heq := monic_unique_residue
    hg hh hg' hh' (hfactor.symm.trans hfactor')
    (hgmap.trans hgmap'.symm) (hhmap.trans hhmap'.symm)
    (by simpa [hgmap, hhmap] using hcoprime0)
  exact Prod.ext heq.1.symm heq.2.symm

/-- Milne, Remark 7.37, in the unit-resultant case of the quantitative
resultant bound.  If the resultant of the approximate factors is a unit, the
inequality
`‖f - g₀h₀‖ < ‖Res(g₀,h₀)‖²`
is exactly the usual Hensel condition modulo the maximal ideal.  The lifted
factors have the same degrees as the approximate factors.

The full nonunit-resultant version cited by Milne requires the stronger
quantitative Hensel theorem; this theorem records the part obtained from the
coprime-reduction Hensel theorem already available in Mathlib. -/
theorem complete_hensel_resultant
    {A : Type*} [SeminormedCommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (hnorm : ∀ x : A, x ∈ maximalIdeal A ↔ ‖x‖ < 1)
    (f g₀ h₀ : A[X]) (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hresultant : ‖resultant g₀ h₀‖ = 1)
    (hclose : (f - g₀ * h₀).supNorm < ‖resultant g₀ h₀‖ ^ 2) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree := by
  let ρ : A →+* ResidueField A := residue A
  have hcloseOne : (f - g₀ * h₀).supNorm < 1 := by
    simpa [hresultant] using hclose
  have herror : (f - g₀ * h₀).map ρ = 0 := by
    ext i
    rw [coeff_map, coeff_zero]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (hnorm _).2
    exact ((f - g₀ * h₀).le_supNorm i).trans_lt hcloseOne
  have hfactor₀ : f.map ρ = g₀.map ρ * h₀.map ρ := by
    have h := congrArg (Polynomial.map ρ) (sub_add_cancel f (g₀ * h₀))
    simp only [Polynomial.map_add, Polynomial.map_mul, herror, zero_add] at h
    exact h.symm
  have hresultantNotMem : resultant g₀ h₀ ∉ maximalIdeal A := by
    intro hmem
    have hlt := (hnorm _).1 hmem
    rw [hresultant] at hlt
    exact lt_irrefl 1 hlt
  have hresultantMapNe : ρ (resultant g₀ h₀) ≠ 0 := by
    intro hz
    apply hresultantNotMem
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hz
  have hresultantMap :
      resultant (g₀.map ρ) (h₀.map ρ) = ρ (resultant g₀ h₀) := by
    simp [hg₀.natDegree_map, hh₀.natDegree_map]
  have hcoprime₀ : IsCoprime (g₀.map ρ) (h₀.map ρ) := by
    rw [← isUnit_resultant_iff_isCoprime (hg₀.map ρ), hresultantMap]
    exact isUnit_iff_ne_zero.mpr hresultantMapNe
  obtain ⟨g, h, hg, hh, hfactor, hgmap, hhmap, -⟩ :=
    adic_hensel_factorization f hf
      (g₀.map ρ) (h₀.map ρ) (hg₀.map ρ) (hh₀.map ρ) hfactor₀ hcoprime₀
  refine ⟨g, h, hg, hh, hfactor, ?_, ?_⟩
  · rw [← hg.natDegree_map ρ, hgmap, hg₀.natDegree_map]
  · rw [← hh.natDegree_map ρ, hhmap, hh₀.natDegree_map]

section QuantitativeLinearFactor

variable {p : ℕ} [Fact p.Prime]

private lemma padic_int_sup (P : ℤ_[p][X]) (a : ℤ_[p]) :
    ‖P.eval a‖ ≤ P.supNorm := by
  by_cases hP : P = 0
  · simp [hP]
  rw [eval_eq_sum]
  have hs : P.support.Nonempty := support_nonempty.mpr hP
  obtain ⟨i, -, hi⟩ := IsNonarchimedean.finset_image_add_of_nonempty
    PadicInt.nonarchimedean (fun i : ℕ ↦ P.coeff i * a ^ i) hs
  refine hi.trans ?_
  rw [norm_mul, norm_pow]
  calc
    ‖P.coeff i‖ * ‖a‖ ^ i ≤ ‖P.coeff i‖ * 1 := by
      gcongr
      exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one a)
    _ = ‖P.coeff i‖ := mul_one _
    _ ≤ P.supNorm := P.le_supNorm i

private lemma padic_sup_derivative (P : ℤ_[p][X]) :
    P.derivative.supNorm ≤ P.supNorm := by
  obtain ⟨i, hi⟩ := P.derivative.exists_eq_supNorm
  rw [hi, coeff_derivative, norm_mul, mul_comm]
  calc
    ‖(i + 1 : ℤ_[p])‖ * ‖P.coeff (i + 1)‖ ≤
        1 * ‖P.coeff (i + 1)‖ := by
      gcongr
      exact PadicInt.norm_le_one _
    _ = ‖P.coeff (i + 1)‖ := one_mul _
    _ ≤ P.supNorm := P.le_supNorm _

/-- The nonunit-resultant part of Milne's Remark 7.37 when the first
approximate factor is linear, over the ring of `p`-adic integers.  Unlike the
coprime-reduction specialization above, the resultant may lie in the maximal
ideal.  The resultant-square estimate is exactly the strong Hensel inequality
at the approximate root. -/
theorem hensel_resultant_sq
    (f g₀ h₀ : ℤ_[p][X]) (hf : f.Monic) (hg₀ : g₀.Monic)
    (hg₀deg : g₀.natDegree = 1)
    (hfdeg : f.natDegree = g₀.natDegree + h₀.natDegree)
    (hclose : (f - g₀ * h₀).supNorm < ‖resultant g₀ h₀‖ ^ 2) :
    ∃ g h : ℤ_[p][X],
      g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree := by
  let a : ℤ_[p] := -g₀.coeff 0
  have hg₀eq : g₀ = X - C a := by
    rw [hg₀.eq_X_add_C hg₀deg]
    simp [a]
  let e : ℤ_[p][X] := f - g₀ * h₀
  have hres : resultant g₀ h₀ = h₀.eval a := by
    change g₀.resultant h₀ g₀.natDegree h₀.natDegree = h₀.eval a
    rw [hg₀deg, hg₀eq]
    exact resultant_X_sub_C_left (g := h₀) (n := h₀.natDegree) a le_rfl
  have heval : f.eval a = e.eval a := by
    simp [e, hg₀eq]
  have heval_le : ‖e.eval a‖ ≤ e.supNorm := padic_int_sup e a
  have hres_le_one : ‖resultant g₀ h₀‖ ≤ 1 := PadicInt.norm_le_one _
  have hres_pos : 0 < ‖resultant g₀ h₀‖ := by
    by_contra hnpos
    have hz : ‖resultant g₀ h₀‖ = 0 :=
      le_antisymm (not_lt.mp hnpos) (norm_nonneg _)
    have : (f - g₀ * h₀).supNorm < 0 := by simpa [hz] using hclose
    exact (not_lt_of_ge (f - g₀ * h₀).supNorm_nonneg) this
  have he_lt_res_sq : ‖e.eval a‖ < ‖resultant g₀ h₀‖ ^ 2 := by
    exact heval_le.trans_lt (by simpa [e] using hclose)
  have hederiv_lt_res : ‖e.derivative.eval a‖ < ‖resultant g₀ h₀‖ := by
    refine (padic_int_sup e.derivative a).trans_lt ?_
    refine (padic_sup_derivative e).trans_lt ?_
    exact lt_of_lt_of_le (by simpa [e] using hclose)
      (by nlinarith [norm_nonneg (resultant g₀ h₀)])
  have hfderiv : ‖f.derivative.eval a‖ = ‖resultant g₀ h₀‖ := by
    have hdecomp : f.derivative.eval a = h₀.eval a + e.derivative.eval a := by
      have hef : f = g₀ * h₀ + e := by simp [e]
      rw [hef, derivative_add, derivative_mul, eval_add, eval_add, eval_mul, eval_mul,
        hg₀eq]
      simp
    rw [hdecomp, ← hres, PadicInt.norm_add_eq_max_of_ne]
    · exact max_eq_left hederiv_lt_res.le
    · exact ne_of_gt hederiv_lt_res
  have hhensel : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2 := by
    rw [heval, hfderiv]
    exact he_lt_res_sq
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hhensel
  let g : ℤ_[p][X] := X - C z
  let h : ℤ_[p][X] := f /ₘ g
  have hg : g.Monic := monic_X_sub_C z
  have hfactor' : g * h = f := by
    simpa [g, h] using (mul_divByMonic_eq_iff_isRoot (p := f) (a := z)).2 hz
  have hh : h.Monic := hg.of_mul_monic_left (hfactor' ▸ hf)
  refine ⟨g, h, hg, hh, hfactor'.symm, ?_, ?_⟩
  · simp [g, hg₀deg]
  · have hdegree := congrArg natDegree hfactor'
    rw [hg.natDegree_mul hh, hfdeg, hg₀deg] at hdegree
    simpa [g] using hdegree

end QuantitativeLinearFactor

end

end Towers.NumberTheory.Milne

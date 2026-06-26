import Submission.ClassField.CrossedProducts.CohomologyClass
import Submission.ClassField.LocalBrauer.RealCrossedProduct

/-!
# Chapter IV, Section 4: `H²(Gal(ℂ/ℝ), ℂˣ)`

For the real quadratic extension, a normalized two-cocycle is determined by
its value on `(conj, conj)`.  The cocycle identity says that this value is a
nonzero real number.  Changing the cocycle by a coboundary changes that value
by a complex norm, hence by a positive real number.  Consequently there are
exactly two cohomology classes, represented by the trivial factor set and by
`realFactorSet`.
-/

namespace Submission.CField.LBrauer

noncomputable section

open scoped ComplexConjugate
open CProduca
open groupCohomology

attribute [local instance] Units.mulDistribMulActionRight

private abbrev RealGal := Gal(ℂ/ℝ)
private abbrev RealCocycle :=
  NMCocycl₂ (G := RealGal) (M := ℂˣ)
private abbrev RealH2 := MHTwo RealGal ℂˣ

/-- A normalized cocycle for `Complex/Real` is determined by its value on
`(conj, conj)`. -/
theorem realCocycle_ext {c d : RealCocycle}
    (h : c (Complex.conjAe, Complex.conjAe) =
      d (Complex.conjAe, Complex.conjAe)) :
    c = d := by
  apply NMCocycl₂.ext
  rintro ⟨sigma, tau⟩
  rcases complex_gal_or sigma with rfl | rfl <;>
    rcases complex_gal_or tau with rfl | rfl
  · simp
  · simp
  · simp
  · exact h

/-- The distinguished value of a normalized real cocycle is fixed by complex
conjugation. -/
theorem real_cocycle_fixed (c : RealCocycle) :
    Complex.conjAe • c (Complex.conjAe, Complex.conjAe) =
      c (Complex.conjAe, Complex.conjAe) := by
  let s : RealGal := Complex.conjAe
  have hc := c.isMulCocycle₂ s s s
  have hs : s * s = 1 := by
    ext z
    change conj (conj z) = z
    simp
  rw [hs] at hc
  simpa [s] using hc.symm

/-- A convenient four-case criterion for two real cocycles to be
cohomologous. -/
theorem cocycle_cohomologous_div
    (c d : RealCocycle) (z : ℂˣ)
    (h : c (Complex.conjAe, Complex.conjAe) /
        d (Complex.conjAe, Complex.conjAe) =
      (Complex.conjAe • z) * z) :
    MHTwo.IsCohomologous c d := by
  classical
  let s : RealGal := Complex.conjAe
  have hone : (1 : RealGal) ≠ s := by
    simpa [s] using Ne.symm conj_ne_one
  have hs : s * s = 1 := by
    ext w
    change conj (conj w) = w
    simp
  refine ⟨fun sigma ↦ if sigma = s then z else 1, ?_⟩
  intro sigma tau
  rcases complex_gal_or sigma with rfl | rfl <;>
    rcases complex_gal_or tau with rfl | rfl
  · simp [s, hone]
  · simp [s, hone]
  · simp [s, hone]
  · change c (s, s) / d (s, s) = (s • z) * z at h
    simpa [s, hone, hs] using h.symm

/-- A nonzero complex number fixed by conjugation is either a complex norm or
the negative of a complex norm. -/
theorem complex_or_neg (a : ℂˣ)
    (ha : Complex.conjAe • a = a) :
    (∃ z : ℂˣ, (Complex.conjAe • z) * z = a) ∨
      (∃ z : ℂˣ, (Complex.conjAe • z) * z = -a) := by
  have ha' : conj (a : ℂ) = (a : ℂ) := by
    exact congrArg Units.val ha
  have hareal : ((a : ℂ).re : ℂ) = (a : ℂ) :=
    Complex.conj_eq_iff_re.mp ha'
  have hre : (a : ℂ).re ≠ 0 := by
    intro h
    have hazero : (a : ℂ) = 0 := by simpa [h] using hareal.symm
    exact a.ne_zero hazero
  rcases lt_or_gt_of_ne hre with hre | hre
  · right
    let z : ℂˣ := Units.mk0 ((Real.sqrt (-(a : ℂ).re) : ℝ) : ℂ) (by
      exact_mod_cast (Real.sqrt_pos.2 (neg_pos.mpr hre)).ne')
    refine ⟨z, ?_⟩
    apply Units.ext
    change conj (z : ℂ) * (z : ℂ) = -(a : ℂ)
    rw [← hareal]
    apply Complex.ext
    · simpa [z, pow_two] using Real.sq_sqrt (neg_nonneg.mpr hre.le)
    · simp [z]
  · left
    let z : ℂˣ := Units.mk0 ((Real.sqrt (a : ℂ).re : ℝ) : ℂ) (by
      exact_mod_cast (Real.sqrt_pos.2 hre).ne')
    refine ⟨z, ?_⟩
    apply Units.ext
    change conj (z : ℂ) * (z : ℂ) = (a : ℂ)
    rw [← hareal]
    apply Complex.ext
    · simpa [z, pow_two] using Real.sq_sqrt hre.le
    · simp [z]

/-- Every normalized factor set for `Complex/Real` is cohomologous either to
the trivial factor set or to Milne's factor set with value `-1`. -/
theorem real_cocycle_cohomologous (c : RealCocycle) :
    MHTwo.IsCohomologous c 1 ∨
      MHTwo.IsCohomologous c realFactorSet := by
  rcases complex_or_neg
      (c (Complex.conjAe, Complex.conjAe))
      (real_cocycle_fixed c) with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    apply cocycle_cohomologous_div c 1 z
    simpa using hz.symm
  · right
    apply cocycle_cohomologous_div c realFactorSet z
    rw [real_set_conj]
    rw [show c (Complex.conjAe, Complex.conjAe) / (-1 : ℂˣ) =
        -c (Complex.conjAe, Complex.conjAe) by
      rw [div_eq_mul_inv]
      simp]
    exact hz.symm

/-- Every class in `H²(Gal(ℂ/ℝ), ℂˣ)` is trivial or represented by
`realFactorSet`. -/
theorem real_or_set (x : RealH2) :
    x = 1 ∨ x = MHTwo.mk realFactorSet := by
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  rw [show (1 : RealH2) = MHTwo.mk 1 from rfl]
  simpa only [MHTwo.mk_eq_iff] using
    real_cocycle_cohomologous c

/-- Milne's real factor set represents a nontrivial cohomology class. -/
theorem real_set_ne :
    MHTwo.mk realFactorSet ≠ (1 : RealH2) := by
  intro htrivial
  have hcoh : MHTwo.IsCohomologous realFactorSet 1 :=
    (MHTwo.mk_eq_iff realFactorSet 1).mp htrivial
  obtain ⟨x, hx⟩ := hcoh
  have hxone : x (1 : RealGal) = 1 := by
    have h := hx (1 : RealGal) 1
    simpa using h
  have hnormUnit :
      (-1 : ℂˣ) =
        (Complex.conjAe • x (Complex.conjAe : RealGal)) *
          x Complex.conjAe := by
    let s : RealGal := Complex.conjAe
    have h := hx s s
    have hs : s * s = 1 := by
      ext w
      change conj (conj w) = w
      simp
    rw [hs] at h
    simpa [s, hxone] using h.symm
  have hnorm :
      (-1 : ℂ) = conj (x (Complex.conjAe : RealGal) : ℂ) *
        (x Complex.conjAe : ℂ) :=
    congrArg Units.val hnormUnit
  have hnorm' :
      (-1 : ℂ) = (Complex.normSq (x (Complex.conjAe : RealGal) : ℂ) : ℂ) :=
    hnorm.trans Complex.normSq_eq_conj_mul_self.symm
  have hre := congrArg Complex.re hnorm'
  have hnonneg := Complex.normSq_nonneg
    (x (Complex.conjAe : RealGal) : ℂ)
  norm_num at hre
  linarith

/-- The nontrivial real cohomology class has order two. -/
@[simp]
theorem real_set_sq :
    MHTwo.mk realFactorSet * MHTwo.mk realFactorSet =
      (1 : RealH2) := by
  rw [← MHTwo.mk_mul]
  change MHTwo.mk (realFactorSet * realFactorSet) =
    MHTwo.mk 1
  congr 1
  apply realCocycle_ext
  simp

private theorem zmod_or_one (a : ZMod 2) :
    a = 0 ∨ a = 1 := by
  have hlt := a.val_lt
  have ha : a.val = 0 ∨ a.val = 1 := by
    omega
  rcases ha with ha | ha
  · left
    apply ZMod.val_injective
    simpa using ha
  · right
    apply ZMod.val_injective
    simpa using ha

/-- The homomorphism from the cyclic group of order two which sends its
generator to the class of `realFactorSet`. -/
noncomputable def zmodReal2 : Multiplicative (ZMod 2) →* RealH2 where
  toFun a := if a.toAdd = 0 then 1 else MHTwo.mk realFactorSet
  map_one' := by simp
  map_mul' := by
    intro a b
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases zmod_or_one a.toAdd with ha | ha <;>
      rcases zmod_or_one b.toAdd with hb | hb <;>
        simp [ha, hb, h11, real_set_sq]

@[simp]
theorem zmod_real_generator :
    zmodReal2 (Multiplicative.ofAdd (1 : ZMod 2)) =
      MHTwo.mk realFactorSet := by
  simp [zmodReal2]

theorem zmod_real_bijective : Function.Bijective zmodReal2 := by
  constructor
  · intro a b hab
    rcases zmod_or_one a.toAdd with ha | ha <;>
      rcases zmod_or_one b.toAdd with hb | hb
    · exact Multiplicative.toAdd.injective (ha.trans hb.symm)
    · exfalso
      have ha' : a = 1 := Multiplicative.toAdd.injective (by simpa using ha)
      have hb' : b = Multiplicative.ofAdd (1 : ZMod 2) :=
        Multiplicative.toAdd.injective hb
      subst a
      subst b
      exact real_set_ne (by
        simpa [zmodReal2] using hab.symm)
    · exfalso
      have ha' : a = Multiplicative.ofAdd (1 : ZMod 2) :=
        Multiplicative.toAdd.injective ha
      have hb' : b = 1 := Multiplicative.toAdd.injective (by simpa using hb)
      subst a
      subst b
      exact real_set_ne (by
        simpa [zmodReal2] using hab)
    · exact Multiplicative.toAdd.injective (ha.trans hb.symm)
  · intro x
    rcases real_or_set x with rfl | rfl
    · exact ⟨Multiplicative.ofAdd 0, by simp [zmodReal2]⟩
    · exact ⟨Multiplicative.ofAdd 1, zmod_real_generator⟩

/-- The explicit cyclic classification
`H²(Gal(ℂ/ℝ), ℂˣ) ≃ Multiplicative (ZMod 2)`. -/
noncomputable def realH2 :
    RealH2 ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.ofBijective zmodReal2 zmod_real_bijective).symm

/-- Under the cyclic classification, `realFactorSet` is the nonzero
generator. -/
@[simp]
theorem real_h_set :
    realH2 (MHTwo.mk realFactorSet) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  apply (MulEquiv.ofBijective zmodReal2
    zmod_real_bijective).injective
  simp [realH2]

end

end Submission.CField.LBrauer

import Submission.NumberTheory.Locals.NewtonRootLifting
import Submission.NumberTheory.Completions.PlaceFactorCorrespondence
import Submission.NumberTheory.Fields.MinusTwoPlaces
import Submission.NumberTheory.ClassGroup.NoExtensionQ
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.FinCases

/-!
# Milne, Chapter 8, Exercise 8-1

The polynomial `X^3 - X^2 - 2X - 8` has three roots in the `2`-adic
integers.  Newton lifting at `0`, `2`, and `1` puts them in the three
different norm strata predicted by its Newton polygon.

This file also computes the polynomial discriminant `-2012` and the field
discriminant `-503`, using the mixed integral basis
`(1, alpha, (alpha^2 + alpha) / 2)`.  This proves the distinction highlighted
by the exercise: `2` divides the power-basis discriminant but not the field
discriminant.
-/

namespace Submission.NumberTheory.Milne

open AbsoluteValue Module NumberField Polynomial
open scoped Matrix NumberField

noncomputable section

local instance twoPrimeFact_1 : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance threePrimeFact_1 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The cubic polynomial in Milne's Exercise 8-1. -/
def twoAdicCubic : ℤ[X] :=
  X ^ 3 - X ^ 2 - 2 * X - 8

/-- The cubic defining the field in Exercise 8-1 is monic. -/
theorem adic_cubic_monic : twoAdicCubic.Monic := by
  rw [show twoAdicCubic = X ^ 3 + (-X ^ 2 - 2 * X - 8) by
    simp only [twoAdicCubic]
    ring]
  apply monic_X_pow_add
  compute_degree
  all_goals norm_num

private theorem adic_cubic_irreducible :
    Irreducible
      (twoAdicCubic.map (Int.castRingHom (ZMod 3))) := by
  let f : (ZMod 3)[X] := X ^ 3 - X ^ 2 - 2 * X - 8
  have hf : twoAdicCubic.map (Int.castRingHom (ZMod 3)) = f := by
    simp [twoAdicCubic, f]
  rw [hf]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdegree : f.natDegree = 3 := by
      dsimp [f]
      compute_degree
      all_goals norm_num
    simp [hdegree]
  · intro x
    fin_cases x <;> norm_num [f, IsRoot.def] <;> decide

/-- The polynomial `X³ - X² - 2X - 8` is irreducible over `ℚ`, so a
chosen root generates a cubic number field. -/
theorem two_adic_irreducible :
    Irreducible (twoAdicCubic.map (algebraMap ℤ ℚ)) := by
  have hZ : Irreducible twoAdicCubic := by
    apply Monic.irreducible_of_irreducible_map
      (Int.castRingHom (ZMod 3)) twoAdicCubic
    · exact adic_cubic_monic
    · exact adic_cubic_irreducible
  exact
    (adic_cubic_monic.irreducible_iff_irreducible_map_fraction_map).1 hZ

/-- The polynomial discriminant in Exercise 8-1 is `-2012`, and in
particular is divisible by `2`. -/
theorem Polynomial_discriminant :
    twoAdicCubic.discr = -2012 := by
  rw [discr_of_degree_eq_three]
  · norm_num [twoAdicCubic, coeff_add, coeff_sub, coeff_mul, coeff_X]
  · simpa [twoAdicCubic] using
      (degree_cubic (R := ℤ) (a := 1) (b := -1) (c := -2) (d := -8) one_ne_zero)

theorem cubictwo_cubic_discriminant :
    (2 : ℤ) ∣ twoAdicCubic.discr := by
  rw [Polynomial_discriminant]
  norm_num

/-- The three `2`-adic roots, separated by their norms.  The first has
valuation at least `2`, the second has valuation exactly `1`, and the third
is a unit. -/
theorem three_adic_roots :
    ∃ α β γ : ℤ_[2],
      twoAdicCubic.aeval α = 0 ∧
        twoAdicCubic.aeval β = 0 ∧
          twoAdicCubic.aeval γ = 0 ∧
            ‖α‖ < (2 : ℝ)⁻¹ ∧ ‖β‖ = (2 : ℝ)⁻¹ ∧ ‖γ‖ = 1 := by
  let F : ℤ[X] := twoAdicCubic
  have hF0 : F.aeval (0 : ℤ_[2]) = (-8 : ℤ_[2]) := by
    norm_num [F, twoAdicCubic, aeval_def]
  have hFd0 : F.derivative.aeval (0 : ℤ_[2]) = (-2 : ℤ_[2]) := by
    norm_num [F, twoAdicCubic, aeval_def]
  have hF2 : F.aeval (2 : ℤ_[2]) = (-8 : ℤ_[2]) := by
    norm_num [F, twoAdicCubic, aeval_def]
  have hFd2 : F.derivative.aeval (2 : ℤ_[2]) = (6 : ℤ_[2]) := by
    norm_num [F, twoAdicCubic, aeval_def]
  have hF1 : F.aeval (1 : ℤ_[2]) = (-10 : ℤ_[2]) := by
    norm_num [F, twoAdicCubic, aeval_def]
  have hFd1 : F.derivative.aeval (1 : ℤ_[2]) = (-1 : ℤ_[2]) := by
    norm_num [F, twoAdicCubic, aeval_def]
  have hnormNegTwo : ‖(-2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    simpa using (@PadicInt.norm_p 2 inferInstance)
  have hnormTwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ :=
    @PadicInt.norm_p 2 inferInstance
  have hnormThree : ‖(3 : ℤ_[2])‖ = 1 := by
    change ‖((3 : ℕ) : ℤ_[2])‖ = 1
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hnormSix : ‖(6 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    rw [show (6 : ℤ_[2]) = 2 * 3 by norm_num, norm_mul, hnormTwo, hnormThree]
    simp
  have hnormNegOne : ‖(-1 : ℤ_[2])‖ = 1 := by simp
  have hboundEight : ‖(-8 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    exact PadicInt.norm_int_le_pow_iff_dvd.mpr (by norm_num)
  have hnewton0 :
      ‖F.aeval (0 : ℤ_[2])‖ < ‖F.derivative.aeval (0 : ℤ_[2])‖ ^ 2 := by
    rw [hF0, hFd0, hnormNegTwo]
    calc
      ‖(-8 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := hboundEight
      _ < ((2 : ℝ)⁻¹) ^ 2 := by norm_num
  have hnewton2 :
      ‖F.aeval (2 : ℤ_[2])‖ < ‖F.derivative.aeval (2 : ℤ_[2])‖ ^ 2 := by
    rw [hF2, hFd2, hnormSix]
    calc
      ‖(-8 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := hboundEight
      _ < ((2 : ℝ)⁻¹) ^ 2 := by norm_num
  have hnewton1 :
      ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF1, hFd1, hnormNegOne, one_pow]
    exact PadicInt.norm_intCast_lt_one_iff.mpr (by norm_num)
  obtain ⟨α, hαroot, hα0, -, -⟩ := padic_newton_root F 0 hnewton0
  obtain ⟨β, hβroot, hβ2, -, -⟩ := padic_newton_root F 2 hnewton2
  obtain ⟨γ, hγroot, hγ1, -, -⟩ := padic_newton_root F 1 hnewton1
  have hαnorm : ‖α‖ < (2 : ℝ)⁻¹ := by
    simpa [hFd0, hnormNegTwo] using hα0
  have hβclose : ‖β - 2‖ < (2 : ℝ)⁻¹ := by
    simpa [hFd2, hnormSix] using hβ2
  have hβnorm : ‖β‖ = (2 : ℝ)⁻¹ := by
    have h : ‖β + -(2 : ℤ_[2])‖ < ‖-(2 : ℤ_[2])‖ := by
      simpa [sub_eq_add_neg, hnormNegTwo] using hβclose
    simpa [hnormNegTwo] using PadicInt.norm_eq_of_norm_add_lt_right h
  have hγclose : ‖γ - 1‖ < 1 := by
    simpa [hFd1, hnormNegOne] using hγ1
  have hγnorm : ‖γ‖ = 1 := by
    have h : ‖γ + -(1 : ℤ_[2])‖ < ‖-(1 : ℤ_[2])‖ := by
      simpa [sub_eq_add_neg] using hγclose
    simpa using PadicInt.norm_eq_of_norm_add_lt_right h
  exact ⟨α, β, γ, by simpa [F] using hαroot, by simpa [F] using hβroot,
    by simpa [F] using hγroot, hαnorm, hβnorm, hγnorm⟩

/-- The cubic splits completely over the `2`-adic integers, hence also over
the `2`-adic field. -/
theorem cubic_splits_int :
    (twoAdicCubic.map (algebraMap ℤ ℤ_[2])).Splits := by
  classical
  obtain ⟨α, β, γ, hαroot, hβroot, hγroot, hαnorm, hβnorm, hγnorm⟩ :=
    three_adic_roots
  let P : ℤ_[2][X] := twoAdicCubic.map (algebraMap ℤ ℤ_[2])
  have hPdegree : P.natDegree = 3 := by
    apply natDegree_eq_of_degree_eq_some
    simpa [P, twoAdicCubic] using
      (degree_cubic (R := ℤ_[2]) (a := 1) (b := -1) (c := -2) (d := -8) one_ne_zero)
  have hPne : P ≠ 0 := by
    intro h
    have := congrArg (fun q : ℤ_[2][X] ↦ q.coeff 3) h
    norm_num [P, twoAdicCubic, coeff_sub, coeff_mul, coeff_X] at this
  have hα : P.IsRoot α := by
    simpa [P, IsRoot.def, aeval_def, eval_map] using hαroot
  have hβ : P.IsRoot β := by
    simpa [P, IsRoot.def, aeval_def, eval_map] using hβroot
  have hγ : P.IsRoot γ := by
    simpa [P, IsRoot.def, aeval_def, eval_map] using hγroot
  have hαmem : α ∈ P.roots := (mem_roots hPne).2 hα
  have hβmem : β ∈ P.roots := (mem_roots hPne).2 hβ
  have hγmem : γ ∈ P.roots := (mem_roots hPne).2 hγ
  have hαβ : α ≠ β := by
    intro h
    subst β
    rw [hβnorm] at hαnorm
    exact (lt_irrefl _ hαnorm)
  have hαγ : α ≠ γ := by
    intro h
    subst γ
    rw [hγnorm] at hαnorm
    norm_num at hαnorm
  have hβγ : β ≠ γ := by
    intro h
    subst γ
    rw [hγnorm] at hβnorm
    norm_num at hβnorm
  have hsubset : ({α, β, γ} : Finset ℤ_[2]) ⊆ P.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Multiset.mem_toFinset]
    rcases hx with rfl | rfl | rfl
    · exact hαmem
    · exact hβmem
    · exact hγmem
  have hthree : 3 ≤ P.roots.card := by
    calc
      3 = ({α, β, γ} : Finset ℤ_[2]).card := by simp [hαβ, hαγ, hβγ]
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hsubset
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
  change P.Splits
  apply splits_iff_card_roots.mpr
  rw [hPdegree]
  have hupper : P.roots.card ≤ 3 := by simpa [hPdegree] using P.card_roots'
  exact le_antisymm hupper hthree

/-- The same complete splitting after passing from `ℤ_[2]` to `ℚ_[2]`. -/
theorem adic_cubic_splits :
    (twoAdicCubic.map (algebraMap ℤ ℚ_[2])).Splits := by
  have h := cubic_splits_int
  simpa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using
    h.map (algebraMap ℤ_[2] ℚ_[2])

/-- An exact factorization into three monic linear factors over `ℚ_[2]`.
The multiset is the multiset of roots, so multiplicities are retained. -/
theorem linear_factors_adic :
    ∃ r : Multiset ℚ_[2],
      r.card = 3 ∧
        twoAdicCubic.map (algebraMap ℤ ℚ_[2]) =
          (r.map fun x ↦ X - C x).prod := by
  let P : ℚ_[2][X] := twoAdicCubic.map (algebraMap ℤ ℚ_[2])
  have hs : P.Splits := by
    simpa [P] using adic_cubic_splits
  have hdegree : P.natDegree = 3 := by
    apply natDegree_eq_of_degree_eq_some
    simpa [P, twoAdicCubic] using
      (degree_cubic (R := ℚ_[2]) (a := 1) (b := -1) (c := -2) (d := -8) one_ne_zero)
  have hmonic : P.Monic := by
    rw [Monic.def, leadingCoeff, hdegree]
    norm_num [P, twoAdicCubic, coeff_sub, coeff_mul, coeff_X]
  refine ⟨P.roots, ?_, ?_⟩
  · rw [← hs.natDegree_eq_card_roots, hdegree]
  · simpa [P] using hs.eq_prod_roots_of_monic hmonic

section AbsoluteValueExtensions

variable {F : Type*} [Field F]

/-- When a separable polynomial splits, its monic irreducible divisors are
parametrized by its distinct roots. -/
noncomputable def monicIrreducibleDivisors
    (p : F[X]) (hp0 : p ≠ 0) (_hsep : p.Separable) (hsplit : p.Splits) :
    p.rootSet F ≃ {g : F[X] // Irreducible g ∧ g.Monic ∧ g ∣ p} where
  toFun x := ⟨X - C x.1, irreducible_X_sub_C x.1, monic_X_sub_C x.1, by
    rw [dvd_iff_isRoot]
    exact (mem_rootSet_of_ne hp0).mp x.2⟩
  invFun g := ⟨-g.1.coeff 0, by
    rw [mem_rootSet_of_ne hp0]
    have hgsplit : g.1.Splits := hsplit.of_dvd hp0 g.2.2.2
    have hdegree : g.1.degree = 1 :=
      hgsplit.degree_eq_one_of_irreducible g.2.1
    have hg : g.1 = X - C (-g.1.coeff 0) := by
      simpa [g.2.2.1.leadingCoeff] using
        (eq_X_add_C_of_degree_eq_one hdegree)
    change p.IsRoot (-g.1.coeff 0)
    rw [← dvd_iff_isRoot, ← hg]
    exact g.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    have hgsplit : g.1.Splits := hsplit.of_dvd hp0 g.2.2.2
    have hdegree : g.1.degree = 1 :=
      hgsplit.degree_eq_one_of_irreducible g.2.1
    simpa [g.2.2.1.leadingCoeff] using
      (eq_X_add_C_of_degree_eq_one hdegree).symm

theorem monic_divisors_splits
    (p : F[X]) (hp0 : p ≠ 0) (hsep : p.Separable) (hsplit : p.Splits) :
    Nat.card {g : F[X] // Irreducible g ∧ g.Monic ∧ g ∣ p} = p.natDegree := by
  rw [Nat.card_congr
    (monicIrreducibleDivisors p hp0 hsep hsplit).symm]
  classical
  simpa using Polynomial.card_rootSet_eq_natDegree (K := F) hsep
    (by simpa using hsplit)

/-- The cubic number field from Exercise 8-1, with its chosen generator. -/
abbrev AdicCubicField :=
  AdjoinRoot (twoAdicCubic.map (algebraMap ℤ ℚ))

noncomputable local instance : Fact
    (Irreducible (twoAdicCubic.map (algebraMap ℤ ℚ))) :=
  ⟨two_adic_irreducible⟩

private theorem adic_cubicrational_height :
    algebraMap ℤ (NumberField.RingOfIntegers ℚ) 2 ∈
      rationalTwoHeight.asIdeal := by
  rw [← Ideal.apply_mem_of_equiv_iff
    (f := Rat.IsIntegralClosure.intEquiv
      (NumberField.RingOfIntegers ℚ))]
  have hgen : Rat.HeightOneSpectrum.natGenerator rationalTwoHeight = 2 :=
    congrArg Subtype.val
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply rationalTwoPrime)
  have h :=
    (Rat.HeightOneSpectrum.natGenerator_dvd_iff rationalTwoHeight).mp
      (show Rat.HeightOneSpectrum.natGenerator rationalTwoHeight ∣ 2 by
        rw [hgen])
  have hmap : Rat.IsIntegralClosure.intEquiv
      (NumberField.RingOfIntegers ℚ)
      (algebraMap ℤ (NumberField.RingOfIntegers ℚ) 2) = 2 := by
    rw [Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    rw [Rat.ringOfIntegersEquiv_apply_coe]
    norm_num only [map_ofNat]
  rw [hmap]
  exact h

private theorem rational_two_nontrivial :
    rationalAdicPlace.val.IsNontrivial := by
  refine ⟨2, by norm_num, ?_⟩
  have hlt : rationalAdicPlace.val 2 < 1 := by
    change ‖FinitePlace.embedding rationalTwoHeight 2‖ < 1
    have h :=
      (FinitePlace.norm_lt_one_iff_mem (K := ℚ) rationalTwoHeight
        (algebraMap ℤ (NumberField.RingOfIntegers ℚ) 2)).2
          adic_cubicrational_height
    simpa only [map_ofNat] using h
  exact ne_of_lt hlt

noncomputable local instance RationalTwoFact :
    Fact rationalAdicPlace.val.IsNontrivial :=
  ⟨rational_two_nontrivial⟩

noncomputable local instance CompletionNontriviallyNormedField :
    NontriviallyNormedField rationalAdicPlace.val.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases (Fact.out : rationalAdicPlace.val.IsNontrivial) with
      ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding rationalAdicPlace.val x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding rationalAdicPlace.val)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

private theorem adic_cubicminpoly_root :
    minpoly ℚ (AdjoinRoot.root
      (twoAdicCubic.map (algebraMap ℤ ℚ))) =
      twoAdicCubic.map (algebraMap ℤ ℚ) := by
  have hm := adic_cubic_monic.map (algebraMap ℤ ℚ)
  simpa only [hm.leadingCoeff, inv_one, C_1, mul_one] using
    (AdjoinRoot.minpoly_root (K := ℚ)
      two_adic_irreducible.ne_zero)

noncomputable local instance CompletionAlgebra :
    Algebra ℚ rationalAdicPlace.val.Completion :=
  (completionEmbedding rationalAdicPlace.val).toAlgebra

noncomputable local instance CompletionUltrametric :
    IsUltrametricDist rationalAdicPlace.val.Completion := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
  intro m
  rw [← map_natCast (completionEmbedding rationalAdicPlace.val),
    norm_completionEmbedding]
  exact
    (show IsNonarchimedean rationalAdicPlace.val from
      fun x y => rationalAdicPlace.add_le x y)
      |>.apply_natCast_le_one

private theorem CompletedPolynomial_splits :
    ((minpoly ℚ (AdjoinRoot.root
      (twoAdicCubic.map (algebraMap ℤ ℚ)))).map
        (completionEmbedding rationalAdicPlace.val)).Splits := by
  have h := adic_cubic_splits.map
    rationalAbsolutePadic.symm.toRingHom
  rw [adic_cubicminpoly_root]
  rw [Polynomial.map_map] at h ⊢
  have hhom :
      rationalAbsolutePadic.symm.toRingHom.comp
          (algebraMap ℤ ℚ_[2]) =
        (completionEmbedding rationalAdicPlace.val).comp
          (algebraMap ℤ ℚ) := by
    ext z
    change rationalAbsolutePadic.symm
        ((z : ℤ) : ℚ_[2]) =
      completionEmbedding rationalAdicPlace.val ((z : ℤ) : ℚ)
    exact rationalAbsolutePadic.symm.commutes (z : ℚ)
  rwa [hhom] at h

private theorem completed_nat_degree :
    ((minpoly ℚ (AdjoinRoot.root
      (twoAdicCubic.map (algebraMap ℤ ℚ)))).map
        (completionEmbedding rationalAdicPlace.val)).natDegree = 3 := by
  rw [adic_cubicminpoly_root]
  apply natDegree_eq_of_degree_eq_some
  have hone : (1 : rationalAdicPlace.val.Completion) ≠ 0 := by
    intro h
    have := congrArg rationalAbsolutePadic h
    norm_num at this
  simpa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    twoAdicCubic] using
    (degree_cubic
      (R := rationalAdicPlace.val.Completion)
      (a := (1 : rationalAdicPlace.val.Completion))
      (b := (-1 : rationalAdicPlace.val.Completion))
      (c := (-2 : rationalAdicPlace.val.Completion))
      (d := (-8 : rationalAdicPlace.val.Completion)) hone)

private theorem CompletedPolynomial_separable :
    ((minpoly ℚ (AdjoinRoot.root
      (twoAdicCubic.map (algebraMap ℤ ℚ)))).map
        (completionEmbedding rationalAdicPlace.val)).Separable := by
  rw [adic_cubicminpoly_root]
  exact two_adic_irreducible.separable.map

private theorem completed_ne_zero :
    (minpoly ℚ (AdjoinRoot.root
      (twoAdicCubic.map (algebraMap ℤ ℚ)))).map
        (completionEmbedding rationalAdicPlace.val) ≠ 0 := by
  exact ((minpoly.monic (Algebra.IsIntegral.isIntegral
    (AdjoinRoot.root
      (twoAdicCubic.map (algebraMap ℤ ℚ))))).map
        (completionEmbedding rationalAdicPlace.val)).ne_zero

/-- The completed minimal polynomial has exactly three irreducible factors. -/
theorem completed_minpoly_factors :
    Nat.card (CompletedMinpolyFactor rationalAdicPlace.val
      (AdjoinRoot.root
        (twoAdicCubic.map (algebraMap ℤ ℚ)))) = 3 := by
  rw [monic_divisors_splits]
  · exact completed_nat_degree
  · exact completed_ne_zero
  · exact CompletedPolynomial_separable
  · exact CompletedPolynomial_splits

/-- Milne, Exercise 8-1: the 2-adic absolute value has exactly three
extensions to the cubic field `ℚ[α]`. -/
theorem adic_absolute_extensions :
    Nat.card {w : AbsoluteValue AdicCubicField ℝ //
      AbsoluteValue.LiesOver w rationalAdicPlace.val} = 3 := by
  let alpha : AdicCubicField :=
    AdjoinRoot.root (twoAdicCubic.map (algebraMap ℤ ℚ))
  have hgen : Algebra.adjoin ℚ {alpha} = ⊤ := by
    exact AdjoinRoot.adjoinRoot_eq_top
  let e := completedMinpolyExtensions
    rationalAdicPlace.val alpha hgen
  calc
    Nat.card {w : AbsoluteValue AdicCubicField ℝ //
        AbsoluteValue.LiesOver w rationalAdicPlace.val} =
        Nat.card (CompletedMinpolyFactor rationalAdicPlace.val alpha) :=
      (Nat.card_congr e).symm
    _ = 3 := completed_minpoly_factors

end AbsoluteValueExtensions

section FieldDiscriminant

noncomputable local instance PolynomialIrreducibleFact : Fact
    (Irreducible (twoAdicCubic.map (algebraMap ℤ ℚ))) :=
  ⟨two_adic_irreducible⟩

private abbrev adicCubicAlpha : AdicCubicField :=
  AdjoinRoot.root (twoAdicCubic.map (algebraMap ℤ ℚ))

/-- The extra algebraic integer needed to pass from the power basis to the
integral basis in Exercise 8-1. -/
private def adicCubicBeta : AdicCubicField :=
  (adicCubicAlpha ^ 2 + adicCubicAlpha) / 2

private theorem cubic_alpha_equation :
    adicCubicAlpha ^ 3 - adicCubicAlpha ^ 2 -
      2 * adicCubicAlpha - 8 = 0 := by
  have h := minpoly.aeval ℚ adicCubicAlpha
  have hmin : minpoly ℚ adicCubicAlpha =
      twoAdicCubic.map (algebraMap ℤ ℚ) := by
    have hm := adic_cubic_monic.map (algebraMap ℤ ℚ)
    simpa only [hm.leadingCoeff, inv_one, C_1, mul_one] using
      (AdjoinRoot.minpoly_root (K := ℚ)
        two_adic_irreducible.ne_zero)
  rw [hmin] at h
  simpa [adicCubicAlpha, twoAdicCubic, aeval_def] using h

private theorem cubic_beta_equation :
    adicCubicBeta ^ 3 - 3 * adicCubicBeta ^ 2 -
      10 * adicCubicBeta - 8 = 0 := by
  dsimp [adicCubicBeta]
  linear_combination
    ((adicCubicAlpha ^ 3 + 4 * adicCubicAlpha ^ 2 +
      3 * adicCubicAlpha + 8) / 8) * cubic_alpha_equation

private theorem cubic_beta_integral :
    IsIntegral ℤ adicCubicBeta := by
  refine ⟨X ^ 3 - 3 * X ^ 2 - 10 * X - 8, ?_, ?_⟩
  · rw [show (X ^ 3 - 3 * X ^ 2 - 10 * X - 8 : ℤ[X]) =
        X ^ 3 + (-3 * X ^ 2 - 10 * X - 8) by ring]
    apply monic_X_pow_add
    compute_degree
    all_goals norm_num
  · simpa [aeval_def] using cubic_beta_equation

private theorem cubic_alpha_integral :
    IsIntegral ℤ adicCubicAlpha := by
  refine ⟨twoAdicCubic, adic_cubic_monic, ?_⟩
  simpa [twoAdicCubic, aeval_def, eval₂_sub, eval₂_mul,
    eval₂_pow] using cubic_alpha_equation

private theorem adic_cubic_finrank :
    Module.finrank ℚ AdicCubicField = 3 := by
  let pb := AdjoinRoot.powerBasis two_adic_irreducible.ne_zero
  rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  apply natDegree_eq_of_degree_eq_some
  simpa [twoAdicCubic] using
    (degree_cubic (R := ℚ) (a := 1) (b := -1) (c := -2) (d := -8) one_ne_zero)

private def cubicMixedFamily : Fin 3 → AdicCubicField :=
  ![1, adicCubicAlpha, adicCubicBeta]

private theorem cubic_mixed_independent :
    LinearIndependent ℚ cubicMixedFamily := by
  let pb := AdjoinRoot.powerBasis two_adic_irreducible.ne_zero
  have hpdim : pb.dim = 3 := by
    rw [← pb.finrank]
    exact adic_cubic_finrank
  let b : Basis (Fin 3) ℚ AdicCubicField :=
    pb.basis.reindex (finCongr hpdim)
  have hb (i : Fin 3) : b i = adicCubicAlpha ^ (i : ℕ) := by
    dsimp only [b]
    rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
    congr 1
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' :
      g 0 + g 1 * adicCubicAlpha + g 2 * adicCubicBeta = 0 := by
    simpa [cubicMixedFamily, Fin.sum_univ_three, Algebra.smul_def] using hg
  let c : Fin 3 → ℚ := ![g 0, g 1 + g 2 / 2, g 2 / 2]
  have hc : ∑ j, c j • b j = 0 := by
    rw [Fin.sum_univ_three]
    have hc0 : c 0 = g 0 := rfl
    have hc1 : c 1 = g 1 + g 2 / 2 := rfl
    have hc2 : c 2 = g 2 / 2 := rfl
    rw [hc0, hc1, hc2]
    rw [hb 0, hb 1, hb 2]
    simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, Fin.val_two,
      Algebra.smul_def]
    simp only [map_add]
    dsimp [adicCubicBeta] at hg'
    convert hg' using 1
    norm_num [Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast]
    ring_nf
  have hz := Fintype.linearIndependent_iff.mp b.linearIndependent c hc
  have hz0 : g 0 = 0 := by simpa [c] using hz 0
  have hz1 : g 1 + g 2 / 2 = 0 := by simpa [c] using hz 1
  have hz2 : g 2 / 2 = 0 := by simpa [c] using hz 2
  have hg2 : g 2 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  fin_cases i
  · exact hz0
  · exact hg1
  · exact hg2

private noncomputable def cubicMixedBasis :
    Basis (Fin 3) ℚ AdicCubicField :=
  basisOfLinearIndependentOfCardEqFinrank
    cubic_mixed_independent (by
      rw [adic_cubic_finrank]
      rfl)

private theorem cubic_mixed_basis (i : Fin 3) :
    cubicMixedBasis i = cubicMixedFamily i := by
  exact congr_fun
    (coe_basisOfLinearIndependentOfCardEqFinrank
      cubic_mixed_independent (by
        rw [adic_cubic_finrank]
        rfl)) i

private theorem adic_cubic_discr :
    Algebra.discr ℚ
      (AdjoinRoot.powerBasis two_adic_irreducible.ne_zero).basis =
        (-2012 : ℚ) := by
  let pb := AdjoinRoot.powerBasis two_adic_irreducible.ne_zero
  have hmin : minpoly ℚ pb.gen =
      twoAdicCubic.map (algebraMap ℤ ℚ) := by
    dsimp [pb]
    have hm := adic_cubic_monic.map (algebraMap ℤ ℚ)
    simpa only [hm.leadingCoeff, inv_one, C_1, mul_one] using
      (AdjoinRoot.minpoly_root (K := ℚ)
        two_adic_irreducible.ne_zero)
  change Algebra.discr ℚ pb.basis = (-2012 : ℚ)
  calc
    Algebra.discr ℚ pb.basis = (minpoly ℚ pb.gen).discr :=
      basis_discr_minpoly pb
    _ = (twoAdicCubic.map (algebraMap ℤ ℚ)).discr := by rw [hmin]
    _ = (-2012 : ℚ) := by
      rw [← polynomial_discr_monic (algebraMap ℤ ℚ)
        twoAdicCubic adic_cubic_monic]
      · rw [Polynomial_discriminant]
        norm_num
      · have hdegree : twoAdicCubic.natDegree = 3 := by
          apply natDegree_eq_of_degree_eq_some
          simpa [twoAdicCubic] using
            (degree_cubic (R := ℤ) (a := 1) (b := -1) (c := -2) (d := -8)
              one_ne_zero)
        omega

private def cubicChangeMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 : ℚ), 0, 0; 0, 1, 1 / 2; 0, 0, 1 / 2]

private theorem cubic_mixed_discr :
    Algebra.discr ℚ cubicMixedBasis = (-503 : ℚ) := by
  let pb := AdjoinRoot.powerBasis two_adic_irreducible.ne_zero
  have hpdim : pb.dim = 3 := by
    rw [← pb.finrank]
    exact adic_cubic_finrank
  let b : Basis (Fin 3) ℚ AdicCubicField :=
    pb.basis.reindex (finCongr hpdim)
  have hb (i : Fin 3) : b i = adicCubicAlpha ^ (i : ℕ) := by
    dsimp only [b]
    rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
    congr 1
  have hbdiscr : Algebra.discr ℚ b = (-2012 : ℚ) := by
    change Algebra.discr ℚ (pb.basis.reindex (finCongr hpdim)) = (-2012 : ℚ)
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex]
    exact adic_cubic_discr
  have hfamily : cubicMixedFamily =
      Matrix.vecMul b
        (cubicChangeMatrix.map (algebraMap ℚ AdicCubicField)) := by
    funext i
    fin_cases i <;>
      simp [cubicMixedFamily, cubicChangeMatrix,
        Matrix.vecMul, dotProduct, Fin.sum_univ_three, hb, adicCubicBeta,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        ] ;
      ring
  rw [show (cubicMixedBasis : Fin 3 → AdicCubicField) =
      cubicMixedFamily from funext cubic_mixed_basis]
  rw [hfamily, Algebra.discr_of_matrix_vecMul, hbdiscr]
  norm_num [cubicChangeMatrix, Matrix.det_fin_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

private theorem cubic_mixed_integral (i : Fin 3) :
    IsIntegral ℤ (cubicMixedBasis i) := by
  rw [cubic_mixed_basis]
  fin_cases i
  · simpa [cubicMixedFamily] using
      (isIntegral_one : IsIntegral ℤ (1 : AdicCubicField))
  · simpa [cubicMixedFamily] using cubic_alpha_integral
  · simpa [cubicMixedFamily] using cubic_beta_integral

/-- The full ring of integers in the cubic field has discriminant `-503`.
The squarefree mixed-basis discriminant forces its index in the integer ring
to be one. -/
theorem two_adic_discr :
    NumberField.discr AdicCubicField = -503 := by
  obtain ⟨d, hd⟩ :=
    sq_discr_basis
      AdicCubicField cubicMixedBasis
        cubic_mixed_integral
  have hdZ : (-503 : ℤ) = d ^ 2 * NumberField.discr AdicCubicField := by
    have hd' := hd
    rw [cubic_mixed_discr] at hd'
    exact_mod_cast hd'
  have hsquarefree : Squarefree (-503 : ℤ) := by
    have hp : Prime (503 : ℤ) := by norm_num
    rw [(show Associated (-503 : ℤ) 503 from
      (Associated.refl (503 : ℤ)).neg_left).squarefree_iff]
    exact hp.squarefree
  have hdunit : IsUnit d := by
    apply hsquarefree d
    refine ⟨NumberField.discr AdicCubicField, ?_⟩
    simpa [pow_two] using hdZ
  rcases Int.isUnit_eq_one_or hdunit with hd1 | hd1
  · rw [hd1] at hdZ
    norm_num at hdZ
    exact hdZ.symm
  · rw [hd1] at hdZ
    norm_num at hdZ
    exact hdZ.symm

/-- Exercise 8-1: although `2` divides the discriminant of the displayed
power basis, it does not divide the discriminant of the full integer ring. -/
theorem dvd_adic_discriminant :
    ¬(2 : ℤ) ∣ NumberField.discr AdicCubicField := by
  rw [two_adic_discr]
  norm_num

end FieldDiscriminant

end

end Submission.NumberTheory.Milne

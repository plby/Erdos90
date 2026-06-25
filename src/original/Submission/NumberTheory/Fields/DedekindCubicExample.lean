import Submission.NumberTheory.Discriminant.FiniteIndexDiscriminant
import Submission.NumberTheory.Discriminant.PolynomialExamples
import Submission.NumberTheory.Discriminant.PowerBasisDiscriminant
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases


/-!
# Milne, Example 2.38: Dedekind's cubic field

For `f = X^3 + X^2 - 2X + 8`, the power-basis discriminant is `-2012`,
but adjoining the extra integer `(alpha^2 - alpha) / 2` gives an integral
basis of discriminant `-503`.
-/

namespace Submission.NumberTheory.Milne

open Module NumberField Polynomial
open scoped Matrix NumberField

noncomputable section

/-- The defining polynomial in Example 2.38. -/
def dedekindCubicPolynomial : ℤ[X] :=
  X ^ 3 + X ^ 2 - 2 * X + 8

theorem dedekind_cubic_monic : dedekindCubicPolynomial.Monic := by
  rw [show dedekindCubicPolynomial = X ^ 3 + (X ^ 2 - 2 * X + 8) by
    simp only [dedekindCubicPolynomial]
    ring]
  apply monic_X_pow_add
  compute_degree
  all_goals norm_num

private theorem dedekind_cubic_irreducible :
    Irreducible (dedekindCubicPolynomial.map (Int.castRingHom (ZMod 3))) := by
  let f : (ZMod 3)[X] := X ^ 3 + X ^ 2 - 2 * X + 8
  have hf : dedekindCubicPolynomial.map (Int.castRingHom (ZMod 3)) = f := by
    simp [dedekindCubicPolynomial, f]
  rw [hf]
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdegree : f.natDegree = 3 := by
      dsimp [f]
      compute_degree
      all_goals norm_num
    simp [hdegree]
  · intro x
    fin_cases x <;> norm_num [f, IsRoot.def] <;> decide

theorem dedekind_irreducible_int :
    Irreducible dedekindCubicPolynomial := by
  apply Monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 3)) dedekindCubicPolynomial
  · exact dedekind_cubic_monic
  · exact dedekind_cubic_irreducible

theorem dedekind_polynomial_irreducible :
    Irreducible (dedekindCubicPolynomial.map (algebraMap ℤ ℚ)) :=
  dedekind_cubic_monic.irreducible_iff_irreducible_map_fraction_map.mp
    dedekind_irreducible_int

@[simp]
theorem dedekind_polynomial_discr :
    dedekindCubicPolynomial.discr = -2012 := by
  simpa [dedekindCubicPolynomial] using
    discr_cube_eight

/-- Dedekind's cubic number field. -/
abbrev DedekindCubicField :=
  AdjoinRoot (dedekindCubicPolynomial.map (algebraMap ℤ ℚ))

noncomputable local instance IrreducibleFact :
    Fact (Irreducible (dedekindCubicPolynomial.map (algebraMap ℤ ℚ))) :=
  ⟨dedekind_polynomial_irreducible⟩

/-- The distinguished root of the defining polynomial. -/
abbrev dedekindCubicAlpha : DedekindCubicField :=
  AdjoinRoot.root (dedekindCubicPolynomial.map (algebraMap ℤ ℚ))

private theorem dedekind_alpha_equation :
    dedekindCubicAlpha ^ 3 + dedekindCubicAlpha ^ 2 -
      2 * dedekindCubicAlpha + 8 = 0 := by
  have h := minpoly.aeval ℚ dedekindCubicAlpha
  have hmin : minpoly ℚ dedekindCubicAlpha =
      dedekindCubicPolynomial.map (algebraMap ℤ ℚ) := by
    have hm := dedekind_cubic_monic.map (algebraMap ℤ ℚ)
    simpa only [hm.leadingCoeff, inv_one, C_1, mul_one] using
      (AdjoinRoot.minpoly_root (K := ℚ)
        dedekind_polynomial_irreducible.ne_zero)
  rw [hmin] at h
  simpa [dedekindCubicPolynomial, aeval_def] using h

theorem dedekind_alpha_integral : IsIntegral ℤ dedekindCubicAlpha := by
  refine ⟨dedekindCubicPolynomial, dedekind_cubic_monic, ?_⟩
  simpa [dedekindCubicPolynomial, aeval_def] using
    dedekind_alpha_equation

/-- The extra integer in Dedekind's integral basis. -/
def dedekindCubicBeta : DedekindCubicField :=
  (dedekindCubicAlpha ^ 2 - dedekindCubicAlpha) / 2

private theorem dedekind_beta_equation :
    dedekindCubicBeta ^ 3 - 3 * dedekindCubicBeta ^ 2 -
      10 * dedekindCubicBeta - 8 = 0 := by
  dsimp [dedekindCubicBeta]
  linear_combination
    ((dedekindCubicAlpha ^ 3 - 4 * dedekindCubicAlpha ^ 2 +
      3 * dedekindCubicAlpha - 8) / 8) * dedekind_alpha_equation

theorem dedekind_beta_integral : IsIntegral ℤ dedekindCubicBeta := by
  refine ⟨X ^ 3 - 3 * X ^ 2 - 10 * X - 8, ?_, ?_⟩
  · rw [show (X ^ 3 - 3 * X ^ 2 - 10 * X - 8 : ℤ[X]) =
        X ^ 3 + (-3 * X ^ 2 - 10 * X - 8) by ring]
    apply monic_X_pow_add
    compute_degree
    all_goals norm_num
  · simpa [aeval_def] using dedekind_beta_equation

theorem dedekind_cubic_finrank :
    Module.finrank ℚ DedekindCubicField = 3 := by
  let pb := AdjoinRoot.powerBasis dedekind_polynomial_irreducible.ne_zero
  rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  apply natDegree_eq_of_degree_eq_some
  simpa [dedekindCubicPolynomial] using
    (degree_cubic (R := ℚ) (a := 1) (b := 1) (c := -2) (d := 8)
      one_ne_zero)

private def dedekindMixedFamily : Fin 3 → DedekindCubicField :=
  ![1, dedekindCubicAlpha, dedekindCubicBeta]

private theorem dedekind_mixed_independent :
    LinearIndependent ℚ dedekindMixedFamily := by
  let pb := AdjoinRoot.powerBasis dedekind_polynomial_irreducible.ne_zero
  have hpdim : pb.dim = 3 := by
    rw [← pb.finrank]
    exact dedekind_cubic_finrank
  let b : Basis (Fin 3) ℚ DedekindCubicField :=
    pb.basis.reindex (finCongr hpdim)
  have hb (i : Fin 3) : b i = dedekindCubicAlpha ^ (i : ℕ) := by
    dsimp only [b]
    rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
    congr 1
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' :
      g 0 + g 1 * dedekindCubicAlpha + g 2 * dedekindCubicBeta = 0 := by
    simpa [dedekindMixedFamily, Fin.sum_univ_three, Algebra.smul_def]
      using hg
  let c : Fin 3 → ℚ := ![g 0, g 1 - g 2 / 2, g 2 / 2]
  have hc : ∑ j, c j • b j = 0 := by
    rw [Fin.sum_univ_three]
    rw [show c 0 = g 0 by rfl, show c 1 = g 1 - g 2 / 2 by rfl,
      show c 2 = g 2 / 2 by rfl]
    rw [hb 0, hb 1, hb 2]
    simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, Fin.val_two,
      Algebra.smul_def]
    have hmapdiv (q : ℚ) :
        algebraMap ℚ DedekindCubicField (q / 2) =
          algebraMap ℚ DedekindCubicField q /
            algebraMap ℚ DedekindCubicField 2 := by
      exact map_div₀ (algebraMap ℚ DedekindCubicField) q 2
    rw [map_sub, hmapdiv]
    norm_num only [map_ofNat]
    have hmap (q : ℚ) :
        algebraMap ℚ DedekindCubicField q = (q : DedekindCubicField) := by
      rw [Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast]
    rw [hmap, hmap, hmap]
    dsimp [dedekindCubicBeta] at hg'
    convert hg' using 1 ; ring
  have hz := Fintype.linearIndependent_iff.mp b.linearIndependent c hc
  have hz0 : g 0 = 0 := by simpa [c] using hz 0
  have hz1 : g 1 - g 2 / 2 = 0 := by simpa [c] using hz 1
  have hz2 : g 2 / 2 = 0 := by simpa [c] using hz 2
  have hg2 : g 2 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  fin_cases i
  · exact hz0
  · exact hg1
  · exact hg2

private noncomputable def dedekindMixedBasis :
    Basis (Fin 3) ℚ DedekindCubicField :=
  basisOfLinearIndependentOfCardEqFinrank
    dedekind_mixed_independent (by
      rw [dedekind_cubic_finrank]
      rfl)

private theorem dedekind_mixed_basis (i : Fin 3) :
    dedekindMixedBasis i = dedekindMixedFamily i := by
  exact congr_fun
    (coe_basisOfLinearIndependentOfCardEqFinrank
      dedekind_mixed_independent (by
        rw [dedekind_cubic_finrank]
        rfl)) i

private theorem dedekind_cubic_discr :
    Algebra.discr ℚ
      (AdjoinRoot.powerBasis dedekind_polynomial_irreducible.ne_zero).basis =
        (-2012 : ℚ) := by
  let pb := AdjoinRoot.powerBasis dedekind_polynomial_irreducible.ne_zero
  have hmin : minpoly ℚ pb.gen =
      dedekindCubicPolynomial.map (algebraMap ℤ ℚ) := by
    dsimp [pb]
    have hm := dedekind_cubic_monic.map (algebraMap ℤ ℚ)
    simpa only [hm.leadingCoeff, inv_one, C_1, mul_one] using
      (AdjoinRoot.minpoly_root (K := ℚ)
        dedekind_polynomial_irreducible.ne_zero)
  calc
    Algebra.discr ℚ pb.basis = (minpoly ℚ pb.gen).discr :=
      basis_discr_minpoly pb
    _ = (dedekindCubicPolynomial.map (algebraMap ℤ ℚ)).discr := by rw [hmin]
    _ = (-2012 : ℚ) := by
      have hmap : dedekindCubicPolynomial.map (algebraMap ℤ ℚ) =
          (X ^ 3 + X ^ 2 - 2 * X + 8 : ℚ[X]) := by
        simp [dedekindCubicPolynomial]
      rw [hmap]
      rw [discr_of_degree_eq_three]
      · norm_num [coeff_add, coeff_sub, coeff_mul, coeff_X]
      · simpa using
          (degree_cubic (R := ℚ) (a := 1) (b := 1) (c := -2) (d := 8)
            one_ne_zero)

private def dedekindChangeMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 : ℚ), 0, 0; 0, 1, -1 / 2; 0, 0, 1 / 2]

private theorem dedekind_mixed_discr :
    Algebra.discr ℚ dedekindMixedBasis = (-503 : ℚ) := by
  let pb := AdjoinRoot.powerBasis dedekind_polynomial_irreducible.ne_zero
  have hpdim : pb.dim = 3 := by
    rw [← pb.finrank]
    exact dedekind_cubic_finrank
  let b : Basis (Fin 3) ℚ DedekindCubicField :=
    pb.basis.reindex (finCongr hpdim)
  have hb (i : Fin 3) : b i = dedekindCubicAlpha ^ (i : ℕ) := by
    dsimp only [b]
    rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
    congr 1
  have hbdiscr : Algebra.discr ℚ b = (-2012 : ℚ) := by
    change Algebra.discr ℚ (pb.basis.reindex (finCongr hpdim)) = (-2012 : ℚ)
    rw [Basis.coe_reindex, Algebra.discr_reindex]
    exact dedekind_cubic_discr
  have hfamily : dedekindMixedFamily =
      Matrix.vecMul b
        (dedekindChangeMatrix.map (algebraMap ℚ DedekindCubicField)) := by
    funext i
    fin_cases i <;>
      simp [dedekindMixedFamily, dedekindChangeMatrix,
        Matrix.vecMul, dotProduct, Fin.sum_univ_three, hb, dedekindCubicBeta,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        ] ;
      ring
  rw [show (dedekindMixedBasis : Fin 3 → DedekindCubicField) =
      dedekindMixedFamily from funext dedekind_mixed_basis]
  rw [hfamily, Algebra.discr_of_matrix_vecMul, hbdiscr]
  norm_num [dedekindChangeMatrix, Matrix.det_fin_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

private theorem dedekind_mixed_integral (i : Fin 3) :
    IsIntegral ℤ (dedekindMixedBasis i) := by
  rw [dedekind_mixed_basis]
  fin_cases i
  · simpa [dedekindMixedFamily] using
      (isIntegral_one : IsIntegral ℤ (1 : DedekindCubicField))
  · simpa [dedekindMixedFamily] using dedekind_alpha_integral
  · simpa [dedekindMixedFamily] using dedekind_beta_integral

/-- Example 2.38: the field discriminant is `-503`. -/
theorem dedekind_field_discr : NumberField.discr DedekindCubicField = -503 := by
  obtain ⟨d, hd⟩ :=
    sq_discr_basis
      DedekindCubicField dedekindMixedBasis
        dedekind_mixed_integral
  have hdZ : (-503 : ℤ) = d ^ 2 * NumberField.discr DedekindCubicField := by
    have hd' := hd
    rw [dedekind_mixed_discr] at hd'
    exact_mod_cast hd'
  have hsquarefree : Squarefree (-503 : ℤ) := by
    have hp : Prime (503 : ℤ) := by norm_num
    rw [(show Associated (-503 : ℤ) 503 from
      (Associated.refl (503 : ℤ)).neg_left).squarefree_iff]
    exact hp.squarefree
  have hdunit : IsUnit d := by
    apply hsquarefree d
    refine ⟨NumberField.discr DedekindCubicField, ?_⟩
    simpa [pow_two] using hdZ
  rcases Int.isUnit_eq_one_or hdunit with hd1 | hd1
  · rw [hd1] at hdZ
    norm_num at hdZ
    exact hdZ.symm
  · rw [hd1] at hdZ
    norm_num at hdZ
    exact hdZ.symm

/-- The chosen root as an element of the ring of integers. -/
def dedekindAlphaInt : RingOfIntegers DedekindCubicField :=
  ⟨dedekindCubicAlpha, dedekind_alpha_integral⟩

/-- The extra integral-basis element in the ring of integers. -/
def BetaInt : RingOfIntegers DedekindCubicField :=
  ⟨dedekindCubicBeta, dedekind_beta_integral⟩

/-- The three displayed integers form an integral basis. -/
theorem exists_integralBasis :
    ∃ b : Basis (Fin 3) ℤ (RingOfIntegers DedekindCubicField),
      (b : Fin 3 → RingOfIntegers DedekindCubicField) =
        ![1, dedekindAlphaInt, BetaInt] := by
  let v : Fin 3 → RingOfIntegers DedekindCubicField :=
    ![1, dedekindAlphaInt, BetaInt]
  have hvcoe :
      (fun i => ((v i : RingOfIntegers DedekindCubicField) :
        DedekindCubicField)) = dedekindMixedBasis := by
    funext i
    rw [dedekind_mixed_basis]
    fin_cases i <;> rfl
  have hvdiscr : Algebra.discr ℤ v = (-503 : ℤ) := by
    apply Rat.intCast_injective
    rw [discr_coe_integers, hvcoe,
      dedekind_mixed_discr]
    norm_num
  let eInt : Free.ChooseBasisIndex ℤ (RingOfIntegers DedekindCubicField) ≃
      Fin 3 :=
    Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
        dedekind_cubic_finrank]
      rfl)
  let bInt : Basis (Fin 3) ℤ (RingOfIntegers DedekindCubicField) :=
    (RingOfIntegers.basis DedekindCubicField).reindex eInt
  have hbIntDiscr : Algebra.discr ℤ bInt = (-503 : ℤ) := by
    rw [NumberField.discr_eq_discr DedekindCubicField bInt]
    exact dedekind_field_discr
  have hbIntDiscr_ne : Algebra.discr ℤ bInt ≠ 0 := by
    rw [hbIntDiscr]
    norm_num
  have hspan : Ideal.span ({Algebra.discr ℤ v} : Set ℤ) =
      Ideal.span ({Algebra.discr ℤ bInt} : Set ℤ) := by
    rw [hvdiscr, hbIntDiscr]
  obtain ⟨b, hb⟩ :=
    (basis_span_discr bInt v hbIntDiscr_ne).mpr hspan
  exact ⟨b, hb⟩

/-- A chosen integral basis for Dedekind's cubic field. -/
noncomputable def IntegralBasis :
    Basis (Fin 3) ℤ (RingOfIntegers DedekindCubicField) :=
  Classical.choose exists_integralBasis

@[simp]
theorem IntegralBasis_apply (i : Fin 3) :
    IntegralBasis i =
      (![1, dedekindAlphaInt, BetaInt] :
          Fin 3 → RingOfIntegers DedekindCubicField) i := by
  exact congr_fun (Classical.choose_spec exists_integralBasis) i

/-- The full ring of integers is the order generated by the two displayed
integral elements `alpha` and `(alpha^2 - alpha) / 2`. -/
theorem adjoin_alpha_beta :
    Algebra.adjoin ℤ
      ({dedekindAlphaInt, BetaInt} :
        Set (RingOfIntegers DedekindCubicField)) = ⊤ := by
  apply top_unique
  intro theta _
  rw [← IntegralBasis.sum_repr theta]
  apply Submodule.sum_mem
    (Algebra.adjoin ℤ
      ({dedekindAlphaInt, BetaInt} :
        Set (RingOfIntegers DedekindCubicField))).toSubmodule
  intro i _
  apply Submodule.smul_mem
  rw [IntegralBasis_apply]
  fin_cases i
  · exact Subalgebra.one_mem _
  · exact Algebra.subset_adjoin (by simp)
  · exact Algebra.subset_adjoin (by simp)

private theorem minpoly_alphaInt :
    minpoly ℤ dedekindAlphaInt = dedekindCubicPolynomial := by
  have hint : IsIntegral ℤ dedekindAlphaInt :=
    Algebra.IsIntegral.isIntegral dedekindAlphaInt
  have heval :
      Polynomial.aeval dedekindAlphaInt dedekindCubicPolynomial = 0 := by
    apply RingOfIntegers.coe_injective
    simpa [dedekindAlphaInt, dedekindCubicPolynomial, aeval_def] using
      dedekind_alpha_equation
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint heval
  symm
  apply eq_of_monic_of_associated dedekind_cubic_monic
    (minpoly.monic hint)
  convert Associated.mul_left (minpoly ℤ dedekindAlphaInt)
    (associated_one_iff_isUnit.2
      ((dedekind_irreducible_int.isUnit_or_isUnit hq).resolve_left
        (minpoly.not_isUnit ℤ dedekindAlphaInt))) using 1
  rw [mul_one]

/-- Example 2.38: the order `ℤ[alpha]` has index exactly two in the ring of
integers. -/
theorem adjoin_index_two :
    (Algebra.adjoin ℤ ({dedekindAlphaInt} :
      Set (RingOfIntegers DedekindCubicField))).toSubmodule.toAddSubgroup.index = 2 := by
  let A := Algebra.adjoin ℤ ({dedekindAlphaInt} :
    Set (RingOfIntegers DedekindCubicField))
  let PB : PowerBasis ℤ A :=
    Algebra.adjoin.powerBasis'
      (Algebra.IsIntegral.isIntegral dedekindAlphaInt)
  have hPBdim : PB.dim = 3 := by
    have hdegree : dedekindCubicPolynomial.natDegree = 3 := by
      apply natDegree_eq_of_degree_eq_some
      simpa [dedekindCubicPolynomial] using
        (degree_cubic (R := ℤ) (a := 1) (b := 1) (c := -2) (d := 8)
          one_ne_zero)
    rw [Algebra.adjoin.powerBasis'_dim,
      minpoly_alphaInt, hdegree]
  let bA : Basis (Fin 3) ℤ A := PB.basis.reindex (finCongr hPBdim)
  let N : Submodule ℤ (RingOfIntegers DedekindCubicField) := A.toSubmodule
  let bN : Basis (Fin 3) ℤ N := bA
  have hbN (i : Fin 3) :
      (bN i : RingOfIntegers DedekindCubicField) =
        dedekindAlphaInt ^ (i : ℕ) := by
    dsimp only [bN, bA]
    rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
    change ((PB.gen ^ ((finCongr hPBdim).symm i : ℕ) : A) :
      RingOfIntegers DedekindCubicField) = _
    rw [Algebra.adjoin.powerBasis'_gen]
    congr 2
  have hbNdiscr :
      Algebra.discr ℤ
        (fun i => (bN i : RingOfIntegers DedekindCubicField)) = -2012 := by
    apply Rat.intCast_injective
    rw [discr_coe_integers]
    let pbQ :=
      AdjoinRoot.powerBasis dedekind_polynomial_irreducible.ne_zero
    have hpbQdim : pbQ.dim = 3 := by
      rw [← pbQ.finrank]
      exact dedekind_cubic_finrank
    let bQ : Basis (Fin 3) ℚ DedekindCubicField :=
      pbQ.basis.reindex (finCongr hpbQdim)
    have hfamily :
        (fun i => (((bN i : RingOfIntegers DedekindCubicField) :
          DedekindCubicField))) =
          bQ := by
      funext i
      rw [hbN i]
      change dedekindCubicAlpha ^ (i : ℕ) = bQ i
      dsimp only [bQ]
      rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
      congr 1
    have hbQdiscr : Algebra.discr ℚ bQ = (-2012 : ℚ) := by
      dsimp only [bQ]
      rw [Basis.coe_reindex, Algebra.discr_reindex]
      exact dedekind_cubic_discr
    rw [hfamily, hbQdiscr]
    norm_num
  have hbIntDiscr : Algebra.discr ℤ IntegralBasis = -503 := by
    rw [NumberField.discr_eq_discr DedekindCubicField
      IntegralBasis]
    exact dedekind_field_discr
  have hindex := discr_submodule_sq
    IntegralBasis N bN
  rw [hbNdiscr, hbIntDiscr] at hindex
  have hsquare : (N.toAddSubgroup.index : ℤ) ^ 2 = 4 := by
    nlinarith
  have hnonneg : (0 : ℤ) ≤ N.toAddSubgroup.index := by positivity
  have hindexZ : (N.toAddSubgroup.index : ℤ) = 2 := by nlinarith
  have hindexN : N.toAddSubgroup.index = 2 := by exact_mod_cast hindexZ
  exact hindexN

private theorem AlphaInt_sq :
    dedekindAlphaInt ^ 2 =
      dedekindAlphaInt + 2 * BetaInt := by
  apply RingOfIntegers.coe_injective
  change dedekindCubicAlpha ^ 2 = dedekindCubicAlpha +
    (algebraMap (RingOfIntegers DedekindCubicField) DedekindCubicField 2) *
      ((dedekindCubicAlpha ^ 2 - dedekindCubicAlpha) / 2)
  norm_num only [map_ofNat]
  ring

private theorem alpha_int_beta :
    dedekindAlphaInt * BetaInt =
      -4 - 2 * BetaInt := by
  apply RingOfIntegers.coe_injective
  change dedekindCubicAlpha *
      ((dedekindCubicAlpha ^ 2 - dedekindCubicAlpha) / 2) =
    -4 - 2 * ((dedekindCubicAlpha ^ 2 - dedekindCubicAlpha) / 2)
  linear_combination (1 / 2 : DedekindCubicField) *
    dedekind_alpha_equation

private theorem BetaInt_sq :
    BetaInt ^ 2 =
      6 - 2 * dedekindAlphaInt + 3 * BetaInt := by
  apply RingOfIntegers.coe_injective
  change ((dedekindCubicAlpha ^ 2 - dedekindCubicAlpha) / 2) ^ 2 =
    6 - 2 * dedekindCubicAlpha +
      3 * ((dedekindCubicAlpha ^ 2 - dedekindCubicAlpha) / 2)
  linear_combination
    ((dedekindCubicAlpha - 3) / 4) * dedekind_alpha_equation

private theorem indexForm_even (y z : ℤ) :
    (2 : ℤ) ∣ 2 * y ^ 3 - 5 * y ^ 2 * z + 3 * y * z ^ 2 + 2 * z ^ 3 := by
  change ((2 : ℕ) : ℤ) ∣
    2 * y ^ 3 - 5 * y ^ 2 * z + 3 * y * z ^ 2 + 2 * z ^ 3
  rw [← (ZMod.intCast_zmod_eq_zero_iff_dvd
    (2 * y ^ 3 - 5 * y ^ 2 * z + 3 * y * z ^ 2 + 2 * z ^ 3) 2)]
  change ((2 * y ^ 3 - 5 * y ^ 2 * z + 3 * y * z ^ 2 +
    2 * z ^ 3 : ℤ) : ZMod 2) = 0
  push_cast
  have hy : (y : ZMod 2) ^ 2 = (y : ZMod 2) := by
    simp
  have hz : (z : ZMod 2) ^ 2 = (z : ZMod 2) := by
    simp
  rw [hy, hz]
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo]
  rw [show (5 : ZMod 2) = 1 by decide,
    show (3 : ZMod 2) = 1 by decide]
  ring_nf

/-- Dedekind's nonmonogenicity conclusion: no algebraic integer generates
the full ring of integers of the cubic field. -/
theorem dedekind_cubic_monogenic (theta : RingOfIntegers DedekindCubicField) :
    Algebra.adjoin ℤ ({theta} : Set (RingOfIntegers DedekindCubicField)) ≠ ⊤ := by
  intro hthetaTop
  let r := IntegralBasis.repr theta
  let x : ℤ := r 0
  let y : ℤ := r 1
  let z : ℤ := r 2
  have htheta : theta =
      (x : RingOfIntegers DedekindCubicField) +
        (y : RingOfIntegers DedekindCubicField) * dedekindAlphaInt +
          (z : RingOfIntegers DedekindCubicField) * BetaInt := by
    have h := (IntegralBasis.sum_repr theta).symm
    rw [Fin.sum_univ_three] at h
    simpa [x, y, z, r, Algebra.smul_def,
      IntegralBasis_apply] using h
  let c0 : ℤ := x ^ 2 - 8 * y * z + 6 * z ^ 2
  let c1 : ℤ := 2 * x * y + y ^ 2 - 2 * z ^ 2
  let c2 : ℤ := 2 * x * z + 2 * y ^ 2 - 4 * y * z + 3 * z ^ 2
  have hthetaSq : theta ^ 2 =
      (c0 : RingOfIntegers DedekindCubicField) +
        (c1 : RingOfIntegers DedekindCubicField) * dedekindAlphaInt +
          (c2 : RingOfIntegers DedekindCubicField) * BetaInt := by
    rw [htheta]
    dsimp [c0, c1, c2]
    push_cast
    linear_combination
      (y : RingOfIntegers DedekindCubicField) ^ 2 * AlphaInt_sq +
      (2 * (y : RingOfIntegers DedekindCubicField) * z) *
        alpha_int_beta +
      (z : RingOfIntegers DedekindCubicField) ^ 2 * BetaInt_sq
  let PB : PowerBasis ℤ (RingOfIntegers DedekindCubicField) :=
    PowerBasis.ofAdjoinEqTop'
      (Algebra.IsIntegral.isIntegral theta) hthetaTop
  have hPBdim : PB.dim = 3 := by
    rw [← PB.finrank, RingOfIntegers.rank, dedekind_cubic_finrank]
  let bTheta : Basis (Fin 3) ℤ (RingOfIntegers DedekindCubicField) :=
    PB.basis.reindex (finCongr hPBdim)
  have hbTheta (i : Fin 3) : bTheta i = theta ^ (i : ℕ) := by
    dsimp only [bTheta]
    rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
    rw [PowerBasis.ofAdjoinEqTop'_gen]
    congr 1
  let P : Matrix (Fin 3) (Fin 3) ℤ :=
    !![1, x, c0; 0, y, c1; 0, z, c2]
  have hb0 : IntegralBasis 0 = 1 := by
    simp
  have hb1 : IntegralBasis 1 = dedekindAlphaInt := by
    simp
  have hb2 : IntegralBasis 2 = BetaInt := by
    simp
  have hthetaB : theta =
      x • IntegralBasis 0 +
        y • IntegralBasis 1 +
          z • IntegralBasis 2 := by
    simpa [Algebra.smul_def, hb0, hb1, hb2] using htheta
  have hthetaSqB : theta ^ 2 =
      c0 • IntegralBasis 0 +
        c1 • IntegralBasis 1 +
          c2 • IntegralBasis 2 := by
    simpa [Algebra.smul_def, hb0, hb1, hb2] using hthetaSq
  have hmatrix : IntegralBasis.toMatrix bTheta = P := by
    ext i j
    rw [Basis.toMatrix_apply]
    fin_cases j
    · rw [hbTheta]
      simp only [pow_zero]
      rw [← hb0, Basis.repr_self]
      fin_cases i <;> simp [P]
    · rw [hbTheta]
      simp only [pow_one, hthetaB, map_add, map_smul,
        Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self]
      fin_cases i <;> simp [P, x, y, z]
    · rw [hbTheta]
      simp only [hthetaSqB, map_add, map_smul,
        Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self]
      fin_cases i <;> simp [P, c0, c1, c2]
  have hdet : P.det = 2 * y ^ 3 - 5 * y ^ 2 * z +
      3 * y * z ^ 2 + 2 * z ^ 3 := by
    simp [P, Matrix.det_fin_three]
    ring
  have hdetEven : (2 : ℤ) ∣ P.det := by
    rw [hdet]
    exact indexForm_even y z
  have hdetUnit : IsUnit P.det := by
    rw [← hmatrix, ← LinearMap.toMatrix_id_eq_basis_toMatrix]
    exact LinearEquiv.isUnit_det
      (LinearEquiv.refl ℤ (RingOfIntegers DedekindCubicField))
        bTheta IntegralBasis
  have hdetDvdOne : P.det ∣ (1 : ℤ) := isUnit_iff_dvd_one.mp hdetUnit
  have : (2 : ℤ) ∣ 1 := hdetEven.trans hdetDvdOne
  norm_num at this

end

end Submission.NumberTheory.Milne

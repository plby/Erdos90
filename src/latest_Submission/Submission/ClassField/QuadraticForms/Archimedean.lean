import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Chapter VIII, Section 6: quadratic forms at archimedean places

This file records the archimedean classification paragraph following Theorem 6.3.
Mathlib already proves the normal-form theorems: over an algebraically closed field a
nondegenerate form is a sum of squares, and over `ℝ` a nondegenerate form is a diagonal
form with coefficients `±1`.  The signature API also proves the uniqueness part of
Sylvester's law of inertia.

The Hasse--Minkowski theorem itself and the nonarchimedean and global classification
theorems later in Section 6 require arithmetic local-global infrastructure not currently
available in the Submission development; they are not asserted here.
-/

namespace Submission.CField.QForms

open QuadraticMap

section Dimension

variable {K M M' : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup M'] [Module K M']

/-- Equivalent quadratic spaces have the same dimension. -/
theorem finrank_equivalent {Q : QuadraticForm K M} {Q' : QuadraticForm K M'}
    (h : Equivalent Q Q') :
    Module.finrank K M = Module.finrank K M' := by
  obtain ⟨e⟩ := h
  exact e.toLinearEquiv.finrank_eq

end Dimension

section AlgebraicallyClosed

variable {K M M' : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup M'] [Module K M'] [FiniteDimensional K M']

/-- The algebraically closed archimedean normal form: a nondegenerate form is a sum of
squares, with one square for each dimension of the underlying vector space. -/
theorem closed_equivalent_squares (Q : QuadraticForm K M)
    (hQ : (associated Q).SeparatingLeft) :
    Equivalent Q
      (weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) :=
  Q.equivalent_weightedSumSquares_of_isAlgClosed hQ

/-- Over an algebraically closed field of characteristic different from two, nondegenerate
quadratic forms are classified by the dimension of their underlying spaces. -/
theorem nondegenerate_equivalent_finrank
    (Q : QuadraticForm K M) (Q' : QuadraticForm K M')
    (hQ : (associated Q).SeparatingLeft)
    (hQ' : (associated Q').SeparatingLeft) :
    Equivalent Q Q' ↔ Module.finrank K M = Module.finrank K M' := by
  constructor
  · exact finrank_equivalent
  · intro hdim
    have hnormal := closed_equivalent_squares Q hQ
    have hnormal' := closed_equivalent_squares Q' hQ'
    rw [hdim] at hnormal
    exact hnormal.trans hnormal'.symm

end AlgebraicallyClosed

section Real

variable {M M' : Type*}
  [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  [AddCommGroup M'] [Module ℝ M'] [FiniteDimensional ℝ M']

/-- Milne's index of negativity is Mathlib's negative signature: the largest dimension of a
subspace on which the form is negative definite. -/
noncomputable def indexOfNegativity (Q : QuadraticForm ℝ M) : ℕ := sigNeg Q

omit [FiniteDimensional ℝ M] in
@[simp] theorem negativity_sig_neg (Q : QuadraticForm ℝ M) :
    indexOfNegativity Q = sigNeg Q := rfl

/-- The index of negativity is attained by a negative-definite subspace and is maximal among
the dimensions of all such subspaces. -/
theorem index_negativity_greatest (Q : QuadraticForm ℝ M) :
    IsGreatest
      {r | ∃ V : Submodule ℝ M, Module.finrank ℝ V = r ∧
        ((-Q).restrict V).PosDef}
      (indexOfNegativity Q) := by
  exact sigNeg_isGreatest Q

/-- The existence part of Sylvester's law: a nondegenerate real form has a diagonalization
whose coefficients are all `-1` or `1`. -/
theorem real_equivalent_squares
    (Q : QuadraticForm ℝ M) (hQ : (associated Q).SeparatingLeft) :
    ∃ w : Fin (Module.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        Equivalent Q (weightedSumSquares ℝ w) :=
  Q.equivalent_one_neg_one_weighted_sum_squared hQ

omit [FiniteDimensional ℝ M] in
/-- In any diagonalization, the index of negativity is exactly the number of negative
coefficients. -/
theorem negativity_negative_coefficients {Q : QuadraticForm ℝ M}
    {I : Type*} [Fintype I] {w : I → ℝ}
    (h : Equivalent Q (weightedSumSquares ℝ w)) :
    indexOfNegativity Q = {i | w i < 0}.ncard := by
  simpa only [indexOfNegativity] using
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares h

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ M'] in
/-- The index of negativity is invariant under equivalence of real quadratic forms. -/
theorem index_negativity_equivalent {Q : QuadraticForm ℝ M}
    {Q' : QuadraticForm ℝ M'} (h : Equivalent Q Q') :
    indexOfNegativity Q = indexOfNegativity Q' := by
  simpa only [indexOfNegativity] using h.sigNeg_eq

omit [FiniteDimensional ℝ M] in
/-- The negative coefficient count is independent of the chosen diagonalization.  This is the
uniqueness part of Sylvester's law of inertia in the form used in the book. -/
theorem negative_count_unique {Q : QuadraticForm ℝ M}
    {I J : Type*} [Fintype I] [Fintype J] {w : I → ℝ} {w' : J → ℝ}
    (h : Equivalent Q (weightedSumSquares ℝ w))
    (h' : Equivalent Q (weightedSumSquares ℝ w')) :
    {i | w i < 0}.ncard = {j | w' j < 0}.ncard := by
  rw [← negativity_negative_coefficients h,
    ← negativity_negative_coefficients h']

/-- Reindexing the variables by an equivalence gives an isometry when the corresponding
weights agree. -/
private def weightedSquaresReindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) {w : I → ℝ} {w' : J → ℝ} (hw : ∀ i, w' (e i) = w i) :
    IsometryEquiv (weightedSumSquares ℝ w) (weightedSumSquares ℝ w') where
  toFun x j := x (e.symm j)
  invFun x i := x (e i)
  left_inv x := by ext i; simp
  right_inv x := by ext j; simp
  map_add' x y := rfl
  map_smul' c x := rfl
  map_app' x := by
    simp only [weightedSumSquares_apply]
    rw [← e.sum_comp]
    simp only [e.symm_apply_apply, hw]

/-- Two `±1` diagonal forms on the same finite index type are equivalent when they have the
same number of negative coefficients. -/
private theorem squares_equivalent_signs
    {I J : Type*} [Fintype I] [Fintype J] {w : I → ℝ} {w' : J → ℝ}
    (hw : ∀ i, w i = -1 ∨ w i = 1) (hw' : ∀ i, w' i = -1 ∨ w' i = 1)
    (hcard : Fintype.card I = Fintype.card J)
    (hneg : {i | w i < 0}.ncard = {i | w' i < 0}.ncard) :
    Equivalent (weightedSumSquares ℝ w) (weightedSumSquares ℝ w') := by
  classical
  have hnegCard : Fintype.card {i // w i < 0} = Fintype.card {j // w' j < 0} := by
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hneg
  let eneg : {i // w i < 0} ≃ {j // w' j < 0} := Fintype.equivOfCardEq hnegCard
  have hnonnegCard : Fintype.card {i // ¬w i < 0} = Fintype.card {j // ¬w' j < 0} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard, hnegCard]
  let enonneg : {i // ¬w i < 0} ≃ {j // ¬w' j < 0} :=
    Fintype.equivOfCardEq hnonnegCard
  let e : I ≃ J :=
    (Equiv.sumCompl fun i ↦ w i < 0).symm |>.trans
      ((Equiv.sumCongr eneg enonneg).trans (Equiv.sumCompl fun j ↦ w' j < 0))
  have e_mem_negative {i : I} (hi : w i < 0) : w' (e i) < 0 := by
    dsimp only [e, Equiv.trans_apply]
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun i ↦ w i < 0) hi]
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (eneg ⟨i, hi⟩).property
  have e_not_mem_negative {i : I} (hi : ¬w i < 0) : ¬w' (e i) < 0 := by
    dsimp only [e, Equiv.trans_apply]
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun i ↦ w i < 0) hi]
    simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact (enonneg ⟨i, hi⟩).property
  have he : ∀ i, w' (e i) = w i := by
    intro i
    rcases hw i with hi | hi <;> rcases hw' (e i) with hj | hj
    · exact hj.trans hi.symm
    · exfalso
      have hi' : w i < 0 := by rw [hi]; norm_num
      have := e_mem_negative hi'
      rw [hj] at this
      norm_num at this
    · exfalso
      have hi' : ¬w i < 0 := by rw [hi]; norm_num
      exact e_not_mem_negative hi' (by rw [hj]; norm_num)
    · exact hj.trans hi.symm
  exact ⟨weightedSquaresReindex e he⟩

/-- For a nondegenerate real form, positive and negative indices add to the dimension. -/
theorem sig_negativity_finrank (Q : QuadraticForm ℝ M)
    (hQ : (associated Q).SeparatingLeft) :
    sigPos Q + indexOfNegativity Q = Module.finrank ℝ M := by
  have hrad : Q.radical = ⊥ := by
    rw [QuadraticMap.radical_eq_ker_associated]
    exact LinearMap.separatingLeft_iff_ker_eq_bot.mp hQ
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hrad, finrank_bot, add_zero] at h
  simpa only [indexOfNegativity] using h

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ M'] in
/-- Equivalence preserves both the dimension and the index of negativity, the two invariants
appearing in the real archimedean classification. -/
theorem equivalent_implies_negativity
    {Q : QuadraticForm ℝ M} {Q' : QuadraticForm ℝ M'} (h : Equivalent Q Q') :
    Module.finrank ℝ M = Module.finrank ℝ M' ∧
      indexOfNegativity Q = indexOfNegativity Q' :=
  ⟨finrank_equivalent h, index_negativity_equivalent h⟩

/-- The real archimedean classification: nondegenerate quadratic forms are equivalent exactly
when they have the same dimension and the same index of negativity. -/
theorem nondegenerate_equivalent_negativity
    (Q : QuadraticForm ℝ M) (Q' : QuadraticForm ℝ M')
    (hQ : (associated Q).SeparatingLeft) (hQ' : (associated Q').SeparatingLeft) :
    Equivalent Q Q' ↔
      Module.finrank ℝ M = Module.finrank ℝ M' ∧
        indexOfNegativity Q = indexOfNegativity Q' := by
  constructor
  · exact equivalent_implies_negativity
  · rintro ⟨hdim, hindex⟩
    obtain ⟨w, hw, hnormal⟩ := real_equivalent_squares Q hQ
    obtain ⟨w', hw', hnormal'⟩ := real_equivalent_squares Q' hQ'
    have hneg : {i | w i < 0}.ncard = {i | w' i < 0}.ncard := by
      rw [← negativity_negative_coefficients hnormal,
        ← negativity_negative_coefficients hnormal']
      exact hindex
    exact hnormal.trans
      ((squares_equivalent_signs hw hw' (by simpa using hdim)
        hneg).trans
        hnormal'.symm)

end Real

end Submission.CField.QForms

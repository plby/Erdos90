import Submission.ClassField.LubinTate.RootValuation

/-!
# Class Field Theory, Chapter I, Proposition 3.4: polynomial surjectivity

For the basic Lubin--Tate polynomial `pi * X + X ^ q`, Milne proves
surjectivity of multiplication by `pi` on the open unit ball by applying the
Newton polygon to `f(X) - alpha`.  The argument below separates that
polynomial assertion from the still-missing analytic construction of the
Lubin--Tate module in an algebraic closure.
-/

namespace Submission.CField.LTate

noncomputable section

open Polynomial
open Submission.CField.FGroups

/-- The basic Lubin--Tate polynomial `pi * X + X ^ q` is monic when
`q > 1`. -/
theorem basic_lubin_monic
    {R : Type*} [CommRing R] [Nontrivial R]
    (pi : R) {q : ℕ} (hq : 1 < q) :
    (basicLubinTate pi q).Monic := by
  have hlowDegree : (C pi * X : R[X]).degree < q :=
    (degree_C_mul_X_le pi).trans_lt (by exact_mod_cast hq)
  rw [basicLubinTate, add_comm]
  exact monic_X_pow_add hlowDegree

/-- The basic Lubin--Tate polynomial has degree `q`. -/
theorem basic_lubin_degree
    {R : Type*} [CommRing R] [Nontrivial R]
    (pi : R) {q : ℕ} (hq : 1 < q) :
    (basicLubinTate pi q).natDegree = q := by
  have hlowDegree : (C pi * X : R[X]).degree < q :=
    (degree_C_mul_X_le pi).trans_lt (by exact_mod_cast hq)
  rw [basicLubinTate, natDegree_add_eq_right_of_degree_lt]
  · simp
  · simpa only [degree_X_pow] using hlowDegree

/-- The basic Lubin--Tate polynomial has no repeated roots when the residue
cardinality condition ensures that `q - 1` is nonzero in the ambient field. -/
theorem basic_lubin_separable
    {L : Type*} [Field L] [IsAlgClosed L] (pi : L) (hpi : pi ≠ 0)
    {q : ℕ} (hq : 1 < q) (hq1 : ((q - 1 : ℕ) : L) ≠ 0) :
    (basicLubinTate pi q).Separable := by
  let g : L[X] := X ^ (q - 1) - C (-pi)
  have hfactor : basicLubinTate pi q = X * g := by
    have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
    have hpow : (X : L[X]) ^ q = X * X ^ (q - 1) := by
      calc
        X ^ q = X ^ (q - 1 + 1) := by rw [hqeq]
        _ = X * X ^ (q - 1) := pow_succ' X (q - 1)
    simp only [basicLubinTate, g, hpow]
    rw [map_neg]
    ring
  have hgsep : g.Separable := by
    exact separable_X_pow_sub_C (-pi) hq1 (neg_ne_zero.mpr hpi)
  have hcoprime : IsCoprime (X : L[X]) g := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (k := L) L X g).2
    intro x
    by_cases hx : x = 0
    · right
      subst x
      have hqsub : 0 < q - 1 := Nat.sub_pos_of_lt hq
      simpa [g, hqsub.ne'] using hpi
    · left
      simpa using hx
  rw [hfactor]
  exact separable_X.mul hgsep hcoprime

/-- The first Lubin--Tate level for the basic polynomial consists of exactly
`q` distinct roots in an algebraically closed field. -/
theorem card_set_lubin
    {L : Type*} [Field L] [IsAlgClosed L]
    (pi : L) (hpi : pi ≠ 0) {q : ℕ}
    (hq : 1 < q) (hq1 : ((q - 1 : ℕ) : L) ≠ 0) :
    Fintype.card ((basicLubinTate pi q).rootSet L) = q := by
  rw [card_rootSet_eq_natDegree
    (basic_lubin_separable pi hpi hq hq1)
    (IsAlgClosed.splits_domain _)]
  exact basic_lubin_degree pi hq

/-- Every root of the basic Lubin--Tate polynomial lies in the valuation-open
unit ball.  This is the first Newton-polygon assertion in Proposition 3.4. -/
theorem valuation_lubin_tate
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (pi : L) {q : ℕ}
    (hq : 1 < q) (hpi : v pi < 1) {x : L}
    (hx : (basicLubinTate pi q).IsRoot x) :
    v x < 1 := by
  let p : L[X] := basicLubinTate pi q
  have hlowDegree : (C pi * X : L[X]).degree < q :=
    (degree_C_mul_X_le pi).trans_lt (by exact_mod_cast hq)
  have hpMonic : p.Monic := by
    change (basicLubinTate pi q).Monic
    rw [basicLubinTate, add_comm]
    exact monic_X_pow_add hlowDegree
  have hpNatDegree : p.natDegree = q := by
    change (basicLubinTate pi q).natDegree = q
    rw [basicLubinTate,
      natDegree_add_eq_right_of_degree_lt]
    · simp
    · simpa only [degree_X_pow] using hlowDegree
  apply valuation_aeval_monic
    (K := L) v hpMonic
  · intro i hi
    have hiq : i ≠ q := ne_of_lt (by simpa [hpNatDegree] using hi)
    by_cases hi1 : i = 1
    · subst i
      simpa [p, basicLubinTate, Nat.ne_of_lt hq] using hpi
    · have hX : X.coeff i = (0 : L) := by
        rw [coeff_X]
        simp [Ne.symm hi1]
      simp [p, basicLubinTate, coeff_X_pow, hiq, hX]
  · simpa [Polynomial.aeval_def, IsRoot] using hx

/-- Every point of valuation less than one has a preimage of valuation less
than one under the basic Lubin--Tate polynomial `pi * X + X ^ q`.

This is the Newton-polygon surjectivity step in Proposition 3.4. -/
theorem lubin_preimage_valuation
    {L Γ : Type*} [Field L] [IsAlgClosed L]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (pi alpha : L) {q : ℕ}
    (hq : 1 < q) (hpi : v pi < 1) (halpha : v alpha < 1) :
    ∃ beta : L, v beta < 1 ∧
      (basicLubinTate pi q).eval beta = alpha := by
  let p : L[X] := X ^ q + (C pi * X - C alpha)
  have hlowDegree : (C pi * X - C alpha : L[X]).degree < q := by
    have hconstant : (C alpha : L[X]).degree ≤ 1 :=
      degree_C_le.trans (by norm_num)
    exact (degree_sub_le (C pi * X) (C alpha)).trans
      (max_le (degree_C_mul_X_le pi) hconstant) |>.trans_lt
        (by exact_mod_cast hq)
  have hpMonic : p.Monic := by
    apply monic_X_pow_add
    exact hlowDegree
  have hpDegree : p.degree = q := by
    change (X ^ q + (C pi * X - C alpha) : L[X]).degree = q
    rw [degree_add_eq_left_of_degree_lt]
    · simp only [degree_X_pow]
    · simpa only [degree_X_pow] using hlowDegree
  have hpNatDegree : p.natDegree = q :=
    natDegree_eq_of_degree_eq_some hpDegree
  have hpDegree0 : p.degree ≠ 0 := by
    rw [hpDegree]
    norm_num [Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)]
  obtain ⟨beta, hbeta⟩ := IsAlgClosed.exists_root p hpDegree0
  have hbetaVal : v beta < 1 := by
    apply valuation_aeval_monic
      (K := L) v hpMonic
    · intro i hi
      have hiq : i ≠ q := ne_of_lt (by simpa [hpNatDegree] using hi)
      by_cases hi0 : i = 0
      · subst i
        have h0q : 0 ≠ q := Nat.ne_of_lt (lt_trans Nat.zero_lt_one hq)
        simpa [p, h0q] using halpha
      by_cases hi1 : i = 1
      · subst i
        simpa [p, Nat.ne_of_lt hq] using hpi
      · have hX : X.coeff i = (0 : L) := by
          rw [coeff_X]
          simp [Ne.symm hi1]
        have hC : (C alpha).coeff i = 0 := by
          simp only [coeff_C]
          rw [if_neg hi0]
        simp [p, coeff_X_pow, hiq, hX, hC]
    · simpa [Polynomial.aeval_def, IsRoot] using hbeta
  refine ⟨beta, hbetaVal, ?_⟩
  have hbeta' : beta ^ q + (pi * beta - alpha) = 0 := by
    simpa [p] using hbeta
  simp only [basicLubinTate, eval_add, eval_mul, eval_C,
    eval_X, eval_pow]
  linear_combination hbeta'

end

end Submission.CField.LTate

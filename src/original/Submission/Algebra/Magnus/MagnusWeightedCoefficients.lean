import Submission.Algebra.Magnus.MagnusWeighted
import Submission.Algebra.Magnus.WeightedSeries


/-!
# Coefficients of the weighted Magnus ideal

This file identifies the closure-defined weighted ideal in the actual Magnus
ring with the coefficientwise divisibility condition used in Section 4 of
Efrat--Chapman.
-/

namespace EChapma
namespace MSeries

variable {R X : Type*} [CommRing R]

/-- The coefficientwise divisibility condition defining the weighted Magnus
ideal through degree `n`. -/
def SatisfiesWeightedCondition
    (e : MDescen) (n : ℕ)
    (f : MSeries R X) : Prop :=
  f 1 = 0 ∧
    ∀ w, 1 ≤ w.length → w.length ≤ n →
      ((e n w.length : ℕ) : R) ∣ f w

/-- Every generator of the weighted Magnus ideal satisfies the corresponding
coefficient divisibility conditions. -/
theorem satisfies_weighted_condition
    (e : MDescen) (n : ℕ)
    {f : MSeries R X}
    (hf : f ∈ weightedIdeal (R := R) (X := X) e n) :
    SatisfiesWeightedCondition e n f := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
      rcases hf with ⟨i, hi, hin, y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · simp [hy 1 (by simpa using hi)]
      · intro w hw hwn
        by_cases hwi : w.length < i
        · rw [nsmul_apply, hy w hwi]
          simp
        · have hiw : i ≤ w.length := Nat.le_of_not_gt hwi
          have hdvd : e n w.length ∣ e n i :=
            e.dvd_of_le hi hiw hwn
          have hcast :
              ((e n w.length : ℕ) : R) ∣ ((e n i : ℕ) : R) :=
            Nat.cast_dvd_cast (α := R) hdvd
          rw [nsmul_apply]
          simpa [nsmul_eq_mul] using
            dvd_mul_of_dvd_left hcast (y w)
  | zero =>
      refine ⟨rfl, ?_⟩
      intro w hw hwn
      exact dvd_zero _
  | add f g hf hg hfc hgc =>
      refine ⟨by simp [hfc.1, hgc.1], ?_⟩
      intro w hw hwn
      exact dvd_add (hfc.2 w hw hwn) (hgc.2 w hw hwn)
  | neg f hf hfc =>
      refine ⟨by simp [hfc.1], ?_⟩
      intro w hw hwn
      exact dvd_neg.mpr (hfc.2 w hw hwn)

/-- For positive `n`, the coefficientwise condition reconstructs an element
of the closure-defined weighted Magnus ideal. -/
theorem weighted_satisfies_condition
    (e : MDescen) {n : ℕ} (hn : 1 ≤ n)
    {f : MSeries R X}
    (hf : SatisfiesWeightedCondition e n f) :
    f ∈ weightedIdeal (R := R) (X := X) e n := by
  classical
  let quotientAtDegree (i : ℕ) : MSeries R X :=
    ⟨fun w =>
      if hi : 1 ≤ i ∧ i < n then
        if hw : w.length = i then
          Classical.choose
            (hf.2 w (by omega) (by omega))
        else 0
      else 0⟩
  let initialPart : MSeries R X :=
    ∑ i ∈ Finset.Ico 1 n, (e n i) • quotientAtDegree i
  let tail : MSeries R X := f - initialPart
  have hquotient
      {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
      VanishesBelow (quotientAtDegree i) i := by
    intro w hw
    simp [quotientAtDegree, hi, hin]
    omega
  have hinitial :
      initialPart ∈ weightedIdeal (R := R) (X := X) e n := by
    apply Ideal.sum_mem
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact
      (magnusAddFiltration (R := R) (X := X)).weightedGenerator_mem
        e hi.1 hi.2.le (hquotient hi.1 hi.2)
  have htail : VanishesBelow tail n := by
    intro w hw
    have hlen : w.length ≤ n := hw.le
    by_cases hwzero : w.length = 0
    · have hwone : w = 1 := FreeMonoid.length_eq_zero.mp hwzero
      subst w
      have hsumzero : initialPart 1 = 0 := by
        simp only [initialPart, sum_apply_series]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_Ico] at hi
        rw [nsmul_apply]
        have hqzero : quotientAtDegree i 1 = 0 :=
          hquotient hi.1 hi.2 1 (by simp; omega)
        simp [hqzero]
      simp [tail, hf.1, hsumzero]
    · have hwpos : 1 ≤ w.length := Nat.one_le_iff_ne_zero.mpr hwzero
      have hwmem : w.length ∈ Finset.Ico 1 n := by
        simpa [Finset.mem_Ico] using And.intro hwpos hw
      have hsum :
          initialPart w =
            (e n w.length) • quotientAtDegree w.length w := by
        simp only [initialPart, sum_apply_series]
        rw [Finset.sum_eq_single w.length]
        · exact nsmul_apply _ _ _
        · intro i hi hine
          rw [Finset.mem_Ico] at hi
          rw [nsmul_apply]
          have hqzero : quotientAtDegree i w = 0 := by
            simp [quotientAtDegree, hi.1, hi.2, Ne.symm hine]
          simp [hqzero]
        · exact fun hnot => (hnot hwmem).elim
      have hchoose :=
        Classical.choose_spec (hf.2 w hwpos hlen)
      have hquotientApply :
          quotientAtDegree w.length w =
            Classical.choose (hf.2 w hwpos hlen) := by
        simp [quotientAtDegree, hwpos, hw]
      change f w - initialPart w = 0
      rw [hsum, hquotientApply]
      simpa [nsmul_eq_mul] using sub_eq_zero.mpr hchoose
  have htailmem :
      tail ∈ weightedIdeal (R := R) (X := X) e n := by
    have hgenerator :=
      (magnusAddFiltration (R := R) (X := X)).weightedGenerator_mem
        e hn le_rfl htail
    simpa [e.diagonal n hn] using hgenerator
  have hdecomp : f = initialPart + tail := by
    simp [tail]
  rw [hdecomp]
  exact Ideal.add_mem _ hinitial htailmem

/-- Coefficient characterization of the actual weighted Magnus ideal. -/
theorem weighted_ideal_coefficients
    (e : MDescen) {n : ℕ} (hn : 1 ≤ n)
    {f : MSeries R X} :
    f ∈ weightedIdeal (R := R) (X := X) e n ↔
      f 1 = 0 ∧
        ∀ w, 1 ≤ w.length → w.length ≤ n →
          ((e n w.length : ℕ) : R) ∣ f w := by
  constructor
  · exact satisfies_weighted_condition e n
  · exact weighted_satisfies_condition e hn

/-- A coefficient in degree `m ≤ n` of an element of the weighted ideal is
divisible by `e(n,m)`. -/
theorem coefficient_dvd_weighted
    (e : MDescen) {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n)
    {f : MSeries R X}
    (hf : f ∈ weightedIdeal (R := R) (X := X) e n)
    {w : FreeMonoid X} (hw : w.length = m) :
    ((e n m : ℕ) : R) ∣ f w := by
  have hn := hm.trans hmn
  simpa [hw] using
    (weighted_ideal_coefficients e hn).mp hf
      |>.2 w (by omega) (by omega)

end MSeries
end EChapma

import Submission.Algebra.FilteredPowers
import Submission.Group.Zassenhaus.RecursiveConditions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn


/-!
# Weighted ideals in recursive filtrations

This file proves the two filtered-ring consequences of conditions (1) and
(2) in Section 6 of Efrat--Chapman.  They are stated for an arbitrary
multiplicative additive filtration and will be applied to the Magnus ring.
-/

namespace EChapma

open scoped Pointwise

variable {A : Type*} [Ring A]

namespace MAFilt

/-- The ordered product of a finite tuple of integer submodules. -/
def orderedSubmoduleProduct {l : ℕ}
    (M : Fin l → Submodule ℤ A) : Submodule ℤ A :=
  (List.ofFn M).prod

@[simp]
theorem ordered_submodule_one
    (M : Fin 1 → Submodule ℤ A) :
    orderedSubmoduleProduct M = M 0 := by
  simp [orderedSubmoduleProduct]

@[simp]
theorem ordered_submodule_succ
    {l : ℕ} (M : Fin (l + 1) → Submodule ℤ A) :
    orderedSubmoduleProduct M =
      M 0 * orderedSubmoduleProduct (fun k : Fin l => M k.succ) := by
  simp [orderedSubmoduleProduct, List.ofFn_succ]

/-- Products of filtration terms land in the term indexed by the sum of
their degrees. -/
theorem ordered_term_product
    (F : MAFilt A)
    {l : ℕ} (hl : 1 ≤ l) (js : Fin l → ℕ) :
    orderedSubmoduleProduct
        (fun k => (F.term (js k)).toIntSubmodule) ≤
      (F.term (∑ k, js k)).toIntSubmodule := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hl0 : l = 0
    · subst l
      simp
    · rw [ordered_submodule_succ]
      rw [Submodule.mul_le]
      intro x hx y hy
      have hy' :
          y ∈ (F.term (∑ k : Fin l, js k.succ)).toIntSubmodule :=
        ih (Nat.one_le_iff_ne_zero.mpr hl0) (fun k : Fin l => js k.succ) hy
      simpa [Fin.sum_univ_succ] using F.mul_mem hx hy'

/-- A product of weighted summands has the product of their integer
coefficients as a common scalar. -/
theorem ordered_weighted_product
    (F : MAFilt A)
    (e : MDescen) (g : ℕ)
    {l : ℕ} (hl : 1 ≤ l) (js : Fin l → ℕ) :
    orderedSubmoduleProduct
        (fun k => F.weightedTermSubmodule e g (js k)) ≤
      (∏ k, (e g (js k) : ℤ)) •
        (F.term (∑ k, js k)).toIntSubmodule := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hl0 : l = 0
    · subst l
      simp [weightedTermSubmodule]
    · rw [ordered_submodule_succ]
      calc
        F.weightedTermSubmodule e g (js 0) *
              orderedSubmoduleProduct
                (fun k : Fin l =>
                  F.weightedTermSubmodule e g (js k.succ)) ≤
            ((e g (js 0) : ℤ) •
                (F.term (js 0)).toIntSubmodule) *
              ((∏ k : Fin l, (e g (js k.succ) : ℤ)) •
                (F.term (∑ k : Fin l, js k.succ)).toIntSubmodule) :=
          mul_le_mul_right
            (ih (Nat.one_le_iff_ne_zero.mpr hl0)
              (fun k : Fin l => js k.succ)) _
        _ = ((e g (js 0) : ℤ) *
              ∏ k : Fin l, (e g (js k.succ) : ℤ)) •
              ((F.term (js 0)).toIntSubmodule *
                (F.term (∑ k : Fin l, js k.succ)).toIntSubmodule) := by
          rw [smul_mul_smul]
        _ ≤ ((e g (js 0) : ℤ) *
              ∏ k : Fin l, (e g (js k.succ) : ℤ)) •
              (F.term (js 0 + ∑ k : Fin l, js k.succ)).toIntSubmodule := by
          apply smul_mono_right
          rw [Submodule.mul_le]
          intro x hx y hy
          exact F.mul_mem hx hy
        _ = (∏ k, (e g (js k) : ℤ)) •
              (F.term (∑ k, js k)).toIntSubmodule := by
          simp [Fin.prod_univ_succ, Fin.sum_univ_succ]

/-- A positive power of an arbitrary supremum expands into the supremum
of all ordered products of its summands. -/
theorem i_sup_submodule
    {ι : Type*} (M : ι → Submodule ℤ A)
    {l : ℕ} (hl : 1 ≤ l) :
    (⨆ i, M i) ^ l ≤
      ⨆ js : Fin l → ι,
        orderedSubmoduleProduct (fun k => M (js k)) := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases hl0 : l = 0
    · subst l
      rw [Submodule.pow_one]
      apply iSup_le
      intro i
      apply le_iSup_of_le (fun _ : Fin 1 => i)
      simp
    · rw [Submodule.pow_succ' (⨆ i, M i) hl0]
      calc
        (⨆ i, M i) * (⨆ i, M i) ^ l ≤
            (⨆ i, M i) *
              (⨆ js : Fin l → ι,
                orderedSubmoduleProduct (fun k => M (js k))) :=
          mul_le_mul_right (ih (Nat.one_le_iff_ne_zero.mpr hl0)) _
        _ = ⨆ i, ⨆ js : Fin l → ι,
              M i * orderedSubmoduleProduct (fun k => M (js k)) := by
          rw [Submodule.iSup_mul]
          apply iSup_congr
          intro i
          rw [Submodule.mul_iSup]
        _ ≤ ⨆ js : Fin (l + 1) → ι,
              orderedSubmoduleProduct (fun k => M (js k)) := by
          apply iSup_le
          intro i
          apply iSup_le
          intro js
          apply le_iSup_of_le (Fin.cons i js)
          simp

/-- Divisibility reverses inclusion between pointwise integer multiples of
an integer submodule. -/
theorem smul_submodule_dvd
    {a b : ℕ} (h : a ∣ b) (M : Submodule ℤ A) :
    (b : ℤ) • M ≤ (a : ℤ) • M := by
  obtain ⟨q, rfl⟩ := h
  intro x hx
  rw [← Submodule.singleton_set_smul] at hx ⊢
  rcases (Submodule.mem_singleton_set_smul
    (N := M) ((a * q : ℕ) : ℤ) x).mp hx with ⟨y, hy, rfl⟩
  apply (Submodule.mem_singleton_set_smul
    (N := M) (a : ℤ) _).mpr
  refine ⟨(q : ℤ) • y, M.smul_mem (q : ℤ) hy, ?_⟩
  simp [mul_smul]

/-- Every pointwise integer multiple of an integer submodule is contained
in that submodule. -/
theorem pointwise_smul_submodule
    (a : ℤ) (M : Submodule ℤ A) :
    a • M ≤ M := by
  intro x hx
  rw [← Submodule.singleton_set_smul] at hx
  rcases (Submodule.mem_singleton_set_smul
    (N := M) a x).mp hx with ⟨y, hy, rfl⟩
  exact M.smul_mem a hy

/-- A single instance of condition (1) gives the corresponding product
inclusion between weighted submodules. -/
theorem weighted_dvd_condition
    (F : MAFilt A)
    (e : MDescen)
    (s t : ℕ)
    (hcomm : ∀ ⦃i j : ℕ⦄,
      1 ≤ i → i ≤ s → 1 ≤ j → j ≤ t →
      e (s + t) (i + j) ∣ e s i * e t j) :
    F.weightedSubmodule e s * F.weightedSubmodule e t ≤
      F.weightedSubmodule e (s + t) := by
  rw [F.submodule_i_sup e s,
    F.submodule_i_sup e t,
    Submodule.iSup_mul]
  apply iSup_le
  intro i
  rw [Submodule.mul_iSup]
  apply iSup_le
  intro j
  rw [F.submodule_i_sup e (s + t)]
  apply le_iSup_of_le
    (⟨i.1 + j.1, by omega, by omega⟩ :
      {k : ℕ // 1 ≤ k ∧ k ≤ s + t})
  calc
    F.weightedTermSubmodule e s i.1 *
          F.weightedTermSubmodule e t j.1 =
        ((e s i.1 : ℤ) * (e t j.1 : ℤ)) •
          ((F.term i.1).toIntSubmodule *
            (F.term j.1).toIntSubmodule) := by
      rw [weightedTermSubmodule, weightedTermSubmodule, smul_mul_smul]
    _ ≤ ((e s i.1 : ℤ) * (e t j.1 : ℤ)) •
          (F.term (i.1 + j.1)).toIntSubmodule := by
      apply smul_mono_right
      rw [Submodule.mul_le]
      intro x hx y hy
      exact F.mul_mem hx hy
    _ ≤ (e (s + t) (i.1 + j.1) : ℤ) •
          (F.term (i.1 + j.1)).toIntSubmodule := by
      simpa [Nat.cast_mul] using
        smul_submodule_dvd
          (A := A)
          (hcomm i.property.1 i.property.2
            j.property.1 j.property.2)
          (F.term (i.1 + j.1)).toIntSubmodule
    _ = F.weightedTermSubmodule e (s + t) (i.1 + j.1) := rfl

/-- Condition (1) from Section 6 gives the corresponding product
inclusion between weighted submodules. -/
theorem weighted_submodule_condition
    (F : MAFilt A)
    (e : MDescen)
    (hcomm : e.HCCondit)
    (s t : ℕ) :
    F.weightedSubmodule e s * F.weightedSubmodule e t ≤
      F.weightedSubmodule e (s + t) :=
  F.weighted_dvd_condition e s t
    fun {_i _j} hi his hj hjt => hcomm hi his hj hjt

/-- Condition (2) from Section 6 controls each nonconstant binomial term
of a power of an arbitrary element of the weighted submodule. -/
theorem choose_submodule_condition
    (F : MAFilt A)
    (e : MDescen)
    (f g : ℕ → ℕ)
    (hpower : e.HasPowerCondition f g)
    {n l : ℕ} (hn : 2 ≤ n) (hl : 1 ≤ l) (hlf : l ≤ f n) :
    (Nat.choose (f n) l : ℤ) •
        (F.weightedSubmodule e (g n)) ^ l ≤
      F.weightedSubmodule e n := by
  rw [F.submodule_i_sup e (g n)]
  calc
    (Nat.choose (f n) l : ℤ) •
          (⨆ i : {i : ℕ // 1 ≤ i ∧ i ≤ g n},
            F.weightedTermSubmodule e (g n) i.1) ^ l ≤
        (Nat.choose (f n) l : ℤ) •
          (⨆ js : Fin l → {i : ℕ // 1 ≤ i ∧ i ≤ g n},
            orderedSubmoduleProduct
              (fun k => F.weightedTermSubmodule e (g n) (js k).1)) := by
      apply smul_mono_right
      exact i_sup_submodule
        (fun i : {i : ℕ // 1 ≤ i ∧ i ≤ g n} =>
          F.weightedTermSubmodule e (g n) i.1) hl
    _ = ⨆ js : Fin l → {i : ℕ // 1 ≤ i ∧ i ≤ g n},
          (Nat.choose (f n) l : ℤ) •
            orderedSubmoduleProduct
              (fun k => F.weightedTermSubmodule e (g n) (js k).1) := by
      rw [Submodule.smul_iSup']
    _ ≤ F.weightedSubmodule e n := by
      apply iSup_le
      intro js
      let degrees : Fin l → ℕ := fun k => (js k).1
      let total : ℕ := ∑ k, degrees k
      let coefficient : ℕ :=
        Nat.choose (f n) l * ∏ k, e (g n) (degrees k)
      calc
        (Nat.choose (f n) l : ℤ) •
              orderedSubmoduleProduct
                (fun k =>
                  F.weightedTermSubmodule e (g n) (js k).1) ≤
            (Nat.choose (f n) l : ℤ) •
              ((∏ k, (e (g n) (degrees k) : ℤ)) •
                (F.term total).toIntSubmodule) := by
          apply smul_mono_right
          simpa [degrees, total] using
            F.ordered_weighted_product e (g n) hl degrees
        _ = (coefficient : ℤ) •
              (F.term total).toIntSubmodule := by
          simp [coefficient, Nat.cast_mul, Nat.cast_prod, smul_smul]
        _ ≤ F.weightedSubmodule e n := by
          by_cases htotal : total ≤ n
          · have hdiv :
                e n total ∣ coefficient := by
              exact hpower hn hl hlf degrees
                (fun k => (js k).property.1)
                (fun k => (js k).property.2)
                htotal
            calc
              (coefficient : ℤ) •
                    (F.term total).toIntSubmodule ≤
                  (e n total : ℤ) •
                    (F.term total).toIntSubmodule :=
                smul_submodule_dvd hdiv _
              _ = F.weightedTermSubmodule e n total := rfl
              _ ≤ F.weightedSubmodule e n := by
                rw [F.submodule_i_sup e n]
                exact le_iSup
                  (fun i : {i : ℕ // 1 ≤ i ∧ i ≤ n} =>
                    F.weightedTermSubmodule e n i.1)
                  ⟨total,
                    (show 1 ≤ total by
                      let k : Fin l := ⟨0, hl⟩
                      have hk : degrees k ≤ total := by
                        have hk' : degrees k ≤ ∑ j, degrees j :=
                          Finset.single_le_sum
                            (f := degrees)
                            (fun _ _ => Nat.zero_le _)
                            (Finset.mem_univ k)
                        simpa [total] using hk'
                      exact (js k).property.1.trans hk),
                    htotal⟩
          · have hdeep :
                (F.term total).toIntSubmodule ≤
                  (F.term n).toIntSubmodule :=
              F.antitone (Nat.le_of_not_ge htotal)
            calc
              (coefficient : ℤ) •
                    (F.term total).toIntSubmodule ≤
                  (coefficient : ℤ) •
                    (F.term n).toIntSubmodule :=
                (smul_mono_right (coefficient : ℤ)) hdeep
              _ ≤ (F.term n).toIntSubmodule :=
                pointwise_smul_submodule _ _
              _ = F.weightedTermSubmodule e n n := by
                simp [weightedTermSubmodule, e.diagonal n (by omega)]
              _ ≤ F.weightedSubmodule e n := by
                rw [F.submodule_i_sup e n]
                exact le_iSup
                  (fun i : {i : ℕ // 1 ≤ i ∧ i ≤ n} =>
                    F.weightedTermSubmodule e n i.1)
                  ⟨n, by omega, le_rfl⟩

/-- Elementwise form of the power-condition bound. -/
theorem choose_nsmul_condition
    (F : MAFilt A)
    (e : MDescen)
    (f g : ℕ → ℕ)
    (hpower : e.HasPowerCondition f g)
    {n l : ℕ} (hn : 2 ≤ n) (hl : 1 ≤ l) (hlf : l ≤ f n)
    {x : A} (hx : x ∈ F.weightedSubgroup e (g n)) :
    Nat.choose (f n) l • x ^ l ∈ F.weightedSubgroup e n := by
  have hxpow :
      x ^ l ∈ (F.weightedSubmodule e (g n)) ^ l :=
    Submodule.pow_mem_pow (F.weightedSubmodule e (g n)) hx l
  have hscaled :
      (Nat.choose (f n) l : ℤ) • x ^ l ∈
        (Nat.choose (f n) l : ℤ) •
          (F.weightedSubmodule e (g n)) ^ l :=
    Submodule.smul_mem_pointwise_smul _ _ _ hxpow
  have hmem :=
    F.choose_submodule_condition
      e f g hpower hn hl hlf hscaled
  simpa [weightedSubmodule] using hmem

/-- The nonconstant binomial tail for an arbitrary exponent. -/
def powerConditionTail (m : ℕ) (x : A) : A :=
  ∑ k ∈ Finset.range m,
    Nat.choose m (k + 1) • x ^ (k + 1)

/-- The arbitrary-exponent tail is `(1+x)^m-1`. -/
theorem sub_condition_tail
    (m : ℕ) (x : A) :
    (1 + x) ^ m - 1 = powerConditionTail m x := by
  rw [add_comm 1 x, (Commute.one_right x).add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ']
  simp [powerConditionTail, nsmul_eq_mul, Nat.cast_comm]

/-- Condition (2) puts the complete nonconstant binomial tail in the
target weighted subgroup. -/
theorem condition_weighted_subgroup
    (F : MAFilt A)
    (e : MDescen)
    (f g : ℕ → ℕ)
    (hpower : e.HasPowerCondition f g)
    {n : ℕ} (hn : 2 ≤ n)
    {x : A} (hx : x ∈ F.weightedSubgroup e (g n)) :
    powerConditionTail (f n) x ∈ F.weightedSubgroup e n := by
  apply (F.weightedSubgroup e n).sum_mem
  intro k hk
  rw [Finset.mem_range] at hk
  exact F.choose_nsmul_condition
    e f g hpower hn (by omega) (by omega) hx

end MAFilt

end EChapma

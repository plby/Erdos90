import Towers.ClassField.FormalGroups.LubinDegreeCorrection

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ τ : Type*} [CommRing R]

theorem nat_order_mul
    {A B : MvPowerSeries τ R} {m n : ℕ}
    (hA : (m : ℕ∞) ≤ A.order) (hB : (n : ℕ∞) ≤ B.order) :
    (m + n : ℕ) ≤ (A * B).order := by
  calc
    (m + n : ℕ∞) = (m : ℕ∞) + (n : ℕ∞) := by simp
    _ ≤ A.order + B.order := add_le_add hA hB
    _ ≤ (A * B).order := le_order_mul

theorem order_sub
    {A B : MvPowerSeries τ R} {n : ℕ}
    (hA : (n : ℕ∞) ≤ A.order) (hB : (n : ℕ∞) ≤ B.order) :
    (n : ℕ∞) ≤ (A - B).order := by
  rw [sub_eq_add_neg]
  refine (le_min hA ?_).trans min_order_le_add
  simpa using hB

theorem nat_finset_sum
    {ι : Type*} {s : Finset ι} {A : ι → MvPowerSeries τ R} {n : ℕ}
    (hA : ∀ i ∈ s, (n : ℕ∞) ≤ (A i).order) :
    (n : ℕ∞) ≤ (∑ i ∈ s, A i).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply coeff_of_lt_order
  exact (by exact_mod_cast hd : (d.degree : ℕ∞) < n) |>.trans_le (hA i hi)

theorem nat_order_sub
    {A B : MvPowerSeries τ R} (hA0 : constantCoeff A = 0)
    (hB0 : constantCoeff B = 0) {m : ℕ} (hm : m ≠ 0)
    (hdiff : (2 : ℕ∞) ≤ (A - B).order) :
    (m + 1 : ℕ) ≤ (A ^ m - B ^ m).order := by
  let S : MvPowerSeries τ R :=
    ∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i)
  have hterm : ∀ i ∈ Finset.range m,
      ((m - 1 : ℕ) : ℕ∞) ≤ (A ^ i * B ^ (m - 1 - i)).order := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hAi : (i : ℕ∞) ≤ (A ^ i).order :=
      le_order_pow_of_constantCoeff_eq_zero i hA0
    have hBi : ((m - 1 - i : ℕ) : ℕ∞) ≤ (B ^ (m - 1 - i)).order :=
      le_order_pow_of_constantCoeff_eq_zero (m - 1 - i) hB0
    have hmul := nat_order_mul hAi hBi
    have hsum : i + (m - 1 - i) = m - 1 := by omega
    simpa only [hsum] using hmul
  have hS : ((m - 1 : ℕ) : ℕ∞) ≤ S.order :=
    nat_finset_sum hterm
  have hprod : ((m + 1 : ℕ) : ℕ∞) ≤ ((A - B) * S).order := by
    have hmul := nat_order_mul hdiff hS
    have hsum : 2 + (m - 1) = m + 1 := by omega
    simpa only [hsum] using hmul
  rw [mul_comm, geom_sum₂_mul] at hprod
  exact hprod

theorem nat_succ_sub
    {ι : Type*} {s : Finset ι} {w : ι → ℕ}
    {A B : ι → MvPowerSeries τ R}
    (hA : ∀ i ∈ s, (w i : ℕ∞) ≤ (A i).order)
    (hB : ∀ i ∈ s, (w i : ℕ∞) ≤ (B i).order)
    (hdiff : ∀ i ∈ s, ((w i + 1 : ℕ) : ℕ∞) ≤ (A i - B i).order) :
    ((∑ i ∈ s, w i) + 1 : ℕ) ≤
      ((∏ i ∈ s, A i) - ∏ i ∈ s, B i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hAis : (w i : ℕ∞) ≤ (A i).order := hA i (Finset.mem_insert_self i s)
      have hBis : (w i : ℕ∞) ≤ (B i).order := hB i (Finset.mem_insert_self i s)
      have hdis : ((w i + 1 : ℕ) : ℕ∞) ≤ (A i - B i).order :=
        hdiff i (Finset.mem_insert_self i s)
      have hiA := ih
        (fun j hj ↦ hA j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hB j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hdiff j (Finset.mem_insert_of_mem hj))
      have hprodA : ((∑ j ∈ s, w j : ℕ) : ℕ∞) ≤ (∏ j ∈ s, A j).order := by
        calc
          ((∑ j ∈ s, w j : ℕ) : ℕ∞) = ∑ j ∈ s, (w j : ℕ∞) := by simp
          _ ≤ ∑ j ∈ s, (A j).order :=
            Finset.sum_le_sum fun j hj ↦ hA j (Finset.mem_insert_of_mem hj)
          _ ≤ (∏ j ∈ s, A j).order := le_order_prod A s
      have hfirst :
          ((w i + (∑ j ∈ s, w j) + 1 : ℕ) : ℕ∞) ≤
            ((A i - B i) * ∏ j ∈ s, A j).order := by
        have hmul := nat_order_mul hdis hprodA
        have hsum : (w i + 1) + ∑ j ∈ s, w j =
            w i + (∑ j ∈ s, w j) + 1 := by omega
        simpa only [hsum] using hmul
      have hsecond :
          ((w i + (∑ j ∈ s, w j) + 1 : ℕ) : ℕ∞) ≤
            (B i * ((∏ j ∈ s, A j) - ∏ j ∈ s, B j)).order := by
        have hmul := nat_order_mul hBis hiA
        have hsum : w i + ((∑ j ∈ s, w j) + 1) =
            w i + (∑ j ∈ s, w j) + 1 := by omega
        simpa only [hsum] using hmul
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have hid :
          A i * (∏ j ∈ s, A j) - B i * ∏ j ∈ s, B j =
            (A i - B i) * (∏ j ∈ s, A j) +
              B i * ((∏ j ∈ s, A j) - ∏ j ∈ s, B j) := by ring
      rw [hid]
      have hsum : ∑ j ∈ insert i s, w j + 1 =
          w i + (∑ j ∈ s, w j) + 1 := by simp [hi]
      rw [hsum]
      exact (le_min hfirst hsecond).trans min_order_le_add

theorem nat_finsupp_sub
    {a b : σ → MvPowerSeries τ R}
    (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (2 : ℕ∞) ≤ (a i - b i).order)
    (e : σ →₀ ℕ) :
    (e.degree + 1 : ℕ) ≤
      (e.prod (fun i m ↦ (a i) ^ m) -
        e.prod (fun i m ↦ (b i) ^ m)).order := by
  classical
  apply nat_succ_sub
  · intro i hi
    exact le_order_pow_of_constantCoeff_eq_zero (e i) (ha0 i)
  · intro i hi
    exact le_order_pow_of_constantCoeff_eq_zero (e i) (hb0 i)
  · intro i hi
    exact nat_order_sub (ha0 i) (hb0 i)
      (Finsupp.mem_support_iff.mp hi) (hab i)

/-- The degree-`n` part of a homogeneous series depends only on the linear
parts of the series substituted for its variables. -/
theorem homogeneous_component_congr
    {a b : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (hb : HasSubst b)
    (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (2 : ℕ∞) ≤ (a i - b i).order)
    {H : MvPowerSeries σ R} {n : ℕ} (hH : IsHomogeneous H n) :
    homogeneousComponent n (subst a H) =
      homogeneousComponent n (subst b H) := by
  ext d
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with hd
  · rw [coeff_subst ha, coeff_subst hb]
    apply finsum_congr
    intro e
    by_cases he : coeff e H = 0
    · simp [he]
    · have hedeg : e.degree = n := by
        simpa only [Finsupp.degree_eq_weight_one] using hH he
      congr 1
      apply coeff_degree_sub
      have hord := nat_finsupp_sub ha0 hb0 hab e
      exact (show (d.degree : ℕ∞) < e.degree + 1 by
        rw [hd, hedeg]
        exact_mod_cast Nat.lt_succ_self n).trans_le hord
  · rfl

end

end Towers.CField.FGroups

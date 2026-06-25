import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Choose.Factorization
import Towers.Group.Zassenhaus.MultiplicativelyDescending

/-!
# Numerical conditions for recursively defined filtrations

This file packages conditions (1) and (2) from Section 6 of
Efrat--Chapman and verifies the first condition for the logarithmic
prime-power coefficients used by the q-Zassenhaus filtration.
-/

namespace EChapma

namespace MDescen

/-- Condition (1) from Section 6, restricted to the chosen set of
commutator pairs. -/
def CommutatorCondition
    (e : MDescen) (T : Set (ℕ × ℕ)) : Prop :=
  ∀ ⦃s t i j : ℕ⦄,
    (s, t) ∈ T →
    1 ≤ i →
    i ≤ s →
    1 ≤ j →
    j ≤ t →
    e (s + t) (i + j) ∣ e s i * e t j

/-- Condition (1) from Section 6, in its strongest form with all pairs `(s,t)`. -/
def HCCondit (e : MDescen) : Prop :=
  ∀ ⦃s t i j : ℕ⦄,
    1 ≤ i →
    i ≤ s →
    1 ≤ j →
    j ≤ t →
    e (s + t) (i + j) ∣ e s i * e t j

/-- The unrestricted condition implies the condition on every chosen set
of commutator pairs. -/
theorem HCCondit.on
    {e : MDescen}
    (h : e.HCCondit) (T : Set (ℕ × ℕ)) :
    e.CommutatorCondition T := by
  intro s t i j _ hi his hj hjt
  exact h hi his hj hjt

/-- Condition (2) from Section 6. -/
def HasPowerCondition
    (e : MDescen) (f g : ℕ → ℕ) : Prop :=
  ∀ ⦃n l : ℕ⦄,
    2 ≤ n →
    1 ≤ l →
    l ≤ f n →
    ∀ js : Fin l → ℕ,
      (∀ k, 1 ≤ js k) →
      (∀ k, js k ≤ g n) →
      (∑ k, js k) ≤ n →
      e n (∑ k, js k) ∣
        Nat.choose (f n) l * ∏ k, e (g n) (js k)

/-- The specialization of condition (1) used for the A-filtration. -/
def HasACondition (e : MDescen) : Prop :=
  ∀ ⦃s i : ℕ⦄,
    1 ≤ i →
    i ≤ s →
    e (s + 1) (i + 1) ∣ e s i

/--
Enlarging the set of available sequence entries while keeping the subset
cardinality fixed can only decrease the gcd.
-/
theorem sequence_coefficient_dvd
    (A : ℕ → ℕ) {s i : ℕ} (hi : 1 ≤ i) (his : i ≤ s) :
    sequenceCoefficient A (s + 1) (i + 1) ∣
      sequenceCoefficient A s i := by
  unfold sequenceCoefficient
  rw [Finset.dvd_gcd_iff]
  intro J hJ
  apply Finset.gcd_dvd
  rw [Finset.mem_powersetCard] at hJ ⊢
  constructor
  · intro x hx
    have hxold := hJ.1 hx
    simp only [Finset.mem_Icc] at hxold ⊢
    omega
  · simpa only [Nat.add_sub_add_right] using hJ.2

/--
Adding the last sequence entry gives the divisibility needed for the
one-factor case of the A-filtration power condition.
-/
theorem sequence_dvd_last
    (A : ℕ → ℕ) {s i : ℕ} (hi : 1 ≤ i) (his : i ≤ s) :
    sequenceCoefficient A (s + 1) i ∣
      A s * sequenceCoefficient A s i := by
  unfold sequenceCoefficient
  rw [show
    A s *
        ((Finset.Icc 1 (s - 1)).powersetCard (s - i)).gcd
          (fun J => ∏ j ∈ J, A j) =
      ((Finset.Icc 1 (s - 1)).powersetCard (s - i)).gcd
        (fun J => A s * ∏ j ∈ J, A j) by
      rw [Finset.gcd_mul_left]
      simp]
  rw [Finset.dvd_gcd_iff]
  intro J hJ
  have hsJ : s ∉ J := by
    intro hs
    have := (Finset.mem_powersetCard.mp hJ).1 hs
    simp only [Finset.mem_Icc] at this
    omega
  have hnew :
      insert s J ∈
        (Finset.Icc 1 (s + 1 - 1)).powersetCard (s + 1 - i) := by
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp [hi.trans his]
      · have hxold := (Finset.mem_powersetCard.mp hJ).1 hx
        simp only [Finset.mem_Icc] at hxold ⊢
        omega
    · rw [Finset.card_insert_of_notMem hsJ]
      rw [(Finset.mem_powersetCard.mp hJ).2]
      omega
  have hdvd :=
    Finset.gcd_dvd
      (f := fun K => ∏ j ∈ K, A j) hnew
  simpa [Finset.prod_insert, hsJ, mul_comm] using hdvd

/-- Condition (1) for the sequence coefficients used by the A-filtration. -/
theorem sequence_commutator_condition (A : ℕ → ℕ) :
    (ofSequence A).HasACondition := by
  intro s i hi his
  exact sequence_coefficient_dvd A hi his

/-- Condition (2) for the sequence coefficients used by the A-filtration. -/
theorem sequence_power_condition (A : ℕ → ℕ) :
    (ofSequence A).HasPowerCondition
      (fun n => A (n - 1)) (fun n => n - 1) := by
  intro n l hn hl hlA js hjs hjs_upper hsum
  by_cases hl2 : 2 ≤ l
  · let k₀ : Fin l := ⟨0, by omega⟩
    let k₁ : Fin l := ⟨1, hl2⟩
    have hkne : k₀ ≠ k₁ := by
      intro h
      have := congrArg Fin.val h
      simp [k₀, k₁] at this
    have hpair :
        js k₀ + js k₁ ≤ ∑ k, js k := by
      calc
        js k₀ + js k₁ = ∑ k ∈ ({k₀, k₁} : Finset (Fin l)), js k :=
          (Finset.sum_pair hkne).symm
        _ ≤ ∑ k, js k :=
          Finset.sum_le_sum_of_subset (by simp)
    have hindex : js k₀ + 1 ≤ ∑ k, js k :=
      (Nat.add_le_add_left (hjs k₁) (js k₀)).trans hpair
    have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hstep :
        sequenceCoefficient A n (js k₀ + 1) ∣
          sequenceCoefficient A (n - 1) (js k₀) := by
      rw [← hn_eq]
      exact sequence_coefficient_dvd A
        (hjs k₀) (hjs_upper k₀)
    have htarget :
        sequenceCoefficient A n (∑ k, js k) ∣
          sequenceCoefficient A (n - 1) (js k₀) := by
      exact
        ((ofSequence A).dvd_of_le (by omega) hindex hsum).trans hstep
    have hfactor :
        sequenceCoefficient A (n - 1) (js k₀) ∣
          ∏ k, sequenceCoefficient A (n - 1) (js k) :=
      Finset.dvd_prod_of_mem
        (fun k => sequenceCoefficient A (n - 1) (js k))
        (Finset.mem_univ k₀)
    exact dvd_mul_of_dvd_right (htarget.trans hfactor) _
  · have hl1 : l = 1 := by omega
    subst l
    have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    rw [← hn_eq]
    simpa [mul_comm] using
      sequence_dvd_last A
        (hjs 0) (hjs_upper 0)

/--
The least exponent needed for `s+t` at index `i+j` is at most the sum
of the exponents needed separately for `(s,i)` and `(t,j)`.
-/
theorem ceiling_log_add
    (p : ℕ) (hp : p.Prime)
    {s t i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ceilingLogExponent p hp (s + t) (i + j) ≤
      ceilingLogExponent p hp s i + ceilingLogExponent p hp t j := by
  let a := ceilingLogExponent p hp s i
  let b := ceilingLogExponent p hp t j
  apply ceiling_log p hp (by omega)
  calc
    s + t ≤ i * p ^ a + j * p ^ b :=
      Nat.add_le_add
        (mul_ceiling_log p hp s i hi)
        (mul_ceiling_log p hp t j hj)
    _ ≤ i * p ^ (a + b) + j * p ^ (a + b) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left i <|
          Nat.pow_le_pow_right hp.pos (by omega))
        (Nat.mul_le_mul_left j <|
          Nat.pow_le_pow_right hp.pos (by omega))
    _ = (i + j) * p ^ (a + b) := (Nat.add_mul _ _ _).symm

/-- Condition (1) for the logarithmic prime-power coefficients (Lemma 8.2(1)). -/
theorem logarithmic_commutator_condition
    (p r : ℕ) (hp : p.Prime) :
    (logarithmicPrimePower p r hp).HCCondit := by
  intro s t i j hi his hj hjt
  simp only [logarithmic_prime_power]
  rw [← pow_add]
  apply pow_dvd_pow
  simpa [Nat.mul_add] using
    Nat.mul_le_mul_left r
      (ceiling_log_add p hp hi hj)

/--
Summing the defining inequalities for the logarithmic exponents gives a
single inequality for the sum of the indices.
-/
theorem ceiling_log_exponent
    (p : ℕ) (hp : p.Prime) (g l : ℕ)
    (js : Fin l → ℕ) (hjs : ∀ k, 1 ≤ js k) :
    l * g ≤
      (∑ k, js k) *
        p ^ ∑ k, ceilingLogExponent p hp g (js k) := by
  let a : Fin l → ℕ := fun k => ceilingLogExponent p hp g (js k)
  calc
    l * g = ∑ _k : Fin l, g := by simp
    _ ≤ ∑ k, js k * p ^ a k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_ceiling_log p hp g (js k) (hjs k)
    _ ≤ ∑ k, js k * p ^ ∑ k, a k := by
      apply Finset.sum_le_sum
      intro k hk
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right hp.pos
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ = (∑ k, js k) * p ^ ∑ k, a k := by
      rw [Finset.sum_mul]

private theorem one_sum_forall
    {l : ℕ} (hl : 1 ≤ l) (js : Fin l → ℕ)
    (hjs : ∀ k, 1 ≤ js k) :
    1 ≤ ∑ k, js k := by
  let k : Fin l := ⟨0, hl⟩
  exact (hjs k).trans <|
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

private theorem prime_dvd_choose
    (p r l : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    (hl : 1 ≤ l) (hlp : l < p) :
    p ^ r ∣ Nat.choose (p ^ r) l := by
  have hp_le_pow : p ≤ p ^ r := by
    simpa using Nat.pow_le_pow_right hp.pos hr
  have hlpow : l ≤ p ^ r := hlp.le.trans hp_le_pow
  have hchoose0 : Nat.choose (p ^ r) l ≠ 0 :=
    Nat.choose_ne_zero hlpow
  apply (hp.pow_dvd_iff_le_factorization hchoose0).mpr
  rw [Nat.factorization_choose_prime_pow hp hlpow (Nat.ne_of_gt hl)]
  rw [Nat.factorization_eq_zero_of_lt hlp]
  simp

/-- Condition (2) for the logarithmic prime-power coefficients (Lemma 8.2(2)). -/
theorem logarithmic_prime_condition
    (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    (logarithmicPrimePower p r hp).HasPowerCondition
      (fun _ => p ^ r) (fun n => n ⌈/⌉ p) := by
  intro n l hn hl hlq js hjs hjs_upper hsum
  let g := n ⌈/⌉ p
  let a : Fin l → ℕ := fun k =>
    ceilingLogExponent p hp g (js k)
  let A := ∑ k, a k
  let S := ∑ k, js k
  have hS : 1 ≤ S := by
    exact one_sum_forall hl js hjs
  have hng : n ≤ p * g := by
    exact (ceilDiv_le_iff_le_mul hp.pos).mp le_rfl
  have hlg : l * g ≤ S * p ^ A := by
    simpa [g, a, A, S] using
      ceiling_log_exponent p hp g l js hjs
  simp only [logarithmic_prime_power]
  rw [Finset.prod_pow_eq_pow_sum]
  by_cases hpl : p ≤ l
  · have hn_bound : n ≤ S * p ^ A := by
      exact hng.trans <|
        (Nat.mul_le_mul_right g hpl).trans hlg
    have htarget :
        ceilingLogExponent p hp n S ≤ A :=
      ceiling_log p hp hS hn_bound
    have hpow :
        p ^ (r * ceilingLogExponent p hp n S) ∣
          p ^ ∑ k, r * a k := by
      apply pow_dvd_pow
      simpa [A, Finset.mul_sum] using
        Nat.mul_le_mul_left r htarget
    exact dvd_mul_of_dvd_right hpow _
  · have hlp : l < p := Nat.lt_of_not_ge hpl
    have hg_bound : g ≤ S * p ^ A := by
      exact (Nat.le_mul_of_pos_left g hl).trans hlg
    have hn_bound : n ≤ S * p ^ (A + 1) := by
      calc
        n ≤ p * g := hng
        _ ≤ p * (S * p ^ A) := Nat.mul_le_mul_left p hg_bound
        _ = S * p ^ (A + 1) := by
          rw [pow_succ]
          ac_rfl
    have htarget :
        ceilingLogExponent p hp n S ≤ A + 1 :=
      ceiling_log p hp hS hn_bound
    have htarget_exp :
        r * ceilingLogExponent p hp n S ≤
          r + ∑ k, r * a k := by
      calc
        r * ceilingLogExponent p hp n S ≤ r * (A + 1) :=
          Nat.mul_le_mul_left r htarget
        _ = r + ∑ k, r * a k := by
          simp [A, Finset.mul_sum, Nat.mul_add, Nat.add_comm]
    have hpow :
        p ^ (r * ceilingLogExponent p hp n S) ∣
          p ^ r * p ^ ∑ k, r * a k := by
      rw [← pow_add]
      exact pow_dvd_pow p htarget_exp
    have hchoose :
        p ^ r ∣ Nat.choose (p ^ r) l :=
      prime_dvd_choose p r l hp hr hl hlp
    exact hpow.trans (Nat.mul_dvd_mul_right hchoose _)

end MDescen

end EChapma

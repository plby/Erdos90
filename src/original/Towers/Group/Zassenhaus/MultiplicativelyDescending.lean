import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Finset.Powerset

/-!
# Multiplicatively descending maps

This file formalizes Section 3 of Efrat--Chapman, *Filtrations of free groups arising
from the lower central series* (arXiv:1601.08006).

The paper indexes its maps only on pairs `(n, i)` with `1 ≤ i ≤ n`.  We use a total
function `ℕ → ℕ → ℕ`; all axioms and definitions explicitly retain the paper's
index restrictions.
-/

namespace EChapma

/-- A multiplicatively descending map (Definition 3.1 of Efrat--Chapman).

The divisibility convention is the one used in the paper:
`e n (i + 1) ∣ e n i`. -/
structure MDescen where
  toFun : ℕ → ℕ → ℕ
  diagonal : ∀ n, 1 ≤ n → toFun n n = 1
  adjacent_dvd : ∀ n i, 1 ≤ i → i < n → toFun n (i + 1) ∣ toFun n i

namespace MDescen

instance : CoeFun MDescen (fun _ => ℕ → ℕ → ℕ) :=
  ⟨MDescen.toFun⟩

/-- Divisibility extends from adjacent indices to arbitrary valid indices. -/
theorem dvd_of_le (e : MDescen) {n i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) :
    e n j ∣ e n i := by
  induction hij with
  | refl => exact dvd_rfl
  | @step j hij ih =>
      exact (e.adjacent_dvd n j (hi.trans hij) (Nat.lt_of_succ_le hjn)).trans
        (ih ((Nat.le_succ j).trans hjn))

/-- A multiplicatively descending map is binomial when the divisibility in
Definition 3.6 holds. -/
def IsBinomial (e : MDescen) : Prop :=
  ∀ ⦃n i l : ℕ⦄,
    1 ≤ i →
    i ≤ n →
    1 ≤ l →
    l ≤ e n i →
    i * l ≤ n →
    e n (i * l) ∣ Nat.choose (e n i) l

/-- The trivial multiplicatively descending map (Example 3.2). -/
def trivial : MDescen where
  toFun n i := if i = n then 1 else 0
  diagonal n _ := if_pos rfl
  adjacent_dvd n i _hi hin := by
    by_cases hsucc : i + 1 = n
    · simp [hsucc, hin.ne]
    · simp [hsucc, hin.ne]

theorem trivial_apply_lt {n i : ℕ} (h : i < n) : trivial n i = 0 := by
  simp [trivial, h.ne]

theorem trivial_apply_diagonal {n : ℕ} : trivial n n = 1 := by
  simp [trivial]

/-- Example 3.2: the trivial multiplicatively descending map is binomial. -/
theorem trivial_isBinomial : trivial.IsBinomial := by
  intro n i l hi hin hl hle hil
  have hilower : i ≤ i * l := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right i hl
  have hEq : i * l = n := by
    by_contra hne
    have hilt : i * l < n := lt_of_le_of_ne hil hne
    have hit : i < n := lt_of_le_of_lt hilower hilt
    simp [trivial_apply_lt hit] at hle
    omega
  subst n
  simp [trivial_apply_diagonal]

/-- The constant-power example `e(n,i) = a^(n-i)` (Example 3.4). -/
def constantPower (a : ℕ) : MDescen where
  toFun n i := a ^ (n - i)
  diagonal n _ := by simp
  adjacent_dvd n i _hi hin := by
    have hsub : n - i = (n - (i + 1)) + 1 := by omega
    rw [hsub, pow_succ]
    exact dvd_mul_right _ _

@[simp] theorem constantPower_apply (a n i : ℕ) :
    constantPower a n i = a ^ (n - i) := rfl

/-- The valuation hypothesis (iii) from Lemma 3.7, written with natural-number
prime factorizations.  On nonzero inputs this is exactly the paper's `p`-adic
valuation condition. -/
def HasValuationCondition (e : MDescen) : Prop :=
  ∀ ⦃n i r p : ℕ⦄,
    1 ≤ i →
    i * p ^ r ≤ n →
    p.Prime →
    e n i ≠ 0 →
    r ≤ (e n i).factorization p →
    (e n (i * p ^ r)).factorization p ≤ (e n i).factorization p - r

private theorem factorization_choose_bound {a l p : ℕ}
    (hl : l ≤ a) (hl0 : l ≠ 0) :
    a.factorization p - l.factorization p ≤ (Nat.choose a l).factorization p := by
  have h :=
    Nat.factorization_le_factorization_choose_add (p := p) hl hl0
  omega

/-- Lemma 3.7: valuation condition (iii) implies binomiality. -/
theorem binomial_valuation_condition (e : MDescen)
    (hvaluation : e.HasValuationCondition) :
    e.IsBinomial := by
  intro n i l hi hin hl hle hil
  have hei0 : e n i ≠ 0 := by omega
  have htarget0 : e n (i * l) ≠ 0 := by
    intro hzero
    have hdvd : e n (i * l) ∣ e n i :=
      e.dvd_of_le hi (Nat.le_mul_of_pos_right i hl)
        hil
    rw [hzero, zero_dvd_iff] at hdvd
    exact hei0 hdvd
  have hchoose0 : Nat.choose (e n i) l ≠ 0 :=
    Nat.choose_ne_zero hle
  rw [← Nat.factorization_le_iff_dvd htarget0 hchoose0]
  intro p
  by_cases hp : p.Prime
  · let r := l.factorization p
    let s := (e n i).factorization p
    have hpr_dvd_l : p ^ r ∣ l := by
      exact hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hl) |>.mpr le_rfl
    have hpr_le_l : p ^ r ≤ l :=
      Nat.le_of_dvd hl hpr_dvd_l
    have hipr : i * p ^ r ≤ n :=
      (Nat.mul_le_mul_left i hpr_le_l).trans hil
    by_cases hsr : s < r
    · have hps_dvd_l : p ^ s ∣ l :=
        (pow_dvd_pow p hsr.le).trans hpr_dvd_l
      have hps_le_l : p ^ s ≤ l :=
        Nat.le_of_dvd hl hps_dvd_l
      have hips : i * p ^ s ≤ n :=
        (Nat.mul_le_mul_left i hps_le_l).trans hil
      have hzero :
          (e n (i * p ^ s)).factorization p = 0 := by
        have := hvaluation hi hips hp hei0 (le_refl s)
        simpa [s] using this
      have hdvd :
          e n (i * l) ∣ e n (i * p ^ s) :=
        e.dvd_of_le (n := n) (i := i * p ^ s) (j := i * l)
          (by
            exact Nat.one_le_iff_ne_zero.mpr <|
              mul_ne_zero (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hi))
                (pow_ne_zero _ hp.ne_zero))
          (Nat.mul_le_mul_left i hps_le_l)
          hil
      have hintermediate0 : e n (i * p ^ s) ≠ 0 := by
        intro hz
        have hto_i : e n (i * p ^ s) ∣ e n i :=
          e.dvd_of_le hi
            (Nat.le_mul_of_pos_right i (pow_pos hp.pos s))
            hips
        rw [hz, zero_dvd_iff] at hto_i
        exact hei0 hto_i
      have hfac :
          (e n (i * l)).factorization p ≤
            (e n (i * p ^ s)).factorization p :=
        (Nat.factorization_le_iff_dvd htarget0
          hintermediate0).2 hdvd p
      rw [hzero] at hfac
      exact hfac.trans (Nat.zero_le _)
    · have hrs : r ≤ s := Nat.le_of_not_gt hsr
      have hcondition :
          (e n (i * p ^ r)).factorization p ≤ s - r := by
        simpa [s] using hvaluation hi hipr hp hei0 hrs
      have hdvd :
          e n (i * l) ∣ e n (i * p ^ r) :=
        e.dvd_of_le (n := n) (i := i * p ^ r) (j := i * l)
          (by
            exact Nat.one_le_iff_ne_zero.mpr <|
              mul_ne_zero (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hi))
                (pow_ne_zero _ hp.ne_zero))
          (Nat.mul_le_mul_left i hpr_le_l)
          hil
      have hintermediate0 : e n (i * p ^ r) ≠ 0 := by
        intro hz
        have hto_i : e n (i * p ^ r) ∣ e n i :=
          e.dvd_of_le hi
            (Nat.le_mul_of_pos_right i (pow_pos hp.pos r))
            hipr
        rw [hz, zero_dvd_iff] at hto_i
        exact hei0 hto_i
      have htarget_le :
          (e n (i * l)).factorization p ≤
            (e n (i * p ^ r)).factorization p :=
        (Nat.factorization_le_iff_dvd htarget0 hintermediate0).2 hdvd p
      exact htarget_le.trans <|
        hcondition.trans <|
          factorization_choose_bound hle (Nat.ne_of_gt hl)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The constant-power family satisfies the valuation criterion from Lemma 3.7. -/
theorem constant_valuation_condition (a : ℕ) :
    (constantPower a).HasValuationCondition := by
  intro n i r p hi hip hp _hne hr
  simp only [constantPower_apply, Nat.factorization_pow, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hr ⊢
  by_cases hr0 : r = 0
  · subst r
    simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hpow : r < p ^ r := Nat.lt_pow_self hp.one_lt
    have hv : 0 < a.factorization p := by
      by_contra hv0
      have hvEq : a.factorization p = 0 := Nat.eq_zero_of_not_pos hv0
      simp only [hvEq, mul_zero, Nat.le_zero] at hr
      exact hr0 hr
    have hgap :
        r ≤ (i * p ^ r - i) * a.factorization p := by
      calc
        r ≤ p ^ r - 1 := by omega
        _ ≤ i * (p ^ r - 1) :=
          Nat.le_mul_of_pos_left _ hi
        _ ≤ (i * (p ^ r - 1)) * a.factorization p :=
          Nat.le_mul_of_pos_right _ hv
        _ = (i * p ^ r - i) * a.factorization p := by
          rw [Nat.mul_sub_one]
    have hdecomp :
        (n - i) * a.factorization p =
          (n - i * p ^ r) * a.factorization p +
            (i * p ^ r - i) * a.factorization p := by
      rw [← Nat.add_mul]
      rw [Nat.sub_add_sub_cancel hip
        (Nat.le_mul_of_pos_right i (pow_pos hp.pos r))]
    omega

/-- Examples 3.4 and 3.8: `e(n,i) = a^(n-i)` is binomial. -/
theorem constant_power_binomial (a : ℕ) :
    (constantPower a).IsBinomial :=
  binomial_valuation_condition _ (constant_valuation_condition a)

/-- The coefficient `e(n,i)` attached to a sequence `A` in Example 3.3:
the gcd of all products of `n-i` entries among `A 1, ..., A (n-1)`. -/
def sequenceCoefficient (A : ℕ → ℕ) (n i : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1)).powersetCard (n - i)).gcd
    (fun J => ∏ j ∈ J, A j)

@[simp] theorem sequenceCoefficient_diagonal (A : ℕ → ℕ) (n : ℕ) :
    sequenceCoefficient A n n = 1 := by
  simp [sequenceCoefficient, Finset.powersetCard_zero]

/-- For a constant sequence, the gcd of the fixed-cardinality products is
the corresponding power. -/
theorem sequenceCoefficient_const
    (a n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    sequenceCoefficient (fun _ => a) n i = a ^ (n - i) := by
  classical
  let S := (Finset.Icc 1 (n - 1)).powersetCard (n - i)
  have hnonempty : S.Nonempty := by
    apply Finset.powersetCard_nonempty_of_le
    simp only [Nat.card_Icc]
    omega
  apply Nat.dvd_antisymm
  · obtain ⟨J, hJ⟩ := hnonempty
    have hdvd :=
      Finset.gcd_dvd
        (f := fun J : Finset ℕ => ∏ _j ∈ J, a) hJ
    have hcard : J.card = n - i :=
      (Finset.mem_powersetCard.mp hJ).2
    simpa [sequenceCoefficient, S, hcard] using hdvd
  · unfold sequenceCoefficient
    apply Finset.dvd_gcd
    intro J hJ
    have hcard : J.card = n - i :=
      (Finset.mem_powersetCard.mp hJ).2
    simp [hcard]

/-- Example 3.3: gcds of fixed-cardinality subproducts form a multiplicatively
descending map. -/
def ofSequence (A : ℕ → ℕ) : MDescen where
  toFun := sequenceCoefficient A
  diagonal n _ := sequenceCoefficient_diagonal A n
  adjacent_dvd n i _hi hin := by
    unfold sequenceCoefficient
    rw [Finset.dvd_gcd_iff]
    intro J hJ
    have hcard : J.card = n - i := (Finset.mem_powersetCard.mp hJ).2
    have hcardpos : 0 < J.card := by omega
    obtain ⟨x, hx⟩ := J.card_pos.mp hcardpos
    have herase_mem :
        J.erase x ∈ (Finset.Icc 1 (n - 1)).powersetCard (n - (i + 1)) := by
      rw [Finset.mem_powersetCard]
      constructor
      · exact (Finset.erase_subset _ _).trans (Finset.mem_powersetCard.mp hJ).1
      · rw [Finset.card_erase_of_mem hx, hcard]
        omega
    have hgcd :
        sequenceCoefficient A n (i + 1) ∣ ∏ j ∈ J.erase x, A j :=
      by
        simpa [sequenceCoefficient] using Finset.gcd_dvd herase_mem
    refine hgcd.trans ?_
    use A x
    rw [Finset.prod_erase_mul _ _ hx]

@[simp] theorem ofSequence_apply (A : ℕ → ℕ) (n i : ℕ) :
    ofSequence A n i = sequenceCoefficient A n i := rfl

private theorem weighted_prime_exponent
    (p n i : ℕ) (hp : p.Prime) :
    ∃ j : ℕ, n ≤ max 1 i * p ^ j := by
  refine ⟨Nat.clog p n, ?_⟩
  calc
    n ≤ p ^ Nat.clog p n := Nat.le_pow_clog hp.one_lt n
    _ = 1 * p ^ Nat.clog p n := by simp
    _ ≤ max 1 i * p ^ Nat.clog p n := by
      gcongr
      exact Nat.le_max_left 1 i

/-- The integer `⌈log_p(n/i)⌉`, characterized without real logarithms as the
least exponent `j` for which `n ≤ i * p^j`.  The `max` makes the definition
total; all paper applications have `1 ≤ i`. -/
noncomputable def ceilingLogExponent
    (p : ℕ) (hp : p.Prime) (n i : ℕ) : ℕ :=
  Nat.find (weighted_prime_exponent p n i hp)

theorem mul_ceiling_log
    (p : ℕ) (hp : p.Prime) (n i : ℕ) (hi : 1 ≤ i) :
    n ≤ i * p ^ ceilingLogExponent p hp n i := by
  simpa [ceilingLogExponent, Nat.max_eq_right hi] using
    Nat.find_spec (weighted_prime_exponent p n i hp)

theorem ceiling_log
    (p : ℕ) (hp : p.Prime) {n i j : ℕ}
    (hi : 1 ≤ i) (hlevel : n ≤ i * p ^ j) :
    ceilingLogExponent p hp n i ≤ j := by
  apply Nat.find_min'
  simpa [Nat.max_eq_right hi] using hlevel

@[simp] theorem ceiling_log_diagonal
    (p : ℕ) (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    ceilingLogExponent p hp n n = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply ceiling_log p hp hn
  simp

theorem ceiling_log_antitone
    (p : ℕ) (hp : p.Prime) {n i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) :
    ceilingLogExponent p hp n j ≤ ceilingLogExponent p hp n i := by
  apply ceiling_log p hp (hi.trans hij)
  exact (mul_ceiling_log p hp n i hi).trans <|
    Nat.mul_le_mul_right (p ^ ceilingLogExponent p hp n i) hij

/-- Multiplication of the index by `p^r` lowers the ceiling-log exponent by
at most `r`, with truncation at zero. -/
theorem ceiling_log_sub
    (p : ℕ) (hp : p.Prime) {n i r : ℕ} (hi : 1 ≤ i) :
    ceilingLogExponent p hp n (i * p ^ r) ≤
      ceilingLogExponent p hp n i - r := by
  let j := ceilingLogExponent p hp n i
  by_cases hrj : r ≤ j
  · apply ceiling_log p hp
      (Nat.one_le_iff_ne_zero.mpr <|
        mul_ne_zero (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hi))
          (pow_ne_zero _ hp.ne_zero))
    calc
      n ≤ i * p ^ j := mul_ceiling_log p hp n i hi
      _ = (i * p ^ r) * p ^ (j - r) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hrj]
  · have hjr : j ≤ r := Nat.le_of_not_ge hrj
    have hzero :
        ceilingLogExponent p hp n (i * p ^ r) = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply ceiling_log p hp
        (Nat.one_le_iff_ne_zero.mpr <|
          mul_ne_zero (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hi))
            (pow_ne_zero _ hp.ne_zero))
      simpa using
        (mul_ceiling_log p hp n i hi).trans
          (Nat.mul_le_mul_left i (Nat.pow_le_pow_right hp.pos hjr))
    simp [hzero]

/-- Example 3.5: `e(n,i) = p^(t⌈log_p(n/i)⌉)`. -/
noncomputable def logarithmicPrimePower
    (p t : ℕ) (hp : p.Prime) : MDescen where
  toFun n i := p ^ (t * ceilingLogExponent p hp n i)
  diagonal n hn := by simp [ceiling_log_diagonal p hp hn]
  adjacent_dvd n i hi hin := by
    apply pow_dvd_pow
    exact Nat.mul_le_mul_left t <|
      ceiling_log_antitone p hp hi (Nat.le_succ i)

@[simp] theorem logarithmic_prime_power
    (p t : ℕ) (hp : p.Prime) (n i : ℕ) :
    logarithmicPrimePower p t hp n i =
      p ^ (t * ceilingLogExponent p hp n i) := rfl

/-- The logarithmic prime-power map satisfies condition (iii) of Lemma 3.7. -/
theorem logarithmic_valuation_condition
    (p t : ℕ) (hp : p.Prime) (ht : 1 ≤ t) :
    (logarithmicPrimePower p t hp).HasValuationCondition := by
  intro n i r q hi _hiq hq _hne hr
  by_cases hqp : q = p
  · subst q
    simp only [logarithmic_prime_power,
      Nat.factorization_pow_self hp] at hr ⊢
    let j := ceilingLogExponent p hp n i
    let j' := ceilingLogExponent p hp n (i * p ^ r)
    have hj' : j' ≤ j - r := by
      exact ceiling_log_sub p hp hi
    by_cases hrj : r ≤ j
    · have hsub :
          t * (j - r) ≤ t * j - r := by
        apply Nat.le_sub_of_add_le
        calc
          t * (j - r) + r ≤ t * (j - r) + t * r := by
            gcongr
            exact Nat.le_mul_of_pos_left r ht
          _ = t * j := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hrj]
      exact (Nat.mul_le_mul_left t hj').trans hsub
    · have hjr : j ≤ r := Nat.le_of_not_ge hrj
      have hj'0 : j' = 0 := by
        have : j' ≤ 0 := by simpa [Nat.sub_eq_zero_of_le hjr] using hj'
        exact Nat.eq_zero_of_le_zero this
      change t * j' ≤ t * j - r
      rw [hj'0]
      exact Nat.zero_le _
  · have hpq : p ≠ q := Ne.symm hqp
    have hfac :
        ∀ k : ℕ, (p ^ k).factorization q = 0 := by
      intro k
      rw [hp.factorization_pow]
      simp [hpq]
    simp only [logarithmic_prime_power, hfac] at hr ⊢
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
    subst r
    simp

/-- Example 3.9: the logarithmic prime-power map is binomial. -/
theorem logarithmic_prime_binomial
    (p t : ℕ) (hp : p.Prime) (ht : 1 ≤ t) :
    (logarithmicPrimePower p t hp).IsBinomial :=
  binomial_valuation_condition _
    (logarithmic_valuation_condition p t hp ht)

private theorem factorization_finset_gcd
    {β : Type*} (s : Finset β) (f : β → ℕ)
    (hgcd : s.gcd f ≠ 0) (p : ℕ) (hp : p.Prime) :
    ∃ x ∈ s, f x ≠ 0 ∧
      (s.gcd f).factorization p = (f x).factorization p := by
  classical
  obtain ⟨x₀, hx₀s, hx₀0⟩ := Finset.gcd_ne_zero_iff.mp hgcd
  have hs0 : ({x ∈ s | f x ≠ 0} : Finset β).Nonempty :=
    ⟨x₀, Finset.mem_filter.mpr ⟨hx₀s, hx₀0⟩⟩
  obtain ⟨x, hxs0, hmin⟩ :=
    Finset.exists_min_image ({x ∈ s | f x ≠ 0} : Finset β)
      (fun y => (f y).factorization p) hs0
  have hxs := (Finset.mem_filter.mp hxs0).1
  have hx0 := (Finset.mem_filter.mp hxs0).2
  refine ⟨x, hxs, hx0, le_antisymm ?_ ?_⟩
  · exact
      ((Nat.factorization_le_iff_dvd hgcd hx0).2
        (Finset.gcd_dvd hxs)) p
  · apply (hp.pow_dvd_iff_le_factorization hgcd).mp
    apply Finset.dvd_gcd
    intro y hys
    by_cases hy0 : f y = 0
    · simp [hy0]
    · apply (hp.pow_dvd_iff_le_factorization hy0).mpr
      exact hmin y (Finset.mem_filter.mpr ⟨hys, hy0⟩)

private theorem sequence_factorization_succ
    (A : ℕ → ℕ) {n i p : ℕ} (hp : p.Prime)
    (hpos : 0 < (sequenceCoefficient A n i).factorization p) :
    (sequenceCoefficient A n (i + 1)).factorization p <
      (sequenceCoefficient A n i).factorization p := by
  classical
  let S := (Finset.Icc 1 (n - 1)).powersetCard (n - i)
  let f : Finset ℕ → ℕ := fun J => ∏ j ∈ J, A j
  have hcoeff0 : sequenceCoefficient A n i ≠ 0 := by
    intro hzero
    simp [hzero] at hpos
  obtain ⟨J, hJS, hJ0, hfactor⟩ :=
    factorization_finset_gcd S f
      (by simpa [S, f, sequenceCoefficient] using hcoeff0) p hp
  have hpJ : p ∣ f J := by
    apply (hp.dvd_iff_one_le_factorization hJ0).mpr
    simpa [← hfactor, S, f, sequenceCoefficient] using hpos
  obtain ⟨x, hxJ, hpx⟩ :=
    (Prime.dvd_finsetProd_iff hp.prime A).mp hpJ
  have hA0 : ∀ y ∈ J, A y ≠ 0 := by
    simpa [f] using (Finset.prod_ne_zero_iff.mp hJ0)
  have herase0 : f (J.erase x) ≠ 0 := by
    simp only [f]
    exact Finset.prod_ne_zero_iff.mpr fun y hy =>
      hA0 y (Finset.mem_of_mem_erase hy)
  have hcard : J.card = n - i := (Finset.mem_powersetCard.mp hJS).2
  have herase_mem :
      J.erase x ∈ (Finset.Icc 1 (n - 1)).powersetCard (n - (i + 1)) := by
    rw [Finset.mem_powersetCard]
    constructor
    · exact (Finset.erase_subset _ _).trans (Finset.mem_powersetCard.mp hJS).1
    · rw [Finset.card_erase_of_mem hxJ, hcard]
      omega
  have hnext_dvd :
      sequenceCoefficient A n (i + 1) ∣ f (J.erase x) := by
    simpa [sequenceCoefficient, f] using Finset.gcd_dvd herase_mem
  have hnext0 : sequenceCoefficient A n (i + 1) ≠ 0 := by
    intro hzero
    rw [hzero, zero_dvd_iff] at hnext_dvd
    exact herase0 hnext_dvd
  have hnext_le :
      (sequenceCoefficient A n (i + 1)).factorization p ≤
        (f (J.erase x)).factorization p :=
    ((Nat.factorization_le_iff_dvd hnext0 herase0).2 hnext_dvd) p
  have hAx0 : A x ≠ 0 := hA0 x hxJ
  have hAxpos : 0 < (A x).factorization p :=
    hp.factorization_pos_of_dvd hAx0 hpx
  have hfactor' :
      (sequenceCoefficient A n i).factorization p =
        (f J).factorization p := by
    simpa [S, f, sequenceCoefficient] using hfactor
  have hsplit :
      (sequenceCoefficient A n i).factorization p =
        (f (J.erase x)).factorization p + (A x).factorization p := by
    rw [hfactor']
    simp only [f]
    rw [← Finset.prod_erase_mul J A hxJ]
    rw [Nat.factorization_mul (by simpa [f] using herase0) hAx0]
    rfl
  omega

private theorem sequence_coefficient_factorization
    (A : ℕ → ℕ) {n i p : ℕ} (hp : p.Prime)
    (hi : 1 ≤ i) (hin : i < n)
    (hcoeff0 : sequenceCoefficient A n i ≠ 0) :
    (sequenceCoefficient A n (i + 1)).factorization p ≤
      (sequenceCoefficient A n i).factorization p - 1 := by
  by_cases hpos : 0 < (sequenceCoefficient A n i).factorization p
  · exact Nat.le_sub_one_of_lt <|
      sequence_factorization_succ A hp hpos
  · have hfac0 :
        (sequenceCoefficient A n i).factorization p = 0 :=
      Nat.eq_zero_of_not_pos hpos
    have hdvd :
        sequenceCoefficient A n (i + 1) ∣ sequenceCoefficient A n i :=
      (ofSequence A).adjacent_dvd n i hi hin
    have hnext0 : sequenceCoefficient A n (i + 1) ≠ 0 := by
      intro hz
      rw [hz, zero_dvd_iff] at hdvd
      exact hcoeff0 hdvd
    have hle :
        (sequenceCoefficient A n (i + 1)).factorization p ≤
          (sequenceCoefficient A n i).factorization p :=
      ((Nat.factorization_le_iff_dvd hnext0 hcoeff0).2 hdvd) p
    simpa [hfac0] using hle

private theorem sequence_factorization_sub
    (A : ℕ → ℕ) {n i r p : ℕ} (hp : p.Prime)
    (hi : 1 ≤ i) (hir : i + r ≤ n)
    (hcoeff0 : sequenceCoefficient A n i ≠ 0) :
    (sequenceCoefficient A n (i + r)).factorization p ≤
      (sequenceCoefficient A n i).factorization p - r := by
  induction r with
  | zero => simp
  | succ r ihr =>
      have hir' : i + r ≤ n := by omega
      have hcurrent0 : sequenceCoefficient A n (i + r) ≠ 0 := by
        have hdvd :
            sequenceCoefficient A n (i + r) ∣ sequenceCoefficient A n i :=
          (ofSequence A).dvd_of_le hi (by omega) hir'
        intro hz
        rw [hz, zero_dvd_iff] at hdvd
        exact hcoeff0 hdvd
      have hstep :
          (sequenceCoefficient A n (i + r + 1)).factorization p ≤
            (sequenceCoefficient A n (i + r)).factorization p - 1 :=
        sequence_coefficient_factorization A hp
          (by omega) (by omega) hcurrent0
      have hind := ihr
      exact hstep.trans <| by omega

private theorem add_mul_pow
    {i p r : ℕ} (hi : 1 ≤ i) (hp : p.Prime) :
    i + r ≤ i * p ^ r := by
  have hr : r ≤ p ^ r - 1 := by
    have := Nat.lt_pow_self hp.one_lt (n := r)
    omega
  calc
    i + r ≤ i + i * (p ^ r - 1) := by
      gcongr
      exact hr.trans (Nat.le_mul_of_pos_left _ hi)
    _ = i * p ^ r := by
      rw [Nat.mul_sub_one]
      exact Nat.add_sub_of_le <|
        Nat.le_mul_of_pos_right i (pow_pos hp.pos r)

/-- Example 3.8: the coefficient map attached to an arbitrary sequence is
binomial. -/
theorem sequence_binomial (A : ℕ → ℕ) :
    (ofSequence A).IsBinomial := by
  apply binomial_valuation_condition
  intro n i r p hi hip hp hcoeff0 _hr
  have hir : i + r ≤ n :=
    (add_mul_pow hi hp).trans hip
  have hadd :
      (sequenceCoefficient A n (i + r)).factorization p ≤
        (sequenceCoefficient A n i).factorization p - r :=
    sequence_factorization_sub A hp hi hir hcoeff0
  have hindex : i + r ≤ i * p ^ r := add_mul_pow hi hp
  have htarget0 : sequenceCoefficient A n (i * p ^ r) ≠ 0 := by
    have hdvd :
        sequenceCoefficient A n (i * p ^ r) ∣ sequenceCoefficient A n i :=
      (ofSequence A).dvd_of_le hi
        (Nat.le_mul_of_pos_right i (pow_pos hp.pos r)) hip
    intro hz
    rw [hz, zero_dvd_iff] at hdvd
    exact hcoeff0 hdvd
  have hintermediate0 : sequenceCoefficient A n (i + r) ≠ 0 := by
    have hdvd :
        sequenceCoefficient A n (i + r) ∣ sequenceCoefficient A n i :=
      (ofSequence A).dvd_of_le hi (by omega) hir
    intro hz
    rw [hz, zero_dvd_iff] at hdvd
    exact hcoeff0 hdvd
  have hdvd :
      sequenceCoefficient A n (i * p ^ r) ∣
        sequenceCoefficient A n (i + r) :=
    (ofSequence A).dvd_of_le (by omega) hindex hip
  exact
    (((Nat.factorization_le_iff_dvd htarget0 hintermediate0).2 hdvd) p).trans hadd

end MDescen

end EChapma

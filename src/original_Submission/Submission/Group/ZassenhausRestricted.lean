import Submission.Group.GolodShafarevichCore
import Submission.Group.LowerCentralStrong
import Submission.Group.PresentationData
import Submission.Group.HallArithmetic
import Submission.Group.ZassenhausExplicit

open scoped commutatorElement

namespace Submission

/-- Taking a `p`th power of a raw Zassenhaus generator multiplies its weight by `p`. -/
lemma generator_set_prime
    {p : ℕ} {G : Type*} [Group G] {n : ℕ} {g : G}
    (hg : g ∈ zassenhausGeneratorSet p G n) :
    g ^ p ∈ zassenhausGeneratorSet p G (p * n) := by
  rcases hg with ⟨i, j, x, hx, hweight, rfl⟩
  refine ⟨i, j + 1, x, hx, ?_, ?_⟩
  · calc
      p * n ≤ p * ((i + 1) * p ^ j) := Nat.mul_le_mul_left p hweight
      _ = (i + 1) * p ^ (j + 1) := by
        simp only [pow_succ]
        ac_rfl
  · rw [pow_succ, pow_mul]

/-- At positive indices, the normal-closure formula is exactly the root closure filtration. -/
lemma formula_term_filtration
    {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]
    (n : ℕ) (hn : 0 < n) :
    Group.zFTerm p n G = zassenhausFiltration p G n := by
  apply le_antisymm
  · haveI : (zassenhausFiltration p G n).Normal :=
      zassenhausFiltration_normal p G n
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases hx with ⟨_hp, _hn, i, j, y, hi, hy, hbound, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨i - 1, j, y, ?_, ?_, rfl⟩
    · simpa [Group.zassenhausLowerTerm] using hy
    · have hpred : i - 1 + 1 = i := by omega
      simpa [hpred] using hbound
  · rw [zassenhausFiltration]
    apply (Subgroup.closure_le _).2
    intro x hx
    rcases hx with ⟨i, j, y, hy, hbound, rfl⟩
    apply Subgroup.subset_normalClosure
    refine ⟨Fact.out, hn, i + 1, j, y, Nat.succ_pos _, ?_, ?_, rfl⟩
    · simpa [Group.zassenhausLowerTerm] using hy
    · exact hbound

/-- If generators have `p`th powers in a normal subgroup and commute modulo it, then every
element of their subgroup closure has `p`th power in that normal subgroup. -/
lemma closure_generator_commutator
    {p : ℕ} {G : Type*} [Group G] {A : Set G} {K : Subgroup G} [K.Normal]
    (hpow : ∀ {a : G}, a ∈ A → a ^ p ∈ K)
    (hcomm : ∀ {a b : G}, a ∈ A → b ∈ A → ⁅a, b⁆ ∈ K) :
    ∀ {x : G},
      x ∈ Subgroup.closure A →
        x ^ p ∈ K := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hcomm_closure :
      ∀ {x y : G},
        x ∈ Subgroup.closure A →
        y ∈ Subgroup.closure A →
          ⁅x, y⁆ ∈ K :=
    commutator_element_closure hcomm
  have hcomm_quotient :
      ∀ {x y : G},
        x ∈ Subgroup.closure A →
        y ∈ Subgroup.closure A →
          Commute (q x) (q y) := by
    intro x y hx hy
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := K) ⁅x, y⁆).mpr
      (hcomm_closure hx hy)
  intro x hx
  let P : (z : G) → z ∈ Subgroup.closure A → Prop :=
    fun z _ => (q z) ^ p = 1
  have hxpow :
      P x hx := by
    apply
      Subgroup.closure_induction
        (p := P)
        (fun a ha => by
          have hqa : q (a ^ p) = 1 :=
            (QuotientGroup.eq_one_iff (N := K) (a ^ p)).mpr (hpow ha)
          simpa [q] using hqa)
        (by
          change (q 1) ^ p = 1
          simp)
        (fun x y hx_mem hy_mem hx_pow hy_pow => by
          change (q (x * y)) ^ p = 1
          have hxy_comm : Commute (q x) (q y) :=
            hcomm_quotient hx_mem hy_mem
          rw [map_mul, hxy_comm.mul_pow, hx_pow, hy_pow, one_mul])
        (fun x _ hx_pow => by
          change (q x⁻¹) ^ p = 1
          simpa [map_inv, inv_pow] using hx_pow)
        hx
  exact
    (QuotientGroup.eq_one_iff (N := K) (x ^ p)).mp
      (by simpa [q] using hxpow)

/-- To prove the `p`-power estimate for a Zassenhaus filtration term, it is enough to know that
raw generators commute modulo the target `D_{p r}`.  The raw-generator `p`th powers themselves
land in `D_{p r}` by definition. -/
lemma filtration_set_bound
    {p : ℕ} {G : Type*} [Group G] {r : ℕ}
    (hcomm :
      ∀ {x y : G},
        x ∈ zassenhausGeneratorSet p G r →
        y ∈ zassenhausGeneratorSet p G r →
          ⁅x, y⁆ ∈ zassenhausFiltration p G (p * r)) :
    ∀ {x : G},
      x ∈ zassenhausFiltration p G r →
        x ^ p ∈ zassenhausFiltration p G (p * r) := by
  intro x hx
  rw [zassenhausFiltration] at hx
  haveI : (zassenhausFiltration p G (p * r)).Normal :=
    zassenhausFiltration_normal p G (p * r)
  exact
    closure_generator_commutator
      (K := zassenhausFiltration p G (p * r))
      (by
        intro a ha
        exact
          Subgroup.subset_closure
            (generator_set_prime ha))
      hcomm hx

/-- For an odd prime, an exact generator of weight two comes from the second lower-central
term, not from a `p`-power. -/
lemma exact_series_ne
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ exactGeneratorSet p G 2) :
    g ∈ Subgroup.lowerCentralSeries G 1 := by
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  have hp3 : 3 ≤ p := by
    have hp2_le : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  have hj0 : j = 0 := by
    by_contra hj_ne
    have hj_pos : 0 < j := Nat.pos_of_ne_zero hj_ne
    have hp_le_pow : p ≤ p ^ j := by
      simpa using
        (pow_le_pow_right' (a := p) (n := 1) (m := j)
          (by omega : 1 ≤ p) hj_pos)
    have hthree_le : 3 ≤ (i + 1) * p ^ j := by
      calc
        3 ≤ p := hp3
        _ ≤ p ^ j := hp_le_pow
        _ ≤ (i + 1) * p ^ j := by
          simpa using Nat.le_mul_of_pos_left (p ^ j) (Nat.succ_pos i)
    omega
  subst j
  have hi : i = 1 := by
    simpa using hweight
  subst i
  have hxg : x = g := by
    simpa using hpow
  simpa [hxg] using hx

/-- For an odd prime, killing `D₃` forces every `p`th power to be trivial. -/
lemma trivial_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration p G 3 = ⊥)
    (x : G) :
    x ^ p = 1 := by
  have hp3 : 3 ≤ p := by
    have hp2_le : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  have hxgen : x ^ p ∈ zassenhausGeneratorSet p G p := by
    refine ⟨0, 1, x, Subgroup.mem_top x, ?_, ?_⟩
    · simp
    · simp
  have hxDp : x ^ p ∈ zassenhausFiltration p G p :=
    set_subset_filtration hxgen
  have hxD3 : x ^ p ∈ zassenhausFiltration p G 3 :=
    zassenhausFiltration_antitone p G hp3 hxDp
  have hxbot : x ^ p ∈ (⊥ : Subgroup G) := by
    simpa [hbot] using hxD3
  simpa using Subgroup.mem_bot.mp hxbot

/-- For an odd prime and a killed `D₃` layer, the restricted `p`-power law is automatic. -/
lemma filtration_trivial_ne
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration p G 3 = ⊥) :
    ∀ {r : ℕ} {x : G},
      x ∈ zassenhausFiltration p G r →
        x ^ p ∈ zassenhausFiltration p G (p * r) := by
  intro r x _hx
  have hxpow : x ^ p = 1 :=
    trivial_ne_two
      (p := p) hp2 hbot x
  rw [hxpow]
  exact Subgroup.one_mem (zassenhausFiltration p G (p * r))

/-- For an odd prime, an exact generator of weight `< 3` lies in the corresponding
lower-central term. -/
lemma exact_set_pred
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 3)
    (hg : g ∈ exactGeneratorSet p G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) := by
  have hnpos : 0 < n :=
    exact_set_pos (p := p) hg
  by_cases hn1 : n = 1
  · have hpred : n - 1 = 0 := by omega
    rw [hpred]
    exact Subgroup.mem_top g
  · have hn2 : n = 2 := by omega
    have hpred : n - 1 = 1 := by omega
    rw [hpred]
    exact
      exact_series_ne
        (p := p) hp2 (by simpa [hn2] using hg)

/-- For odd primes, exact-generator commutators below weight three have the expected additive
Zassenhaus bound. -/
lemma element_filtration_exact
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type*} [Group G]
    {r s : ℕ} {x y : G}
    (hr : r < 3)
    (hs : s < 3)
    (hx : x ∈ exactGeneratorSet p G r)
    (hy : y ∈ exactGeneratorSet p G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (r + s) := by
  have hrpos : 0 < r :=
    exact_set_pos (p := p) hx
  have hspos : 0 < s :=
    exact_set_pos (p := p) hy
  have hx_lcs :
      x ∈ Subgroup.lowerCentralSeries G (r - 1) :=
    exact_set_pred
      (p := p) hp2 hr hx
  have hy_lcs :
      y ∈ Subgroup.lowerCentralSeries G (s - 1) :=
    exact_set_pred
      (p := p) hp2 hs hy
  have hcomm :
      ⁅x, y⁆ ∈
        zassenhausFiltration p G (((r - 1) + 1) + ((s - 1) + 1)) :=
    exact_subset_filtration
      (exact_set_series
        (p := p) hx_lcs hy_lcs)
  have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
    omega
  simpa [hindex] using hcomm

/-- On a killed layer, exact-weight checks below the killed weight also suffice for the
generator-level commutation bound used to lift `p`th powers through a subgroup closure. -/
lemma commutator_killed_bound
    {p : ℕ} {G : Type*} [Group G] {n : ℕ}
    (hbot : zassenhausFiltration p G n = ⊥)
    (hexact :
      ∀ {r a b : ℕ} {x y : G},
        r ≤ a →
        r ≤ b →
        a < n →
        b < n →
        x ∈ exactGeneratorSet p G a →
        y ∈ exactGeneratorSet p G b →
          ⁅x, y⁆ ∈ zassenhausFiltration p G (p * r)) :
    ∀ {r : ℕ} {x y : G},
      x ∈ zassenhausGeneratorSet p G r →
      y ∈ zassenhausGeneratorSet p G r →
        ⁅x, y⁆ ∈ zassenhausFiltration p G (p * r) := by
  intro r x y hx hy
  rcases or_exact_trivial
      hbot hx with hxone | ⟨a, hra, han, hxa⟩
  · simp [hxone]
  rcases or_exact_trivial
      hbot hy with hyone | ⟨b, hrb, hbn, hyb⟩
  · simp [hyone]
  exact hexact hra hrb han hbn hxa hyb

/-- Killed-layer exact-weight commutator checks give the full `p`-power law whenever they imply
that same-level raw generators commute modulo `D_{p r}`. -/
lemma killed_set_bound
    {p : ℕ} {G : Type*} [Group G] {n : ℕ}
    (hbot : zassenhausFiltration p G n = ⊥)
    (hexact :
      ∀ {r a b : ℕ} {x y : G},
        r ≤ a →
        r ≤ b →
        a < n →
        b < n →
        x ∈ exactGeneratorSet p G a →
        y ∈ exactGeneratorSet p G b →
          ⁅x, y⁆ ∈ zassenhausFiltration p G (p * r)) :
    ∀ {r : ℕ} {x : G},
      x ∈ zassenhausFiltration p G r →
        x ^ p ∈ zassenhausFiltration p G (p * r) := by
  intro r x hx
  exact
    filtration_set_bound
      (commutator_killed_bound
        hbot
        hexact)
      hx

/-- Lower-central terms belong to the root Zassenhaus term with the matching one-based
weight.  This restricted-series-local name avoids colliding with the finite-shadow helper. -/
lemma lower_filtration_restricted
    {p : ℕ} {G : Type*} [Group G]
    (i : ℕ) :
    Subgroup.lowerCentralSeries G i ≤ zassenhausFiltration p G (i + 1) := by
  intro x hx
  exact
    Subgroup.subset_closure
      ⟨i, 0, x, hx, by simp, by simp⟩

/-- A `p`th power of a lower-central element belongs to the root Zassenhaus term whose weight is
multiplied by `p`. -/
lemma lower_pow_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i : ℕ} {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i) :
    x ^ p ∈ zassenhausFiltration p G (p * (i + 1)) := by
  exact
    exact_subset_filtration
      ⟨i, 1, x, hx, by simp [Nat.mul_comm], by simp⟩

/-- A `p^a`th power of a lower-central element belongs to the root Zassenhaus term whose weight
is multiplied by `p^a`. -/
lemma lower_central_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i a : ℕ} {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i) :
    x ^ (p ^ a) ∈ zassenhausFiltration p G ((i + 1) * p ^ a) := by
  exact
    exact_subset_filtration
      ⟨i, a, x, hx, rfl, rfl⟩

/-- Any power whose exponent is divisible by `p` of a lower-central element has the same
one-step `p`-weighted Zassenhaus bound. -/
lemma central_series_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i n : ℕ} {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i) :
    x ^ (p * n) ∈ zassenhausFiltration p G (p * (i + 1)) := by
  rw [pow_mul]
  exact
    (zassenhausFiltration p G (p * (i + 1))).pow_mem
      (lower_pow_filtration (p := p) hx)
      n

/-- Any power whose exponent is divisible by `p^a` of a lower-central element has the same
`p^a`-weighted Zassenhaus bound. -/
lemma lower_series_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i a n : ℕ} {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i) :
    x ^ ((p ^ a) * n) ∈ zassenhausFiltration p G ((i + 1) * p ^ a) := by
  rw [pow_mul]
  exact
    (zassenhausFiltration p G ((i + 1) * p ^ a)).pow_mem
      (lower_central_filtration (p := p) hx)
      n

/-- A prime-power binomial coefficient supplies exactly the Zassenhaus gain predicted by its
`p`-adic valuation. -/
lemma lower_choose_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i a k : ℕ} {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hk : k ≤ p ^ a)
    (hk0 : k ≠ 0) :
    x ^ Nat.choose (p ^ a) k ∈
      zassenhausFiltration p G ((i + 1) * p ^ (a - multiplicity p k)) := by
  obtain ⟨n, hn⟩ :=
    multiplicity_dvd_choose
      (p := p) (a := a) (k := k) hk hk0
  rw [hn]
  exact
    lower_series_filtration
      (p := p) hx

/-- For an interior binomial coefficient `choose p k`, divisibility by the prime `p` gives one
full `p`-weighted Zassenhaus gain. -/
lemma series_choose_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i k : ℕ} {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hk_pos : 0 < k)
    (hk_lt : k < p) :
    x ^ Nat.choose p k ∈ zassenhausFiltration p G (p * (i + 1)) := by
  obtain ⟨n, hn⟩ :=
    (Fact.out : Nat.Prime p).dvd_choose_self (Nat.ne_of_gt hk_pos) hk_lt
  rw [hn]
  exact central_series_filtration (p := p) hx

/-- A commutator of lower-central elements is a raw Zassenhaus generator of summed weight. -/
lemma commutator_set_series
    {p : ℕ} {G : Type*} [Group G] {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, y⁆ ∈ zassenhausGeneratorSet p G ((i + 1) + (j + 1)) := by
  exact
    exact_set_subset
      (exact_set_series hx hy)

/-- If an intermediate subgroup contains the successor filtration term but is still strictly
smaller than the current term, some exact-weight generator escapes it. -/
lemma exact_generator_succ
    {p : ℕ} {G : Type*} [Group G]
    {n : ℕ} {K : Subgroup G}
    (hnext : zassenhausFiltration p G (n + 1) ≤ K)
    (hlt : K < zassenhausFiltration p G n) :
    ∃ g : G, g ∈ exactGeneratorSet p G n ∧ g ∉ K := by
  by_contra hnone
  have hexact : exactGeneratorSet p G n ⊆ K := by
    intro g hg
    by_contra hgK
    exact hnone ⟨g, hg, hgK⟩
  have hclosure :
      Subgroup.closure (exactGeneratorSet p G n) ≤ K :=
    (Subgroup.closure_le K).2 hexact
  have hle : zassenhausFiltration p G n ≤ K := by
    rw [exact_sup_succ]
    exact sup_le hclosure hnext
  exact (not_le_of_gt hlt) hle

/-- The escaping exact generator for a positive layer has its `p`th power in every intermediate
subgroup containing the successor term. -/
lemma exact_not_succ
    {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]
    {n : ℕ} (hn : 0 < n) {K : Subgroup G}
    (hnext : zassenhausFiltration p G (n + 1) ≤ K)
    (hlt : K < zassenhausFiltration p G n) :
    ∃ g : G,
      g ∈ exactGeneratorSet p G n ∧
        g ∉ K ∧
          g ^ p ∈ K := by
  rcases exact_generator_succ hnext hlt with ⟨g, hg, hgK⟩
  exact
    ⟨g, hg, hgK,
      hnext (exact_filtration_succ hn hg)⟩

end Submission

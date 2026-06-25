import Towers.Group.HallOrbit
import Towers.Group.HallWords
import Towers.Group.HallArithmetic


open scoped commutatorElement

namespace Towers

/-- A choose-powered repeated-left Hall factor belongs directly to the weighted commutator-word
subgroup at the one-sided prime-power cutoff.

Unlike the coarser Zassenhaus-filtration statement, this records the exact normal subgroup in which
future Hall collection takes place. -/
lemma iterated_element_choose
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {A B a r : ℕ}
    {x y : G}
    (hr : r + 1 ≤ p ^ a) :
    leftIteratedElement x ⁅x, y⁆ r ^ Nat.choose (p ^ a) (r + 1) ∈
      weightedCommutatorSubgroup p
        (HPAtom.eval (G := G) x y)
        (HPAtom.weight A B)
        (A * p ^ a + B) := by
  let w : CWord HPAtom :=
    CWord.pairLeftIterate r
  have hweight :
      A * p ^ a + B ≤
        w.weight (HPAtom.weight A B) *
          p ^ (a - multiplicity p (r + 1)) := by
    simpa [w] using
      (add_sub_multiplicity
        (p := p) (a := a) (k := r + 1) A B hr (Nat.succ_ne_zero r))
  have hdvd :
      p ^ (a - multiplicity p (r + 1)) ∣ Nat.choose (p ^ a) (r + 1) :=
    multiplicity_dvd_choose hr (Nat.succ_ne_zero r)
  simpa [w] using
    (w.evalpowmem_weightpowercomm_wordsubgroupdvd
      (f := HPAtom.eval (G := G) x y)
      (wt := HPAtom.weight A B)
      (cutoff := A * p ^ a + B)
      hweight hdvd)

/-- Every choose-powered factor in the collected prime-power left-conjugate orbit belongs to the
weighted commutator-word subgroup at the final one-sided cutoff. -/
lemma iterated_choose_pair
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {A B a : ℕ}
    {x y : G} :
    leftIteratedChoose x ⁅x, y⁆ (p ^ a) ≤
      weightedCommutatorSubgroup p
        (HPAtom.eval (G := G) x y)
        (HPAtom.weight A B)
        (A * p ^ a + B) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨r, hr, rfl⟩
  exact
    iterated_element_choose
      (by omega)

/-- A pairwise bracket among repeated-left Hall factors belongs to the weighted commutator-word
subgroup whenever its exact Hall weight reaches the requested cutoff. -/
lemma element_iterated_weighted
    {p : ℕ}
    {G : Type*} [Group G]
    {A B cutoff r s : ℕ}
    {x y : G}
    (hweight : cutoff ≤ (r + s + 2) * A + 2 * B) :
    ⁅leftIteratedElement x ⁅x, y⁆ r,
        leftIteratedElement x ⁅x, y⁆ s⁆ ∈
      weightedCommutatorSubgroup p
        (HPAtom.eval (G := G) x y)
        (HPAtom.weight A B)
        cutoff := by
  let w : CWord HPAtom :=
    CWord.iteratePairwiseError r s
  have hw :
      cutoff ≤ w.weight (HPAtom.weight A B) := by
    simpa [w] using hweight
  simpa [w] using
    (w.evalmem_weightpower_commwordsubg
      (p := p)
      (f := HPAtom.eval (G := G) x y)
      (wt := HPAtom.weight A B)
      (cutoff := cutoff)
      hw)

lemma conjugate_pairwise_choose
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x c : G} (n : ℕ)
    (hcomm :
      ∀ r s : ℕ,
        ⁅leftIteratedElement x c r,
            leftIteratedElement x c s⁆ ∈ K)
    (hfactor :
      ∀ r : ℕ, r < n →
        leftIteratedElement x c r ^ Nat.choose n (r + 1) ∈ K) :
    leftConjugateProduct x c n ∈ K := by
  apply
    (show
      leftIteratedChoose x c n ⊔
          iteratedPairwiseComm x c ≤ K by
        apply sup_le
        · apply (Subgroup.closure_le K).mpr
          rintro z ⟨r, hr, rfl⟩
          exact hfactor r hr
        · apply Subgroup.normalClosure_le_normal
          rintro z ⟨r, s, _hrs, rfl⟩
          exact hcomm r s)
  exact sup_pairwise_comm x c n

/-- The prime-power left-conjugate orbit is absorbed by the weighted Hall-pair subgroup whenever
every unequal pairwise Hall error has already reached the final cutoff. -/
lemma conjugate_pairwise_cutoff
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {A B a : ℕ}
    {x y : G}
    (hpair :
      ∀ r s : ℕ, r ≠ s →
        A * p ^ a + B ≤ (r + s + 2) * A + 2 * B) :
    leftConjugateProduct x ⁅x, y⁆ (p ^ a) ∈
      weightedCommutatorSubgroup p
        (HPAtom.eval (G := G) x y)
        (HPAtom.weight A B)
        (A * p ^ a + B) := by
  apply
    conjugate_pairwise_choose
      (weightedCommutatorSubgroup p
        (HPAtom.eval (G := G) x y)
        (HPAtom.weight A B)
        (A * p ^ a + B))
      (p ^ a)
  · intro r s
    by_cases hrs : r = s
    · subst s
      simp
    · exact
        element_iterated_weighted
          (hpair r s hrs)
  · intro r hr
    exact
      iterated_element_choose
        (by omega)

/-- A prime power in the left commutator input belongs to the weighted Hall-pair subgroup whenever
every unequal pairwise Hall error has already reached the final cutoff. -/
lemma element_pairwise_cutoff
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {A B a : ℕ}
    {x y : G}
    (hpair :
      ∀ r s : ℕ, r ≠ s →
        A * p ^ a + B ≤ (r + s + 2) * A + 2 * B) :
    ⁅x ^ (p ^ a), y⁆ ∈
      weightedPairSubgroup p x y A B (A * p ^ a + B) := by
  rw [commutator_element_conjugate]
  exact
    conjugate_pairwise_cutoff
      hpair

/-- The terminating Hall-collection case gives the expected explicit root-Zassenhaus estimate for
a prime power in the left commutator input. -/
lemma filtration_pairwise_cutoff
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (hpair :
      ∀ r s : ℕ, r ≠ s →
        (i + 1) * p ^ a + (j + 1) ≤
          (r + s + 2) * (i + 1) + 2 * (j + 1)) :
    ⁅x ^ (p ^ a), y⁆ ∈
      zassenhausFiltration p G ((i + 1) * p ^ a + (j + 1)) :=
  weighted_pair_filtration hx hy
    (element_pairwise_cutoff
      hpair)

/-- The prime-power left-conjugate orbit is absorbed by the weighted Hall-pair subgroup whenever
the final one-sided cutoff is no larger than the least possible weight of an unequal pairwise Hall
error.

This is the bounded collection range of the Hall argument.  Larger prime powers require recursive
collection of the pairwise errors rather than a single abelianization step. -/
lemma conjugate_weighted_pair
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {A B a : ℕ}
    {x y : G}
    (hcutoff : A * p ^ a + B ≤ 3 * A + 2 * B) :
    leftConjugateProduct x ⁅x, y⁆ (p ^ a) ∈
      weightedCommutatorSubgroup p
        (HPAtom.eval (G := G) x y)
        (HPAtom.weight A B)
        (A * p ^ a + B) := by
  apply
    conjugate_pairwise_cutoff
  intro r s hrs
  apply hcutoff.trans
  have hrs_pos : 1 ≤ r + s := by omega
  have hthree : 3 ≤ r + s + 2 := by omega
  exact
    Nat.add_le_add_right
      (Nat.mul_le_mul_right A hthree)
      (2 * B)

/-- In the bounded Hall-collection range, a prime power in the left commutator input belongs to
the weighted Hall-pair subgroup at its expected one-sided cutoff. -/
lemma commutator_element_weighted
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {A B a : ℕ}
    {x y : G}
    (hcutoff : A * p ^ a + B ≤ 3 * A + 2 * B) :
    ⁅x ^ (p ^ a), y⁆ ∈
      weightedPairSubgroup p x y A B (A * p ^ a + B) := by
  rw [commutator_element_conjugate]
  exact
    conjugate_weighted_pair
      hcutoff

/-- The bounded Hall-collection range already gives the expected explicit Zassenhaus estimate for
a prime power in the left commutator input. -/
lemma commutator_filtration_three
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (hcutoff :
      (i + 1) * p ^ a + (j + 1) ≤
        3 * (i + 1) + 2 * (j + 1)) :
    ⁅x ^ (p ^ a), y⁆ ∈
      zassenhausFiltration p G ((i + 1) * p ^ a + (j + 1)) :=
  weighted_pair_filtration hx hy
    (commutator_element_weighted
      hcutoff)

/-- The symmetric bounded Hall-collection range gives the expected explicit Zassenhaus estimate
for a prime power in the right commutator input. -/
lemma commutator_element_three
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (hcutoff :
      (i + 1) + (j + 1) * p ^ a ≤
        2 * (i + 1) + 3 * (j + 1)) :
    ⁅x, y ^ (p ^ a)⁆ ∈
      zassenhausFiltration p G ((i + 1) + (j + 1) * p ^ a) := by
  let K : Subgroup G :=
    zassenhausFiltration p G ((i + 1) + (j + 1) * p ^ a)
  have hcutoff' :
      (j + 1) * p ^ a + (i + 1) ≤
        3 * (j + 1) + 2 * (i + 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcutoff
  have hleft :
      ⁅y ^ (p ^ a), x⁆ ∈ K := by
    have h :=
      commutator_filtration_three
        (p := p) (i := j) (j := i) (a := a)
        (x := y) (y := x) hy hx hcutoff'
    simpa [K, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hinv : ⁅y ^ (p ^ a), x⁆⁻¹ ∈ K :=
    K.inv_mem hleft
  simpa [K, commutatorElement_inv] using hinv

/-- Bounded left prime-power Hall collection, with the target relaxed along a lower Zassenhaus
weight bound. -/
lemma element_filtration_three
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a r : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (hr : r ≤ (i + 1) * p ^ a)
    (hcutoff :
      (i + 1) * p ^ a + (j + 1) ≤
        3 * (i + 1) + 2 * (j + 1)) :
    ⁅x ^ (p ^ a), y⁆ ∈
      zassenhausFiltration p G (r + (j + 1)) := by
  have h :=
    commutator_filtration_three
      (p := p) (i := i) (j := j) (a := a)
      (x := x) (y := y) hx hy hcutoff
  exact
    zassenhausFiltration_antitone p G
      (Nat.add_le_add_right hr (j + 1)) h

/-- Bounded right prime-power Hall collection, with the target relaxed along a lower Zassenhaus
weight bound. -/
lemma commutator_element_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a s : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (hs : s ≤ (j + 1) * p ^ a)
    (hcutoff :
      (i + 1) + (j + 1) * p ^ a ≤
        2 * (i + 1) + 3 * (j + 1)) :
    ⁅x, y ^ (p ^ a)⁆ ∈
      zassenhausFiltration p G ((i + 1) + s) := by
  have h :=
    commutator_element_three
      (p := p) (i := i) (j := j) (a := a)
      (x := x) (y := y) hx hy hcutoff
  exact
    zassenhausFiltration_antitone p G
      (Nat.add_le_add_left hs (i + 1)) h

lemma element_iterated_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j r s : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅leftIteratedElement x ⁅x, y⁆ r,
        leftIteratedElement x ⁅x, y⁆ s⁆ ∈
      zassenhausFiltration p G
        ((r + s + 2) * (i + 1) + 2 * (j + 1)) := by
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hr :
      leftIteratedElement x ⁅x, y⁆ r ∈
        Subgroup.lowerCentralSeries G (r * (i + 1) + (i + j + 1)) :=
    iterated_element_series hx hxy r
  have hs :
      leftIteratedElement x ⁅x, y⁆ s ∈
        Subgroup.lowerCentralSeries G (s * (i + 1) + (i + j + 1)) :=
    iterated_element_series hx hxy s
  have hmem :=
    commutator_element_series
      (p := p) hr hs
  have hindex :
      (r * (i + 1) + (i + j + 1) + 1) +
          (s * (i + 1) + (i + j + 1) + 1) =
        (r + s + 2) * (i + 1) + 2 * (j + 1) := by
    ring
  simpa only [hindex] using hmem

end Towers

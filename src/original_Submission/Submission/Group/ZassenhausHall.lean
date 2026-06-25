import Submission.Group.HallOrbit
import Submission.Group.HallArithmetic
import Submission.Group.ZassenhausRestricted

open scoped commutatorElement

namespace Submission

/-- Coarse powered form of lower-central strong centrality. This records the part of the
Hall-Petresco argument that uses only normality: taking arbitrary natural powers of either
commutator input preserves membership in the unweighted summed lower-central term. -/
lemma element_filtration_series
    {p : ℕ} {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (a b : ℕ) :
    ⁅x ^ a, y ^ b⁆ ∈ zassenhausFiltration p G ((i + 1) + (j + 1)) := by
  let K : Subgroup G := zassenhausFiltration p G ((i + 1) + (j + 1))
  letI : K.Normal :=
    zassenhausFiltration_normal p G ((i + 1) + (j + 1))
  exact
    commutator_element_pow K
      (commutator_element_series hx hy)
      a b

/-- Base case of the weighted Hall-Petresco commutator estimate. -/
lemma element_filtration_base
    {p : ℕ} {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x ^ (p ^ 0), y ^ (p ^ 0)⁆ ∈
      zassenhausFiltration p G ((i + 1) * p ^ 0 + (j + 1) * p ^ 0) := by
  simpa using
    (commutator_element_series
      (p := p) hx hy)

/-- The first Hall correction for a power in the left commutator input has the expected
Zassenhaus weight. -/
lemma inv_commutator_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x ^ n, y⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
      zassenhausFiltration p G (2 * (i + 1) + (j + 1)) := by
  have hmem :
      ⁅x ^ n, y⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
        Subgroup.lowerCentralSeries G (2 * i + j + 2) :=
    inv_commutator_series hx hy n
  have hroot :
      ⁅x ^ n, y⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
        zassenhausFiltration p G ((2 * i + j + 2) + 1) :=
    lower_filtration_restricted
      (p := p) (2 * i + j + 2) hmem
  have hindex :
      (2 * i + j + 2) + 1 = 2 * (i + 1) + (j + 1) := by
    omega
  simpa [hindex] using hroot

/-- The symmetric first Hall correction for a power in the right commutator input has the
expected Zassenhaus weight. -/
lemma inv_element_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x, y ^ n⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
      zassenhausFiltration p G ((i + 1) + 2 * (j + 1)) := by
  have hmem :
      ⁅x, y ^ n⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
        Subgroup.lowerCentralSeries G (i + 2 * j + 2) :=
    inv_element_series hx hy n
  have hroot :
      ⁅x, y ^ n⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
        zassenhausFiltration p G ((i + 2 * j + 2) + 1) :=
    lower_filtration_restricted
      (p := p) (i + 2 * j + 2) hmem
  have hindex :
      (i + 2 * j + 2) + 1 = (i + 1) + 2 * (j + 1) := by
    omega
  simpa [hindex] using hroot

/-- The class-three Hall correction for a power in the left commutator input has the expected
Zassenhaus weight. -/
lemma element_nested_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x ^ n, y⁆ *
        ((⁅x, ⁅x, y⁆⁆ ^ Nat.choose n 2) * (⁅x, y⁆ ^ n))⁻¹ ∈
      zassenhausFiltration p G (3 * (i + 1) + (j + 1)) := by
  have hmem :
      ⁅x ^ n, y⁆ *
          ((⁅x, ⁅x, y⁆⁆ ^ Nat.choose n 2) * (⁅x, y⁆ ^ n))⁻¹ ∈
        Subgroup.lowerCentralSeries G (3 * i + j + 3) :=
    element_nested_series
      hx hy n
  have hroot :
      ⁅x ^ n, y⁆ *
          ((⁅x, ⁅x, y⁆⁆ ^ Nat.choose n 2) * (⁅x, y⁆ ^ n))⁻¹ ∈
        zassenhausFiltration p G ((3 * i + j + 3) + 1) :=
    lower_filtration_restricted
      (p := p) (3 * i + j + 3) hmem
  have hindex :
      (3 * i + j + 3) + 1 = 3 * (i + 1) + (j + 1) := by
    omega
  simpa [hindex] using hroot

/-- The symmetric class-three Hall correction for a power in the right commutator input has the
expected Zassenhaus weight. -/
lemma inv_nested_filtration
    {p : ℕ} {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x, y ^ n⁆ *
        ((⁅x, y⁆ ^ n) * (⁅y, ⁅x, y⁆⁆ ^ Nat.choose n 2))⁻¹ ∈
      zassenhausFiltration p G ((i + 1) + 3 * (j + 1)) := by
  have hmem :
      ⁅x, y ^ n⁆ *
          ((⁅x, y⁆ ^ n) * (⁅y, ⁅x, y⁆⁆ ^ Nat.choose n 2))⁻¹ ∈
        Subgroup.lowerCentralSeries G (i + 3 * j + 3) :=
    inv_nested_series
      hx hy n
  have hroot :
      ⁅x, y ^ n⁆ *
          ((⁅x, y⁆ ^ n) * (⁅y, ⁅x, y⁆⁆ ^ Nat.choose n 2))⁻¹ ∈
        zassenhausFiltration p G ((i + 3 * j + 3) + 1) :=
    lower_filtration_restricted
      (p := p) (i + 3 * j + 3) hmem
  have hindex :
      (i + 3 * j + 3) + 1 = (i + 1) + 3 * (j + 1) := by
    omega
  simpa [hindex] using hroot

/-- For `p = 2`, the first Hall correction already proves the weighted estimate for a square
in the left commutator input.  For odd primes, the higher Hall corrections are genuinely needed. -/
lemma commutator_sq_filtration
    {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x ^ 2, y⁆ ∈
      zassenhausFiltration 2 G (2 * (i + 1) + (j + 1)) := by
  let K : Subgroup G :=
    zassenhausFiltration 2 G (2 * (i + 1) + (j + 1))
  have herror :
      ⁅x ^ 2, y⁆ * (⁅x, y⁆ ^ 2)⁻¹ ∈ K :=
    inv_commutator_filtration
      (p := 2) hx hy 2
  have hpow :
      ⁅x, y⁆ ^ 2 ∈
        zassenhausFiltration 2 G (2 * ((i + 1) + (j + 1))) :=
    exact_subset_filtration
      (exact_set_prime
        (p := 2)
        (exact_set_series
          (p := 2) (i := i) (j := j) (x := x) (y := y) hx hy))
  have hmain : ⁅x, y⁆ ^ 2 ∈ K :=
    zassenhausFiltration_antitone 2 G (by omega) hpow
  simpa [K, mul_assoc] using K.mul_mem herror hmain

/-- For `p = 3`, the class-three Hall correction proves the weighted estimate for a cube in the
left commutator input. -/
lemma commutator_cube_filtration
    {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x ^ 3, y⁆ ∈
      zassenhausFiltration 3 G (3 * (i + 1) + (j + 1)) := by
  let K : Subgroup G :=
    zassenhausFiltration 3 G (3 * (i + 1) + (j + 1))
  have herror :
      ⁅x ^ 3, y⁆ *
          ((⁅x, ⁅x, y⁆⁆ ^ Nat.choose 3 2) * (⁅x, y⁆ ^ 3))⁻¹ ∈ K :=
    element_nested_filtration
      (p := 3) hx hy 3
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hbasePow :
      ⁅x, y⁆ ^ 3 ∈
        zassenhausFiltration 3 G (3 * ((i + 1) + (j + 1))) :=
    exact_subset_filtration
      (exact_set_prime
        (p := 3)
        (exact_set_series hx hy))
  have hbasePowK : ⁅x, y⁆ ^ 3 ∈ K :=
    zassenhausFiltration_antitone 3 G (by omega) hbasePow
  have hnestedPow :
      ⁅x, ⁅x, y⁆⁆ ^ 3 ∈
        zassenhausFiltration 3 G (3 * ((i + 1) + ((i + j + 1) + 1))) :=
    exact_subset_filtration
      (exact_set_prime
        (p := 3)
        (exact_set_series hx hxy))
  have hnestedPowK : ⁅x, ⁅x, y⁆⁆ ^ 3 ∈ K :=
    zassenhausFiltration_antitone 3 G (by omega) hnestedPow
  have hchoose : Nat.choose 3 2 = 3 := by
    norm_num [Nat.choose]
  have hcorrection :
      (⁅x, ⁅x, y⁆⁆ ^ Nat.choose 3 2) * (⁅x, y⁆ ^ 3) ∈ K := by
    rw [hchoose]
    exact K.mul_mem hnestedPowK hbasePowK
  simpa [K, mul_assoc] using K.mul_mem herror hcorrection

/-- For `p = 3`, the symmetric class-three Hall correction proves the weighted estimate for a
cube in the right commutator input. -/
lemma element_cube_filtration
    {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, y ^ 3⁆ ∈
      zassenhausFiltration 3 G ((i + 1) + 3 * (j + 1)) := by
  let K : Subgroup G :=
    zassenhausFiltration 3 G ((i + 1) + 3 * (j + 1))
  have herror :
      ⁅x, y ^ 3⁆ *
          ((⁅x, y⁆ ^ 3) * (⁅y, ⁅x, y⁆⁆ ^ Nat.choose 3 2))⁻¹ ∈ K :=
    inv_nested_filtration
      (p := 3) hx hy 3
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hbasePow :
      ⁅x, y⁆ ^ 3 ∈
        zassenhausFiltration 3 G (3 * ((i + 1) + (j + 1))) :=
    exact_subset_filtration
      (exact_set_prime
        (p := 3)
        (exact_set_series hx hy))
  have hbasePowK : ⁅x, y⁆ ^ 3 ∈ K :=
    zassenhausFiltration_antitone 3 G (by omega) hbasePow
  have hnestedPow :
      ⁅y, ⁅x, y⁆⁆ ^ 3 ∈
        zassenhausFiltration 3 G (3 * ((j + 1) + ((i + j + 1) + 1))) :=
    exact_subset_filtration
      (exact_set_prime
        (p := 3)
        (exact_set_series hy hxy))
  have hnestedPowK : ⁅y, ⁅x, y⁆⁆ ^ 3 ∈ K :=
    zassenhausFiltration_antitone 3 G (by omega) hnestedPow
  have hchoose : Nat.choose 3 2 = 3 := by
    norm_num [Nat.choose]
  have hcorrection :
      (⁅x, y⁆ ^ 3) * (⁅y, ⁅x, y⁆⁆ ^ Nat.choose 3 2) ∈ K := by
    rw [hchoose]
    exact K.mul_mem hbasePowK hnestedPowK
  simpa [K, mul_assoc] using K.mul_mem herror hcorrection

/-- For `p = 2`, the symmetric first Hall correction proves the weighted estimate for a square
in the right commutator input. -/
lemma element_sq_filtration
    {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, y ^ 2⁆ ∈
      zassenhausFiltration 2 G ((i + 1) + 2 * (j + 1)) := by
  let K : Subgroup G :=
    zassenhausFiltration 2 G ((i + 1) + 2 * (j + 1))
  have herror :
      ⁅x, y ^ 2⁆ * (⁅x, y⁆ ^ 2)⁻¹ ∈ K :=
    inv_element_filtration
      (p := 2) hx hy 2
  have hpow :
      ⁅x, y⁆ ^ 2 ∈
        zassenhausFiltration 2 G (2 * ((i + 1) + (j + 1))) :=
    exact_subset_filtration
      (exact_set_prime
        (p := 2)
        (exact_set_series
          (p := 2) (i := i) (j := j) (x := x) (y := y) hx hy))
  have hmain : ⁅x, y⁆ ^ 2 ∈ K :=
    zassenhausFiltration_antitone 2 G (by omega) hpow
  simpa [K, mul_assoc] using K.mul_mem herror hmain

/-- The two-sided square commutator has the expected weight-four Zassenhaus depth at `p = 2`.

This is the small Hall-Petresco case that is not available from the one-sided square estimates
alone.  We collect `[a²,b]` modulo `D₄`, show the resulting correction has
square in `D₄`, and then
collect the right square. -/
lemma commutator_element_sq
    {G : Type*} [Group G] (a b : G) :
    ⁅a ^ 2, b ^ 2⁆ ∈ zassenhausFiltration 2 G 4 := by
  let K : Subgroup G := zassenhausFiltration 2 G 4
  letI : K.Normal := zassenhausFiltration_normal 2 G 4
  let c : G := ⁅a, b⁆
  let u : G := ⁅a, c⁆
  let v : G := c ^ 2
  have hc_lcs : c ∈ Subgroup.lowerCentralSeries G 1 := by
    dsimp [c]
    exact
      lower_commutator_succ 0 0
        (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top a) (Subgroup.mem_top b))
  have hu_lcs : u ∈ Subgroup.lowerCentralSeries G 2 := by
    dsimp [u]
    exact
      lower_commutator_succ 0 1
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hc_lcs)
  have hc_exact : c ∈ exactGeneratorSet 2 G 2 := by
    dsimp [c]
    exact
      exact_set_series
        (p := 2) (i := 0) (j := 0) (x := a) (y := b)
        (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hvK : v ∈ K := by
    have h :=
      exact_subset_filtration
        (exact_set_prime (p := 2) hc_exact)
    simpa [K, v, Nat.mul_comm] using h
  have hu2K : u ^ 2 ∈ K := by
    have h :
        u ^ 2 ∈ zassenhausFiltration 2 G (2 * (2 + 1)) :=
      lower_pow_filtration
        (p := 2) hu_lcs
    exact zassenhausFiltration_antitone 2 G (by norm_num) h
  have hchoose : Nat.choose 2 2 = 1 := by
    norm_num [Nat.choose]
  have hleftApprox :
      ⁅a ^ 2, b⁆ * (u * v)⁻¹ ∈ K := by
    have h :=
      element_nested_filtration
        (p := 2) (G := G) (i := 0) (j := 0) (x := a) (y := b)
        (Subgroup.mem_top a) (Subgroup.mem_top b) 2
    simpa [K, c, u, v, hchoose] using h
  have huv2K : (u * v) ^ 2 ∈ K := by
    apply (QuotientGroup.eq_one_iff (N := K) ((u * v) ^ 2)).mp
    have hvq : QuotientGroup.mk' K v = 1 :=
      (QuotientGroup.eq_one_iff (N := K) v).mpr hvK
    have hu2q : QuotientGroup.mk' K (u ^ 2) = 1 :=
      (QuotientGroup.eq_one_iff (N := K) (u ^ 2)).mpr hu2K
    calc
      QuotientGroup.mk' K ((u * v) ^ 2) =
          (QuotientGroup.mk' K u * QuotientGroup.mk' K v) ^ 2 := by
            simp
      _ = (QuotientGroup.mk' K u) ^ 2 := by
            rw [hvq]
            simp
      _ = QuotientGroup.mk' K (u ^ 2) := by
            simp
      _ = 1 := hu2q
  have hleftSq : ⁅a ^ 2, b⁆ ^ 2 ∈ K := by
    have hcongr :
        ⁅a ^ 2, b⁆ ^ 2 * ((u * v) ^ 2)⁻¹ ∈ K :=
      mul_inv_pow K hleftApprox 2
    have hmul := K.mul_mem hcongr huv2K
    simpa [mul_assoc] using hmul
  have hbu : ⁅b, u⁆ ∈ K := by
    have h :
        ⁅b, u⁆ ∈ zassenhausFiltration 2 G ((0 + 1) + (2 + 1)) :=
      commutator_element_series
        (p := 2) (Subgroup.mem_top b) hu_lcs
    simpa [K] using h
  have hbv : ⁅b, v⁆ ∈ K := by
    have h :
        ⁅b, c ^ 2⁆ ∈ zassenhausFiltration 2 G ((0 + 1) + 2 * (1 + 1)) :=
      element_sq_filtration
        (G := G) (i := 0) (j := 1) (x := b) (y := c)
        (Subgroup.mem_top b) hc_lcs
    have hK : ⁅b, c ^ 2⁆ ∈ K :=
      zassenhausFiltration_antitone 2 G (by norm_num) h
    simpa [v] using hK
  have hbuv : ⁅b, u * v⁆ ∈ K := by
    rw [element_mul_right]
    have hconj : u * ⁅b, v⁆ * u⁻¹ ∈ K :=
      (show K.Normal from inferInstance).conj_mem ⁅b, v⁆ hbv u
    simpa [mul_assoc] using K.mul_mem hbu hconj
  have hnested : ⁅b, ⁅a ^ 2, b⁆⁆ ∈ K := by
    have hcongr :
        ⁅b, ⁅a ^ 2, b⁆⁆ * ⁅b, u * v⁆⁻¹ ∈ K :=
      inv_commutator K
        (by simp : b * b⁻¹ ∈ K) hleftApprox
    have hmul := K.mul_mem hcongr hbuv
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  have comm_right_mem_K :
      ∀ {x y : G}, y ∈ K → ⁅x, y⁆ ∈ K := by
    intro x y hy
    rw [commutatorElement_def]
    exact
      K.mul_mem
        ((show K.Normal from inferInstance).conj_mem y hy x)
        (K.inv_mem hy)
  have htriple : ⁅b, ⁅b, ⁅a ^ 2, b⁆⁆⁆ ∈ K :=
    comm_right_mem_K hnested
  have hcross : ⁅⁅a ^ 2, b⁆, ⁅b, ⁅a ^ 2, b⁆⁆⁆ ∈ K :=
    comm_right_mem_K hnested
  have hrightApprox :
      ⁅a ^ 2, b ^ 2⁆ *
          ((⁅a ^ 2, b⁆ ^ 2) * ⁅b, ⁅a ^ 2, b⁆⁆)⁻¹ ∈ K := by
    have h :=
      mul_inv_nested
        K htriple hcross 2
    simpa [hchoose] using h
  have hcorrection :
      (⁅a ^ 2, b⁆ ^ 2) * ⁅b, ⁅a ^ 2, b⁆⁆ ∈ K :=
    K.mul_mem hleftSq hnested
  have hmul := K.mul_mem hrightApprox hcorrection
  simpa only [K, mul_assoc, inv_mul_cancel, mul_one] using hmul

/-- At `p = 2`, an exact generator of weight two is either lower-central of weight two or
a square of an arbitrary element. -/
lemma exact_or_sq
    {p : ℕ} [Fact p.Prime] (hp2 : p = 2)
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ exactGeneratorSet p G 2) :
    g ∈ Subgroup.lowerCentralSeries G 1 ∨ ∃ x : G, x ^ 2 = g := by
  subst p
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    left
    have hi : i = 1 := by
      simpa using hweight
    subst i
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · by_cases hj1 : j = 1
    · subst j
      right
      have hi : i = 0 := by
        simpa using hweight
      subst i
      refine ⟨x, ?_⟩
      simpa using hpow
    · have hj2 : 2 ≤ j := by omega
      have hfour_le_pow : 4 ≤ 2 ^ j := by
        simpa using
          (pow_le_pow_right' (a := 2) (n := 2) (m := j)
            (by omega : 1 ≤ 2) hj2)
      have hfour_le : 4 ≤ (i + 1) * 2 ^ j := by
        exact hfour_le_pow.trans
          (by
            exact Nat.le_mul_of_pos_left (2 ^ j) (Nat.succ_pos i))
      omega

/-- At `p = 2`, an exact generator of weight three comes from the third lower-central term. -/
lemma exact_generator_set
    {p : ℕ} [Fact p.Prime] (hp2 : p = 2)
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ exactGeneratorSet p G 3) :
    g ∈ Subgroup.lowerCentralSeries G 2 := by
  subst p
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    have hi : i = 2 := by
      simpa using hweight
    subst i
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · by_cases hj1 : j = 1
    · subst j
      omega
    · have hj2 : 2 ≤ j := by omega
      have hfour_le_pow : 4 ≤ 2 ^ j := by
        simpa using
          (pow_le_pow_right' (a := 2) (n := 2) (m := j)
            (by omega : 1 ≤ 2) hj2)
      have hfour_le : 4 ≤ (i + 1) * 2 ^ j := by
        exact hfour_le_pow.trans
          (by
            exact Nat.le_mul_of_pos_left (2 ^ j) (Nat.succ_pos i))
      omega

/-- At `p = 2`, exact generators below weight four are lower-central except for the possible
weight-two square case. -/
lemma exact_set_cases
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 4)
    (hg : g ∈ exactGeneratorSet 2 G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) ∨
      n = 2 ∧ ∃ x : G, x ^ 2 = g := by
  have hnpos : 0 < n :=
    exact_set_pos (p := 2) hg
  by_cases hn1 : n = 1
  · left
    have hpred : n - 1 = 0 := by omega
    rw [hpred]
    exact Subgroup.mem_top g
  · by_cases hn2 : n = 2
    · rcases
        exact_or_sq
          (p := 2) rfl (by simpa [hn2] using hg) with h_lcs | hsq
      · left
        have hpred : n - 1 = 1 := by omega
        simpa [hpred] using h_lcs
      · right
        exact ⟨hn2, hsq⟩
    · have hn3 : n = 3 := by omega
      left
      have hpred : n - 1 = 2 := by omega
      simpa [hpred] using
        (exact_generator_set
          (p := 2) rfl (by simpa [hn3] using hg))

/-- At `p = 2`, an exact generator of weight four is either lower-central of weight four,
the square of a second lower-central element, or a fourth power. -/
lemma set_four_cases
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ exactGeneratorSet 2 G 4) :
    g ∈ Subgroup.lowerCentralSeries G 3 ∨
      (∃ x : G, x ∈ Subgroup.lowerCentralSeries G 1 ∧ x ^ 2 = g) ∨
        ∃ x : G, x ^ 4 = g := by
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    left
    have hi : i = 3 := by
      simpa using hweight
    subst i
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · by_cases hj1 : j = 1
    · subst j
      right
      left
      have hi : i = 1 := by
        omega
      subst i
      exact ⟨x, hx, by simpa using hpow⟩
    · by_cases hj2 : j = 2
      · subst j
        right
        right
        have hi : i = 0 := by
          omega
        subst i
        refine ⟨x, ?_⟩
        simpa [pow_succ] using hpow
      · have hj3 : 3 ≤ j := by omega
        have height_le_pow : 8 ≤ 2 ^ j := by
          simpa using
            (pow_le_pow_right' (a := 2) (n := 3) (m := j)
              (by omega : 1 ≤ 2) hj3)
        have height_le : 8 ≤ (i + 1) * 2 ^ j := by
          exact height_le_pow.trans
            (by
              exact Nat.le_mul_of_pos_left (2 ^ j) (Nat.succ_pos i))
        omega

/-- At `p = 2`, exact-generator commutators below weight four have the expected additive
Zassenhaus bound. -/
lemma element_exact_four
    {G : Type*} [Group G]
    {r s : ℕ} {x y : G}
    (hr : r < 4)
    (hs : s < 4)
    (hx : x ∈ exactGeneratorSet 2 G r)
    (hy : y ∈ exactGeneratorSet 2 G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration 2 G (r + s) := by
  have hrpos : 0 < r :=
    exact_set_pos (p := 2) hx
  have hspos : 0 < s :=
    exact_set_pos (p := 2) hy
  rcases exact_set_cases hr hx with
    hx_lcs | ⟨hr2, a, hax⟩
  · rcases exact_set_cases hs hy with
      hy_lcs | ⟨hs2, b, hby⟩
    · have hcomm :
          ⁅x, y⁆ ∈
            zassenhausFiltration 2 G (((r - 1) + 1) + ((s - 1) + 1)) :=
        exact_subset_filtration
          (exact_set_series
            (p := 2) hx_lcs hy_lcs)
      have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
        omega
      simpa [hindex] using hcomm
    · have hcomm :
          ⁅x, b ^ 2⁆ ∈
            zassenhausFiltration 2 G (((r - 1) + 1) + 2 * (0 + 1)) :=
        element_sq_filtration
          (G := G) (i := r - 1) (j := 0) (x := x) (y := b)
          hx_lcs (Subgroup.mem_top b)
      have hindex : ((r - 1) + 1) + 2 * (0 + 1) = r + s := by
        omega
      simpa [hby, hindex] using hcomm
  · rcases exact_set_cases hs hy with
      hy_lcs | ⟨hs2, b, hby⟩
    · have hcomm :
          ⁅a ^ 2, y⁆ ∈
            zassenhausFiltration 2 G (2 * (0 + 1) + ((s - 1) + 1)) :=
        commutator_sq_filtration
          (G := G) (i := 0) (j := s - 1) (x := a) (y := y)
          (Subgroup.mem_top a) hy_lcs
      have hindex : 2 * (0 + 1) + ((s - 1) + 1) = r + s := by
        omega
      simpa [hax, hindex] using hcomm
    · have hcomm :
          ⁅a ^ 2, b ^ 2⁆ ∈ zassenhausFiltration 2 G 4 :=
        commutator_element_sq a b
      have hindex : 4 = r + s := by omega
      simpa [hax, hby, hindex] using hcomm

/-- In a killed `D₃` layer at `p = 2`, exact generators of weights below three have additive
commutator depth. -/
lemma filtration_killed_exact
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration 2 G 3 = ⊥)
    {r s : ℕ} {x y : G}
    (hr : r < 3)
    (hs : s < 3)
    (hx : x ∈ exactGeneratorSet 2 G r)
    (hy : y ∈ exactGeneratorSet 2 G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration 2 G (r + s) := by
  have hrpos : 0 < r :=
    exact_set_pos (p := 2) hx
  have hspos : 0 < s :=
    exact_set_pos (p := 2) hy
  have trivial_of_mem_D3 :
      ∀ {g : G}, g ∈ zassenhausFiltration 2 G 3 → g = 1 := by
    intro g hg
    have hgbot : g ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hg
    simpa using Subgroup.mem_bot.mp hgbot
  have exact_one_one :
      ∀ {u v : G},
        u ∈ exactGeneratorSet 2 G 1 →
        v ∈ exactGeneratorSet 2 G 1 →
          ⁅u, v⁆ ∈ zassenhausFiltration 2 G 2 := by
    intro u v _hu _hv
    exact
      exact_subset_filtration
        (exact_set_series
          (p := 2) (i := 0) (j := 0) (x := u) (y := v)
          (Subgroup.mem_top u) (Subgroup.mem_top v))
  have exact_one_two :
      ∀ {u v : G},
        u ∈ exactGeneratorSet 2 G 1 →
        v ∈ exactGeneratorSet 2 G 2 →
          ⁅u, v⁆ ∈ zassenhausFiltration 2 G 3 := by
    intro u v _hu hv
    rcases
        exact_or_sq
          (p := 2) rfl hv with hv_lcs | ⟨w, hwv⟩
    · exact
        exact_subset_filtration
          (exact_set_series
            (p := 2) (i := 0) (j := 1) (x := u) (y := v)
            (Subgroup.mem_top u) hv_lcs)
    · have hsq :
          ⁅u, w ^ 2⁆ ∈ zassenhausFiltration 2 G 3 := by
        simpa using
          (element_sq_filtration
            (G := G) (i := 0) (j := 0) (x := u) (y := w)
            (Subgroup.mem_top u) (Subgroup.mem_top w))
      simpa [hwv] using hsq
  have exact_two_one :
      ∀ {u v : G},
        u ∈ exactGeneratorSet 2 G 2 →
        v ∈ exactGeneratorSet 2 G 1 →
          ⁅u, v⁆ ∈ zassenhausFiltration 2 G 3 := by
    intro u v hu _hv
    rcases
        exact_or_sq
          (p := 2) rfl hu with hu_lcs | ⟨w, hwu⟩
    · exact
        exact_subset_filtration
          (exact_set_series
            (p := 2) (i := 1) (j := 0) (x := u) (y := v)
            hu_lcs (Subgroup.mem_top v))
    · have hsq :
          ⁅w ^ 2, v⁆ ∈ zassenhausFiltration 2 G 3 := by
        simpa using
          (commutator_sq_filtration
            (G := G) (i := 0) (j := 0) (x := w) (y := v)
            (Subgroup.mem_top w) (Subgroup.mem_top v))
      simpa [hwu] using hsq
  have exact_two_two :
      ∀ {u v : G},
        u ∈ exactGeneratorSet 2 G 2 →
        v ∈ exactGeneratorSet 2 G 2 →
          ⁅u, v⁆ ∈ zassenhausFiltration 2 G 4 := by
    intro u v hu hv
    rcases
        exact_or_sq
          (p := 2) rfl hu with hu_lcs | ⟨a, hau⟩
    · rcases
          exact_or_sq
            (p := 2) rfl hv with hv_lcs | ⟨b, hbv⟩
      · exact
          exact_subset_filtration
            (exact_set_series
              (p := 2) (i := 1) (j := 1) (x := u) (y := v)
              hu_lcs hv_lcs)
      · have hsq :
            ⁅u, b ^ 2⁆ ∈ zassenhausFiltration 2 G 4 := by
          simpa using
            (element_sq_filtration
              (G := G) (i := 1) (j := 0) (x := u) (y := b)
              hu_lcs (Subgroup.mem_top b))
        simpa [hbv] using hsq
    · rcases
          exact_or_sq
            (p := 2) rfl hv with hv_lcs | ⟨b, hbv⟩
      · have hsq :
            ⁅a ^ 2, v⁆ ∈ zassenhausFiltration 2 G 4 := by
          simpa using
            (commutator_sq_filtration
              (G := G) (i := 0) (j := 1) (x := a) (y := v)
              (Subgroup.mem_top a) hv_lcs)
        simpa [hau] using hsq
      · have hD3 :
            ⁅a ^ 2, b ^ 2⁆ ∈ zassenhausFiltration 2 G 3 := by
          simpa using
            (element_sq_filtration
              (G := G) (i := 0) (j := 0) (x := a ^ 2) (y := b)
              (Subgroup.mem_top (a ^ 2)) (Subgroup.mem_top b))
        have hone : ⁅a ^ 2, b ^ 2⁆ = 1 :=
          trivial_of_mem_D3 hD3
        have hone_uv : ⁅u, v⁆ = 1 := by
          simpa [← hau, ← hbv] using hone
        rw [hone_uv]
        exact Subgroup.one_mem (zassenhausFiltration 2 G 4)
  have hr_cases : r = 1 ∨ r = 2 := by omega
  have hs_cases : s = 1 ∨ s = 2 := by omega
  rcases hr_cases with rfl | rfl
  · rcases hs_cases with rfl | rfl
    · exact exact_one_one hx hy
    · exact exact_one_two hx hy
  · rcases hs_cases with rfl | rfl
    · exact exact_two_one hx hy
    · exact exact_two_two hx hy

/-- At `p = 3`, an exact generator of weight three is either a third lower-central element or
an ordinary cube. -/
lemma exact_or_cube
    {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ exactGeneratorSet p G 3) :
    g ∈ Subgroup.lowerCentralSeries G 2 ∨ ∃ x : G, x ^ 3 = g := by
  subst p
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    left
    have hi : i = 2 := by
      simpa using hweight
    subst i
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · by_cases hj1 : j = 1
    · subst j
      right
      have hi : i = 0 := by
        simpa using hweight
      subst i
      exact ⟨x, by simpa using hpow⟩
    · have hj2 : 2 ≤ j := by omega
      have hnine_le_pow : 9 ≤ 3 ^ j := by
        simpa using
          (pow_le_pow_right' (a := 3) (n := 2) (m := j)
            (by omega : 1 ≤ 3) hj2)
      have hnine_le : 9 ≤ (i + 1) * 3 ^ j := by
        exact hnine_le_pow.trans
          (by
            exact Nat.le_mul_of_pos_left (3 ^ j) (Nat.succ_pos i))
      omega

/-- For primes other than two and three, an exact generator of weight three comes only from the
third lower-central term. -/
lemma exact_set_ne
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ exactGeneratorSet p G 3) :
    g ∈ Subgroup.lowerCentralSeries G 2 := by
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    have hi : i = 2 := by
      simpa using hweight
    subst i
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
    have hp4 : 4 ≤ p := by
      have hp2_le : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      omega
    have hp_le_pow : p ≤ p ^ j := by
      simpa using
        (pow_le_pow_right' (a := p) (n := 1) (m := j)
          (by omega : 1 ≤ p) hj_pos)
    have hfour_le : 4 ≤ (i + 1) * p ^ j := by
      calc
        4 ≤ p := hp4
        _ ≤ p ^ j := hp_le_pow
        _ ≤ (i + 1) * p ^ j := by
          exact Nat.le_mul_of_pos_left (p ^ j) (Nat.succ_pos i)
    omega

/-- For primes at least five, exact generators below weight four lie in their matching
lower-central terms. -/
lemma exact_four_pred
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 4)
    (hg : g ∈ exactGeneratorSet p G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) := by
  have hnpos : 0 < n :=
    exact_set_pos (p := p) hg
  by_cases hn1 : n = 1
  · have hpred : n - 1 = 0 := by omega
    rw [hpred]
    exact Subgroup.mem_top g
  · by_cases hn2 : n = 2
    · have hpred : n - 1 = 1 := by omega
      rw [hpred]
      exact
        exact_series_ne
          (p := p) hp2 (by simpa [hn2] using hg)
    · have hn3 : n = 3 := by omega
      have hpred : n - 1 = 2 := by omega
      rw [hpred]
      exact
        exact_set_ne
          (p := p) hp2 hp3 (by simpa [hn3] using hg)

/-- For primes at least five, exact generators below weight five lie in their matching
lower-central terms. -/
lemma five_lcs_pred
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 5)
    (hg : g ∈ exactGeneratorSet p G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) := by
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    have hn_eq : n = i + 1 := by
      simpa using hweight
    have hpred : n - 1 = i := by omega
    rw [hpred]
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
    have hp5 : 5 ≤ p :=
      (Fact.out : Nat.Prime p).five_le_of_ne_two_of_ne_three hp2 hp3
    have hp_le_pow : p ≤ p ^ j := by
      simpa using
        (pow_le_pow_right' (a := p) (n := 1) (m := j)
          (by omega : 1 ≤ p) hj_pos)
    have hfive_le : 5 ≤ (i + 1) * p ^ j := by
      calc
        5 ≤ p := hp5
        _ ≤ p ^ j := hp_le_pow
        _ ≤ (i + 1) * p ^ j := by
          exact Nat.le_mul_of_pos_left (p ^ j) (Nat.succ_pos i)
    omega

/-- At `p = 3`, exact generators below weight four are lower-central except for the possible
weight-three cube case. -/
lemma exact_four_cases
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 4)
    (hg : g ∈ exactGeneratorSet 3 G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) ∨
      n = 3 ∧ ∃ x : G, x ^ 3 = g := by
  by_cases hnlt3 : n < 3
  · left
    exact
      exact_set_pred
        (p := 3) (by norm_num) hnlt3 hg
  · have hn3 : n = 3 := by omega
    rcases
        exact_or_cube
          (p := 3) rfl (by simpa [hn3] using hg) with h_lcs | hcube
    · left
      have hpred : n - 1 = 2 := by omega
      simpa [hpred] using h_lcs
    · right
      exact ⟨hn3, hcube⟩

/-- At `p = 3`, an exact generator of weight four comes from the fourth lower-central term. -/
lemma exact_set_four
    {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ exactGeneratorSet p G 4) :
    g ∈ Subgroup.lowerCentralSeries G 3 := by
  subst p
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    have hi : i = 3 := by
      simpa using hweight
    subst i
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · by_cases hj1 : j = 1
    · subst j
      omega
    · have hj2 : 2 ≤ j := by omega
      have hnine_le_pow : 9 ≤ 3 ^ j := by
        simpa using
          (pow_le_pow_right' (a := 3) (n := 2) (m := j)
            (by omega : 1 ≤ 3) hj2)
      have hnine_le : 9 ≤ (i + 1) * 3 ^ j := by
        exact hnine_le_pow.trans
          (by
            exact Nat.le_mul_of_pos_left (3 ^ j) (Nat.succ_pos i))
      omega

/-- At `p = 3`, exact generators below weight five are lower-central except for the possible
weight-three cube case. -/
lemma exact_five_cases
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 5)
    (hg : g ∈ exactGeneratorSet 3 G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) ∨
      n = 3 ∧ ∃ x : G, x ^ 3 = g := by
  by_cases hnlt4 : n < 4
  · exact exact_four_cases hnlt4 hg
  · have hn4 : n = 4 := by omega
    left
    have hpred : n - 1 = 3 := by omega
    rw [hpred]
    exact
      exact_set_four
        (p := 3) rfl (by simpa [hn4] using hg)

/-- A raw `p = 3` Zassenhaus generator at level four is either genuinely lower-central of
weight four or already lies in `D₅`. -/
lemma four_or_five
    {G : Type*} [Group G] {g : G}
    (hg : g ∈ zassenhausGeneratorSet 3 G 4) :
    g ∈ Subgroup.lowerCentralSeries G 3 ∨ g ∈ zassenhausFiltration 3 G 5 := by
  rcases subset_exact_union (p := 3) (G := G) 4 hg with
    hExact | hHigh
  · left
    exact
      exact_set_four
        (p := 3) rfl hExact
  · right
    exact set_subset_filtration hHigh

/-- At `p = 3`, commutators with a right input in `D₄` land in `D₅`. -/
lemma element_filtration_five
    {G : Type*} [Group G]
    (x : G) {y : G}
    (hy : y ∈ zassenhausFiltration 3 G 4) :
    ⁅x, y⁆ ∈ zassenhausFiltration 3 G 5 := by
  let K : Subgroup G := zassenhausFiltration 3 G 5
  haveI : K.Normal := zassenhausFiltration_normal 3 G 5
  have comm_right_mem_K :
      ∀ {u v : G}, v ∈ K → ⁅u, v⁆ ∈ K := by
    intro u v hv
    rw [commutatorElement_def]
    exact
      K.mul_mem
        ((show K.Normal from inferInstance).conj_mem v hv u)
        (K.inv_mem hv)
  have hgen :
      ∀ {u v : G},
        u ∈ zassenhausGeneratorSet 3 G 1 →
        v ∈ zassenhausGeneratorSet 3 G 4 →
          ⁅u, v⁆ ∈ zassenhausFiltration 3 G (1 + 4) := by
    intro u v _hu hv
    rcases four_or_five hv with
      hv_lcs | hvK
    · have hcomm :
          ⁅u, v⁆ ∈ zassenhausFiltration 3 G ((0 + 1) + (3 + 1)) :=
        commutator_element_series
          (p := 3) (Subgroup.mem_top u) hv_lcs
      simpa using hcomm
    · simpa [K] using comm_right_mem_K hvK
  have hx : x ∈ zassenhausFiltration 3 G 1 := by
    rw [zassenhausFiltration_one]
    exact Subgroup.mem_top x
  have h :=
    element_set_bound
      (p := 3) (G := G) (r := 1) (s := 4) hgen hx hy
  simpa using h

/-- At `p = 3`, the quotient `D₄/D₅` has exponent three. -/
lemma filtration_five_four
    {G : Type*} [Group G]
    {x : G}
    (hx : x ∈ zassenhausFiltration 3 G 4) :
    x ^ 3 ∈ zassenhausFiltration 3 G 5 := by
  let K : Subgroup G := zassenhausFiltration 3 G 5
  haveI : K.Normal := zassenhausFiltration_normal 3 G 5
  have comm_right_mem_K :
      ∀ {u v : G}, v ∈ K → ⁅u, v⁆ ∈ K := by
    intro u v hv
    rw [commutatorElement_def]
    exact
      K.mul_mem
        ((show K.Normal from inferInstance).conj_mem v hv u)
        (K.inv_mem hv)
  have comm_left_mem_K :
      ∀ {u v : G}, u ∈ K → ⁅u, v⁆ ∈ K := by
    intro u v hu
    have hinv : ⁅v, u⁆⁻¹ ∈ K :=
      K.inv_mem (comm_right_mem_K hu)
    simpa [commutatorElement_inv] using hinv
  have hpow :
      ∀ {a : G}, a ∈ zassenhausGeneratorSet 3 G 4 → a ^ 3 ∈ K := by
    intro a ha
    rcases four_or_five ha with
      ha_lcs | haK
    · have hgen : a ^ 3 ∈ zassenhausGeneratorSet 3 G 5 := by
        refine ⟨3, 1, a, ha_lcs, ?_, by simp⟩
        norm_num
      exact Subgroup.subset_closure hgen
    · exact K.pow_mem haK 3
  have hcomm :
      ∀ {a b : G},
        a ∈ zassenhausGeneratorSet 3 G 4 →
        b ∈ zassenhausGeneratorSet 3 G 4 →
          ⁅a, b⁆ ∈ K := by
    intro a b ha hb
    rcases four_or_five ha with
      ha_lcs | haK
    · rcases four_or_five hb with
        hb_lcs | hbK
      · have hcomm :
            ⁅a, b⁆ ∈ zassenhausFiltration 3 G ((3 + 1) + (3 + 1)) :=
          commutator_element_series
            (p := 3) ha_lcs hb_lcs
        exact zassenhausFiltration_antitone 3 G (by norm_num) hcomm
      · exact comm_right_mem_K hbK
    · exact comm_left_mem_K haK
  change x ∈ Subgroup.closure (zassenhausGeneratorSet 3 G 4) at hx
  simpa [K] using
    (closure_generator_commutator
      (p := 3) (G := G) (A := zassenhausGeneratorSet 3 G 4) (K := K)
      hpow hcomm hx)

/-- The p=3 degree-five cube-cube commutator estimate. -/
lemma element_cube_five
    {G : Type*} [Group G] (a b : G) :
    ⁅a ^ 3, b ^ 3⁆ ∈ zassenhausFiltration 3 G 5 := by
  let K : Subgroup G := zassenhausFiltration 3 G 5
  haveI : K.Normal := zassenhausFiltration_normal 3 G 5
  let c : G := ⁅a ^ 3, b⁆
  have hc4 : c ∈ zassenhausFiltration 3 G 4 := by
    simpa [c] using
      (commutator_cube_filtration
        (G := G) (i := 0) (j := 0) (x := a) (y := b)
        (Subgroup.mem_top a) (Subgroup.mem_top b))
  have hnested : ⁅b, c⁆ ∈ K := by
    simpa [K] using
      (element_filtration_five
        (G := G) b hc4)
  have happrox : ⁅a ^ 3, b ^ 3⁆ * (c ^ 3)⁻¹ ∈ K := by
    simpa [c] using
      (inv_element_nested
        (K := K) hnested 3)
  have hc_pow : c ^ 3 ∈ K := by
    simpa [K] using
      (filtration_five_four hc4)
  have hmul : (⁅a ^ 3, b ^ 3⁆ * (c ^ 3)⁻¹) * c ^ 3 ∈ K :=
    K.mul_mem happrox hc_pow
  simpa [K, mul_assoc] using hmul

/-- For primes at least five, exact-generator commutators below weight four have the expected
additive Zassenhaus bound. -/
lemma
    filtration_exact_five
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {G : Type*} [Group G]
    {r s : ℕ} {x y : G}
    (hr : r < 4)
    (hs : s < 4)
    (hx : x ∈ exactGeneratorSet p G r)
    (hy : y ∈ exactGeneratorSet p G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (r + s) := by
  have hrpos : 0 < r :=
    exact_set_pos (p := p) hx
  have hspos : 0 < s :=
    exact_set_pos (p := p) hy
  have hx_lcs :
      x ∈ Subgroup.lowerCentralSeries G (r - 1) :=
    exact_four_pred
      (p := p) hp2 hp3 hr hx
  have hy_lcs :
      y ∈ Subgroup.lowerCentralSeries G (s - 1) :=
    exact_four_pred
      (p := p) hp2 hp3 hs hy
  have hcomm :
      ⁅x, y⁆ ∈
        zassenhausFiltration p G (((r - 1) + 1) + ((s - 1) + 1)) :=
    exact_subset_filtration
      (exact_set_series
        (p := p) hx_lcs hy_lcs)
  have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
    omega
  simpa [hindex] using hcomm

/-- For primes at least five, exact-generator commutators below weight five have the expected
additive Zassenhaus bound. -/
lemma element_exact_five
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {G : Type*} [Group G]
    {r s : ℕ} {x y : G}
    (hr : r < 5)
    (hs : s < 5)
    (hx : x ∈ exactGeneratorSet p G r)
    (hy : y ∈ exactGeneratorSet p G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (r + s) := by
  have hrpos : 0 < r :=
    exact_set_pos (p := p) hx
  have hspos : 0 < s :=
    exact_set_pos (p := p) hy
  have hx_lcs :
      x ∈ Subgroup.lowerCentralSeries G (r - 1) :=
    five_lcs_pred
      (p := p) hp2 hp3 hr hx
  have hy_lcs :
      y ∈ Subgroup.lowerCentralSeries G (s - 1) :=
    five_lcs_pred
      (p := p) hp2 hp3 hs hy
  have hcomm :
      ⁅x, y⁆ ∈
        zassenhausFiltration p G (((r - 1) + 1) + ((s - 1) + 1)) :=
    exact_subset_filtration
      (exact_set_series
        (p := p) hx_lcs hy_lcs)
  have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
    omega
  simpa [hindex] using hcomm

/-- For primes at least seven, exact generators below weight six lie in their matching
lower-central terms. -/
lemma lcs_pred_seven
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 6)
    (hg : g ∈ exactGeneratorSet p G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) := by
  rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
  by_cases hj0 : j = 0
  · subst j
    have hn_eq : n = i + 1 := by
      simpa using hweight
    have hpred : n - 1 = i := by omega
    rw [hpred]
    have hxg : x = g := by
      simpa using hpow
    simpa [hxg] using hx
  · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
    have hp7 : 7 ≤ p := by
      have hpprime : Nat.Prime p := Fact.out
      have hp2_le : 2 ≤ p := hpprime.two_le
      by_contra hlt
      have hp_le_six : p ≤ 6 := by omega
      interval_cases p
      · exact (hp2 rfl).elim
      · exact (hp3 rfl).elim
      · norm_num at hpprime
      · exact (hp5 rfl).elim
      · norm_num at hpprime
    have hp_le_pow : p ≤ p ^ j := by
      simpa using
        (pow_le_pow_right' (a := p) (n := 1) (m := j)
          (by omega : 1 ≤ p) hj_pos)
    have hseven_le : 7 ≤ (i + 1) * p ^ j := by
      calc
        7 ≤ p := hp7
        _ ≤ p ^ j := hp_le_pow
        _ ≤ (i + 1) * p ^ j := by
          exact Nat.le_mul_of_pos_left (p ^ j) (Nat.succ_pos i)
    omega

/-- For primes at least seven, exact-generator commutators below weight six have the expected
additive Zassenhaus bound. -/
lemma exact_six_seven
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    {G : Type*} [Group G]
    {r s : ℕ} {x y : G}
    (hr : r < 6)
    (hs : s < 6)
    (hx : x ∈ exactGeneratorSet p G r)
    (hy : y ∈ exactGeneratorSet p G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (r + s) := by
  have hrpos : 0 < r :=
    exact_set_pos (p := p) hx
  have hspos : 0 < s :=
    exact_set_pos (p := p) hy
  have hx_lcs :
      x ∈ Subgroup.lowerCentralSeries G (r - 1) :=
    lcs_pred_seven
      (p := p) hp2 hp3 hp5 hr hx
  have hy_lcs :
      y ∈ Subgroup.lowerCentralSeries G (s - 1) :=
    lcs_pred_seven
      (p := p) hp2 hp3 hp5 hs hy
  have hcomm :
      ⁅x, y⁆ ∈
        zassenhausFiltration p G (((r - 1) + 1) + ((s - 1) + 1)) :=
    exact_subset_filtration
      (exact_set_series
        (p := p) hx_lcs hy_lcs)
  have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
    omega
  simpa [hindex] using hcomm

/-- At `p = 5`, exact generators below weight six are lower-central except for the possible
weight-five fifth-power case. -/
lemma six_five_cases
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 6)
    (hg : g ∈ exactGeneratorSet 5 G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) ∨
      n = 5 ∧ ∃ x : G, x ^ 5 = g := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases hnlt5 : n < 5
  · left
    exact
      five_lcs_pred
        (p := 5) (by norm_num) (by norm_num) hnlt5 hg
  · have hn5 : n = 5 := by omega
    rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
    by_cases hj0 : j = 0
    · subst j
      left
      have hi : i = 4 := by
        simpa [hn5] using hweight
      subst i
      have hpred : n - 1 = 4 := by omega
      rw [hpred]
      have hxg : x = g := by
        simpa using hpow
      simpa [hxg] using hx
    · right
      have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
      have hj1 : j = 1 := by
        by_contra hj_ne_one
        have hj2 : 2 ≤ j := by omega
        have hpow25 : 25 ≤ 5 ^ j := by
          simpa using
            (pow_le_pow_right' (a := 5) (n := 2) (m := j)
              (by omega : 1 ≤ 5) hj2)
        have hweight_ge : 25 ≤ (i + 1) * 5 ^ j := by
          exact hpow25.trans
            (Nat.le_mul_of_pos_left (5 ^ j) (Nat.succ_pos i))
        omega
      subst j
      have hi : i = 0 := by
        omega
      subst i
      exact ⟨hn5, x, by simpa using hpow⟩

/-- In a killed `D₆` layer at `p = 5`, additive exact-generator commutator depth follows from
the remaining fifth-power commutator estimate. -/
lemma six_5_fifth
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration 5 G 6 = ⊥)
    (hfifth :
      ∀ a b : G, ⁅a ^ 5, b⁆ ∈ zassenhausFiltration 5 G 6)
    {r s : ℕ} {x y : G}
    (hr : r < 6)
    (hs : s < 6)
    (hx : x ∈ exactGeneratorSet 5 G r)
    (hy : y ∈ exactGeneratorSet 5 G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration 5 G (r + s) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have trivial_of_mem_D6 :
      ∀ {g : G}, g ∈ zassenhausFiltration 5 G 6 → g = 1 := by
    intro g hg
    have hgbot : g ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hg
    simpa using Subgroup.mem_bot.mp hgbot
  have hfifth_right :
      ∀ a b : G, ⁅a, b ^ 5⁆ ∈ zassenhausFiltration 5 G 6 := by
    intro a b
    have hleft : ⁅b ^ 5, a⁆ ∈ zassenhausFiltration 5 G 6 := hfifth b a
    have hinv : ⁅b ^ 5, a⁆⁻¹ ∈ zassenhausFiltration 5 G 6 :=
      (zassenhausFiltration 5 G 6).inv_mem hleft
    simpa [commutatorElement_inv] using hinv
  rcases six_five_cases hr hx with
    hx_lcs | ⟨hr5, a, hax⟩
  · rcases six_five_cases hs hy with
      hy_lcs | ⟨hs5, b, hby⟩
    · have hcomm :
          ⁅x, y⁆ ∈
            zassenhausFiltration 5 G (((r - 1) + 1) + ((s - 1) + 1)) :=
        exact_subset_filtration
          (exact_set_series
            (p := 5) hx_lcs hy_lcs)
      have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
        have hrpos : 0 < r :=
          exact_set_pos (p := 5) hx
        have hspos : 0 < s :=
          exact_set_pos (p := 5) hy
        omega
      simpa [hindex] using hcomm
    · subst s
      have hD6 : ⁅x, b ^ 5⁆ ∈ zassenhausFiltration 5 G 6 :=
        hfifth_right x b
      have hone : ⁅x, b ^ 5⁆ = 1 := trivial_of_mem_D6 hD6
      have hone_xy : ⁅x, y⁆ = 1 := by
        simpa [hby] using hone
      rw [hone_xy]
      exact Subgroup.one_mem (zassenhausFiltration 5 G (r + 5))
  · rcases six_five_cases hs hy with
      hy_lcs | ⟨hs5, b, hby⟩
    · subst r
      have hD6 : ⁅a ^ 5, y⁆ ∈ zassenhausFiltration 5 G 6 :=
        hfifth a y
      have hone : ⁅a ^ 5, y⁆ = 1 := trivial_of_mem_D6 hD6
      have hone_xy : ⁅x, y⁆ = 1 := by
        simpa [hax] using hone
      rw [hone_xy]
      exact Subgroup.one_mem (zassenhausFiltration 5 G (5 + s))
    · subst r
      subst s
      have hD6 : ⁅a ^ 5, y⁆ ∈ zassenhausFiltration 5 G 6 :=
        hfifth a y
      have hone : ⁅a ^ 5, y⁆ = 1 := trivial_of_mem_D6 hD6
      have hone_xy : ⁅x, y⁆ = 1 := by
        simpa [hax] using hone
      rw [hone_xy]
      exact Subgroup.one_mem (zassenhausFiltration 5 G (5 + 5))

/-- At `p = 3`, exact generators below weight six are lower-central except for the possible
weight-three cube case. -/
lemma exact_six_cases
    {G : Type*} [Group G] {n : ℕ} {g : G}
    (hn : n < 6)
    (hg : g ∈ exactGeneratorSet 3 G n) :
    g ∈ Subgroup.lowerCentralSeries G (n - 1) ∨
      n = 3 ∧ ∃ x : G, x ^ 3 = g := by
  by_cases hnlt5 : n < 5
  · exact exact_five_cases hnlt5 hg
  · have hn5 : n = 5 := by omega
    left
    rcases hg with ⟨i, j, x, hx, hweight, hpow⟩
    by_cases hj0 : j = 0
    · subst j
      have hi : i = 4 := by
        simpa [hn5] using hweight
      subst i
      have hpred : n - 1 = 4 := by omega
      rw [hpred]
      have hxg : x = g := by
        simpa using hpow
      simpa [hxg] using hx
    · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
      have hthree_le_pow : 3 ≤ 3 ^ j := by
        simpa using
          (pow_le_pow_right' (a := 3) (n := 1) (m := j)
            (by omega : 1 ≤ 3) hj_pos)
      have hthree_le : 3 ≤ (i + 1) * 3 ^ j := by
        exact hthree_le_pow.trans
          (Nat.le_mul_of_pos_left (3 ^ j) (Nat.succ_pos i))
      have hj1 : j = 1 := by
        by_contra hj_ne_one
        have hj2 : 2 ≤ j := by omega
        have hnine_le_pow : 9 ≤ 3 ^ j := by
          simpa using
            (pow_le_pow_right' (a := 3) (n := 2) (m := j)
              (by omega : 1 ≤ 3) hj2)
        have hnine_le : 9 ≤ (i + 1) * 3 ^ j := by
          exact hnine_le_pow.trans
            (Nat.le_mul_of_pos_left (3 ^ j) (Nat.succ_pos i))
        omega
      subst j
      omega

/-- In degree six at `p = 3`, additive exact-generator commutator depth is reduced to the
remaining cube-cube estimate in `D₆`. -/
lemma six_3_cube
    {G : Type*} [Group G]
    (hcube :
      ∀ a b : G, ⁅a ^ 3, b ^ 3⁆ ∈ zassenhausFiltration 3 G 6)
    {r s : ℕ} {x y : G}
    (hr : r < 6)
    (hs : s < 6)
    (hx : x ∈ exactGeneratorSet 3 G r)
    (hy : y ∈ exactGeneratorSet 3 G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration 3 G (r + s) := by
  rcases exact_six_cases hr hx with
    hx_lcs | ⟨hr3, a, hax⟩
  · rcases exact_six_cases hs hy with
      hy_lcs | ⟨hs3, b, hby⟩
    · have hcomm :
          ⁅x, y⁆ ∈
            zassenhausFiltration 3 G (((r - 1) + 1) + ((s - 1) + 1)) :=
        exact_subset_filtration
          (exact_set_series
            (p := 3) hx_lcs hy_lcs)
      have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
        have hrpos : 0 < r :=
          exact_set_pos (p := 3) hx
        have hspos : 0 < s :=
          exact_set_pos (p := 3) hy
        omega
      simpa [hindex] using hcomm
    · subst s
      have hcomm :
          ⁅x, b ^ 3⁆ ∈
            zassenhausFiltration 3 G (((r - 1) + 1) + 3 * (0 + 1)) :=
        element_cube_filtration
          (G := G) (i := r - 1) (j := 0) (x := x) (y := b)
          hx_lcs (Subgroup.mem_top b)
      have hrpos : 0 < r :=
        exact_set_pos (p := 3) hx
      have hindex : ((r - 1) + 1) + 3 * (0 + 1) = r + 3 := by
        omega
      simpa [hby, hindex] using hcomm
  · rcases exact_six_cases hs hy with
      hy_lcs | ⟨hs3, b, hby⟩
    · subst r
      have hcomm :
          ⁅a ^ 3, y⁆ ∈
            zassenhausFiltration 3 G (3 * (0 + 1) + ((s - 1) + 1)) :=
        commutator_cube_filtration
          (G := G) (i := 0) (j := s - 1) (x := a) (y := y)
          (Subgroup.mem_top a) hy_lcs
      have hspos : 0 < s :=
        exact_set_pos (p := 3) hy
      have hindex : 3 * (0 + 1) + ((s - 1) + 1) = 3 + s := by
        omega
      simpa [hax, hindex] using hcomm
    · subst r
      subst s
      simpa [hax, hby] using hcube a b

/-- In a killed `D₄` layer at `p = 3`, exact generators of weights below four have additive
commutator depth.  The only non-lower-central case is the cube-cube commutator, which is already
in `D₄` and hence trivial in the killed layer. -/
lemma element_killed_exact
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration 3 G 4 = ⊥)
    {r s : ℕ} {x y : G}
    (hr : r < 4)
    (hs : s < 4)
    (hx : x ∈ exactGeneratorSet 3 G r)
    (hy : y ∈ exactGeneratorSet 3 G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration 3 G (r + s) := by
  have hrpos : 0 < r :=
    exact_set_pos (p := 3) hx
  have hspos : 0 < s :=
    exact_set_pos (p := 3) hy
  have trivial_of_mem_D4 :
      ∀ {g : G}, g ∈ zassenhausFiltration 3 G 4 → g = 1 := by
    intro g hg
    have hgbot : g ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hg
    simpa using Subgroup.mem_bot.mp hgbot
  rcases exact_four_cases hr hx with
    hx_lcs | ⟨hr3, a, hax⟩
  · rcases exact_four_cases hs hy with
      hy_lcs | ⟨hs3, b, hby⟩
    · have hcomm :
          ⁅x, y⁆ ∈
            zassenhausFiltration 3 G (((r - 1) + 1) + ((s - 1) + 1)) :=
        exact_subset_filtration
          (exact_set_series
            (p := 3) hx_lcs hy_lcs)
      have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
        omega
      simpa [hindex] using hcomm
    · have hcomm :
          ⁅x, b ^ 3⁆ ∈
            zassenhausFiltration 3 G (((r - 1) + 1) + 3 * (0 + 1)) :=
        element_cube_filtration
          (G := G) (i := r - 1) (j := 0) (x := x) (y := b)
          hx_lcs (Subgroup.mem_top b)
      have hindex : ((r - 1) + 1) + 3 * (0 + 1) = r + s := by
        omega
      simpa [hby, hindex] using hcomm
  · rcases exact_four_cases hs hy with
      hy_lcs | ⟨hs3, b, hby⟩
    · have hcomm :
          ⁅a ^ 3, y⁆ ∈
            zassenhausFiltration 3 G (3 * (0 + 1) + ((s - 1) + 1)) :=
        commutator_cube_filtration
          (G := G) (i := 0) (j := s - 1) (x := a) (y := y)
          (Subgroup.mem_top a) hy_lcs
      have hindex : 3 * (0 + 1) + ((s - 1) + 1) = r + s := by
        omega
      simpa [hax, hindex] using hcomm
    · have hD4 :
          ⁅a ^ 3, b ^ 3⁆ ∈ zassenhausFiltration 3 G 4 := by
        simpa using
          (commutator_cube_filtration
            (G := G) (i := 0) (j := 0) (x := a) (y := b ^ 3)
            (Subgroup.mem_top a) (Subgroup.mem_top (b ^ 3)))
      have hone : ⁅a ^ 3, b ^ 3⁆ = 1 :=
        trivial_of_mem_D4 hD4
      have hone_xy : ⁅x, y⁆ = 1 := by
        simpa [hax, hby] using hone
      rw [hone_xy]
      exact Subgroup.one_mem (zassenhausFiltration 3 G (r + s))

/-- In a killed `D₅` layer at `p = 3`, the additive exact-generator commutator law follows
from a cube-cube estimate. -/
lemma
    five_3_cube
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration 3 G 5 = ⊥)
    (hcube :
      ∀ a b : G, ⁅a ^ 3, b ^ 3⁆ ∈ zassenhausFiltration 3 G 5)
    {r s : ℕ} {x y : G}
    (hr : r < 5)
    (hs : s < 5)
    (hx : x ∈ exactGeneratorSet 3 G r)
    (hy : y ∈ exactGeneratorSet 3 G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration 3 G (r + s) := by
  have trivial_of_mem_D5 :
      ∀ {g : G}, g ∈ zassenhausFiltration 3 G 5 → g = 1 := by
    intro g hg
    have hgbot : g ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hg
    simpa using Subgroup.mem_bot.mp hgbot
  rcases exact_five_cases hr hx with
    hx_lcs | ⟨hr3, a, hax⟩
  · rcases exact_five_cases hs hy with
      hy_lcs | ⟨hs3, b, hby⟩
    · have hcomm :
          ⁅x, y⁆ ∈
            zassenhausFiltration 3 G (((r - 1) + 1) + ((s - 1) + 1)) :=
        exact_subset_filtration
          (exact_set_series
            (p := 3) hx_lcs hy_lcs)
      have hindex : ((r - 1) + 1) + ((s - 1) + 1) = r + s := by
        have hrpos : 0 < r :=
          exact_set_pos (p := 3) hx
        have hspos : 0 < s :=
          exact_set_pos (p := 3) hy
        omega
      simpa [hindex] using hcomm
    · subst s
      have hcomm :
          ⁅x, b ^ 3⁆ ∈
            zassenhausFiltration 3 G (((r - 1) + 1) + 3 * (0 + 1)) :=
        element_cube_filtration
          (G := G) (i := r - 1) (j := 0) (x := x) (y := b)
          hx_lcs (Subgroup.mem_top b)
      have hrpos : 0 < r :=
        exact_set_pos (p := 3) hx
      have hindex : ((r - 1) + 1) + 3 * (0 + 1) = r + 3 := by
        omega
      simpa [hby, hindex] using hcomm
  · rcases exact_five_cases hs hy with
      hy_lcs | ⟨hs3, b, hby⟩
    · subst r
      have hcomm :
          ⁅a ^ 3, y⁆ ∈
            zassenhausFiltration 3 G (3 * (0 + 1) + ((s - 1) + 1)) :=
        commutator_cube_filtration
          (G := G) (i := 0) (j := s - 1) (x := a) (y := y)
          (Subgroup.mem_top a) hy_lcs
      have hspos : 0 < s :=
        exact_set_pos (p := 3) hy
      have hindex : 3 * (0 + 1) + ((s - 1) + 1) = 3 + s := by
        omega
      simpa [hax, hindex] using hcomm
    · have hD5 : ⁅a ^ 3, b ^ 3⁆ ∈ zassenhausFiltration 3 G 5 :=
        hcube a b
      have hone : ⁅a ^ 3, b ^ 3⁆ = 1 :=
        trivial_of_mem_D5 hD5
      have hone_xy : ⁅x, y⁆ = 1 := by
        simpa [hax, hby] using hone
      rw [hone_xy]
      exact Subgroup.one_mem (zassenhausFiltration 3 G (r + s))

/-- In a killed `D₅` layer at `p = 3`, exact generators of weights below five have additive
commutator depth. -/
lemma commutator_element_five
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration 3 G 5 = ⊥)
    {r s : ℕ} {x y : G}
    (hr : r < 5)
    (hs : s < 5)
    (hx : x ∈ exactGeneratorSet 3 G r)
    (hy : y ∈ exactGeneratorSet 3 G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration 3 G (r + s) := by
  exact
    five_3_cube
      (G := G) hbot
      (fun a b => element_cube_five a b)
      hr hs hx hy

/-- In a killed `D₄` layer, odd-prime exact generators of weights below four have additive
commutator depth. -/
lemma
    killed_exact_odd
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration p G 4 = ⊥)
    {r s : ℕ} {x y : G}
    (hr : r < 4)
    (hs : s < 4)
    (hx : x ∈ exactGeneratorSet p G r)
    (hy : y ∈ exactGeneratorSet p G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (r + s) := by
  by_cases hp3 : p = 3
  · subst p
    exact
      element_killed_exact
        (G := G) hbot hr hs hx hy
  · exact
      filtration_exact_five
        (p := p) hp2 hp3 hr hs hx hy

/-- In a killed `D₄` layer, exact generators of weights below four have additive commutator
depth for every prime. -/
lemma killed_exact_four
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (hbot : zassenhausFiltration p G 4 = ⊥)
    {r s : ℕ} {x y : G}
    (hr : r < 4)
    (hs : s < 4)
    (hx : x ∈ exactGeneratorSet p G r)
    (hy : y ∈ exactGeneratorSet p G s) :
    ⁅x, y⁆ ∈ zassenhausFiltration p G (r + s) := by
  by_cases hp2 : p = 2
  · subst p
    exact
      element_exact_four
        (G := G) hr hs hx hy
  · exact
      killed_exact_odd
        (p := p) hp2 hbot hr hs hx hy

/-- Each left-iterated Hall factor, raised to its prime-power binomial coefficient, already lies
in the final one-sided weighted commutator target. -/
lemma iterated_element_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a r : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (hr : r + 1 ≤ p ^ a) :
    leftIteratedElement x ⁅x, y⁆ r ^ Nat.choose (p ^ a) (r + 1) ∈
      zassenhausFiltration p G ((i + 1) * p ^ a + (j + 1)) := by
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hiter :
      leftIteratedElement x ⁅x, y⁆ r ∈
        Subgroup.lowerCentralSeries G (r * (i + 1) + (i + j + 1)) :=
    iterated_element_series hx hxy r
  have hfactor :=
    lower_choose_filtration
      (p := p) hiter hr (Nat.succ_ne_zero r)
  apply
    (zassenhausFiltration_antitone p G ?_) hfactor
  have hindex :
      r * (i + 1) + (i + j + 1) + 1 =
        (r + 1) * (i + 1) + (j + 1) := by
    ring
  rw [hindex]
  exact
    add_sub_multiplicity
      (p := p) (a := a) (k := r + 1)
      (i + 1) (j + 1) hr (Nat.succ_ne_zero r)

/-- The choose-powered factors in a prime-power left-conjugate orbit all lie in the one-sided
weighted Zassenhaus target. -/
lemma iterated_choose_filtration
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    leftIteratedChoose x ⁅x, y⁆ (p ^ a) ≤
      zassenhausFiltration p G ((i + 1) * p ^ a + (j + 1)) := by
  apply (Subgroup.closure_le _).2
  rintro z ⟨r, hr, rfl⟩
  exact
    iterated_element_filtration
      hx hy (by omega)

/-- Unequal pairwise brackets among the iterated left Hall factors begin in weighted
lower-central degree `3 * (i + 1) + 2 * (j + 1)`. -/
lemma iterated_pairwise_comm
    {G : Type*} [Group G]
    {i j : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    iteratedPairwiseComm x ⁅x, y⁆ ≤
      Subgroup.lowerCentralSeries G (3 * (i + 1) + 2 * (j + 1) - 1) := by
  apply Subgroup.normalClosure_le_normal
  rintro z ⟨r, s, hrs, rfl⟩
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
  have hcomm :
      ⁅leftIteratedElement x ⁅x, y⁆ r,
          leftIteratedElement x ⁅x, y⁆ s⁆ ∈
        Subgroup.lowerCentralSeries G
          ((r * (i + 1) + (i + j + 1)) +
            (s * (i + 1) + (i + j + 1)) + 1) :=
    lower_commutator_succ
      (r * (i + 1) + (i + j + 1))
      (s * (i + 1) + (i + j + 1))
      (Subgroup.commutator_mem_commutator hr hs)
  apply Subgroup.lowerCentralSeries_antitone ?_ hcomm
  have hrsum : 1 ≤ r + s := by
    omega
  have hmul : i + 1 ≤ (r + s) * (i + 1) := by
    simpa using Nat.mul_le_mul_right (i + 1) hrsum
  have hleft :
      3 * (i + 1) + 2 * (j + 1) - 1 =
        (i + 1) + (2 * i + 2 * j + 3) := by
    omega
  have hright :
      (r * (i + 1) + (i + j + 1)) +
          (s * (i + 1) + (i + j + 1)) + 1 =
        (r + s) * (i + 1) + (2 * i + 2 * j + 3) := by
    ring
  rw [hleft, hright]
  exact Nat.add_le_add_right hmul _

/-- A prime-power left-conjugate orbit is in its weighted Zassenhaus target up to an explicit
deeper mixed lower-central error term. -/
lemma conjugate_sup_series
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    leftConjugateProduct x ⁅x, y⁆ (p ^ a) ∈
      zassenhausFiltration p G ((i + 1) * p ^ a + (j + 1)) ⊔
        Subgroup.lowerCentralSeries G (3 * (i + 1) + 2 * (j + 1) - 1) := by
  exact
    (sup_le_sup
      (iterated_choose_filtration
        hx hy)
      (iterated_pairwise_comm hx hy))
      (sup_pairwise_comm
        x ⁅x, y⁆ (p ^ a))

/-- A power in the left commutator input is in its weighted Zassenhaus target up to the
first explicit mixed lower-central Hall error term. -/
lemma filtration_sup_series
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {i j a : ℕ} {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x ^ (p ^ a), y⁆ ∈
      zassenhausFiltration p G ((i + 1) * p ^ a + (j + 1)) ⊔
        Subgroup.lowerCentralSeries G (3 * (i + 1) + 2 * (j + 1) - 1) := by
  rw [commutator_element_conjugate]
  exact
    conjugate_sup_series
      hx hy

end Submission

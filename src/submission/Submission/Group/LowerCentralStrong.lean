import Mathlib

open scoped commutatorElement

namespace Submission

/-- Expand a commutator whose left input is a product. -/
lemma element_mul_left
    {G : Type*} [Group G] (x y z : G) :
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

/-- Expand a commutator whose right input is a product. -/
lemma element_mul_right
    {G : Type*} [Group G] (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ := by
  simp only [commutatorElement_def]
  group

/-- Recurrence for a commutator whose left input is a natural power. -/
lemma element_left_succ
    {G : Type*} [Group G] (x y : G) (n : ℕ) :
    ⁅x ^ (n + 1), y⁆ =
      x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ * ⁅x ^ n, y⁆ := by
  rw [pow_succ, element_mul_left]

/-- Recurrence for a commutator whose right input is a natural power. -/
lemma commutator_element_succ
    {G : Type*} [Group G] (x y : G) (n : ℕ) :
    ⁅x, y ^ (n + 1)⁆ =
      ⁅x, y ^ n⁆ * y ^ n * ⁅x, y⁆ * (y ^ n)⁻¹ := by
  rw [pow_succ, element_mul_right]

/-- If a basic commutator belongs to a normal subgroup, then so do commutators with natural
powers in the left input. -/
lemma commutator_element_left
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hxy : ⁅x, y⁆ ∈ K) :
    ∀ n : ℕ, ⁅x ^ n, y⁆ ∈ K := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, element_left_succ]
      exact
        K.mul_mem
          ((inferInstance : K.Normal).conj_mem ⁅x, y⁆ hxy (x ^ n))
          ih

/-- If a basic commutator belongs to a normal subgroup, then so do commutators with natural
powers in the right input. -/
lemma commutator_element_right
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hxy : ⁅x, y⁆ ∈ K) :
    ∀ n : ℕ, ⁅x, y ^ n⁆ ∈ K := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, commutator_element_succ]
      simpa [mul_assoc] using
        K.mul_mem
          ih
          ((inferInstance : K.Normal).conj_mem ⁅x, y⁆ hxy (y ^ n))

/-- If a basic commutator belongs to a normal subgroup, then commutators of arbitrary natural
powers belong to it as well. -/
lemma commutator_element_pow
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hxy : ⁅x, y⁆ ∈ K)
    (m n : ℕ) :
    ⁅x ^ m, y ^ n⁆ ∈ K := by
  exact
    commutator_element_right K
      (commutator_element_left K hxy m)
      n

/-- Right-coset congruence modulo a normal subgroup is equality in the quotient group. -/
lemma mul_inv_quotient
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G} :
    x * y⁻¹ ∈ K ↔
      QuotientGroup.mk' K x = QuotientGroup.mk' K y := by
  simpa [div_eq_mul_inv] using
    (QuotientGroup.eq_iff_div_mem (N := K) (x := x) (y := y)).symm

/-- Right-coset congruence modulo a normal subgroup is compatible with multiplication. -/
lemma inv_of_mem
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x x' y y' : G}
    (hx : x * x'⁻¹ ∈ K)
    (hy : y * y'⁻¹ ∈ K) :
    (x * y) * (x' * y')⁻¹ ∈ K := by
  rw [mul_inv_quotient K] at hx hy ⊢
  simp only [map_mul]
  rw [hx, hy]

/-- Right-coset congruence modulo a normal subgroup is compatible with inversion. -/
lemma of_inv_mem
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hxy : x * y⁻¹ ∈ K) :
    x⁻¹ * (y⁻¹)⁻¹ ∈ K := by
  rw [mul_inv_quotient K] at hxy ⊢
  simpa only [map_inv] using congrArg Inv.inv hxy

/-- Right-coset congruence modulo a normal subgroup is compatible with natural powers. -/
lemma mul_inv_pow
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hxy : x * y⁻¹ ∈ K)
    (n : ℕ) :
    x ^ n * (y ^ n)⁻¹ ∈ K := by
  rw [mul_inv_quotient K] at hxy ⊢
  simpa only [map_pow] using congrArg (fun z => z ^ n) hxy

/-- Right-coset congruence modulo a normal subgroup is compatible with commutators. -/
lemma inv_commutator
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x x' y y' : G}
    (hx : x * x'⁻¹ ∈ K)
    (hy : y * y'⁻¹ ∈ K) :
    ⁅x, y⁆ * ⁅x', y'⁆⁻¹ ∈ K := by
  rw [mul_inv_quotient K] at hx hy ⊢
  simp only [map_commutatorElement]
  rw [hx, hy]

/-- If two elements commute modulo a normal subgroup, natural powers distribute over their
product modulo that subgroup. -/
lemma mul_inv_commutator
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hxy : ⁅x, y⁆ ∈ K)
    (n : ℕ) :
    (x * y) ^ n * (x ^ n * y ^ n)⁻¹ ∈ K := by
  rw [mul_inv_quotient K]
  have hcomm :
      Commute (QuotientGroup.mk' K x) (QuotientGroup.mk' K y) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅x, y⁆).mpr hxy
  simpa only [map_mul, map_pow] using hcomm.mul_pow n

/-- If `x` commutes with its commutator with `y`, powers in the left input pull out of the
commutator. This is the class-two Hall collection identity. -/
lemma element_left_commute
    {G : Type*} [Group G]
    {x y : G}
    (hcomm : Commute x ⁅x, y⁆) :
    ∀ n : ℕ, ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [element_left_succ, ih]
      have hconj :
          x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ = ⁅x, y⁆ := by
        rw [(hcomm.pow_left n).eq, mul_inv_cancel_right]
      rw [hconj, ← pow_succ']

/-- If `y` commutes with the commutator of `x` and `y`, powers in the right input pull out of the
commutator. This is the symmetric class-two Hall collection identity. -/
lemma commutator_element_commute
    {G : Type*} [Group G]
    {x y : G}
    (hcomm : Commute y ⁅x, y⁆) :
    ∀ n : ℕ, ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [commutator_element_succ, ih]
      have hconj :
          y ^ n * ⁅x, y⁆ * (y ^ n)⁻¹ = ⁅x, y⁆ := by
        rw [(hcomm.pow_left n).eq, mul_inv_cancel_right]
      calc
        ⁅x, y⁆ ^ n * y ^ n * ⁅x, y⁆ * (y ^ n)⁻¹ =
            ⁅x, y⁆ ^ n * (y ^ n * ⁅x, y⁆ * (y ^ n)⁻¹) := by
              group
        _ = ⁅x, y⁆ ^ n * ⁅x, y⁆ := by rw [hconj]
        _ = ⁅x, y⁆ ^ (n + 1) := by rw [pow_succ]

/-- Class-two Hall collection modulo a normal subgroup, for powers in the left commutator input. -/
lemma inv_commutator_nested
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hnested : ⁅x, ⁅x, y⁆⁆ ∈ K)
    (n : ℕ) :
    ⁅x ^ n, y⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈ K := by
  rw [mul_inv_quotient K]
  have hcomm :
      Commute (QuotientGroup.mk' K x)
        ⁅QuotientGroup.mk' K x, QuotientGroup.mk' K y⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅x, ⁅x, y⁆⁆).mpr hnested
  simpa only [map_commutatorElement, map_pow] using
    element_left_commute hcomm n

/-- Class-two Hall collection modulo a normal subgroup, for powers in the right commutator input. -/
lemma inv_element_nested
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (hnested : ⁅y, ⁅x, y⁆⁆ ∈ K)
    (n : ℕ) :
    ⁅x, y ^ n⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈ K := by
  rw [mul_inv_quotient K]
  have hcomm :
      Commute (QuotientGroup.mk' K y)
        ⁅QuotientGroup.mk' K x, QuotientGroup.mk' K y⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅y, ⁅x, y⁆⁆).mpr hnested
  simpa only [map_commutatorElement, map_pow] using
    commutator_element_commute hcomm n

/-- Class-three Hall collection modulo a normal subgroup, for powers in the left commutator
input.  The first nontrivial binomial correction is the square-level commutator
`[x,[x,y]] ^ choose n 2`. -/
lemma commutator_element_nested
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (htriple : ⁅x, ⁅x, ⁅x, y⁆⁆⁆ ∈ K)
    (hcross : ⁅⁅x, y⁆, ⁅x, ⁅x, y⁆⁆⁆ ∈ K)
    (n : ℕ) :
    ⁅x ^ n, y⁆ *
        ((⁅x, ⁅x, y⁆⁆ ^ Nat.choose n 2) * (⁅x, y⁆ ^ n))⁻¹ ∈ K := by
  rw [mul_inv_quotient K]
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let X : G ⧸ K := q x
  let Y : G ⧸ K := q y
  let C : G ⧸ K := q ⁅x, y⁆
  let D : G ⧸ K := q ⁅x, ⁅x, y⁆⁆
  have hC : ⁅X, Y⁆ = C := by
    change ⁅q x, q y⁆ = q ⁅x, y⁆
    rw [map_commutatorElement]
  have hXD : Commute X D := by
    rw [← commutatorElement_eq_one_iff_commute]
    change ⁅q x, q ⁅x, ⁅x, y⁆⁆⁆ = 1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr htriple
  have hCD : Commute C D := by
    rw [← commutatorElement_eq_one_iff_commute]
    change ⁅q ⁅x, y⁆, q ⁅x, ⁅x, y⁆⁆⁆ = 1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hcross
  have hconj :
      ∀ m : ℕ, X ^ m * C * (X ^ m)⁻¹ = D ^ m * C := by
    intro m
    have hpull : ⁅X ^ m, C⁆ = D ^ m := by
      calc
        ⁅X ^ m, C⁆ = ⁅X, C⁆ ^ m :=
          element_left_commute hXD m
        _ = D ^ m := by
          congr 1
    calc
      X ^ m * C * (X ^ m)⁻¹ =
          ⁅X ^ m, C⁆ * C := by
            simp only [commutatorElement_def]
            group
      _ = D ^ m * C := by rw [hpull]
  have hcollect :
      ∀ m : ℕ, ⁅X ^ m, Y⁆ = D ^ Nat.choose m 2 * C ^ m := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hchoose :
            Nat.choose (m + 1) 2 = m + Nat.choose m 2 := by
          rw [show m + 1 = Nat.succ m by omega,
            show 2 = Nat.succ 1 by omega, Nat.choose_succ_succ,
            Nat.choose_one_right]
        rw [element_left_succ, hC, hconj m, ih]
        calc
          D ^ m * C * (D ^ Nat.choose m 2 * C ^ m) =
              D ^ m * (C * D ^ Nat.choose m 2) * C ^ m := by
                group
          _ = D ^ m * (D ^ Nat.choose m 2 * C) * C ^ m := by
                rw [(hCD.pow_right (Nat.choose m 2)).eq]
          _ = D ^ (m + Nat.choose m 2) * C ^ (m + 1) := by
                rw [pow_add, pow_succ]
                group
          _ = D ^ Nat.choose (m + 1) 2 * C ^ (m + 1) := by
                rw [hchoose]
  simpa only [q, X, Y, C, D, map_commutatorElement, map_pow, map_mul] using
    hcollect n

/-- Symmetric class-three Hall collection modulo a normal subgroup, for powers in the right
commutator input. -/
lemma mul_inv_nested
    {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y : G}
    (htriple : ⁅y, ⁅y, ⁅x, y⁆⁆⁆ ∈ K)
    (hcross : ⁅⁅x, y⁆, ⁅y, ⁅x, y⁆⁆⁆ ∈ K)
    (n : ℕ) :
    ⁅x, y ^ n⁆ *
        ((⁅x, y⁆ ^ n) * (⁅y, ⁅x, y⁆⁆ ^ Nat.choose n 2))⁻¹ ∈ K := by
  rw [mul_inv_quotient K]
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let X : G ⧸ K := q x
  let Y : G ⧸ K := q y
  let C : G ⧸ K := q ⁅x, y⁆
  let D : G ⧸ K := q ⁅y, ⁅x, y⁆⁆
  have hC : ⁅X, Y⁆ = C := by
    change ⁅q x, q y⁆ = q ⁅x, y⁆
    rw [map_commutatorElement]
  have hYD : Commute Y D := by
    rw [← commutatorElement_eq_one_iff_commute]
    change ⁅q y, q ⁅y, ⁅x, y⁆⁆⁆ = 1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr htriple
  have hCD : Commute C D := by
    rw [← commutatorElement_eq_one_iff_commute]
    change ⁅q ⁅x, y⁆, q ⁅y, ⁅x, y⁆⁆⁆ = 1
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hcross
  have hconj :
      ∀ m : ℕ, Y ^ m * C * (Y ^ m)⁻¹ = D ^ m * C := by
    intro m
    have hpull : ⁅Y ^ m, C⁆ = D ^ m := by
      calc
        ⁅Y ^ m, C⁆ = ⁅Y, C⁆ ^ m :=
          element_left_commute hYD m
        _ = D ^ m := by
          congr 1
    calc
      Y ^ m * C * (Y ^ m)⁻¹ =
          ⁅Y ^ m, C⁆ * C := by
            simp only [commutatorElement_def]
            group
      _ = D ^ m * C := by rw [hpull]
  have hcollect :
      ∀ m : ℕ, ⁅X, Y ^ m⁆ = C ^ m * D ^ Nat.choose m 2 := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hchoose :
            Nat.choose (m + 1) 2 = m + Nat.choose m 2 := by
          rw [show m + 1 = Nat.succ m by omega,
            show 2 = Nat.succ 1 by omega, Nat.choose_succ_succ,
            Nat.choose_one_right]
        rw [commutator_element_succ, hC, ih]
        calc
          C ^ m * D ^ Nat.choose m 2 * Y ^ m * C * (Y ^ m)⁻¹ =
              C ^ m * D ^ Nat.choose m 2 * (Y ^ m * C * (Y ^ m)⁻¹) := by
                group
          _ = C ^ m * D ^ Nat.choose m 2 * (D ^ m * C) := by
                exact
                  congrArg
                    (fun z => C ^ m * D ^ Nat.choose m 2 * z)
                    (hconj m)
          _ =
              C ^ m * (D ^ (Nat.choose m 2 + m) * C) := by
                rw [pow_add]
                group
          _ = C ^ m * (C * D ^ (Nat.choose m 2 + m)) := by
                rw [← (hCD.pow_right (Nat.choose m 2 + m)).eq]
          _ = C ^ (m + 1) * D ^ (m + Nat.choose m 2) := by
                rw [pow_succ, Nat.add_comm (Nat.choose m 2) m]
                group
          _ = C ^ (m + 1) * D ^ Nat.choose (m + 1) 2 := by
                rw [hchoose]
  simpa only [q, X, Y, C, D, map_commutatorElement, map_pow, map_mul] using
    hcollect n

/-- Iterated commutators with a fixed left input:
`c`, `[x,c]`, `[x,[x,c]]`, and so on. -/
def leftIteratedElement
    {G : Type*} [Group G]
    (x c : G) :
    ℕ → G
  | 0 => c
  | n + 1 => ⁅x, leftIteratedElement x c n⁆

@[simp]
lemma left_iterated_element
    {G : Type*} [Group G]
    (x c : G) :
    leftIteratedElement x c 0 = c :=
  rfl

@[simp]
lemma iterated_element_succ
    {G : Type*} [Group G]
    (x c : G)
    (n : ℕ) :
    leftIteratedElement x c (n + 1) =
      ⁅x, leftIteratedElement x c n⁆ :=
  rfl

/-- Conjugating an iterated commutator introduces the next iterated commutator as a left
factor. -/
lemma conjugate_iterated_element
    {G : Type*} [Group G]
    (x c : G)
    (n : ℕ) :
    x * leftIteratedElement x c n * x⁻¹ =
      leftIteratedElement x c (n + 1) *
        leftIteratedElement x c n := by
  simp only [iterated_element_succ, commutatorElement_def]
  group

/-- Product of the conjugate orbit `x^(n-1) c x^(-(n-1)) ... x c x^-1 c`. -/
def leftConjugateProduct
    {G : Type*} [Group G]
    (x c : G) :
    ℕ → G
  | 0 => 1
  | n + 1 => x ^ n * c * (x ^ n)⁻¹ * leftConjugateProduct x c n

@[simp]
lemma left_conjugate_orbit
    {G : Type*} [Group G]
    (x c : G) :
    leftConjugateProduct x c 0 = 1 :=
  rfl

@[simp]
lemma left_conjugate_succ
    {G : Type*} [Group G]
    (x c : G)
    (n : ℕ) :
    leftConjugateProduct x c (n + 1) =
      x ^ n * c * (x ^ n)⁻¹ * leftConjugateProduct x c n :=
  rfl

/-- A commutator with a powered left input is exactly the conjugate-orbit product of the basic
commutator. -/
lemma commutator_element_conjugate
    {G : Type*} [Group G]
    (x y : G) :
    ∀ n : ℕ,
      ⁅x ^ n, y⁆ = leftConjugateProduct x ⁅x, y⁆ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [element_left_succ, left_conjugate_succ, ih]

/-- Quotient form of the Three Subgroups Lemma: two rotated commutator bounds imply the third. -/
lemma commutator_rotate
    {G : Type*} [Group G]
    {H₁ H₂ H₃ K : Subgroup G} [K.Normal]
    (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ K)
    (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ K) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ K := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have map_eq_bot_of_le (H : Subgroup G) (hH : H ≤ K) :
      H.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff H).mpr
    simpa [q] using hH
  rw [← QuotientGroup.ker_mk' K, ← Subgroup.map_eq_bot_iff]
  rw [Subgroup.map_commutator, Subgroup.map_commutator]
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact map_eq_bot_of_le _ h₁
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact map_eq_bot_of_le _ h₂

/-- Strong centrality of the lower central series:
`[γ_(i+1), γ_(j+1)] ≤ γ_(i+j+2)` in Mathlib's zero-based indexing. -/
lemma lower_commutator_succ
    {G : Type*} [Group G] (i j : ℕ) :
    ⁅Subgroup.lowerCentralSeries G i, Subgroup.lowerCentralSeries G j⁆ ≤
      Subgroup.lowerCentralSeries G (i + j + 1) := by
  induction i generalizing j with
  | zero =>
      simpa [Subgroup.lowerCentralSeries_zero, Subgroup.lowerCentralSeries_succ,
        Subgroup.commutator_comm] using
        (show
          ⁅Subgroup.lowerCentralSeries G j, (⊤ : Subgroup G)⁆ ≤
            Subgroup.lowerCentralSeries G (j + 1) from le_rfl)
  | succ i ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      apply commutator_rotate
      · have h :
            ⁅Subgroup.lowerCentralSeries G (j + 1), Subgroup.lowerCentralSeries G i⁆ ≤
              Subgroup.lowerCentralSeries G (i + j + 2) := by
          rw [Subgroup.commutator_comm]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (j + 1)
        rw [Subgroup.commutator_comm (⊤ : Subgroup G) (Subgroup.lowerCentralSeries G j)]
        change
          ⁅Subgroup.lowerCentralSeries G (j + 1), Subgroup.lowerCentralSeries G i⁆ ≤
            Subgroup.lowerCentralSeries G (i + 1 + j + 1)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · have h :
            ⁅Subgroup.lowerCentralSeries G j, Subgroup.lowerCentralSeries G i⁆ ≤
              Subgroup.lowerCentralSeries G (i + j + 1) := by
          rw [Subgroup.commutator_comm]
          exact ih j
        exact
          (Subgroup.commutator_mono h le_rfl).trans
            (by
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (show
                  ⁅Subgroup.lowerCentralSeries G (i + j + 1), (⊤ : Subgroup G)⁆ ≤
                    Subgroup.lowerCentralSeries G (i + j + 2) from le_rfl))

/-- Each additional left-nested commutator with an element of `γ_(i+1)` increases the
lower-central index by `i + 1`. -/
lemma iterated_element_series
    {G : Type*} [Group G]
    {i j : ℕ}
    {x c : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hc : c ∈ Subgroup.lowerCentralSeries G j) :
    ∀ n : ℕ,
      leftIteratedElement x c n ∈
        Subgroup.lowerCentralSeries G (n * (i + 1) + j) := by
  intro n
  induction n with
  | zero =>
      simpa using hc
  | succ n ih =>
      have hmem :
          ⁅x, leftIteratedElement x c n⁆ ∈
            Subgroup.lowerCentralSeries G (i + (n * (i + 1) + j) + 1) :=
        lower_commutator_succ i (n * (i + 1) + j)
          (Subgroup.commutator_mem_commutator hx ih)
      have hindex :
          i + (n * (i + 1) + j) + 1 =
            (n + 1) * (i + 1) + j := by
        ring
      simpa [hindex] using hmem

/-- The class-two collection error for a power in the left commutator input belongs to the next
relevant lower-central term. In one-based notation the bound is
`[x^n,y] [x,y]^-n ∈ γ_(2(i+1)+(j+1))`. -/
lemma inv_commutator_series
    {G : Type*} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x ^ n, y⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
      Subgroup.lowerCentralSeries G (2 * i + j + 2) := by
  let K : Subgroup G := Subgroup.lowerCentralSeries G (2 * i + j + 2)
  letI : K.Normal := inferInstance
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hnested :
      ⁅x, ⁅x, y⁆⁆ ∈ K := by
    have hmem :
        ⁅x, ⁅x, y⁆⁆ ∈
          Subgroup.lowerCentralSeries G (i + (i + j + 1) + 1) :=
      lower_commutator_succ i (i + j + 1)
        (Subgroup.commutator_mem_commutator hx hxy)
    simpa [K, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  exact
    inv_commutator_nested
      K hnested n

/-- The symmetric class-two collection error for a power in the right commutator input belongs
to the next relevant lower-central term. In one-based notation the bound is
`[x,y^n] [x,y]^-n ∈ γ_((i+1)+2(j+1))`. -/
lemma inv_element_series
    {G : Type*} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x, y ^ n⁆ * (⁅x, y⁆ ^ n)⁻¹ ∈
      Subgroup.lowerCentralSeries G (i + 2 * j + 2) := by
  let K : Subgroup G := Subgroup.lowerCentralSeries G (i + 2 * j + 2)
  letI : K.Normal := inferInstance
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hnested :
      ⁅y, ⁅x, y⁆⁆ ∈ K := by
    have hmem :
        ⁅y, ⁅x, y⁆⁆ ∈
          Subgroup.lowerCentralSeries G (j + (i + j + 1) + 1) :=
      lower_commutator_succ j (i + j + 1)
        (Subgroup.commutator_mem_commutator hy hxy)
    simpa [K, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  exact
    inv_element_nested
      K hnested n

/-- The class-three collection error for a power in the left commutator input belongs to the
third relevant lower-central term.  In one-based notation the extracted expression is
`[x,[x,y]]^(choose n 2) * [x,y]^n`, and the remaining error has weight
`3(i+1) + (j+1)`. -/
lemma element_nested_series
    {G : Type*} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x ^ n, y⁆ *
        ((⁅x, ⁅x, y⁆⁆ ^ Nat.choose n 2) * (⁅x, y⁆ ^ n))⁻¹ ∈
      Subgroup.lowerCentralSeries G (3 * i + j + 3) := by
  let K : Subgroup G := Subgroup.lowerCentralSeries G (3 * i + j + 3)
  letI : K.Normal := inferInstance
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hnested :
      ⁅x, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries G (2 * i + j + 2) := by
    have hmem :
        ⁅x, ⁅x, y⁆⁆ ∈
          Subgroup.lowerCentralSeries G (i + (i + j + 1) + 1) :=
      lower_commutator_succ i (i + j + 1)
        (Subgroup.commutator_mem_commutator hx hxy)
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  have htriple : ⁅x, ⁅x, ⁅x, y⁆⁆⁆ ∈ K := by
    have hmem :
        ⁅x, ⁅x, ⁅x, y⁆⁆⁆ ∈
          Subgroup.lowerCentralSeries G (i + (2 * i + j + 2) + 1) :=
      lower_commutator_succ i (2 * i + j + 2)
        (Subgroup.commutator_mem_commutator hx hnested)
    have hindex :
        i + (2 * i + j + 2) + 1 = 3 * i + j + 3 := by
      omega
    change ⁅x, ⁅x, ⁅x, y⁆⁆⁆ ∈ Subgroup.lowerCentralSeries G (3 * i + j + 3)
    rw [← hindex]
    exact hmem
  have hcross : ⁅⁅x, y⁆, ⁅x, ⁅x, y⁆⁆⁆ ∈ K := by
    have hmem :
        ⁅⁅x, y⁆, ⁅x, ⁅x, y⁆⁆⁆ ∈
          Subgroup.lowerCentralSeries G ((i + j + 1) + (2 * i + j + 2) + 1) :=
      lower_commutator_succ (i + j + 1) (2 * i + j + 2)
        (Subgroup.commutator_mem_commutator hxy hnested)
    exact
      Subgroup.lowerCentralSeries_antitone (by omega)
        (show
          ⁅⁅x, y⁆, ⁅x, ⁅x, y⁆⁆⁆ ∈
            Subgroup.lowerCentralSeries G ((i + j + 1) + (2 * i + j + 2) + 1) from hmem)
  exact
    commutator_element_nested
      K htriple hcross n

/-- Symmetric class-three collection error for a power in the right commutator input. -/
lemma inv_nested_series
    {G : Type*} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (n : ℕ) :
    ⁅x, y ^ n⁆ *
        ((⁅x, y⁆ ^ n) * (⁅y, ⁅x, y⁆⁆ ^ Nat.choose n 2))⁻¹ ∈
      Subgroup.lowerCentralSeries G (i + 3 * j + 3) := by
  let K : Subgroup G := Subgroup.lowerCentralSeries G (i + 3 * j + 3)
  letI : K.Normal := inferInstance
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    lower_commutator_succ i j
      (Subgroup.commutator_mem_commutator hx hy)
  have hnested :
      ⁅y, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries G (i + 2 * j + 2) := by
    have hmem :
        ⁅y, ⁅x, y⁆⁆ ∈
          Subgroup.lowerCentralSeries G (j + (i + j + 1) + 1) :=
      lower_commutator_succ j (i + j + 1)
        (Subgroup.commutator_mem_commutator hy hxy)
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  have htriple : ⁅y, ⁅y, ⁅x, y⁆⁆⁆ ∈ K := by
    have hmem :
        ⁅y, ⁅y, ⁅x, y⁆⁆⁆ ∈
          Subgroup.lowerCentralSeries G (j + (i + 2 * j + 2) + 1) :=
      lower_commutator_succ j (i + 2 * j + 2)
        (Subgroup.commutator_mem_commutator hy hnested)
    have hindex :
        j + (i + 2 * j + 2) + 1 = i + 3 * j + 3 := by
      omega
    change ⁅y, ⁅y, ⁅x, y⁆⁆⁆ ∈ Subgroup.lowerCentralSeries G (i + 3 * j + 3)
    rw [← hindex]
    exact hmem
  have hcross : ⁅⁅x, y⁆, ⁅y, ⁅x, y⁆⁆⁆ ∈ K := by
    have hmem :
        ⁅⁅x, y⁆, ⁅y, ⁅x, y⁆⁆⁆ ∈
          Subgroup.lowerCentralSeries G ((i + j + 1) + (i + 2 * j + 2) + 1) :=
      lower_commutator_succ (i + j + 1) (i + 2 * j + 2)
        (Subgroup.commutator_mem_commutator hxy hnested)
    exact
      Subgroup.lowerCentralSeries_antitone (by omega)
        (show
          ⁅⁅x, y⁆, ⁅y, ⁅x, y⁆⁆⁆ ∈
            Subgroup.lowerCentralSeries G ((i + j + 1) + (i + 2 * j + 2) + 1) from hmem)
  exact
    mul_inv_nested
      K htriple hcross n

end Submission

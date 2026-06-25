import Submission.Group.Edmonton.MinimalNormal
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.NoncommRing

/-!
# The Edmonton Notes on Nilpotent Groups: Section 3 commutator identities

This file begins Section 3 with the Hall-Witt identity.
-/

namespace Submission
namespace Edmonton

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- Hall's left-normed triple commutator `[x,y,z] = [[x,y],z]`. -/
def hallTripleCommutator (x y z : G) : G :=
  hallCommutator (hallCommutator x y) z

/-- **Hall, Lemma 3.1 (Hall-Witt identity).** -/
theorem hallWitt_identity (x y z : G) :
    hallConjugate (hallTripleCommutator x y⁻¹ z) y *
        hallConjugate (hallTripleCommutator y z⁻¹ x) z *
        hallConjugate (hallTripleCommutator z x⁻¹ y) x =
      1 := by
  simp [hallTripleCommutator, hallCommutator, hallConjugate, mul_assoc]

/-- **Hall, Lemma 3.2 (Three Subgroups Lemma modulo a normal subgroup).**
If two cyclic rotations of a triple subgroup commutator lie in `N`, then
so does the third. -/
theorem threeSubgroups_le {X Y Z N : Subgroup G} [N.Normal]
    (hX : ⁅⁅Y, Z⁆, X⁆ ≤ N) (hY : ⁅⁅Z, X⁆, Y⁆ ≤ N) :
    ⁅⁅X, Y⁆, Z⁆ ≤ N := by
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hXmap : (⁅⁅Y, Z⁆, X⁆).map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa [f, QuotientGroup.ker_mk'] using hX
  have hYmap : (⁅⁅Z, X⁆, Y⁆).map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa [f, QuotientGroup.ker_mk'] using hY
  have hZmap :
      ⁅⁅X.map f, Y.map f⁆, Z.map f⁆ = ⊥ := by
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · simpa only [← Subgroup.map_commutator] using hXmap
    · simpa only [← Subgroup.map_commutator] using hYmap
  have hmap : (⁅⁅X, Y⁆, Z⁆).map f = ⊥ := by
    simpa only [Subgroup.map_commutator] using hZmap
  rw [Subgroup.map_eq_bot_iff] at hmap
  simpa [f, QuotientGroup.ker_mk'] using hmap

/-- **Hall, Corollary after Lemma 3.2.** If `X`, `Y`, and `Z` are normal,
then `[X,Y,Z]` lies in `[Y,Z,X][Z,X,Y]`. -/
theorem triple_cyclic_sup {X Y Z : Subgroup G} [X.Normal] [Y.Normal] [Z.Normal] :
    ⁅⁅X, Y⁆, Z⁆ ≤ ⁅⁅Y, Z⁆, X⁆ ⊔ ⁅⁅Z, X⁆, Y⁆ := by
  apply threeSubgroups_le
  · exact le_sup_left
  · exact le_sup_right

/-- Hall's cyclic reformulation of the Hall-Witt identity. -/
theorem hall_witt_cyclic (x y z : G) :
    hallTripleCommutator x y (hallConjugate z x) *
        hallTripleCommutator z x (hallConjugate y z) *
        hallTripleCommutator y z (hallConjugate x y) =
      1 := by
  simp [hallTripleCommutator, hallCommutator, hallConjugate, mul_assoc]

/-- A group is metabelian when its derived subgroup is abelian. -/
def Group.IsMetabelian (G : Type u) [Group G] : Prop :=
  ⁅commutator G, commutator G⁆ = ⊥

/-- In a metabelian group, any two elements of the derived subgroup have
trivial Hall commutator. -/
lemma hall_commutator_metabelian
    (hG : Group.IsMetabelian G) {a b : G}
    (ha : a ∈ commutator G) (hb : b ∈ commutator G) :
    hallCommutator a b = 1 := by
  have hab :
      hallCommutator a b ∈ ⁅commutator G, commutator G⁆ :=
    hall_commutator ha hb
  rw [hG] at hab
  exact Subgroup.mem_bot.mp hab

/-- In a metabelian group, conjugating the right argument does not change a
Hall commutator whose left argument lies in the derived subgroup. -/
lemma commutator_conjugate_metabelian
    (hG : Group.IsMetabelian G) {a : G} (ha : a ∈ commutator G) (z x : G) :
    hallCommutator a (hallConjugate z x) = hallCommutator a z := by
  let d := hallCommutator z x
  have hd : d ∈ commutator G :=
    hall_commutator (X := ⊤) (Y := ⊤) trivial trivial
  have had : hallCommutator a d = 1 :=
    hall_commutator_metabelian hG ha hd
  have hac : hallCommutator a z ∈ commutator G :=
    hall_commutator (X := ⊤) (Y := ⊤) trivial trivial
  have hcd : hallCommutator (hallCommutator a z) d = 1 :=
    hall_commutator_metabelian hG hac hd
  have hconj :
      hallConjugate (hallCommutator a z) d = hallCommutator a z := by
    calc
      hallConjugate (hallCommutator a z) d =
          hallCommutator a z * hallCommutator (hallCommutator a z) d := by
        simp [hallConjugate, hallCommutator, mul_assoc]
      _ = hallCommutator a z := by rw [hcd, mul_one]
  rw [show hallConjugate z x = z * d by
    simp [d, hallConjugate, hallCommutator, mul_assoc]]
  rw [commutator_mul_right, had, hconj, one_mul]

/-- Hall's cyclic triple-commutator identity for metabelian groups. -/
theorem hall_witt_metabelian (hG : Group.IsMetabelian G) (x y z : G) :
    hallTripleCommutator x y z *
        hallTripleCommutator z x y *
        hallTripleCommutator y z x =
      1 := by
  simp only [hallTripleCommutator]
  rw [← commutator_conjugate_metabelian hG
      (hall_commutator (X := ⊤) (Y := ⊤) trivial trivial) z x,
    ← commutator_conjugate_metabelian hG
      (hall_commutator (X := ⊤) (Y := ⊤) trivial trivial) y z,
    ← commutator_conjugate_metabelian hG
      (hall_commutator (X := ⊤) (Y := ⊤) trivial trivial) x y]
  simpa only [hallTripleCommutator] using hall_witt_cyclic x y z

/-- The subgroup of elements that centralize `A` modulo the normal subgroup
`N`. -/
def centralizerModulo (A N : Subgroup G) [N.Normal] : Subgroup G :=
  (Subgroup.centralizer
    (A.map (QuotientGroup.mk' N) : Set (G ⧸ N))).comap
      (QuotientGroup.mk' N)

/-- A subgroup `B` centralizes `A` modulo `N` exactly when `[A,B] ≤ N`. -/
lemma commutator_centralizer_modulo
    (A B N : Subgroup G) [N.Normal] :
    ⁅A, B⁆ ≤ N ↔ B ≤ centralizerModulo A N := by
  rw [centralizerModulo, ← Subgroup.map_le_iff_le_comap,
    ← Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.commutator_comm, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- Hall's subgroup `K_j`: the elements of `K` that centralize every `H_i`
modulo `H_{i+j}`. -/
noncomputable def hallKTerm
    (H : ℕ → Subgroup G) (K : Subgroup G)
    (hN : ∀ n, (H n).Normal) (j : ℕ) : Subgroup G :=
  K ⊓ ⨅ i, @centralizerModulo G _ (H i) (H (i + j)) (hN (i + j))

/-- Every Hall term `K_j` is contained in `K`. -/
lemma hall_k_term (H : ℕ → Subgroup G) (K : Subgroup G)
    (hN : ∀ n, (H n).Normal) (j : ℕ) :
    hallKTerm H K hN j ≤ K :=
  inf_le_left

/-- The defining commutator property of Hall's `K_j`. -/
lemma commutator_k_term
    (H : ℕ → Subgroup G) (K : Subgroup G)
    (hN : ∀ n, (H n).Normal) (i j : ℕ) :
    ⁅H i, hallKTerm H K hN j⁆ ≤ H (i + j) := by
  letI : (H (i + j)).Normal := hN (i + j)
  apply (commutator_centralizer_modulo
    (H i) (hallKTerm H K hN j) (H (i + j))).mpr
  exact inf_le_right.trans (iInf_le _ i)

/-- If `[H_i,K] ≤ H_{i+1}`, then Hall's first term is exactly `K`. -/
lemma k_term_one
    (H : ℕ → Subgroup G) (K : Subgroup G)
    (hN : ∀ n, (H n).Normal)
    (hstep : ∀ i, ⁅H i, K⁆ ≤ H (i + 1)) :
    hallKTerm H K hN 1 = K := by
  apply le_antisymm (hall_k_term H K hN 1)
  rw [hallKTerm]
  refine le_inf le_rfl (le_iInf fun i ↦ ?_)
  letI : (H (i + 1)).Normal := hN (i + 1)
  exact (commutator_centralizer_modulo
    (H i) K (H (i + 1))).mp (hstep i)

/-- The first conclusion of Hall's Theorem 3.3: the Hall terms form an
`N`-series. -/
theorem k_term_commutator
    (H : ℕ → Subgroup G) (K : Subgroup G)
    (hN : ∀ n, (H n).Normal) (j l : ℕ) :
    ⁅hallKTerm H K hN j, hallKTerm H K hN l⁆ ≤
      hallKTerm H K hN (j + l) := by
  rw [hallKTerm]
  refine le_inf
    ((Subgroup.commutator_mono
      (hall_k_term H K hN j) (hall_k_term H K hN l)).trans
        K.commutator_le_self)
    (le_iInf fun i ↦ ?_)
  letI : (H (i + (j + l))).Normal := hN (i + (j + l))
  apply (commutator_centralizer_modulo
    (H i) ⁅hallKTerm H K hN j, hallKTerm H K hN l⁆
      (H (i + (j + l)))).mp
  rw [Subgroup.commutator_comm (H i)]
  apply threeSubgroups_le
  · calc
      ⁅⁅hallKTerm H K hN l, H i⁆, hallKTerm H K hN j⁆ =
          ⁅⁅H i, hallKTerm H K hN l⁆, hallKTerm H K hN j⁆ := by
            rw [Subgroup.commutator_comm (hallKTerm H K hN l)]
      _ ≤ ⁅H (i + l), hallKTerm H K hN j⁆ :=
        Subgroup.commutator_mono
          (commutator_k_term H K hN i l) le_rfl
      _ ≤ H ((i + l) + j) :=
        commutator_k_term H K hN (i + l) j
      _ = H (i + (j + l)) := by
        simp only [Nat.add_comm, Nat.add_left_comm]
  · calc
      ⁅⁅H i, hallKTerm H K hN j⁆, hallKTerm H K hN l⁆ ≤
          ⁅H (i + j), hallKTerm H K hN l⁆ :=
        Subgroup.commutator_mono
          (commutator_k_term H K hN i j) le_rfl
      _ ≤ H ((i + j) + l) :=
        commutator_k_term H K hN (i + j) l
      _ = H (i + (j + l)) := by rw [Nat.add_assoc]

/-- **Hall, Theorem 3.3, ambient-normal form.** The lower central terms of
`K` satisfy Hall's commutator bounds. Mathlib indexes the lower central
series from zero, so `ambientLowerSeries K n` is Hall's
`γ_{n+1}(K)`. -/
theorem series_bounds_ambient
    (H : ℕ → Subgroup G) (K : Subgroup G)
    (hN : ∀ n, (H n).Normal)
    (hstep : ∀ i, ⁅H i, K⁆ ≤ H (i + 1)) :
    (∀ j l, ⁅hallKTerm H K hN j, hallKTerm H K hN l⁆ ≤
        hallKTerm H K hN (j + l)) ∧
      ∀ i n, ⁅H i, ambientLowerSeries K n⁆ ≤ H (i + (n + 1)) := by
  have hcomm :
      ∀ j l, ⁅hallKTerm H K hN j, hallKTerm H K hN l⁆ ≤
        hallKTerm H K hN (j + l) :=
    k_term_commutator H K hN
  refine ⟨hcomm, ?_⟩
  have hlower :
      ∀ n, ambientLowerSeries K n ≤ hallKTerm H K hN (n + 1) := by
    intro n
    induction n with
    | zero =>
        rw [ambient_series_zero, k_term_one H K hN hstep]
    | succ n ih =>
        rw [ambient_series_succ]
        exact (Subgroup.commutator_mono ih
          (k_term_one H K hN hstep).ge).trans (hcomm (n + 1) 1)
  intro i n
  exact (Subgroup.commutator_mono le_rfl (hlower n)).trans
    (commutator_k_term H K hN i (n + 1))

/-- If `[A,B] ≤ A`, then every element of `B` normalizes `A`. -/
lemma normalizer_commutator {A B : Subgroup G}
    (hcomm : ⁅A, B⁆ ≤ A) :
    B ≤ Subgroup.normalizer A := by
  have hconj :
      ∀ {b : G}, b ∈ B → ∀ {a : G}, a ∈ A → b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    have hc : ⁅a, b⁆ ∈ A :=
      hcomm (Subgroup.commutator_mem_commutator ha hb)
    rw [show b * a * b⁻¹ = ⁅a, b⁆⁻¹ * a by
      simp [commutatorElement_def, mul_assoc]]
    exact A.mul_mem (A.inv_mem hc) ha
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hconj hb
  · intro hba
    simpa [mul_assoc] using hconj (B.inv_mem hb) hba

/-- Hall's original hypotheses imply that every term of the series is normal
in the subgroup generated by `H₀` and `K`. -/
lemma series_term_sup
    (H : ℕ → Subgroup G) (H₀ K : Subgroup G)
    (hzero : H 0 = H₀) (hanti : Antitone H)
    (hN : ∀ n, (H n).subgroupOf H₀ |>.Normal)
    (hstep : ∀ i, ⁅H i, K⁆ ≤ H (i + 1)) (n : ℕ) :
    ((H n).subgroupOf (H₀ ⊔ K)).Normal := by
  have hnH₀ : H n ≤ H₀ := by
    simpa only [hzero] using hanti (Nat.zero_le n)
  have hcomm : ⁅H n, K⁆ ≤ H n :=
    (hstep n).trans (hanti (Nat.le_succ n))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (hnH₀.trans le_sup_left)]
  letI : ((H n).subgroupOf H₀).Normal := hN n
  exact sup_le
    (Subgroup.le_normalizer_of_normal_subgroupOf hnH₀)
    (normalizer_commutator hcomm)

/-- **Hall, Theorem 3.3.** This is the form used after replacing the ambient
group by `⟨H,K⟩`; `series_term_sup` establishes its normality
hypothesis from Hall's original descending-series assumptions. -/
theorem series_commutator_bounds
    (H : ℕ → Subgroup G) (K : Subgroup G)
    (hN : ∀ n, (H n).Normal)
    (hstep : ∀ i, ⁅H i, K⁆ ≤ H (i + 1)) :
    (∀ j l, ⁅hallKTerm H K hN j, hallKTerm H K hN l⁆ ≤
        hallKTerm H K hN (j + l)) ∧
      ∀ i n, ⁅H i, ambientLowerSeries K n⁆ ≤ H (i + (n + 1)) :=
  series_bounds_ambient H K hN hstep

/-- The lower central series of the whole group, viewed in the ambient group,
is unchanged. -/
lemma ambient_series_top (n : ℕ) :
    ambientLowerSeries (⊤ : Subgroup G) n = Subgroup.lowerCentralSeries G n := by
  apply central_series_surjective
  intro x
  exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩

/-- Consecutive upper-central-series terms satisfy the defining commutator
bound. -/
lemma upper_series_commutator (n : ℕ) :
    ⁅Subgroup.upperCentralSeries G (n + 1), ⊤⁆ ≤ Subgroup.upperCentralSeries G n := by
  rw [Subgroup.commutator_le]
  intro x hx y _
  exact Subgroup.upperCentralSeries_isAscendingCentralSeries G |>.2 x n hx y

/-- **Hall, Theorem 3.4(i).** In zero-based Mathlib indexing,
`[Γ_{i+1},Γ_{j+1}] ≤ Γ_{i+j+2}`. -/
theorem lower_central_commutator (i j : ℕ) :
    ⁅Subgroup.lowerCentralSeries G i, Subgroup.lowerCentralSeries G j⁆ ≤
      Subgroup.lowerCentralSeries G (i + j + 1) := by
  have h :=
    (series_commutator_bounds (Subgroup.lowerCentralSeries G) (⊤ : Subgroup G)
      (fun _ ↦ inferInstance)
      (fun n ↦ by
        change Subgroup.lowerCentralSeries G (n + 1) ≤ Subgroup.lowerCentralSeries G (n + 1)
        exact le_rfl)).2 i j
  simpa only [ambient_series_top, Nat.add_assoc] using h

/-- **Hall, Theorem 3.4(ii).** Here Mathlib's
`Subgroup.lowerCentralSeries G (j - 1)` is Hall's `Γ_j`. -/
theorem upper_lower_commutator (i j : ℕ) :
    ⁅Subgroup.upperCentralSeries G i, Subgroup.lowerCentralSeries G (j - 1)⁆ ≤
      Subgroup.upperCentralSeries G (i - j) := by
  cases j with
  | zero =>
      simpa using
        (Subgroup.commutator_le_left
          (Subgroup.upperCentralSeries G i) (⊤ : Subgroup G))
  | succ j =>
      let H : ℕ → Subgroup G := fun t ↦ Subgroup.upperCentralSeries G (i - t)
      have hstep : ∀ t, ⁅H t, (⊤ : Subgroup G)⁆ ≤ H (t + 1) := by
        intro t
        by_cases hti : t < i
        · have hindex : i - t = (i - (t + 1)) + 1 := by omega
          rw [show H t = Subgroup.upperCentralSeries G ((i - (t + 1)) + 1) by
              simp only [H, hindex],
            show H (t + 1) = Subgroup.upperCentralSeries G (i - (t + 1)) by rfl]
          exact upper_series_commutator (i - (t + 1))
        · have hit : i - t = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hti)
          have hits : i - (t + 1) = 0 := by omega
          simp only [H, hit, hits, Subgroup.upperCentralSeries_zero,
            Subgroup.commutator_bot_left, bot_le]
      have h :=
        (series_commutator_bounds H (⊤ : Subgroup G) (fun _ ↦ inferInstance) hstep).2 0 j
      simpa only [H, Nat.zero_add, ambient_series_top,
        Nat.succ_sub_one] using h

/-- The particular case `[Z_i,Γ_i] = 1` of Hall's Theorem 3.4(ii). -/
theorem upper_lower_bot (i : ℕ) :
    ⁅Subgroup.upperCentralSeries G i, Subgroup.lowerCentralSeries G (i - 1)⁆ = ⊥ := by
  apply le_bot_iff.mp
  simpa only [Nat.sub_self, Subgroup.upperCentralSeries_zero] using
    upper_lower_commutator (G := G) i i

/-- **Hall, Theorem 3.4(iii).** The `k`th derived subgroup lies in Hall's
`Γ_{2^k}`, represented by Mathlib's zero-based index `2^k - 1`. -/
theorem derived_le_lower (k : ℕ) :
    derivedSeries G k ≤ Subgroup.lowerCentralSeries G (2 ^ k - 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [derivedSeries_succ]
      calc
        ⁅derivedSeries G k, derivedSeries G k⁆ ≤
            ⁅Subgroup.lowerCentralSeries G (2 ^ k - 1),
              Subgroup.lowerCentralSeries G (2 ^ k - 1)⁆ :=
          Subgroup.commutator_mono ih ih
        _ ≤ Subgroup.lowerCentralSeries G ((2 ^ k - 1) + (2 ^ k - 1) + 1) :=
          lower_central_commutator (2 ^ k - 1) (2 ^ k - 1)
        _ = Subgroup.lowerCentralSeries G (2 ^ (k + 1) - 1) := by
          congr 1
          have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
          simp only [pow_succ]
          omega

/-- **Hall, Theorem 3.4.** The three standard commutator bounds. -/
theorem central_series_bounds :
    (∀ i j, ⁅Subgroup.lowerCentralSeries G i, Subgroup.lowerCentralSeries G j⁆ ≤
        Subgroup.lowerCentralSeries G (i + j + 1)) ∧
      (∀ i j, ⁅Subgroup.upperCentralSeries G i, Subgroup.lowerCentralSeries G (j - 1)⁆ ≤
        Subgroup.upperCentralSeries G (i - j)) ∧
      ∀ k, derivedSeries G k ≤ Subgroup.lowerCentralSeries G (2 ^ k - 1) :=
  ⟨lower_central_commutator,
    upper_lower_commutator,
    derived_le_lower⟩

/-- Every ambient lower-central-series term of a subgroup lies in that
subgroup. -/
lemma ambient_lower_series (K : Subgroup G) (n : ℕ) :
    ambientLowerSeries K n ≤ K := by
  exact Subgroup.map_subtype_le (Subgroup.lowerCentralSeries K n)

/-- If the `(r-1)`st zero-based lower-central term of `K` is trivial, then
`K` is nilpotent of class less than the positive integer `r`. -/
lemma nilpotent_ambient_bot
    (K : Subgroup G) {r : ℕ} (hr : 0 < r)
    (hterm : ambientLowerSeries K (r - 1) = ⊥) :
    Group.IsNilpotent K ∧ Group.nilpotencyClass K < r := by
  have hlower : Subgroup.lowerCentralSeries K (r - 1) = ⊥ := by
    rw [ambientLowerSeries] at hterm
    exact
      (Subgroup.map_eq_bot_iff_of_injective
        (H := Subgroup.lowerCentralSeries K (r - 1)) K.subtype_injective).mp hterm
  have hnil : Group.IsNilpotent K :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨r - 1, hlower⟩
  letI : Group.IsNilpotent K := hnil
  exact ⟨hnil,
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hlower).trans_lt
      (by omega)⟩

/-- **Hall, Lemma 3.5, faithful-action form.** Suppose `G₀` and `A` lie in
one ambient group, `A` acts faithfully on `G₀` by conjugation, and a normal
series from `G₀` to `1` is lowered by commutation with `A`. Then both `A`
and `[G₀,A]` are nilpotent of class less than the length of the series.

Hall obtains this setting by embedding a group and its automorphism group in
the holomorph. -/
theorem faithful_action_nilpotent
    (G₀ A : Subgroup G) (H : ℕ → Subgroup G) (r : ℕ)
    (hr : 0 < r) (hzero : H 0 = G₀) (hrbot : H r = ⊥)
    (hN : ∀ i, (H i).Normal)
    (hstep : ∀ i, ⁅H i, A⁆ ≤ H (i + 1))
    (hfaithful : A ⊓ Subgroup.centralizer (G₀ : Set G) = ⊥) :
    (Group.IsNilpotent A ∧ Group.nilpotencyClass A < r) ∧
      (Group.IsNilpotent ↥(⁅G₀, A⁆ : Subgroup G) ∧
        Group.nilpotencyClass (G := ↥(⁅G₀, A⁆ : Subgroup G)) < r) := by
  have hAcomm :
      ⁅G₀, ambientLowerSeries A (r - 1)⁆ = ⊥ := by
    apply le_bot_iff.mp
    have h :=
      (series_commutator_bounds H A hN hstep).2 0 (r - 1)
    simpa only [hzero, Nat.zero_add,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne'), hrbot] using h
  have hAterm : ambientLowerSeries A (r - 1) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfaithful]
    refine le_inf (ambient_lower_series A (r - 1)) ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    exact hAcomm
  have hAclass :=
    nilpotent_ambient_bot A hr hAterm
  let C : Subgroup G := ⁅G₀, A⁆
  have hC_le : C ≤ H 1 := by
    simpa only [C, hzero] using hstep 0
  have hCstep : ∀ i, ⁅H i, C⁆ ≤ H (i + 1) := by
    intro i
    rw [Subgroup.commutator_comm (H i)]
    apply threeSubgroups_le
    · calc
        ⁅⁅A, H i⁆, G₀⁆ = ⁅⁅H i, A⁆, G₀⁆ := by
          rw [Subgroup.commutator_comm A]
        _ ≤ ⁅H (i + 1), G₀⁆ :=
          Subgroup.commutator_mono (hstep i) le_rfl
        _ ≤ H (i + 1) :=
          Subgroup.commutator_le_left (H (i + 1)) G₀
    · calc
        ⁅⁅H i, G₀⁆, A⁆ ≤ ⁅H i, A⁆ :=
          Subgroup.commutator_mono
            (Subgroup.commutator_le_left (H i) G₀) le_rfl
        _ ≤ H (i + 1) := hstep i
  have hClower : ∀ n, ambientLowerSeries C n ≤ H (n + 1) := by
    intro n
    induction n with
    | zero =>
        simpa only [ambient_series_zero] using hC_le
    | succ n ih =>
        rw [ambient_series_succ]
        exact (Subgroup.commutator_mono ih le_rfl).trans (hCstep (n + 1))
  have hCterm : ambientLowerSeries C (r - 1) = ⊥ := by
    apply le_bot_iff.mp
    have h := hClower (r - 1)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne'), hrbot] at h
    exact h
  exact ⟨hAclass,
    nilpotent_ambient_bot C hr hCterm⟩

/-- A square matrix is upper unitriangular when its diagonal entries
are one and its entries below the diagonal vanish. -/
def UnitriangularMatrix
    {R : Type*} [Ring R] {n : ℕ}
    (x : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i, x i i = 1) ∧ ∀ i j, j < i → x i j = 0

/-- A subgroup of matrix units consists of exactly the upper
unitriangular matrices. -/
def UpperUnitriangularMatrix
    {R : Type*} [Ring R] {n : ℕ}
    (T : Subgroup (Matrix (Fin n) (Fin n) R)ˣ) : Prop :=
  ∀ x : (Matrix (Fin n) (Fin n) R)ˣ,
    x ∈ T ↔ UnitriangularMatrix (x : Matrix (Fin n) (Fin n) R)

/-- A matrix has upper degree `k` when it vanishes below its `k`th
superdiagonal. -/
def MatrixUpperDegree
    {R : Type*} [Ring R] {n : ℕ} (k : ℕ)
    (x : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j.val < i.val + k → x i j = 0

/-- An upper-triangular matrix vanishes below its diagonal. -/
def UpperTriangularMatrix
    {R : Type*} [Ring R] {n : ℕ}
    (x : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j < i → x i j = 0

lemma triangular_matrix_unitriangular
    {R : Type*} [Ring R] {n : ℕ}
    {x : Matrix (Fin n) (Fin n) R}
    (hx : UnitriangularMatrix x) :
    UpperTriangularMatrix x :=
  hx.2

lemma matrix_upper_add
    {R : Type*} [Ring R] {n k : ℕ}
    {x y : Matrix (Fin n) (Fin n) R}
    (hx : MatrixUpperDegree k x) (hy : MatrixUpperDegree k y) :
    MatrixUpperDegree k (x + y) := by
  intro i j hij
  rw [Matrix.add_apply, hx i j hij, hy i j hij, add_zero]

lemma matrix_upper_neg
    {R : Type*} [Ring R] {n k : ℕ}
    {x : Matrix (Fin n) (Fin n) R}
    (hx : MatrixUpperDegree k x) :
    MatrixUpperDegree k (-x) := by
  intro i j hij
  rw [Matrix.neg_apply, hx i j hij, neg_zero]

lemma matrix_degree_sub
    {R : Type*} [Ring R] {n k : ℕ}
    {x y : Matrix (Fin n) (Fin n) R}
    (hx : MatrixUpperDegree k x) (hy : MatrixUpperDegree k y) :
    MatrixUpperDegree k (x - y) := by
  rw [sub_eq_add_neg]
  exact matrix_upper_add hx (matrix_upper_neg hy)

/-- Matrix multiplication adds upper degrees. -/
lemma matrix_upper_degree
    {R : Type*} [Ring R] {n a b : ℕ}
    {x y : Matrix (Fin n) (Fin n) R}
    (hx : MatrixUpperDegree a x) (hy : MatrixUpperDegree b y) :
    MatrixUpperDegree (a + b) (x * y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hci : c.val < i.val + a
  · rw [hx i c hci, zero_mul]
  · rw [hy c j (by omega), mul_zero]

/-- Multiplying on the right by an upper-triangular matrix preserves an
upper-degree bound. -/
lemma matrix_upper_triangular
    {R : Type*} [Ring R] {n k : ℕ}
    {x y : Matrix (Fin n) (Fin n) R}
    (hx : MatrixUpperDegree k x) (hy : UpperTriangularMatrix y) :
    MatrixUpperDegree k (x * y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hci : c.val < i.val + k
  · rw [hx i c hci, zero_mul]
  · rw [hy c j (by omega), mul_zero]

/-- Unitriangularity is the degree-one condition on `x - 1`. -/
lemma matrix_upper_sub
    {R : Type*} [Ring R] {n : ℕ}
    (x : Matrix (Fin n) (Fin n) R) :
    MatrixUpperDegree 1 (x - 1) ↔ UnitriangularMatrix x := by
  constructor
  · intro hx
    constructor
    · intro i
      have h := hx i i (by omega)
      simpa only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] using h
    · intro i j hji
      have h := hx i j (by omega)
      simpa only [Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_gt hji),
        sub_zero] using h
  · rintro ⟨hdiag, hlower⟩ i j hij
    by_cases hji : j = i
    · subst j
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, hdiag, sub_self]
    · have hlt : j < i := by omega
      have hijne : i ≠ j := fun hij ↦ hji hij.symm
      simp only [Matrix.sub_apply, Matrix.one_apply, if_neg hijne, hlower i j hlt,
        sub_zero]

/-- The ring identity behind the filtered commutator calculations. -/
lemma commutator_element_units
    {R : Type*} [Ring R] (x y : Rˣ) :
    (((⁅x, y⁆ : Rˣ) : R) - 1) =
      (((x : R) - 1) * ((y : R) - 1) -
          ((y : R) - 1) * ((x : R) - 1)) *
        ((x⁻¹ : Rˣ) : R) * ((y⁻¹ : Rˣ) : R) := by
  have hxx : (x : R) * ((x⁻¹ : Rˣ) : R) = 1 :=
    x.val_inv
  have hyy : (y : R) * ((y⁻¹ : Rˣ) : R) = 1 :=
    y.val_inv
  have hone :
      ((y : R) * (x : R)) * ((x⁻¹ : Rˣ) : R) *
          ((y⁻¹ : Rˣ) : R) = 1 := by
    simp only [mul_assoc, hxx, mul_one, hyy]
  simp only [commutatorElement_def, Units.val_mul]
  calc
    ((x : R) * (y : R)) * ((x⁻¹ : Rˣ) : R) * ((y⁻¹ : Rˣ) : R) - 1 =
        ((x : R) * (y : R)) * ((x⁻¹ : Rˣ) : R) * ((y⁻¹ : Rˣ) : R) -
          ((y : R) * (x : R)) * ((x⁻¹ : Rˣ) : R) *
            ((y⁻¹ : Rˣ) : R) := by rw [hone]
    _ = (((x : R) - 1) * ((y : R) - 1) -
          ((y : R) - 1) * ((x : R) - 1)) *
        ((x⁻¹ : Rˣ) : R) * ((y⁻¹ : Rˣ) : R) := by
      noncomm_ring

/-- The degree-`k` filtration subgroup inside a unitriangular matrix group. -/
noncomputable def unitriangularDegreeSubgroup
    {R : Type*} [Ring R] {n : ℕ}
    (T : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hT : UpperUnitriangularMatrix T) (k : ℕ) : Subgroup T where
  carrier := {x | MatrixUpperDegree k ((x.1 : Matrix (Fin n) (Fin n) R) - 1)}
  one_mem' := by
    intro i j _
    simp
  mul_mem' := by
    intro x y hx hy
    have hytri :
        UpperTriangularMatrix (y.1 : Matrix (Fin n) (Fin n) R) :=
      triangular_matrix_unitriangular ((hT y.1).mp y.2)
    change MatrixUpperDegree k
      (((x * y).1 : Matrix (Fin n) (Fin n) R) - 1)
    rw [show
        (((x * y).1 : Matrix (Fin n) (Fin n) R) - 1) =
          ((x.1 : Matrix (Fin n) (Fin n) R) - 1) *
              (y.1 : Matrix (Fin n) (Fin n) R) +
            ((y.1 : Matrix (Fin n) (Fin n) R) - 1) by
      change (((x.1 * y.1 : (Matrix (Fin n) (Fin n) R)ˣ) :
          Matrix (Fin n) (Fin n) R) - 1) = _
      rw [Units.val_mul]
      noncomm_ring]
    exact matrix_upper_add
      (matrix_upper_triangular hx hytri) hy
  inv_mem' := by
    intro x hx
    have hxinvtri :
        UpperTriangularMatrix ((x⁻¹).1 : Matrix (Fin n) (Fin n) R) :=
      triangular_matrix_unitriangular
        ((hT (x⁻¹).1).mp (x⁻¹).2)
    change MatrixUpperDegree k
      (((x⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1)
    rw [show
        (((x⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1) =
          -(((x.1 : Matrix (Fin n) (Fin n) R) - 1) *
            ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) by
      have hxx :
          (x.1 : Matrix (Fin n) (Fin n) R) *
              ((x⁻¹).1 : Matrix (Fin n) (Fin n) R) = 1 :=
        x.1.val_inv
      calc
        ((x⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1 =
            -(1 - ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) := by
          noncomm_ring
        _ = -((x.1 : Matrix (Fin n) (Fin n) R) *
              ((x⁻¹).1 : Matrix (Fin n) (Fin n) R) -
            ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) := by rw [hxx]
        _ = -(((x.1 : Matrix (Fin n) (Fin n) R) - 1) *
            ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) := by
          rw [sub_mul, one_mul]]
    exact matrix_upper_neg
      (matrix_upper_triangular hx hxinvtri)

lemma unitriangular_degree_top
    {R : Type*} [Ring R] {n : ℕ}
    (T : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hT : UpperUnitriangularMatrix T) :
    unitriangularDegreeSubgroup T hT 1 = ⊤ := by
  apply top_unique
  intro x _
  exact (matrix_upper_sub
    (x.1 : Matrix (Fin n) (Fin n) R)).mpr ((hT x.1).mp x.2)

lemma unitriangular_dim_bot
    {R : Type*} [Ring R] {n : ℕ}
    (T : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hT : UpperUnitriangularMatrix T) :
    unitriangularDegreeSubgroup T hT n = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h := hx i j (by omega)
  simpa only [Matrix.sub_apply, sub_eq_zero] using h

lemma unitriangular_degree_commutator
    {R : Type*} [Ring R] {n : ℕ}
    (T : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hT : UpperUnitriangularMatrix T) (i j : ℕ) :
    ⁅unitriangularDegreeSubgroup T hT i,
        unitriangularDegreeSubgroup T hT j⁆ ≤
      unitriangularDegreeSubgroup T hT (i + j) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxy := matrix_upper_degree hx hy
  have hyx : MatrixUpperDegree (i + j)
      (((y.1 : Matrix (Fin n) (Fin n) R) - 1) *
        ((x.1 : Matrix (Fin n) (Fin n) R) - 1)) := by
    simpa only [Nat.add_comm] using matrix_upper_degree hy hx
  have hsub := matrix_degree_sub hxy hyx
  have hxinvtri :
      UpperTriangularMatrix ((x⁻¹).1 : Matrix (Fin n) (Fin n) R) :=
    triangular_matrix_unitriangular
      ((hT (x⁻¹).1).mp (x⁻¹).2)
  have hyinvtri :
      UpperTriangularMatrix ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) :=
    triangular_matrix_unitriangular
      ((hT (y⁻¹).1).mp (y⁻¹).2)
  change MatrixUpperDegree (i + j)
    (((⁅x, y⁆ : T).1 : Matrix (Fin n) (Fin n) R) - 1)
  rw [show
      (((⁅x, y⁆ : T).1 : Matrix (Fin n) (Fin n) R) - 1) =
        (((x.1 : Matrix (Fin n) (Fin n) R) - 1) *
              ((y.1 : Matrix (Fin n) (Fin n) R) - 1) -
            ((y.1 : Matrix (Fin n) (Fin n) R) - 1) *
              ((x.1 : Matrix (Fin n) (Fin n) R) - 1)) *
          ((x⁻¹).1 : Matrix (Fin n) (Fin n) R) *
            ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) by
    exact commutator_element_units x.1 y.1]
  exact matrix_upper_triangular
    (matrix_upper_triangular hsub hxinvtri) hyinvtri

/-- **Corollary to Hall, Lemma 3.5.** The upper-unitriangular
`n × n` matrices over a unital associative ring form a nilpotent group
of class less than `n`. -/
theorem upperUnitriangular_nilpotent
    {R : Type*} [Ring R] {n : ℕ}
    (T : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hn : 0 < n) (hT : UpperUnitriangularMatrix T) :
    Group.IsNilpotent T ∧ Group.nilpotencyClass T < n := by
  let K : ℕ → Subgroup T := unitriangularDegreeSubgroup T hT
  have hKtop : K 1 = ⊤ :=
    unitriangular_degree_top T hT
  have hKbot : K n = ⊥ :=
    unitriangular_dim_bot T hT
  have hcomm : ∀ i j, ⁅K i, K j⁆ ≤ K (i + j) :=
    unitriangular_degree_commutator T hT
  have hlower : ∀ i, Subgroup.lowerCentralSeries T i ≤ K (i + 1) := by
    intro i
    induction i with
    | zero =>
        rw [Subgroup.lowerCentralSeries_zero, hKtop]
    | succ i ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        exact (Subgroup.commutator_mono ih hKtop.ge).trans (hcomm (i + 1) 1)
  have hterm : Subgroup.lowerCentralSeries T (n - 1) = ⊥ := by
    apply le_bot_iff.mp
    have h := hlower (n - 1)
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne'), hKbot] using h
  have hnil : Group.IsNilpotent T :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n - 1, hterm⟩
  letI : Group.IsNilpotent T := hnil
  exact ⟨hnil,
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hterm).trans_lt
      (by omega)⟩

/-- Hall's subgroup `K_i = 1 + 𝔨^i`, realized inside the unit group of
the ambient ring. -/
def idealUnitSubgroup
    {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] (i : ℕ) :
    Subgroup Rˣ where
  carrier := {x | (x : R) - 1 ∈ I ^ i}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change (x : R) * (y : R) - 1 ∈ I ^ i
    rw [show (x : R) * (y : R) - 1 =
        ((x : R) - 1) * (y : R) + ((y : R) - 1) by noncomm_ring]
    exact (I ^ i).add_mem ((I ^ i).mul_mem_right (y : R) hx) hy
  inv_mem' := by
    intro x hx
    change ((x⁻¹ : Rˣ) : R) - 1 ∈ I ^ i
    rw [show ((x⁻¹ : Rˣ) : R) - 1 =
        -(((x⁻¹ : Rˣ) : R) * ((x : R) - 1)) by
      rw [mul_sub]
      simp]
    exact (I ^ i).neg_mem ((I ^ i).mul_mem_left ((x⁻¹ : Rˣ) : R) hx)

/-- Products in ideal powers add filtration degrees. -/
lemma ideal_pow_add
    {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]
    {a b : R} {i j : ℕ} (ha : a ∈ I ^ i) (hb : b ∈ I ^ j) :
    a * b ∈ I ^ (i + j) := by
  rw [Ideal.IsTwoSided.pow_add]
  exact Ideal.mul_mem_mul ha hb

/-- Commutators of principal units add filtration degrees. -/
lemma ideal_subgroup_commutator
    {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] (i j : ℕ) :
    ⁅idealUnitSubgroup I i, idealUnitSubgroup I j⁆ ≤
      idealUnitSubgroup I (i + j) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  change (((⁅x, y⁆ : Rˣ) : R) - 1) ∈ I ^ (i + j)
  change (x : R) - 1 ∈ I ^ i at hx
  change (y : R) - 1 ∈ I ^ j at hy
  have hxy :
      ((x : R) - 1) * ((y : R) - 1) ∈ I ^ (i + j) :=
    ideal_pow_add I hx hy
  have hyx :
      ((y : R) - 1) * ((x : R) - 1) ∈ I ^ (i + j) := by
    simpa only [Nat.add_comm] using ideal_pow_add I hy hx
  have hsub :
      ((x : R) - 1) * ((y : R) - 1) -
          ((y : R) - 1) * ((x : R) - 1) ∈ I ^ (i + j) :=
    (I ^ (i + j)).sub_mem hxy hyx
  have hright :
      (((x : R) - 1) * ((y : R) - 1) -
            ((y : R) - 1) * ((x : R) - 1)) *
          ((x⁻¹ : Rˣ) : R) * ((y⁻¹ : Rˣ) : R) ∈ I ^ (i + j) :=
    (I ^ (i + j)).mul_mem_right ((y⁻¹ : Rˣ) : R)
      ((I ^ (i + j)).mul_mem_right ((x⁻¹ : Rˣ) : R) hsub)
  rwa [commutator_element_units]

/-- If an ideal power vanishes, so does the corresponding group of
principal units. -/
lemma ideal_bot_pow
    {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] (n : ℕ)
    (hnilpotent : I ^ n = ⊥) :
    idealUnitSubgroup I n = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Units.ext
  change (x : R) - 1 ∈ I ^ n at hx
  have hxzero : (x : R) - 1 = 0 := by
    apply Ideal.mem_bot.mp
    rwa [hnilpotent] at hx
  exact sub_eq_zero.mp hxzero

/-- **Hall, Theorem 3.6.** If `𝔨 ^ n = 0`, the principal-unit
subgroups `K_i = 1 + 𝔨^i` satisfy `[K_i,K_j] ≤ K_(i+j)`;
`K_1` is nilpotent of class less than `n`, and
`γ_i(K_1) ≤ K_i`. -/
theorem ideal_commutator_bounds
    {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] (n : ℕ)
    (hn : 0 < n)
    (hnilpotent : I ^ n = ⊥) :
    (∀ i j, ⁅idealUnitSubgroup I i, idealUnitSubgroup I j⁆ ≤
      idealUnitSubgroup I (i + j)) ∧
    Group.IsNilpotent (idealUnitSubgroup I 1) ∧
    Group.nilpotencyClass (idealUnitSubgroup I 1) < n ∧
    ∀ i, ambientLowerSeries (idealUnitSubgroup I 1) (i - 1) ≤
      idealUnitSubgroup I i := by
  have hcomm :
      ∀ i j, ⁅idealUnitSubgroup I i, idealUnitSubgroup I j⁆ ≤
        idealUnitSubgroup I (i + j) :=
    ideal_subgroup_commutator I
  have hlowerZero :
      ∀ i, ambientLowerSeries (idealUnitSubgroup I 1) i ≤
        idealUnitSubgroup I (i + 1) := by
    intro i
    induction i with
    | zero =>
        rw [ambient_series_zero]
    | succ i ih =>
        rw [ambient_series_succ]
        exact (Subgroup.commutator_mono ih le_rfl).trans (hcomm (i + 1) 1)
  have hlower :
      ∀ i, ambientLowerSeries (idealUnitSubgroup I 1) (i - 1) ≤
        idealUnitSubgroup I i := by
    intro i
    cases i with
    | zero =>
        intro x _
        change (x : R) - 1 ∈ I ^ 0
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ i =>
        simpa only [Nat.succ_sub_one] using hlowerZero i
  have hterm :
      ambientLowerSeries (idealUnitSubgroup I 1) (n - 1) = ⊥ := by
    apply le_bot_iff.mp
    exact (hlower n).trans
      (ideal_bot_pow I n hnilpotent).le
  have hclass :=
    nilpotent_ambient_bot
      (idealUnitSubgroup I 1) hn hterm
  exact ⟨hcomm, hclass.1, hclass.2, hlower⟩

/-- The lower-central-series commutator bound inside an ambient group. -/
theorem ambient_series_commutator
    (H : Subgroup G) (i j : ℕ) :
    ⁅ambientLowerSeries H i, ambientLowerSeries H j⁆ ≤
      ambientLowerSeries H (i + j + 1) := by
  change
    ⁅(Subgroup.lowerCentralSeries H i).map H.subtype,
      (Subgroup.lowerCentralSeries H j).map H.subtype⁆ ≤
      (Subgroup.lowerCentralSeries H (i + j + 1)).map H.subtype
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (lower_central_commutator (G := H) i j)

/-- The one-variable induction at the heart of Hall's Lemma 3.7. -/
lemma ambient_lower_step
    (H K : Subgroup G) [H.Normal]
    (hHK : ⁅H, K⁆ ≤ ambientLowerSeries H 1) :
    ∀ i, ⁅ambientLowerSeries H i, K⁆ ≤
      ambientLowerSeries H (i + 1) := by
  intro i
  induction i with
  | zero =>
      simpa only [ambient_series_zero] using hHK
  | succ i ih =>
      rw [ambient_series_succ]
      apply threeSubgroups_le
      · calc
          ⁅⁅H, K⁆, ambientLowerSeries H i⁆ ≤
              ⁅ambientLowerSeries H 1,
                ambientLowerSeries H i⁆ :=
            Subgroup.commutator_mono hHK le_rfl
          _ ≤ ambientLowerSeries H (1 + i + 1) :=
            ambient_series_commutator H 1 i
          _ = ambientLowerSeries H ((i + 1) + 1) := by
            congr 2
            omega
      · calc
          ⁅⁅K, ambientLowerSeries H i⁆, H⁆ =
              ⁅⁅ambientLowerSeries H i, K⁆, H⁆ := by
            rw [Subgroup.commutator_comm K]
          _ ≤ ⁅ambientLowerSeries H (i + 1), H⁆ :=
            Subgroup.commutator_mono ih le_rfl
          _ = ambientLowerSeries H ((i + 1) + 1) := by
            exact (ambient_series_succ H (i + 1)).symm

/-- **Hall, Lemma 3.7, zero-based ambient-normal form.** -/
theorem ambient_lower_commutator
    (H K : Subgroup G) [H.Normal]
    (hHK : ⁅H, K⁆ ≤ ambientLowerSeries H 1) (i j : ℕ) :
    ⁅ambientLowerSeries H i, ambientLowerSeries K j⁆ ≤
      ambientLowerSeries H (i + j + 1) := by
  exact
    (series_commutator_bounds (ambientLowerSeries H) K
      (fun _ ↦ inferInstance) (ambient_lower_step H K hHK)).2 i j

/-- **Hall, Lemma 3.7.** If `[H,K] ≤ H'`, then
`[γ_i(H),γ_j(K)] ≤ γ_{i+j}(H)` for positive `i,j`. As elsewhere, the
ambient-normal hypothesis is obtained by working inside `H ⊔ K`. -/
theorem lower_commutator_derived
    (H K : Subgroup G) [H.Normal]
    (hHK : ⁅H, K⁆ ≤ ambientLowerSeries H 1)
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    ⁅ambientLowerSeries H (i - 1),
        ambientLowerSeries K (j - 1)⁆ ≤
      ambientLowerSeries H (i + j - 1) := by
  have h :=
    ambient_lower_commutator H K hHK (i - 1) (j - 1)
  have hindex : (i - 1) + (j - 1) + 1 = i + j - 1 := by omega
  simpa only [hindex] using h

/-- **Hall, Corollary after Lemma 3.7, faithful-action form.** If `H` has
class `c`, and `K` acts faithfully while inducing the identity on `H/H'`,
then `γ_j(K)` acts trivially on every
`γ_i(H) / γ_{i+j}(H)`, and `K` has class less than `c`. -/
theorem faithful_abelianization_nilpotent
    (H K : Subgroup G) [H.Normal] {c : ℕ}
    (hc : 0 < c) (hH : NilpotentClass H c)
    (hHK : ⁅H, K⁆ ≤ ambientLowerSeries H 1)
    (hfaithful : K ⊓ Subgroup.centralizer (H : Set G) = ⊥) :
    (∀ i j, ⁅ambientLowerSeries H i,
        ambientLowerSeries K j⁆ ≤
      ambientLowerSeries H (i + j + 1)) ∧
      Group.IsNilpotent K ∧ Group.nilpotencyClass K < c := by
  have hbounds :
      ∀ i j, ⁅ambientLowerSeries H i,
          ambientLowerSeries K j⁆ ≤
        ambientLowerSeries H (i + j + 1) :=
    ambient_lower_commutator H K hHK
  have hHterm : ambientLowerSeries H c = ⊥ := by
    letI : Group.IsNilpotent H := hH.1
    have hlower : Subgroup.lowerCentralSeries H c = ⊥ :=
      Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hH.2.le
    rw [ambientLowerSeries, hlower, Subgroup.map_bot]
  have hcomm :
      ⁅H, ambientLowerSeries K (c - 1)⁆ = ⊥ := by
    apply le_bot_iff.mp
    have h := hbounds 0 (c - 1)
    simpa only [ambient_series_zero, Nat.zero_add,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hc.ne'), hHterm] using h
  have hKterm : ambientLowerSeries K (c - 1) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfaithful]
    refine le_inf (ambient_lower_series K (c - 1)) ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    exact hcomm
  exact ⟨hbounds,
    nilpotent_ambient_bot K hc hKterm⟩

/-- Hall's iterated relative-commutator sequence:
`H_0 = H` and `H_(i+1) = [H_i,K]`. -/
def relativeCommutatorSeries (H K : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | i + 1 => ⁅relativeCommutatorSeries H K i, K⁆

@[simp]
theorem relative_series_zero (H K : Subgroup G) :
    relativeCommutatorSeries H K 0 = H :=
  rfl

@[simp]
theorem relative_series_succ (H K : Subgroup G) (i : ℕ) :
    relativeCommutatorSeries H K (i + 1) =
      ⁅relativeCommutatorSeries H K i, K⁆ :=
  rfl

instance relative_series_normal
    (H K : Subgroup G) [H.Normal] [K.Normal] (i : ℕ) :
    (relativeCommutatorSeries H K i).Normal := by
  induction i with
  | zero => simpa only [relative_series_zero] using inferInstanceAs H.Normal
  | succ i ih =>
      simpa only [relative_series_succ] using
        inferInstanceAs (⁅relativeCommutatorSeries H K i, K⁆ : Subgroup G).Normal

theorem relative_series_mono
    {H H' K K' : Subgroup G} (hH : H ≤ H') (hK : K ≤ K') :
    ∀ i, relativeCommutatorSeries H K i ≤
      relativeCommutatorSeries H' K' i
  | 0 => hH
  | i + 1 =>
      Subgroup.commutator_mono
        (relative_series_mono hH hK i) hK

theorem relative_commutator_add
    (H K : Subgroup G) (i j : ℕ) :
    relativeCommutatorSeries H K (i + j) =
      relativeCommutatorSeries (relativeCommutatorSeries H K i) K j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simpa only [Nat.add_assoc, relative_series_succ] using
        congrArg (fun L : Subgroup G => ⁅L, K⁆) ih

theorem relative_series_add
    (H K : Subgroup G) (i : ℕ) :
    relativeCommutatorSeries ⁅H, K⁆ K i =
      relativeCommutatorSeries H K (i + 1) := by
  rw [show i + 1 = 1 + i by omega, relative_commutator_add,
    relative_series_succ, relative_series_zero]

theorem relative_commutator_left
    (H K : Subgroup G) [H.Normal] [K.Normal] :
    ∀ i, relativeCommutatorSeries H K i ≤ H
  | 0 => le_rfl
  | i + 1 =>
      (Subgroup.commutator_le_left
        (relativeCommutatorSeries H K i) K).trans
          (relative_commutator_left H K i)

theorem relative_series_sup
    (H H' K : Subgroup G) [H.Normal] [H'.Normal] [K.Normal] :
    ∀ i, relativeCommutatorSeries (H ⊔ H') K i =
      relativeCommutatorSeries H K i ⊔
        relativeCommutatorSeries H' K i
  | 0 => rfl
  | i + 1 => by
      rw [relative_series_succ, relative_series_succ,
        relative_series_succ, relative_series_sup H H' K i,
        commutator_sup_left]

theorem relative_series_top (i : ℕ) :
    relativeCommutatorSeries (⊤ : Subgroup G) ⊤ i =
      Subgroup.lowerCentralSeries G i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simpa only [relative_series_succ, Subgroup.lowerCentralSeries_succ] using
        congrArg (fun L : Subgroup G => ⁅L, (⊤ : Subgroup G)⁆) ih

theorem relative_ambient_central
    (H : Subgroup G) :
    ∀ i, relativeCommutatorSeries H H i = ambientLowerSeries H i
  | 0 => by
      rw [relative_series_zero, ambient_series_zero]
  | i + 1 => by
      rw [relative_series_succ, ambient_series_succ,
        relative_ambient_central H i]

theorem commutator_ambient_step
    (A B : Subgroup G) [A.Normal] [B.Normal] :
    ⁅⁅A, B⁆, (⊤ : Subgroup G)⁆ ≤
      ⁅⁅A, (⊤ : Subgroup G)⁆, B⁆ ⊔
        ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆ := by
  apply threeSubgroups_le
  · calc
      ⁅⁅B, (⊤ : Subgroup G)⁆, A⁆ =
          ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆ := by
            rw [Subgroup.commutator_comm ⁅B, (⊤ : Subgroup G)⁆ A]
      _ ≤ ⁅⁅A, (⊤ : Subgroup G)⁆, B⁆ ⊔
          ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆ := le_sup_right
  · calc
      ⁅⁅(⊤ : Subgroup G), A⁆, B⁆ =
          ⁅⁅A, (⊤ : Subgroup G)⁆, B⁆ := by
            rw [Subgroup.commutator_comm (⊤ : Subgroup G) A]
      _ ≤ ⁅⁅A, (⊤ : Subgroup G)⁆, B⁆ ⊔
          ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆ := le_sup_left

theorem relative_commutator_series
    (A B A' B' : Subgroup G) [A.Normal] [B.Normal] [A'.Normal] [B'.Normal]
    (a b : ℕ)
    (hA : relativeCommutatorSeries A ⊤ a ≤ A')
    (hB : relativeCommutatorSeries B ⊤ b ≤ B') :
    relativeCommutatorSeries ⁅A, B⁆ ⊤ (a + b) ≤
      ⁅A', B⁆ ⊔ ⁅A, B'⁆ := by
  induction a generalizing A B A' B' b with
  | zero =>
      calc
        relativeCommutatorSeries ⁅A, B⁆ ⊤ (0 + b) ≤ ⁅A, B⁆ := by
          simpa only [Nat.zero_add] using
            relative_commutator_left ⁅A, B⁆ ⊤ b
        _ ≤ ⁅A', B⁆ :=
          Subgroup.commutator_mono
            (by simpa only [relative_series_zero] using hA) le_rfl
        _ ≤ ⁅A', B⁆ ⊔ ⁅A, B'⁆ := le_sup_left
  | succ a iha =>
      induction b generalizing A B A' B' with
      | zero =>
          calc
            relativeCommutatorSeries ⁅A, B⁆ ⊤ ((a + 1) + 0) ≤ ⁅A, B⁆ := by
              simpa only [Nat.add_zero] using
                relative_commutator_left ⁅A, B⁆ ⊤ (a + 1)
            _ ≤ ⁅A, B'⁆ :=
              Subgroup.commutator_mono le_rfl
                (by simpa only [relative_series_zero] using hB)
            _ ≤ ⁅A', B⁆ ⊔ ⁅A, B'⁆ := le_sup_right
      | succ b ihb =>
          have hleft :
              relativeCommutatorSeries ⁅⁅A, (⊤ : Subgroup G)⁆, B⁆ ⊤
                  (a + (b + 1)) ≤
                ⁅A', B⁆ ⊔ ⁅A, B'⁆ := by
            refine (iha ⁅A, (⊤ : Subgroup G)⁆ B A' B' (b + 1) ?_ hB).trans ?_
            · simpa only [relative_series_add,
                Nat.succ_eq_add_one] using hA
            · exact sup_le le_sup_left
                ((Subgroup.commutator_mono
                  (Subgroup.commutator_le_left A (⊤ : Subgroup G))
                  le_rfl).trans le_sup_right)
          have hright :
              relativeCommutatorSeries ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆ ⊤
                  (a + (b + 1)) ≤
                ⁅A', B⁆ ⊔ ⁅A, B'⁆ := by
            have hright' :=
              ihb A ⁅B, (⊤ : Subgroup G)⁆ A' B' hA
                (by
                  simpa only [relative_series_add,
                    Nat.succ_eq_add_one] using hB)
            refine (show
              relativeCommutatorSeries ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆ ⊤
                  (a + (b + 1)) ≤
                ⁅A', ⁅B, (⊤ : Subgroup G)⁆⁆ ⊔ ⁅A, B'⁆ by
                  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
                    Nat.succ_eq_add_one] using hright').trans ?_
            exact sup_le
              ((Subgroup.commutator_mono le_rfl
                (Subgroup.commutator_le_left B (⊤ : Subgroup G))).trans
                  le_sup_left)
              le_sup_right
          calc
            relativeCommutatorSeries ⁅A, B⁆ ⊤
                ((a + 1) + (b + 1)) =
                relativeCommutatorSeries ⁅⁅A, B⁆, (⊤ : Subgroup G)⁆ ⊤
                  (a + (b + 1)) := by
                    rw [relative_series_add]
                    congr 1
                    omega
            _ ≤ relativeCommutatorSeries
                (⁅⁅A, (⊤ : Subgroup G)⁆, B⁆ ⊔
                  ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆) ⊤
                    (a + (b + 1)) :=
              relative_series_mono
                (commutator_ambient_step A B) le_rfl _
            _ = relativeCommutatorSeries ⁅⁅A, (⊤ : Subgroup G)⁆, B⁆ ⊤
                  (a + (b + 1)) ⊔
                relativeCommutatorSeries ⁅A, ⁅B, (⊤ : Subgroup G)⁆⁆ ⊤
                  (a + (b + 1)) :=
              relative_series_sup _ _ _ _
            _ ≤ ⁅A', B⁆ ⊔ ⁅A, B'⁆ :=
              sup_le hleft hright

/-- A finite cost sufficient to lower ambient commutators through `c`
successive terms of the lower central series of a normal subgroup. -/
def hallExtensionCost (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | c + 1 => hallExtensionCost d c + (c + 1) * d

theorem relative_ambient_step
    (H : Subgroup G) [H.Normal] (d : ℕ)
    (hbase : relativeCommutatorSeries H ⊤ d ≤
      ambientLowerSeries H 1) :
    ∀ c, relativeCommutatorSeries (ambientLowerSeries H c) ⊤
        ((c + 1) * d) ≤
      ambientLowerSeries H (c + 1)
  | 0 => by
      simpa only [Nat.zero_add, Nat.one_mul, ambient_series_zero] using
        hbase
  | c + 1 => by
      have h :=
        relative_commutator_series
          (ambientLowerSeries H c) H
          (ambientLowerSeries H (c + 1))
          (ambientLowerSeries H 1)
          ((c + 1) * d) d
          (relative_ambient_step H d hbase c)
          hbase
      calc
        relativeCommutatorSeries (ambientLowerSeries H (c + 1)) ⊤
            (((c + 1) + 1) * d) =
            relativeCommutatorSeries
              ⁅ambientLowerSeries H c, H⁆ ⊤
                ((c + 1) * d + d) := by
                  rw [ambient_series_succ, Nat.add_mul, Nat.one_mul]
        _ ≤ ⁅ambientLowerSeries H (c + 1), H⁆ ⊔
              ⁅ambientLowerSeries H c,
                ambientLowerSeries H 1⁆ :=
          h
        _ ≤ ambientLowerSeries H ((c + 1) + 1) := by
          refine sup_le ?_ ?_
          · exact (ambient_series_succ H (c + 1)).symm.le
          · simpa only [Nat.add_assoc] using
              ambient_series_commutator H c 1

theorem relative_ambient_cost
    (H : Subgroup G) [H.Normal] (d : ℕ)
    (hbase : relativeCommutatorSeries H ⊤ d ≤
      ambientLowerSeries H 1) :
    ∀ c, relativeCommutatorSeries H ⊤ (hallExtensionCost d c) ≤
      ambientLowerSeries H c
  | 0 => by
      rw [hallExtensionCost, relative_series_zero,
        ambient_series_zero]
  | c + 1 => by
      calc
        relativeCommutatorSeries H ⊤ (hallExtensionCost d (c + 1)) =
            relativeCommutatorSeries
              (relativeCommutatorSeries H ⊤ (hallExtensionCost d c)) ⊤
                ((c + 1) * d) := by
                  rw [hallExtensionCost, relative_commutator_add]
        _ ≤ relativeCommutatorSeries (ambientLowerSeries H c) ⊤
              ((c + 1) * d) :=
          relative_series_mono
            (relative_ambient_cost
              H d hbase c) le_rfl _
        _ ≤ ambientLowerSeries H (c + 1) :=
          relative_ambient_step H d hbase c

/-- **Hall, bis Lemma 3.8.** If `H ◁ K`, and both `H` and `K / H'`
are nilpotent, then `K` is nilpotent. -/
theorem nilpotent_normal_derived
    (H : Subgroup G) [H.Normal]
    (hH : Group.IsNilpotent H)
    (hquotient : Group.IsNilpotent (G ⧸ ambientLowerSeries H 1)) :
    Group.IsNilpotent G := by
  obtain ⟨c, hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hH
  obtain ⟨d, hd⟩ :=
    (nilpotent_lower_central
      (ambientLowerSeries H 1)).mp hquotient
  have hbase :
      relativeCommutatorSeries H ⊤ d ≤ ambientLowerSeries H 1 := by
    calc
      relativeCommutatorSeries H ⊤ d ≤
          relativeCommutatorSeries (⊤ : Subgroup G) ⊤ d :=
        relative_series_mono le_top le_rfl d
      _ = Subgroup.lowerCentralSeries G d :=
        relative_series_top d
      _ ≤ ambientLowerSeries H 1 := hd
  have hcost :=
    relative_ambient_cost H d hbase c
  have hHterm : ambientLowerSeries H c = ⊥ := by
    rw [ambientLowerSeries, hc, Subgroup.map_bot]
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨d + hallExtensionCost d c, le_bot_iff.mp ?_⟩
  calc
    Subgroup.lowerCentralSeries G (d + hallExtensionCost d c) =
        relativeCommutatorSeries (Subgroup.lowerCentralSeries G d) ⊤
          (hallExtensionCost d c) := by
      rw [← relative_series_top (G := G),
        relative_commutator_add, relative_series_top]
    _ ≤ relativeCommutatorSeries H ⊤ (hallExtensionCost d c) :=
      relative_series_mono
        (hd.trans (ambient_lower_series H 1)) le_rfl _
    _ ≤ ambientLowerSeries H c := hcost
    _ = ⊥ := hHterm

lemma ambient_series_antitone
    (K : Subgroup G) {i j : ℕ} (hij : i ≤ j) :
    ambientLowerSeries K j ≤ ambientLowerSeries K i :=
  Subgroup.map_mono (Subgroup.lowerCentralSeries_antitone hij)

theorem relative_series_ambient
    (K : Subgroup G) (i : ℕ) :
    ∀ j, relativeCommutatorSeries (ambientLowerSeries K i) K j =
      ambientLowerSeries K (i + j)
  | 0 => by rw [relative_series_zero, Nat.add_zero]
  | j + 1 => by
      rw [relative_series_succ,
        relative_series_ambient K i j,
        ← ambient_series_succ]
      congr 1

lemma triple_commutator_centralizes
    (H K C H' : Subgroup G)
    (hCK : C ≤ K) (hcentral : ⁅⁅H, K⁆, C⁆ = ⊥)
    (hHC : ⁅H, C⁆ ≤ H')
    {x y z : G} (hx : x ∈ C) (hy : y ∈ K) (hz : z ∈ H) :
    hallTripleCommutator x y⁻¹ z ∈ ⁅H', K⁆ := by
  have hmiddle_mem :
      hallTripleCommutator y z⁻¹ x ∈ ⁅⁅H, K⁆, C⁆ := by
    apply hall_commutator
    · rw [Subgroup.commutator_comm H K]
      exact hall_commutator hy (H.inv_mem hz)
    · exact hx
  have hmiddle : hallTripleCommutator y z⁻¹ x = 1 := by
    rw [hcentral] at hmiddle_mem
    exact Subgroup.mem_bot.mp hmiddle_mem
  have hthird : hallTripleCommutator z x⁻¹ y ∈ ⁅H', K⁆ := by
    exact hall_commutator
      (hHC (hall_commutator hz (C.inv_mem hx))) hy
  have hthirdConj :
      hallConjugate (hallTripleCommutator z x⁻¹ y) x ∈ ⁅H', K⁆ := by
    simpa only [hallConjugate, inv_inv] using
      conjugate_commutator_right
        (X := H') (Y := K) (K.inv_mem (hCK hx)) hthird
  have hfirstConj :
      hallConjugate (hallTripleCommutator x y⁻¹ z) y ∈ ⁅H', K⁆ := by
    have heq :
        hallConjugate (hallTripleCommutator x y⁻¹ z) y =
          (hallConjugate (hallTripleCommutator z x⁻¹ y) x)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h := hallWitt_identity x y z
      rw [hmiddle] at h
      simpa [hallConjugate] using h
    rw [heq]
    exact (⁅H', K⁆ : Subgroup G).inv_mem hthirdConj
  simpa [hallConjugate, mul_assoc] using
    conjugate_commutator_right
      (X := H') (Y := K) hy hfirstConj

lemma commutator_right_centralizes
    (H K C H' : Subgroup G)
    (hCK : C ≤ K) (hcentral : ⁅⁅H, K⁆, C⁆ = ⊥)
    (hHC : ⁅H, C⁆ ≤ H') :
    ⁅H, ⁅C, K⁆⁆ ≤ ⁅H', K⁆ := by
  have hcomm_le_K : ⁅C, K⁆ ≤ K :=
    (Subgroup.commutator_mono hCK le_rfl).trans K.commutator_le_self
  have hHall :
      ∀ {t : G}, t ∈ ⁅C, K⁆ → ∀ {z : G}, z ∈ H →
        hallCommutator t z ∈ ⁅H', K⁆ := by
    intro t ht
    rw [Subgroup.commutator_def] at ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
        rintro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := ht
        rw [commutator_element_inv]
        exact triple_commutator_centralizes
          H K C H' hCK hcentral hHC (C.inv_mem hx) hy hz
    | one =>
        intro z _
        simp [hallCommutator]
    | mul a b ha hb hha hhb =>
        intro z hz
        rw [commutator_mul_left]
        exact (⁅H', K⁆ : Subgroup G).mul_mem
          (by
            simpa only [hallConjugate, inv_inv] using
              conjugate_commutator_right
                (X := H') (Y := K) (K.inv_mem (hcomm_le_K hb)) (hha hz))
          (hhb hz)
    | inv a ha hha =>
        intro z hz
        simpa [hallCommutator, hallConjugate, mul_assoc] using
          conjugate_commutator_right
            (X := H') (Y := K) (hcomm_le_K ha)
              ((⁅H', K⁆ : Subgroup G).inv_mem (hha hz))
  rw [Subgroup.commutator_le]
  intro z hz t ht
  rw [commutator_element_inv,
    commutator_swap_inv]
  exact (⁅H', K⁆ : Subgroup G).inv_mem
    (hHall ((⁅C, K⁆ : Subgroup G).inv_mem ht) (H.inv_mem hz))

lemma relative_series_left
    (H K : Subgroup G) (hstep : ⁅H, K⁆ ≤ H) :
    ∀ i, relativeCommutatorSeries H K i ≤ H
  | 0 => le_rfl
  | i + 1 =>
      (Subgroup.commutator_mono
        (relative_series_left H K hstep i)
        le_rfl).trans hstep

lemma commutator_relative_series
    (H K C : Subgroup G) (hCK : C ≤ K) (hCstep : ⁅C, K⁆ ≤ C)
    (hcentral : ⁅⁅H, K⁆, C⁆ = ⊥) :
    ∀ i, ⁅H, relativeCommutatorSeries C K i⁆ ≤
      relativeCommutatorSeries H K (i + 1)
  | 0 => by
      simpa only [relative_series_zero,
        relative_series_succ] using
          Subgroup.commutator_mono le_rfl hCK
  | i + 1 => by
      rw [relative_series_succ, relative_series_succ]
      apply commutator_right_centralizes
        H K (relativeCommutatorSeries C K i)
          (relativeCommutatorSeries H K (i + 1))
      · exact
          (relative_series_left C K hCstep i).trans
            hCK
      · apply le_bot_iff.mp
        exact (Subgroup.commutator_mono le_rfl
          (relative_series_left C K hCstep i)).trans
            hcentral.le
      · exact commutator_relative_series H K C hCK hCstep hcentral i

/-- **Hall, Theorem 3.8.** If the `r`th relative-commutator term is
trivial, then `[H, γ_(1 + choose r 2)(K)] = 1`.  Mathlib's lower
central series is zero-based, so the displayed `γ` has index
`choose r 2`. -/
theorem trivial_implies_centralizes
    (H K : Subgroup G) (r : ℕ)
    (hterm : relativeCommutatorSeries H K r = ⊥) :
    ⁅H, ambientLowerSeries K (Nat.choose r 2)⁆ = ⊥ := by
  induction r generalizing H with
  | zero =>
      rw [relative_series_zero] at hterm
      simp only [Nat.choose, ambient_series_zero, hterm,
        Subgroup.commutator_bot_left]
  | succ r ih =>
      cases r with
      | zero =>
          simpa [relative_series_succ,
            ambient_series_zero] using hterm
      | succ r =>
          let H₁ : Subgroup G := ⁅H, K⁆
          let C : Subgroup G :=
            ambientLowerSeries K (Nat.choose (r + 1) 2)
          have hH₁term : relativeCommutatorSeries H₁ K (r + 1) = ⊥ := by
            dsimp only [H₁]
            rw [relative_series_add]
            simpa only [Nat.add_assoc] using hterm
          have hcentral : ⁅H₁, C⁆ = ⊥ := by
            dsimp only [H₁, C]
            exact ih ⁅H, K⁆ hH₁term
          have hCK : C ≤ K := by
            exact ambient_lower_series K (Nat.choose (r + 1) 2)
          have hCstep : ⁅C, K⁆ ≤ C := by
            dsimp only [C]
            rw [← ambient_series_succ]
            exact ambient_series_antitone K (Nat.le_succ _)
          have htransport :=
            commutator_relative_series H K C hCK hCstep hcentral
              (r + 1)
          have hindex :
              Nat.choose (r + 1) 2 + (r + 1) = Nat.choose (r + 2) 2 := by
            calc
              Nat.choose (r + 1) 2 + (r + 1) =
                  (r + 1) + Nat.choose (r + 1) 2 := Nat.add_comm _ _
              _ = Nat.choose ((r + 1) + 1) 2 := by
                simpa only [Nat.choose_one_right] using
                  (Nat.choose_succ_succ' (r + 1) 1).symm
              _ = Nat.choose (r + 2) 2 := rfl
          apply le_bot_iff.mp
          calc
            ⁅H, ambientLowerSeries K
                (Nat.choose (Nat.succ (Nat.succ r)) 2)⁆ =
                ⁅H, relativeCommutatorSeries C K (r + 1)⁆ := by
                  rw [relative_series_ambient,
                    hindex]
            _ ≤ relativeCommutatorSeries H K ((r + 1) + 1) :=
              htransport
            _ = ⊥ := by
              simpa only [Nat.add_assoc] using hterm

/-- The action used to realize a subgroup of automorphisms inside its
restricted holomorph. -/
def subgroupAutomorphismAction (A : Subgroup (MulAut G)) : A →* MulAut G :=
  A.subtype

/-- The semidirect product of a group by a chosen subgroup of its
automorphism group. -/
abbrev SubgroupHolomorph (A : Subgroup (MulAut G)) :=
  G ⋊[subgroupAutomorphismAction A] A

/-- The base-group embedding into a restricted holomorph. -/
def subgroupHolomorphBase (A : Subgroup (MulAut G)) :
    G →* SubgroupHolomorph A :=
  SemidirectProduct.inl

/-- The automorphism-subgroup embedding into a restricted holomorph. -/
def subgroupHolomorphAutomorphism (A : Subgroup (MulAut G)) :
    A →* SubgroupHolomorph A :=
  SemidirectProduct.inr

lemma subgroup_holomorph_step
    (A : Subgroup (MulAut G)) (H H' : Subgroup G)
    (hstep : ∀ x, x ∈ H → ∀ a : A, x⁻¹ * a.1 x ∈ H') :
    ⁅H.map (subgroupHolomorphBase A),
        (subgroupHolomorphAutomorphism A).range⁆ ≤
      H'.map (subgroupHolomorphBase A) := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨a, rfl⟩
  refine ⟨x * a.1 x⁻¹, ?_, ?_⟩
  · simpa only [inv_inv] using hstep x⁻¹ (H.inv_mem hx) a
  · change
      subgroupHolomorphBase A (x * a.1 x⁻¹) =
        ⁅subgroupHolomorphBase A x, subgroupHolomorphAutomorphism A a⁆
    symm
    have haut :
        subgroupHolomorphAutomorphism A a *
            subgroupHolomorphBase A x⁻¹ *
              subgroupHolomorphAutomorphism A a⁻¹ =
          subgroupHolomorphBase A (a.1 x⁻¹) := by
      simpa only [subgroupHolomorphBase, subgroupHolomorphAutomorphism] using
        (SemidirectProduct.inl_aut
          (φ := subgroupAutomorphismAction A) a x⁻¹).symm
    calc
      ⁅subgroupHolomorphBase A x, subgroupHolomorphAutomorphism A a⁆ =
          subgroupHolomorphBase A x *
            (subgroupHolomorphAutomorphism A a *
              subgroupHolomorphBase A x⁻¹ *
                subgroupHolomorphAutomorphism A a⁻¹) := by
          simp only [commutatorElement_def, map_inv, mul_assoc]
      _ = subgroupHolomorphBase A x *
          subgroupHolomorphBase A (a.1 x⁻¹) := by
        rw [haut]
      _ = subgroupHolomorphBase A (x * a.1 x⁻¹) := by
        rw [map_inv, map_mul]

lemma holomorph_automorphism_centralizer
    (A : Subgroup (MulAut G)) (a : A)
    (ha : subgroupHolomorphAutomorphism A a ∈
      Subgroup.centralizer
        ((subgroupHolomorphBase A).range :
          Set (SubgroupHolomorph A))) :
    a = 1 := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  have hx :=
    (Subgroup.mem_centralizer_iff.mp ha)
      (subgroupHolomorphBase A x) ⟨x, rfl⟩
  have hconj :
      subgroupHolomorphBase A x =
        subgroupHolomorphAutomorphism A a *
          subgroupHolomorphBase A x *
            subgroupHolomorphAutomorphism A a⁻¹ := by
    calc
      subgroupHolomorphBase A x =
          (subgroupHolomorphBase A x *
            subgroupHolomorphAutomorphism A a) *
              subgroupHolomorphAutomorphism A a⁻¹ := by
        simpa only [map_inv] using
          (mul_inv_cancel_right
            (subgroupHolomorphBase A x)
            (subgroupHolomorphAutomorphism A a)).symm
      _ = (subgroupHolomorphAutomorphism A a *
          subgroupHolomorphBase A x) *
            subgroupHolomorphAutomorphism A a⁻¹ := by rw [hx]
  have haut :
      subgroupHolomorphAutomorphism A a *
          subgroupHolomorphBase A x *
            subgroupHolomorphAutomorphism A a⁻¹ =
        subgroupHolomorphBase A (a.1 x) := by
    simpa only [subgroupHolomorphBase, subgroupHolomorphAutomorphism] using
      (SemidirectProduct.inl_aut
        (φ := subgroupAutomorphismAction A) a x).symm
  rw [haut] at hconj
  exact SemidirectProduct.inl_injective hconj |>.symm

lemma lower_ambient_range
    {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (n : ℕ) :
    (Subgroup.lowerCentralSeries X n).map f =
      ambientLowerSeries f.range n := by
  rw [ambientLowerSeries]
  calc
    (Subgroup.lowerCentralSeries X n).map f =
        ((Subgroup.lowerCentralSeries X n).map f.rangeRestrict).map f.range.subtype := by
          rw [Subgroup.map_map, f.subtype_comp_rangeRestrict]
    _ = (Subgroup.lowerCentralSeries f.range n).map f.range.subtype := by
      rw [central_series_surjective
        f.rangeRestrict f.rangeRestrict_surjective]

/-- **Corollary to Hall, Theorem 3.8.** An automorphism group lowering
a subgroup chain of length `r` is nilpotent of class at most
`choose r 2`. -/
theorem automorphism_lowering_chain
    (A : Subgroup (MulAut G)) (H : ℕ → Subgroup G) (r : ℕ)
    (hzero : H 0 = ⊤) (hr : H r = ⊥)
    (hstep : ∀ i x, x ∈ H i → ∀ a : A, x⁻¹ * a.1 x ∈ H (i + 1)) :
    Group.IsNilpotent A ∧ Group.nilpotencyClass A ≤ Nat.choose r 2 := by
  let ι := subgroupHolomorphBase A
  let ρ := subgroupHolomorphAutomorphism A
  have hrelative :
      ∀ i, relativeCommutatorSeries ((H 0).map ι) ρ.range i ≤ (H i).map ι := by
    intro i
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
        rw [relative_series_succ]
        exact (Subgroup.commutator_mono ih le_rfl).trans
          (subgroup_holomorph_step A (H i) (H (i + 1)) (hstep i))
  have hrelbot :
      relativeCommutatorSeries ((H 0).map ι) ρ.range r = ⊥ := by
    apply le_bot_iff.mp
    calc
      relativeCommutatorSeries ((H 0).map ι) ρ.range r ≤ (H r).map ι :=
        hrelative r
      _ = ⊥ := by rw [hr, Subgroup.map_bot]
  have hcentral :
      ⁅(H 0).map ι,
          ambientLowerSeries ρ.range (Nat.choose r 2)⁆ = ⊥ :=
    trivial_implies_centralizes ((H 0).map ι) ρ.range r hrelbot
  have hambient :
      ambientLowerSeries ρ.range (Nat.choose r 2) = ⊥ := by
    apply le_bot_iff.mp
    intro t ht
    have htRange : t ∈ ρ.range :=
      ambient_lower_series ρ.range (Nat.choose r 2) ht
    obtain ⟨a, rfl⟩ := htRange
    have hcentralSwap :
        ⁅ambientLowerSeries ρ.range (Nat.choose r 2), (H 0).map ι⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hcentral
    have haCentral :
        ρ a ∈ Subgroup.centralizer ((ι.range : Subgroup (SubgroupHolomorph A)) :
          Set (SubgroupHolomorph A)) := by
      rw [← show (H 0).map ι = ι.range by
        rw [hzero, ← MonoidHom.range_eq_map]]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralSwap) ht
    have ha : a = 1 := by
      exact holomorph_automorphism_centralizer A a haCentral
    exact Subgroup.mem_bot.mpr (by rw [ha, map_one])
  have hρinjective : Function.Injective ρ := by
    exact SemidirectProduct.inr_injective
  have hmap :
      (Subgroup.lowerCentralSeries A (Nat.choose r 2)).map ρ = ⊥ := by
    rw [lower_ambient_range, hambient]
  have hlower : Subgroup.lowerCentralSeries A (Nat.choose r 2) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.lowerCentralSeries A (Nat.choose r 2)) hρinjective).mp hmap
  have hnil : Group.IsNilpotent A :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨Nat.choose r 2, hlower⟩
  letI : Group.IsNilpotent A := hnil
  exact ⟨hnil, Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hlower⟩

end Edmonton
end Submission

import Mathlib.GroupTheory.Nilpotent

/-!
# The Edmonton Notes on Nilpotent Groups: central series

This file begins a formalization of Section 1 of Philip Hall's Edmonton notes.

Mathlib numbers both central series from zero:

* `Subgroup.upperCentralSeries G 0 = ⊥`, agreeing with Hall's `Z₀ = 1`;
* `Subgroup.lowerCentralSeries G 0 = ⊤`, so Mathlib's `Subgroup.lowerCentralSeries G n`
  is Hall's `Γ_{n+1}`.
-/

namespace Submission
namespace Edmonton

open Group
open scoped commutatorElement

/-- A group is nilpotent of exactly class `c`. -/
def NilpotentClass (G : Type*) [Group G] (c : ℕ) : Prop :=
  Group.IsNilpotent G ∧ Group.nilpotencyClass G = c

/-- Hall's strict upper-central-series characterization of class `c`. -/
def UpperSeriesClass (G : Type*) [Group G] (c : ℕ) : Prop :=
  Subgroup.upperCentralSeries G c = ⊤ ∧
    StrictMonoOn (Subgroup.upperCentralSeries G) (Set.Iic c)

/-- Hall's strict lower-central-series characterization of class `c`.

Because Mathlib starts the lower central series at zero, the endpoint here is
`Subgroup.lowerCentralSeries G c = ⊥`, corresponding to Hall's `Γ_{c+1} = 1`.
-/
def LowerSeriesClass (G : Type*) [Group G] (c : ℕ) : Prop :=
  Subgroup.lowerCentralSeries G c = ⊥ ∧
    StrictAntiOn (Subgroup.lowerCentralSeries G) (Set.Iic c)

namespace lowerCentralSeries

variable {G : Type*} [Group G]

/-- Once two consecutive lower-central-series terms agree, all later terms
agree with them. -/
lemma eq_ge_succ {a b : ℕ} (hab : a ≤ b)
    (h : Subgroup.lowerCentralSeries G a = Subgroup.lowerCentralSeries G (a + 1)) :
    Subgroup.lowerCentralSeries G a = Subgroup.lowerCentralSeries G b := by
  refine Nat.le_induction rfl ?_ b hab
  grind only [Subgroup.lowerCentralSeries]

/-- Equality of any two distinct lower-central-series terms forces the series
to be constant from the earlier term onward. -/
lemma eq_ge_gt {a b c : ℕ} (hab : a < b) (hac : a ≤ c)
    (h : Subgroup.lowerCentralSeries G a = Subgroup.lowerCentralSeries G b) :
    Subgroup.lowerCentralSeries G a = Subgroup.lowerCentralSeries G c := by
  apply eq_ge_succ hac
  apply le_antisymm
  · rw [h]
    exact Subgroup.lowerCentralSeries_antitone (Nat.succ_le_of_lt hab)
  · exact Subgroup.lowerCentralSeries_antitone (Nat.le_succ a)

/-- Before the nilpotency class is reached, the lower central series strictly
decreases. This is the lower-series counterpart of Mathlib's
`Subgroup.upperCentralSeries.StrictMonoOn`. -/
lemma strict_anti_nilpotent [Group.IsNilpotent G] :
    StrictAntiOn (Subgroup.lowerCentralSeries G) (Set.Iic (Group.nilpotencyClass G)) := by
  intro a ha b hb hab
  apply lt_of_le_of_ne
  · exact Subgroup.lowerCentralSeries_antitone hab.le
  · intro hba
    have ha_bot : Subgroup.lowerCentralSeries G a = ⊥ :=
      (eq_ge_gt hab ha hba.symm).trans
        Subgroup.lowerCentralSeries_nilpotencyClass
    have hclass_le_a :
        Group.nilpotencyClass G ≤ a :=
      Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp ha_bot
    exact (not_lt_of_ge hb) (lt_of_le_of_lt hclass_le_a hab)

end lowerCentralSeries

variable {G : Type*} [Group G] {c : ℕ}

/-- The upper-central-series half of Hall's Lemma 1.1. -/
theorem nilpotent_upper_series :
    NilpotentClass G c ↔ UpperSeriesClass G c := by
  constructor
  · rintro ⟨hG, rfl⟩
    letI : Group.IsNilpotent G := hG
    exact
      ⟨Subgroup.upperCentralSeries_nilpotencyClass,
        Subgroup.upperCentralSeries.StrictMonoOn G⟩
  · rintro ⟨hc_top, hstrict⟩
    have hG : Group.IsNilpotent G := ⟨⟨c, hc_top⟩⟩
    letI : Group.IsNilpotent G := hG
    refine ⟨hG, le_antisymm ?_ ?_⟩
    · exact
        Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp hc_top
    · by_contra hnot
      have hclass_lt_c : Group.nilpotencyClass G < c :=
        Nat.lt_of_not_ge hnot
      have htop_lt_top :=
        hstrict hclass_lt_c.le (le_refl c) hclass_lt_c
      rw [Subgroup.upperCentralSeries_nilpotencyClass, hc_top] at htop_lt_top
      exact (lt_irrefl (⊤ : Subgroup G)) htop_lt_top

/-- The lower-central-series half of Hall's Lemma 1.1. -/
theorem nilpotent_lower_series :
    NilpotentClass G c ↔ LowerSeriesClass G c := by
  constructor
  · rintro ⟨hG, rfl⟩
    letI : Group.IsNilpotent G := hG
    exact
      ⟨Subgroup.lowerCentralSeries_nilpotencyClass,
        lowerCentralSeries.strict_anti_nilpotent⟩
  · rintro ⟨hc_bot, hstrict⟩
    have hG : Group.IsNilpotent G :=
      Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c, hc_bot⟩
    letI : Group.IsNilpotent G := hG
    refine ⟨hG, le_antisymm ?_ ?_⟩
    · exact
        Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hc_bot
    · by_contra hnot
      have hclass_lt_c : Group.nilpotencyClass G < c :=
        Nat.lt_of_not_ge hnot
      have hbot_lt_bot :=
        hstrict hclass_lt_c.le (le_refl c) hclass_lt_c
      rw [Subgroup.lowerCentralSeries_nilpotencyClass, hc_bot] at hbot_lt_bot
      exact (lt_irrefl (⊥ : Subgroup G)) hbot_lt_bot

/-- **Hall, Lemma 1.1.** The strict upper and lower central series detect the
same nilpotency class. -/
theorem upper_series_lower :
    UpperSeriesClass G c ↔ LowerSeriesClass G c :=
  nilpotent_upper_series.symm.trans nilpotent_lower_series

/-- A surjective group homomorphism maps every lower-central-series term
onto the corresponding term of its codomain. -/
lemma central_series_surjective
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    Subgroup.map f (Subgroup.lowerCentralSeries G n) = Subgroup.lowerCentralSeries H n := by
  apply le_antisymm
  · exact Subgroup.lowerCentralSeries.map f n
  · induction n with
    | zero =>
        rw [Subgroup.lowerCentralSeries_zero, Subgroup.lowerCentralSeries_zero]
        exact (Subgroup.map_top_of_surjective f hf).ge
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ]
        exact
          Subgroup.commutator_le_map_commutator ih
            ((Subgroup.map_top_of_surjective f hf).ge)

/-- **Hall, Lemma 1.2 (quotient formula).** The lower central series of
`G ⧸ K` is the image of the lower central series of `G`. -/
theorem lower_series_quotient
    (K : Subgroup G) [K.Normal] (n : ℕ) :
    Subgroup.lowerCentralSeries (G ⧸ K) n =
      Subgroup.map (QuotientGroup.mk' K) (Subgroup.lowerCentralSeries G n) := by
  exact
    (central_series_surjective
      (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) n).symm

/-- Preimage form of Hall's quotient formula:
`γₙ(G/K)` corresponds to `K γₙ(G)`, represented as a subgroup supremum. -/
theorem lower_series_comap
    (K : Subgroup G) [K.Normal] (n : ℕ) :
    Subgroup.comap (QuotientGroup.mk' K) (Subgroup.lowerCentralSeries (G ⧸ K) n) =
      K ⊔ Subgroup.lowerCentralSeries G n := by
  rw [lower_series_quotient, QuotientGroup.comap_map_mk']

/-- **Hall, Lemma 1.2 (nilpotence criterion).** A quotient `G ⧸ K` is
nilpotent exactly when `K` contains a term of the lower central series of
`G`. -/
theorem nilpotent_lower_central
    (K : Subgroup G) [K.Normal] :
    Group.IsNilpotent (G ⧸ K) ↔
      ∃ n : ℕ, Subgroup.lowerCentralSeries G n ≤ K := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmap :
        Subgroup.map (QuotientGroup.mk' K) (Subgroup.lowerCentralSeries G n) = ⊥ := by
      rw [← lower_series_quotient, hn]
    exact
      (Subgroup.map_eq_bot_iff (Subgroup.lowerCentralSeries G n)).mp hmap
        |>.trans_eq (QuotientGroup.ker_mk' K)
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [lower_series_quotient, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hn

/-- The subgroup Hall writes as `⟨x, G'⟩`. -/
def generatorDerivedSubgroup (x : G) : Subgroup G :=
  Subgroup.closure {x} ⊔ commutator G

/-- The first lower-central term becomes central after quotienting by the
second lower-central term. -/
lemma lower_series_center :
    Subgroup.map (QuotientGroup.mk' (Subgroup.lowerCentralSeries G 2))
        (Subgroup.lowerCentralSeries G 1) ≤
      Subgroup.center (G ⧸ Subgroup.lowerCentralSeries G 2) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨z, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.lowerCentralSeries G 2) z
  rw [← commutatorElement_eq_one_iff_mul_comm,
    ← map_commutatorElement]
  change ((⁅z, a⁆ : G) : G ⧸ Subgroup.lowerCentralSeries G 2) = 1
  apply (QuotientGroup.eq_one_iff ⁅z, a⁆).mpr
  change ⁅z, a⁆ ∈ ⁅Subgroup.lowerCentralSeries G 1, (⊤ : Subgroup G)⁆
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top z) ha

/-- The derived subgroup of `⟨x, G'⟩` lies one lower-central step deeper
than the generic subgroup bound. -/
lemma derived_series_two
    (x : G) :
    ⁅generatorDerivedSubgroup x, generatorDerivedSubgroup x⁆ ≤
      Subgroup.lowerCentralSeries G 2 := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [generatorDerivedSubgroup,
    Subgroup.mem_sup_of_normal_right] at ha hb
  rcases ha with ⟨xa, hxa, ga, hga, rfl⟩
  rcases hb with ⟨xb, hxb, gb, hgb, rfl⟩
  rcases Subgroup.mem_closure_singleton.mp hxa with ⟨m, rfl⟩
  rcases Subgroup.mem_closure_singleton.mp hxb with ⟨n, rfl⟩
  let q : G →* G ⧸ Subgroup.lowerCentralSeries G 2 :=
    QuotientGroup.mk' (Subgroup.lowerCentralSeries G 2)
  have hga_center : q ga ∈ Subgroup.center (G ⧸ Subgroup.lowerCentralSeries G 2) := by
    apply lower_series_center
    exact Subgroup.mem_map_of_mem q hga
  have hgb_center : q gb ∈ Subgroup.center (G ⧸ Subgroup.lowerCentralSeries G 2) := by
    apply lower_series_center
    exact Subgroup.mem_map_of_mem q hgb
  have hpow :
      Commute (q x ^ m) (q x ^ n) :=
    Commute.zpow_zpow_self (q x) m n
  have hpow_ga : Commute (q x ^ m) (q ga) :=
    (Subgroup.mem_center_iff.mp hga_center (q x ^ m))
  have hpow_gb : Commute (q x ^ m) (q gb) :=
    (Subgroup.mem_center_iff.mp hgb_center (q x ^ m))
  have hga_pow : Commute (q ga) (q x ^ n) :=
    (Subgroup.mem_center_iff.mp hga_center (q x ^ n)).symm
  have hga_gb : Commute (q ga) (q gb) :=
    (Subgroup.mem_center_iff.mp hgb_center (q ga))
  apply (QuotientGroup.eq_one_iff ⁅x ^ m * ga, x ^ n * gb⁆).mp
  change q ⁅x ^ m * ga, x ^ n * gb⁆ = 1
  rw [map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  simpa [q, map_mul, map_zpow] using
    ((hpow.mul_right hpow_gb).mul_left
      (hga_pow.mul_right hga_gb)).eq

/-- Every positive lower-central term of `⟨x, G'⟩` maps one step deeper
into the lower central series of `G`. -/
lemma generator_derived_series
    (x : G) (n : ℕ) :
    Subgroup.map (generatorDerivedSubgroup x).subtype
        (Subgroup.lowerCentralSeries (generatorDerivedSubgroup x) (n + 1)) ≤
      Subgroup.lowerCentralSeries G (n + 2) := by
  induction n with
  | zero =>
      simpa [Subgroup.lowerCentralSeries_one,
        Subgroup.map_subtype_commutator] using
        derived_series_two x
  | succ n ih =>
      change
        Subgroup.map (generatorDerivedSubgroup x).subtype
            ⁅Subgroup.lowerCentralSeries (generatorDerivedSubgroup x) (n + 1), ⊤⁆ ≤
          Subgroup.lowerCentralSeries G (n + 3)
      rw [Subgroup.map_commutator]
      have htop :
          Subgroup.map (generatorDerivedSubgroup x).subtype
              (⊤ : Subgroup (generatorDerivedSubgroup x)) ≤
            (⊤ : Subgroup G) :=
        (Subgroup.map_subtype_le
          (H := generatorDerivedSubgroup x) ⊤).trans le_top
      exact
        (Subgroup.commutator_mono ih htop).trans
          (by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (show
                ⁅Subgroup.lowerCentralSeries G (n + 2), (⊤ : Subgroup G)⁆ ≤
                  Subgroup.lowerCentralSeries G (n + 3) from le_rfl))

/-- The subgroup clause of Hall's Lemma 1.3. -/
theorem subgroup_nilpotency_class
    (H : Subgroup G) (hG : NilpotentClass G c) :
    Group.IsNilpotent H ∧ Group.nilpotencyClass H ≤ c := by
  letI : Group.IsNilpotent G := hG.1
  exact ⟨inferInstance, (H.nilpotencyClass_le).trans_eq hG.2⟩

/-- The quotient clause of Hall's Lemma 1.3. -/
theorem quotient_nilpotency_class
    (K : Subgroup G) [K.Normal] (hG : NilpotentClass G c) :
    Group.IsNilpotent (G ⧸ K) ∧ Group.nilpotencyClass (G ⧸ K) ≤ c := by
  letI : Group.IsNilpotent G := hG.1
  exact ⟨inferInstance, (Group.nilpotencyClass_quotient_le K).trans_eq hG.2⟩

/-- **Hall, Lemma 1.3 (sharper subgroup bound).** If `G` has class `c > 1`,
then `⟨x, G'⟩` has class at most `c - 1`. -/
theorem derived_nilpotency_class
    (x : G) (hG : NilpotentClass G c) (hc : 1 < c) :
    Group.nilpotencyClass (generatorDerivedSubgroup x) ≤ c - 1 := by
  letI : Group.IsNilpotent G := hG.1
  let H := generatorDerivedSubgroup x
  letI : Group.IsNilpotent H := Subgroup.isNilpotent H
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = k + 2 := by
    use c - 2
    omega
  rw [← Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  apply
    (Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.lowerCentralSeries H (k + 2 - 1)) H.subtype_injective).mp
  apply le_bot_iff.mp
  calc
    Subgroup.map H.subtype (Subgroup.lowerCentralSeries H (k + 2 - 1)) ≤
        Subgroup.lowerCentralSeries G (k + 2) := by
      simpa [H, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        generator_derived_series (G := G) x k
    _ = ⊥ := by
      rw [← hG.2]
      exact Subgroup.lowerCentralSeries_nilpotencyClass

/-- **Hall, Lemma 1.4 (center clause).** A nontrivial finite `p`-group has
nontrivial center. -/
theorem center_ne_bot
    {p n : ℕ} [Fact p.Prime] [Finite G]
    (hcard : Nat.card G = p ^ n) (hn : 0 < n) :
    (⊥ : Subgroup G) < Subgroup.center G := by
  have hP : IsPGroup p G := IsPGroup.of_card hcard
  letI : Nontrivial G :=
    (hP.nontrivial_iff_card).mpr ⟨n, hn, hcard⟩
  exact hP.bot_lt_center

/-- Corrected class clause of Hall's Lemma 1.4.

The printed hypothesis `p^n > 1` only implies `0 < n`, but the claimed
conclusion `class(G) < n` is false for a group of order `p`. The conclusion is
valid with the necessary assumption `1 < n`.
-/
theorem nilpotency_log_order
    {p n : ℕ} [Fact p.Prime] [Finite G]
    (hcard : Nat.card G = p ^ n) (hn : 1 < n) :
    Group.nilpotencyClass G < n := by
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      have hP : IsPGroup p G := IsPGroup.of_card hcard
      letI : Group.IsNilpotent G := hP.isNilpotent
      letI : Nontrivial G :=
        (hP.nontrivial_iff_card).mpr ⟨n, by omega, hcard⟩
      let Q := G ⧸ Subgroup.center G
      have hPQ : IsPGroup p Q :=
        hP.to_quotient (Subgroup.center G)
      obtain ⟨m, hm⟩ := hPQ.exists_card_eq
      obtain ⟨k, hk_pos, hk⟩ :=
        IsPGroup.card_center_eq_prime_pow hcard (by omega)
      have hnm : n = m + k := by
        apply Nat.pow_right_injective ((Fact.out : Nat.Prime p).two_le)
        calc
          p ^ n = Nat.card G := hcard.symm
          _ = Nat.card Q * Nat.card (Subgroup.center G) :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup
              (Subgroup.center G)
          _ = p ^ m * p ^ k := by rw [hm, hk]
          _ = p ^ (m + k) := (pow_add p m k).symm
      have hm_lt_n : m < n := by omega
      by_cases hm_one : m ≤ 1
      · have hQ_dvd_p : Nat.card Q ∣ p := by
          rw [hm]
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm_one with rfl | rfl <;>
            simp
        letI : IsCyclic Q := isCyclic_of_card_dvd_prime hQ_dvd_p
        let _ : CommGroup G :=
          commGroupOfCyclicCenterQuotient
            (QuotientGroup.mk' (Subgroup.center G))
            (by rw [QuotientGroup.ker_mk'])
        exact CommGroup.nilpotencyClass_le_one.trans_lt hn
      · have hclassQ_lt : Group.nilpotencyClass Q < m :=
          ih m hm_lt_n hm (by omega)
        have hclassQ_lt' :
            Group.nilpotencyClass (G ⧸ Subgroup.center G) < m := by
          simpa [Q] using hclassQ_lt
        rw [Group.nilpotencyClass_eq_quotient_center_plus_one]
        omega

end Edmonton
end Submission

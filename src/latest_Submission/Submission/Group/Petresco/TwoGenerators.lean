import Submission.Group.Edmonton.HallEmbeddings
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Petresco words on two generators

This file packages the two-generator specialization used after Hall's
definition of the Petresco words in Section 6.
-/

namespace Submission
namespace Edmonton

open scoped Pointwise IsMulCommutative

universe u

variable {G : Type u}

/-- Evaluate a two-variable word at the ordered pair `(x, y)`. -/
def twoGeneratorAssignment (x y : G) : Bool → G
  | false => x
  | true => y

@[simp]
lemma two_assignment_false (x y : G) :
    twoGeneratorAssignment x y false = x :=
  rfl

@[simp]
lemma two_assignment_true (x y : G) :
    twoGeneratorAssignment x y true = y :=
  rfl

variable [Group G]

/-- The value denoted by `τ_k(x, y)` for a two-variable word family `τ`. -/
def petrescoWordValue (tau : ℕ → FreeGroup Bool) (k : ℕ) (x y : G) : G :=
  wordEval (tau k) (twoGeneratorAssignment x y)

/-- The family of two-generator values `k ↦ τ_k(x, y)`. -/
def petrescoWordValues (tau : ℕ → FreeGroup Bool) (x y : G) : ℕ → G :=
  fun k => petrescoWordValue tau k x y

/-- Hall's canonical two-generator Petresco word `τ_k(x, y)`. -/
def twoGeneratorPetresco (k : ℕ) : FreeGroup Bool :=
  petrescoWord [false, true] k

/-- Hall's canonical two-generator Petresco value `τ_k(x, y)`. -/
def twoPetrescoValue (k : ℕ) (x y : G) : G :=
  petrescoWordValue twoGeneratorPetresco k x y

/-- Hall's canonical family of two-generator Petresco values. -/
def twoPetrescoValues (x y : G) : ℕ → G :=
  fun k => twoPetrescoValue k x y

/-- A group has a two-generator Petresco separator when one ordered pair
has nontrivial canonical Petresco value in every positive weight. -/
def TPSepara (G : Type*) [Group G] : Prop :=
  ∃ x y : G,
    ∀ n : ℕ, 0 < n → twoPetrescoValue n x y ≠ 1

/-- Canonical two-generator Petresco values commute with group
homomorphisms. -/
lemma two_petresco_value
    {H : Type*} [Group H] (f : G →* H) (n : ℕ) (x y : G) :
    f (twoPetrescoValue n x y) =
      twoPetrescoValue n (f x) (f y) := by
  simp [twoPetrescoValue, twoGeneratorPetresco,
    petrescoWordValue, word_eval_petresco, twoGeneratorAssignment,
    map_petrescoTerm]

/-- An injective homomorphism transports a Petresco separator into its
codomain. In particular, a separator in a subgroup is a separator in the
ambient group. -/
lemma TPSepara.map_of_injective
    {H : Type*} [Group H] (h : TPSepara G)
    (f : G →* H) (hf : Function.Injective f) :
    TPSepara H := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨f x, f y, ?_⟩
  intro n hn htrivial
  apply hxy n hn
  apply hf
  rw [two_petresco_value, htrivial, map_one]

/-- A separator in a quotient, or more generally in any surjective
homomorphic image, lifts to a separator in the source. -/
lemma TPSepara.of_surjective
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (h : TPSepara H) :
    TPSepara G := by
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨x, rfl⟩ := hf x
  obtain ⟨y, rfl⟩ := hf y
  refine ⟨x, y, ?_⟩
  intro n hn htrivial
  apply hxy n hn
  rw [← two_petresco_value f, htrivial, map_one]

/-- A separator in a subgroup is a separator in the ambient group. -/
lemma TPSepara.of_subgroup
    (H : Subgroup G) (h : TPSepara H) :
    TPSepara G :=
  h.map_of_injective H.subtype Subtype.coe_injective

/-- A separator in a quotient lifts to a separator in the source. -/
lemma TPSepara.of_quotient
    (N : Subgroup G) [N.Normal]
    (h : TPSepara (G ⧸ N)) :
    TPSepara G :=
  h.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- A subgroup minimal among the nonnilpotent subgroups of an ambient
group. -/
def MNSubgro (H : Subgroup G) : Prop :=
  ¬ Group.IsNilpotent H ∧
    ∀ K : Subgroup G, K ≤ H → ¬ Group.IsNilpotent K → K = H

/-- A group is minimal nonnilpotent when it is not nilpotent but all its
proper subgroups are nilpotent. -/
def Group.IMNonnil (G : Type*) [Group G] : Prop :=
  ¬ Group.IsNilpotent G ∧
    ∀ H : Subgroup G, H < ⊤ → Group.IsNilpotent H

/-- A finite nonnilpotent group has a maximal subgroup which is not
normal. -/
lemma coatom_not_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ M : Subgroup G, IsCoatom M ∧ ¬ M.Normal := by
  by_contra h
  push Not at h
  apply hnil
  exact ((Group.isNilpotent_of_finite_tfae (G := G)).out 2 0).mp h

/-- A maximal subgroup descends across a surjection when it contains the
kernel. -/
lemma Subgroup.coatom_mapsurj_kerle
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f)
    {M : Subgroup G} (hM : IsCoatom M) (hker : f.ker ≤ M) :
    IsCoatom (M.map f) := by
  have hcomap :
      (M.map f).comap f = M :=
    Subgroup.comap_map_eq_self hker
  constructor
  · intro htop
    apply hM.1
    rw [← hcomap, htop, Subgroup.comap_top]
  · intro K hMK
    have hcomaplt :
        (M.map f).comap f < K.comap f :=
      (Subgroup.comap_lt_comap_of_surjective hf).mpr hMK
    have hKcomap :
        K.comap f = ⊤ := by
      apply hM.2
      rwa [hcomap] at hcomaplt
    rw [← Subgroup.map_comap_eq_self_of_surjective hf K, hKcomap,
      Subgroup.map_top_of_surjective f hf]

/-- A nontrivial nilpotent group has nontrivial center. -/
lemma center_nontrivial_nilpotent
    [Nontrivial G] [Group.IsNilpotent G] :
    Subgroup.center G ≠ ⊥ := by
  intro hcenter
  have hzero_succ :
      Subgroup.upperCentralSeries G 0 = Subgroup.upperCentralSeries G (0 + 1) := by
    simp [hcenter]
  have hconstant :
      Subgroup.upperCentralSeries G 0 =
        Subgroup.upperCentralSeries G (Group.nilpotencyClass G) :=
    Subgroup.upperCentralSeries.eq_ge_of_eq_succ
      (G := G) (Nat.zero_le _) hzero_succ
  rw [Subgroup.upperCentralSeries_zero, Subgroup.upperCentralSeries_nilpotencyClass] at hconstant
  exact top_ne_bot hconstant.symm

/-- A nonnormal maximal subgroup is self-normalizing. -/
lemma IsCoatom.normalizer_eqself_notnormal
    {M : Subgroup G} (hM : IsCoatom M) (hMnormal : ¬ M.Normal) :
    Subgroup.normalizer (M : Set G) = M := by
  exact (hM.le_iff.mp Subgroup.le_normalizer).resolve_left
    (mt Subgroup.normalizer_eq_top_iff.mp hMnormal)

/-- Conjugation preserves maximal subgroups. -/
lemma IsCoatom.conjAct
    {M : Subgroup G} (hM : IsCoatom M) (g : ConjAct G) :
    IsCoatom (g • M) := by
  simpa [Subgroup.pointwise_smul_def] using
    (OrderIso.isCoatom_iff
      (MulDistribMulAction.toMulEquiv G g).mapSubgroup M).mpr hM

/-- Every subgroup in the conjugation orbit of a maximal subgroup is
maximal. -/
lemma IsCoatom.mem_orbit_conjact
    {M H : Subgroup G} (hM : IsCoatom M)
    (hH : H ∈ MulAction.orbit (ConjAct G) M) :
    IsCoatom H := by
  obtain ⟨g, rfl⟩ :=
    MulAction.mem_orbit_iff.mp hH
  exact IsCoatom.conjAct hM g

/-- A nonnormal maximal subgroup has a distinct conjugate maximal
subgroup. -/
lemma IsCoatom.exists_ne_conjact
    {M : Subgroup G} (hM : IsCoatom M) (hMnormal : ¬ M.Normal) :
    ∃ g : G, IsCoatom (ConjAct.toConjAct g • M) ∧
      ConjAct.toConjAct g • M ≠ M := by
  have hnormalizer :
      Subgroup.normalizer (M : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact mt Subgroup.normalizer_eq_top_iff.mp hMnormal
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt hnormalizer
  exact ⟨g, IsCoatom.conjAct hM _, fun h ↦
    hg (Subgroup.conjAct_pointwise_smul_iff.mp h)⟩

/-- Inside a minimal nonnilpotent group, a nontrivial proper subgroup of
a maximal subgroup has a strictly larger ambient normalizer intersection
with that maximal subgroup. -/
lemma Group.IMNonnil.lt_infnormalizer_ltcoatom
    (hG : Group.IMNonnil G)
    {D M : Subgroup G} (hDM : D < M) (hM : IsCoatom M) :
    D < M ⊓ Subgroup.normalizer (D : Set G) := by
  letI : Group.IsNilpotent M :=
    hG.2 M hM.lt_top
  have hDsubgroupOf :
      D.subgroupOf M < (⊤ : Subgroup M) := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hDM.2 (Subgroup.subgroupOf_eq_top.mp htop)
  have hnormalizer :
      D.subgroupOf M <
        Subgroup.normalizer (D.subgroupOf M : Set M) :=
    Group.normalizerCondition_of_isNilpotent (G := M) _ hDsubgroupOf
  rw [← Subgroup.subgroupOf_normalizer_eq hDM.le] at hnormalizer
  have hmap :=
    Subgroup.map_subtype_lt_map_subtype.mpr hnormalizer
  simpa [Subgroup.map_subgroupOf_eq_of_le hDM.le,
    Subgroup.subgroupOf_map_subtype, inf_comm] using hmap

/-- An intersection of two distinct maximal subgroups. -/
def DistinctCoatomIntersection (D : Subgroup G) : Prop :=
  ∃ M K : Subgroup G,
    IsCoatom M ∧ IsCoatom K ∧ M ≠ K ∧ D = M ⊓ K

/-- A finite nonnilpotent group has an intersection of two distinct
maximal subgroups. -/
lemma distinct_coatom_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ D : Subgroup G, DistinctCoatomIntersection D := by
  obtain ⟨M, hM, hMnormal⟩ :=
    coatom_not_nilpotent (G := G) hnil
  obtain ⟨g, hconj, hne⟩ :=
    IsCoatom.exists_ne_conjact hM hMnormal
  exact ⟨M ⊓ ConjAct.toConjAct g • M, M,
    ConjAct.toConjAct g • M, hM, hconj, Ne.symm hne, rfl⟩

/-- Among the intersections of distinct maximal subgroups in a finite
nonnilpotent group, one is maximal under inclusion. -/
lemma distinct_coatom_intersection
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ D : Subgroup G,
      DistinctCoatomIntersection D ∧
        ∀ E : Subgroup G, DistinctCoatomIntersection E → D ≤ E → E ≤ D := by
  classical
  let S : Set (Subgroup G) := {D | DistinctCoatomIntersection D}
  obtain ⟨D, hD⟩ :=
    distinct_coatom_nilpotent
      (G := G) hnil
  obtain ⟨D, hDS, hDmaximal⟩ :=
    (Set.toFinite S).exists_maximal (show S.Nonempty from ⟨D, hD⟩)
  exact ⟨D, hDS, fun E hES hDE ↦ hDmaximal hES hDE⟩

/-- In a hypothetical finite simple minimal nonnilpotent group, distinct
maximal subgroups have trivial intersection. -/
lemma Group.IMNonnil.inf_eqbot_coatomne
    [Finite G] [IsSimpleGroup G] (hG : Group.IMNonnil G)
    {M K : Subgroup G} (hM : IsCoatom M) (hK : IsCoatom K)
    (hMK : M ≠ K) :
    M ⊓ K = ⊥ := by
  obtain ⟨D, hDintersection, hDmaximal⟩ :=
    distinct_coatom_intersection
      (G := G) hG.1
  obtain ⟨A, B, hA, hB, hAB, rfl⟩ := hDintersection
  have hDA : A ⊓ B < A := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    apply hAB
    exact ((hA.le_iff_eq hB.ne_top).mp (inf_eq_left.mp h)).symm
  have hDB : A ⊓ B < B := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro h
    apply hAB
    exact (hB.le_iff_eq hA.ne_top).mp (inf_eq_right.mp h)
  have hDbot : A ⊓ B = ⊥ := by
    by_contra hDne
    rcases eq_top_or_exists_le_coatom
        (Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G)) with
      hnormalizer | ⟨L, hL, hnormalizerL⟩
    · have hDnormal : (A ⊓ B).Normal :=
        Subgroup.normalizer_eq_top_iff.mp hnormalizer
      exact hDne (hDnormal.eq_bot_or_eq_top.resolve_right fun hDtop ↦
        hA.ne_top (top_unique (hDtop ▸ inf_le_left)))
    · by_cases hLA : L = A
      · have hBL : B ≠ L := by
          intro hBL
          exact hAB (hLA.symm.trans hBL.symm)
        have hlt :
            A ⊓ B < B ⊓ L := by
          exact lt_of_lt_of_le
            (hG.lt_infnormalizer_ltcoatom hDB hB)
            (inf_le_inf le_rfl hnormalizerL)
        exact hlt.2
          (hDmaximal (B ⊓ L)
            ⟨B, L, hB, hL, hBL, rfl⟩ hlt.le)
      · have hlt :
            A ⊓ B < A ⊓ L := by
          exact lt_of_lt_of_le
            (hG.lt_infnormalizer_ltcoatom hDA hA)
            (inf_le_inf le_rfl hnormalizerL)
        exact hlt.2
          (hDmaximal (A ⊓ L)
            ⟨A, L, hA, hL, Ne.symm hLA, rfl⟩ hlt.le)
  have hbotle : (⊥ : Subgroup G) ≤ M ⊓ K :=
    bot_le
  exact le_antisymm
    ((hDmaximal (M ⊓ K) ⟨M, K, hM, hK, hMK, rfl⟩
      (hDbot ▸ hbotle)).trans_eq hDbot)
    bot_le

/-- The conjugation orbit of a self-normalizing subgroup has cardinality
equal to its index. -/
lemma ncard_act_self
    (M : Subgroup G)
    (hnormalizer : Subgroup.normalizer (M : Set G) = M) :
    (MulAction.orbit (ConjAct G) M).ncard = M.index := by
  let q : G →* ConjAct G :=
    ConjAct.toConjAct.toMonoidHom
  have hcomap :
      (MulAction.stabilizer (ConjAct G) M).comap q =
        Subgroup.normalizer (M : Set G) := by
    ext g
    simp [q, MulAction.mem_stabilizer_iff,
      Subgroup.conjAct_pointwise_smul_iff]
  calc
    (MulAction.orbit (ConjAct G) M).ncard =
        (MulAction.stabilizer (ConjAct G) M).index :=
      (MulAction.index_stabilizer (ConjAct G) M).symm
    _ = ((MulAction.stabilizer (ConjAct G) M).comap q).index := by
      simp [Subgroup.index_comap, q, Subgroup.relIndex_top_right]
    _ = (Subgroup.normalizer (M : Set G)).index :=
      congrArg Subgroup.index hcomap
    _ = M.index :=
      congrArg Subgroup.index hnormalizer

/-- Removing the identity from a subgroup removes exactly one element. -/
lemma ncard_coe_diff (H : Subgroup G) :
    ((H : Set G) \ {1}).ncard = Nat.card H - 1 := by
  rw [Set.ncard_diff_singleton_of_mem H.one_mem,
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

/-- The nonidentity parts of pairwise trivially-intersecting conjugates
of a self-normalizing subgroup occupy `|G| - [G : M]` elements. -/
lemma ncard_act_diff
    [Finite G] (M : Subgroup G)
    (hnormalizer : Subgroup.normalizer (M : Set G) = M)
    (hinter :
      ∀ H ∈ MulAction.orbit (ConjAct G) M,
        ∀ K ∈ MulAction.orbit (ConjAct G) M,
          H ≠ K → H ⊓ K = ⊥) :
    (⋃ H ∈ MulAction.orbit (ConjAct G) M,
      ((H : Set G) \ {1})).ncard =
        Nat.card G - M.index := by
  classical
  let O : Set (Subgroup G) :=
    MulAction.orbit (ConjAct G) M
  have hOfinite : Set.Finite O :=
    Set.toFinite O
  have hpieceFinite :
      ∀ H ∈ O, Set.Finite ((H : Set G) \ {1}) := by
    intro H _
    exact Set.toFinite _
  have hdisjoint :
      O.PairwiseDisjoint (fun H : Subgroup G ↦ (H : Set G) \ {1}) := by
    intro H hHO K hKO hHK
    change Disjoint ((H : Set G) \ {1}) ((K : Set G) \ {1})
    rw [Set.disjoint_left]
    intro x hxH hxK
    have hxinf : x ∈ H ⊓ K :=
      ⟨hxH.1, hxK.1⟩
    rw [hinter H hHO K hKO hHK] at hxinf
    exact hxH.2 (by simpa using hxinf)
  have hcard :
      ∀ H ∈ O, Nat.card H = Nat.card M := by
    intro H hHO
    obtain ⟨g, rfl⟩ :=
      MulAction.mem_orbit_iff.mp hHO
    exact Nat.card_congr (Subgroup.equivSMul g M).toEquiv |>.symm
  change (⋃ H ∈ O, ((H : Set G) \ {1})).ncard =
    Nat.card G - M.index
  rw [Set.Finite.ncard_biUnion hOfinite hpieceFinite hdisjoint]
  calc
    ∑ᶠ H ∈ O, ((H : Set G) \ {1}).ncard =
        ∑ᶠ _H ∈ O, (Nat.card M - 1) := by
      apply finsum_mem_congr rfl
      intro H hHO
      rw [ncard_coe_diff, hcard H hHO]
    _ = Nat.card G - M.index := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hOfinite,
        Finset.sum_const, nsmul_eq_mul,
        ← Set.ncard_eq_toFinset_card O hOfinite,
        ncard_act_self M hnormalizer,
        Nat.mul_sub_one, Nat.cast_id, mul_comm M.index (Nat.card M),
        M.card_mul_index]

/-- A finite minimal nonnilpotent group is not simple. This is the
nonsimplicity step in Schmidt's theorem. -/
lemma Group.IMNonnil.not_simple_group
    [Finite G] (hG : Group.IMNonnil G) :
    ¬ IsSimpleGroup G := by
  intro hsimple
  letI : IsSimpleGroup G :=
    hsimple
  obtain ⟨M, hM, hMnormal⟩ :=
    coatom_not_nilpotent (G := G) hG.1
  have hnormalizerM :
      Subgroup.normalizer (M : Set G) = M :=
    IsCoatom.normalizer_eqself_notnormal hM hMnormal
  have hinterM :
      ∀ H ∈ MulAction.orbit (ConjAct G) M,
        ∀ K ∈ MulAction.orbit (ConjAct G) M,
          H ≠ K → H ⊓ K = ⊥ := by
    intro H hHO K hKO hHK
    exact hG.inf_eqbot_coatomne
      (IsCoatom.mem_orbit_conjact hM hHO)
      (IsCoatom.mem_orbit_conjact hM hKO) hHK
  let UM : Set G :=
    ⋃ H ∈ MulAction.orbit (ConjAct G) M, ((H : Set G) \ {1})
  have hUMcard :
      UM.ncard = Nat.card G - M.index := by
    exact ncard_act_diff
      M hnormalizerM hinterM
  let W : Set G :=
    Set.univ \ {1}
  have hWcard :
      W.ncard = Nat.card G - 1 := by
    change (Set.univ \ {1} : Set G).ncard = Nat.card G - 1
    rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ 1),
      Set.ncard_univ]
  have hMindex :
      1 < M.index :=
    Subgroup.one_lt_index_of_ne_top hM.ne_top
  have hMindexLe :
      M.index ≤ Nat.card G :=
    Nat.le_of_dvd Nat.card_pos M.index_dvd_card
  have hUMltW :
      UM.ncard < W.ncard := by
    rw [hUMcard, hWcard]
    omega
  obtain ⟨x, hxW, hxUM⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hUMltW
  have hxne : x ≠ 1 := by
    simpa [W] using hxW
  have hzpowers :
      Subgroup.zpowers x ≠ (⊤ : Subgroup G) := by
    intro htop
    apply hG.1
    letI : IsCyclic G :=
      isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, htop⟩
    letI : CommGroup G :=
      IsCyclic.commGroup
    exact CommGroup.isNilpotent
  obtain ⟨K, hK, hzpowersK⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.zpowers x)).resolve_left hzpowers
  have hxK : x ∈ K :=
    hzpowersK (Subgroup.mem_zpowers x)
  have hKnotOrbit :
      K ∉ MulAction.orbit (ConjAct G) M := by
    intro hKO
    apply hxUM
    exact Set.mem_iUnion₂.mpr
      ⟨K, hKO, hxK, by simpa using hxne⟩
  have hKnormal : ¬ K.Normal := by
    intro hnormal
    have hKbot :
        K = (⊥ : Subgroup G) :=
      hnormal.eq_bot_or_eq_top.resolve_right hK.ne_top
    have hxone : x = 1 := by
      rw [hKbot] at hxK
      simpa using hxK
    exact hxne hxone
  have hnormalizerK :
      Subgroup.normalizer (K : Set G) = K :=
    IsCoatom.normalizer_eqself_notnormal hK hKnormal
  have hinterK :
      ∀ H ∈ MulAction.orbit (ConjAct G) K,
        ∀ L ∈ MulAction.orbit (ConjAct G) K,
          H ≠ L → H ⊓ L = ⊥ := by
    intro H hHO L hLO hHL
    exact hG.inf_eqbot_coatomne
      (IsCoatom.mem_orbit_conjact hK hHO)
      (IsCoatom.mem_orbit_conjact hK hLO) hHL
  let UK : Set G :=
    ⋃ H ∈ MulAction.orbit (ConjAct G) K, ((H : Set G) \ {1})
  have hUKcard :
      UK.ncard = Nat.card G - K.index := by
    exact ncard_act_diff
      K hnormalizerK hinterK
  have hUMUKdisjoint :
      Disjoint UM UK := by
    rw [Set.disjoint_left]
    intro y hyUM hyUK
    obtain ⟨H, hHO, hyH⟩ :=
      Set.mem_iUnion₂.mp hyUM
    obtain ⟨L, hLO, hyL⟩ :=
      Set.mem_iUnion₂.mp hyUK
    have hHL : H ≠ L := by
      intro hHL
      apply hKnotOrbit
      obtain ⟨g, hg⟩ :=
        MulAction.mem_orbit_iff.mp
          (MulAction.mem_orbit_symm.mp hLO)
      exact hg ▸ MulAction.mem_orbit_of_mem_orbit g (hHL ▸ hHO)
    have hyinf : y ∈ H ⊓ L :=
      ⟨hyH.1, hyL.1⟩
    rw [hG.inf_eqbot_coatomne
      (IsCoatom.mem_orbit_conjact hM hHO)
      (IsCoatom.mem_orbit_conjact hK hLO) hHL] at hyinf
    exact hyH.2 (by simpa using hyinf)
  have hunionSubset :
      UM ∪ UK ⊆ W := by
    rintro y (hyUM | hyUK)
    · obtain ⟨H, _, hyH⟩ :=
        Set.mem_iUnion₂.mp hyUM
      exact ⟨Set.mem_univ y, hyH.2⟩
    · obtain ⟨H, _, hyH⟩ :=
        Set.mem_iUnion₂.mp hyUK
      exact ⟨Set.mem_univ y, hyH.2⟩
  have hcardUnion :
      UM.ncard + UK.ncard ≤ W.ncard := by
    rw [← Set.ncard_union_eq hUMUKdisjoint]
    exact Set.ncard_le_ncard hunionSubset
  have hMnebot :
      M ≠ (⊥ : Subgroup G) := by
    intro hMbot
    apply hMnormal
    rw [hMbot]
    infer_instance
  have hKnebot :
      K ≠ (⊥ : Subgroup G) := by
    intro hKbot
    rw [hKbot] at hxK
    exact hxne (by simpa using hxK)
  have hMindexBound :
      2 * M.index ≤ Nat.card G := by
    calc
      2 * M.index ≤ Nat.card M * M.index := by
        exact Nat.mul_le_mul_right M.index
          ((Subgroup.one_lt_card_iff_ne_bot M).mpr hMnebot)
      _ = Nat.card G :=
        M.card_mul_index
  have hKindexBound :
      2 * K.index ≤ Nat.card G := by
    calc
      2 * K.index ≤ Nat.card K * K.index := by
        exact Nat.mul_le_mul_right K.index
          ((Subgroup.one_lt_card_iff_ne_bot K).mpr hKnebot)
      _ = Nat.card G :=
        K.card_mul_index
  rw [hUMcard, hUKcard, hWcard] at hcardUnion
  omega

/-- A quotient of a minimal nonnilpotent group is either nilpotent or
again minimal nonnilpotent. -/
lemma Group.IMNonnil.quot_nilpo_minno
    (hG : Group.IMNonnil G) (N : Subgroup G) [N.Normal] :
    Group.IsNilpotent (G ⧸ N) ∨
      Group.IMNonnil (G ⧸ N) := by
  by_cases hnil : Group.IsNilpotent (G ⧸ N)
  · exact Or.inl hnil
  · refine Or.inr ⟨hnil, ?_⟩
    intro H hH
    let q : G →* G ⧸ N :=
      QuotientGroup.mk' N
    have hqsurjective : Function.Surjective q :=
      QuotientGroup.mk'_surjective N
    have hcomap :
        H.comap q < (⊤ : Subgroup G) := by
      rw [← Subgroup.comap_top q]
      exact (Subgroup.comap_lt_comap_of_surjective hqsurjective).mpr hH
    have hnilcomap :
        Group.IsNilpotent (H.comap q) :=
      hG.2 (H.comap q) hcomap
    letI : Group.IsNilpotent (H.comap q) :=
      hnilcomap
    have hnilmap :
        Group.IsNilpotent ((H.comap q).map q) :=
      Group.nilpotent_of_surjective
        (q.subgroupMap (H.comap q))
        (q.subgroupMap_surjective (H.comap q))
    rwa [Subgroup.map_comap_eq_self_of_surjective hqsurjective H] at hnilmap

/-- A finite minimal nonnilpotent group has a nontrivial proper normal
subgroup. -/
lemma Group.IMNonnil.exists_nontr_prope
    [Finite G] (hG : Group.IMNonnil G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  letI : Nontrivial G := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsubsingleton
    apply hG.1
    letI : Subsingleton G :=
      hsubsingleton
    infer_instance
  have hnotsimple :
      ¬ IsSimpleGroup G :=
    hG.not_simple_group
  by_contra h
  push Not at h
  apply hnotsimple
  apply IsSimpleGroup.mk
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · exact Or.inr (h N hN hNbot)

/-- Auxiliary induction statement for Schmidt's theorem. -/
lemma solvable_minimal_nonnilpotent
    (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G],
      Nat.card G = n →
        Group.IMNonnil G →
          IsSolvable G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G hgroup hfinite hcard hG
      obtain ⟨N, hNnormal, hNnebot, hNnetop⟩ :=
        hG.exists_nontr_prope
      letI : N.Normal :=
        hNnormal
      have hNnilpotent :
          Group.IsNilpotent N :=
        hG.2 N (lt_top_iff_ne_top.mpr hNnetop)
      have hquotientCard :
          Nat.card (G ⧸ N) < n := by
        rw [← hcard,
          Subgroup.card_eq_card_quotient_mul_card_subgroup N]
        exact lt_mul_of_one_lt_right Nat.card_pos
          ((Subgroup.one_lt_card_iff_ne_bot N).mpr hNnebot)
      have hquotientSolvable :
          IsSolvable (G ⧸ N) := by
        rcases hG.quot_nilpo_minno N with
          hquotientNilpotent | hquotientMinimal
        · letI : Group.IsNilpotent (G ⧸ N) :=
            hquotientNilpotent
          infer_instance
        · exact ih (Nat.card (G ⧸ N)) hquotientCard
            (G ⧸ N) rfl hquotientMinimal
      letI : Group.IsNilpotent N :=
        hNnilpotent
      letI : IsSolvable (G ⧸ N) :=
        hquotientSolvable
      apply solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      rw [QuotientGroup.ker_mk', N.range_subtype]

/-- **Schmidt's theorem.** A finite minimal nonnilpotent group is
solvable. -/
theorem Group.IMNonnil.isSolvable
    [Finite G] (hG : Group.IMNonnil G) :
    IsSolvable G :=
  solvable_minimal_nonnilpotent
    (Nat.card G) G rfl hG

/-- A solvable group is locally solvable. -/
lemma Group.locally_solvable_solvable
    (hG : IsSolvable G) :
    Group.IsLocallySolvable G := by
  intro H _
  letI : IsSolvable G :=
    hG
  infer_instance

/-- Minimal normal subgroups of finite minimal nonnilpotent groups are
abelian. -/
lemma Group.IMNonnil.mul_comm_minnormal
    [Finite G] (hG : Group.IMNonnil G)
    {A : Subgroup G} (hA : IMNormal A) :
    IsMulCommutative A := by
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (minimal_locally_solvable
        (Group.locally_solvable_solvable
          (Group.IMNonnil.isSolvable hG))
        hA))

/-- Chief factors of finite minimal nonnilpotent groups are abelian. -/
lemma Group.IMNonnil.mulcom_mapqu_propn
    [Finite G] (hG : Group.IMNonnil G)
    {N K : Subgroup G} [N.Normal]
    (hN : MPBelow N K) (hKnormal : K.Normal) :
    IsMulCommutative (K.map (QuotientGroup.mk' N)) := by
  have hquotientSolvable : IsSolvable (G ⧸ N) := by
    letI : IsSolvable G :=
      Group.IMNonnil.isSolvable hG
    infer_instance
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (minimal_locally_solvable
        (Group.locally_solvable_solvable hquotientSolvable)
        (hN.map_quot_minnormal hKnormal)))

/-- Every proper subgroup of a minimal nonnilpotent subgroup is
nilpotent. -/
lemma MNSubgro.nilpotent_lt
    {H K : Subgroup G} (hH : MNSubgro H)
    (hKH : K < H) :
    Group.IsNilpotent K := by
  by_contra hK
  exact hKH.ne (hH.2 K hKH.le hK)

/-- A subgroup minimal among the nonnilpotent ambient subgroups is
intrinsically a minimal nonnilpotent group. -/
lemma MNSubgro.to_group
    {H : Subgroup G} (hH : MNSubgro H) :
    Group.IMNonnil H := by
  refine ⟨hH.1, ?_⟩
  intro K hK
  have hmaplt : K.map H.subtype < H := by
    calc
      K.map H.subtype < (⊤ : Subgroup H).map H.subtype :=
        Subgroup.map_subtype_lt_map_subtype.mpr hK
      _ = H := by
        rw [← MonoidHom.range_eq_map, H.range_subtype]
  have hnil : Group.IsNilpotent (K.map H.subtype) :=
    hH.nilpotent_lt hmaplt
  letI : Group.IsNilpotent (K.map H.subtype) := hnil
  exact Group.nilpotent_of_mulEquiv
    (K.equivMapOfInjective H.subtype H.subtype_injective).symm

/-- Every finite nonnilpotent group contains a subgroup minimal among its
nonnilpotent subgroups. -/
lemma minimal_nonnilpotent_subgroup
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ H : Subgroup G, MNSubgro H := by
  classical
  let S : Set (Subgroup G) := {H | ¬ Group.IsNilpotent H}
  have hSne : S.Nonempty := by
    refine ⟨⊤, ?_⟩
    intro htop
    apply hnil
    letI : Group.IsNilpotent (⊤ : Subgroup G) := htop
    exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv
  obtain ⟨H, hHS, hHminimal⟩ := (Set.toFinite S).exists_minimal hSne
  refine ⟨H, hHS, ?_⟩
  intro K hKH hK
  exact le_antisymm hKH (hHminimal hK hKH)

/-- To prove Hall's finite Petresco separator theorem, it suffices to
prove it for subgroups minimal among finite nonnilpotent groups. -/
theorem separator_minimal_nonnilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G)
    (hminimal :
      ∀ H : Subgroup G, MNSubgro H →
        TPSepara H) :
    TPSepara G := by
  obtain ⟨H, hH⟩ :=
    minimal_nonnilpotent_subgroup (G := G) hnil
  exact (hminimal H hH).of_subgroup H

/-- A finite nonnilpotent group has a Sylow subgroup which is not
normal. -/
lemma sylow_not_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G),
      ¬ (P : Subgroup G).Normal := by
  classical
  by_contra h
  push Not at h
  apply hnil
  exact ((Group.isNilpotent_of_finite_tfae (G := G)).out 3 0).mp h

/-- A finite minimal nonnilpotent group has a nonnormal Sylow subgroup
whose normalizer is a proper nilpotent subgroup. -/
lemma sylow_minimal_nonnilpotent
    [Finite G] (hG : Group.IMNonnil G) :
    ∃ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G),
      ¬ (P : Subgroup G).Normal ∧
        Group.IsNilpotent
          (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  obtain ⟨p, hp, P, hP⟩ :=
    sylow_not_nilpotent (G := G) hG.1
  refine ⟨p, hp, P, hP, hG.2 _ ?_⟩
  exact lt_top_iff_ne_top.mpr (mt Subgroup.normalizer_eq_top_iff.mp hP)

/-- A finite minimal nonnilpotent group has a proper nilpotent
self-normalizing subgroup. -/
lemma normalizer_minimal_nonnilpotent
    [Finite G] (hG : Group.IMNonnil G) :
    ∃ H : Subgroup G,
      H < ⊤ ∧ Group.IsNilpotent H ∧
        Subgroup.normalizer (H : Set G) = H := by
  obtain ⟨p, hp, P, hPnormal, hPnormalizerNilpotent⟩ :=
    sylow_minimal_nonnilpotent
      (G := G) hG
  letI : Fact p.Prime := hp
  refine
    ⟨Subgroup.normalizer ((P : Subgroup G) : Set G),
      lt_top_iff_ne_top.mpr (mt Subgroup.normalizer_eq_top_iff.mp hPnormal),
      hPnormalizerNilpotent, ?_⟩
  exact Sylow.normalizer_normalizer P

/-- The ordered tail `τ_2(x, y)^(w choose 2) ⋯ τ_w(x, y)`. -/
def petrescoTailProduct (tau : ℕ → G) (w : ℕ) : G :=
  ((((List.range w).drop 1).map fun j =>
    tau (j + 1) ^ Nat.choose w (j + 1))).prod

/-- Split Hall's binomial product into its `τ_1` factor and the tail. -/
lemma petresco_binomial_tail (tau : ℕ → G) (w : ℕ) :
    petrescoBinomialProduct tau w =
      tau 1 ^ w * petrescoTailProduct tau w := by
  rw [petresco_prod_range]
  cases w with
  | zero =>
      simp [petrescoTailProduct]
  | succ w =>
      simp [petrescoTailProduct, List.range_succ_eq_map,
        Nat.choose_one_right]

/-- For two generators, Hall's recurrence begins with
`x^w y^w = (xy)^w τ_2(x, y)^(w choose 2) ⋯ τ_w(x, y)`. -/
lemma IPFam.twoGenerators
    {x y : G} {tau : ℕ → G} (h : IPFam [x, y] tau) (w : ℕ) :
    x ^ w * y ^ w = (x * y) ^ w * petrescoTailProduct tau w := by
  have hfirst : tau 1 = x * y := by
    simpa using h.first
  have hw := h w
  rw [petresco_binomial_tail, hfirst] at hw
  simpa using hw

/-- Word-valued form of the two-generator Petresco recurrence. -/
lemma petresco_values_generators
    {tau : ℕ → FreeGroup Bool} {x y : G}
    (h : IPFam [x, y] (petrescoWordValues tau x y)) (w : ℕ) :
    x ^ w * y ^ w =
      (x * y) ^ w * petrescoTailProduct (petrescoWordValues tau x y) w :=
  h.twoGenerators w

/-- **Hall-Petresco, two-generator form.**
`x^w y^w = (xy)^w τ_2(x, y)^(w choose 2) ⋯ τ_w(x, y)`. -/
theorem petresco_two_generators (x y : G) (w : ℕ) :
    x ^ w * y ^ w =
      (x * y) ^ w * petrescoTailProduct (twoPetrescoValues x y) w := by
  have h :
      IPFam [x, y] (twoPetrescoValues x y) := by
    simpa [twoPetrescoValues, twoPetrescoValue,
      twoGeneratorPetresco, petrescoWordValue, twoGeneratorAssignment]
      using petresco_word_family [false, true]
        (twoGeneratorAssignment x y)
  exact h.twoGenerators w

/-- A generic two-generator word value lies in `γ_k` when supplied with
a formal factorization into commutators of weight at least `k`. -/
theorem petresco_formal_factorization
    (tau : ℕ → FreeGroup Bool) (k : ℕ)
    (hfactor :
      ∀ f : Bool → G, ∃ l : List (FormalCommutator Bool),
        (∀ c ∈ l, k ≤ formalWeight c) ∧
          wordEval (tau k) f =
            (l.map (formalGroupCommutator f)).prod)
    (x y : G) :
    petrescoWordValue tau k x y ∈ Subgroup.lowerCentralSeries G (k - 1) := by
  apply verbal_formal_factorization
    (G := G) (tau k) k hfactor
  exact Subgroup.subset_closure ⟨twoGeneratorAssignment x y, rfl⟩

/-- The actual recursively defined two-generator Petresco value lies in
Hall's one-based lower-central term `γ_k`. -/
theorem petresco_value_series
    (k : ℕ) (x y : G) :
    twoPetrescoValue k x y ∈
      Subgroup.lowerCentralSeries G (k - 1) := by
  simpa [twoPetrescoValue, twoGeneratorPetresco,
    petrescoWordValue, word_eval_petresco, twoGeneratorAssignment] using
    (petresco_lower_series [x, y] k)

/-- On an abelian normal subgroup, commutation on the right by `x` is a
group endomorphism. -/
noncomputable def hallDifferenceHom
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) :
    A →* A :=
  (invMonoidHom : A →* A) *
    (MulAut.conjNormal x⁻¹).toMonoidHom

@[simp]
lemma coe_difference_hom
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A) :
    (hallDifferenceHom A x a : G) = hallCommutator (a : G) x := by
  simp [hallDifferenceHom, hallCommutator, mul_assoc]

/-- The kernel of the Hall difference endomorphism consists exactly of
the elements commuting with the acting element. -/
lemma hall_difference_commute
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A) :
    hallDifferenceHom A x a = 1 ↔ Commute (a : G) x := by
  constructor
  · intro h
    apply (hall_commutator_commute (a : G) x).mp
    rw [← coe_difference_hom]
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    change (hallDifferenceHom A x a : G) = 1
    rw [coe_difference_hom]
    exact (hall_commutator_commute (a : G) x).mpr h

/-- Fixed-point-free conjugation on an abelian normal subgroup makes the
Hall difference endomorphism injective. -/
lemma difference_injective_commute
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G)
    (hfixed : ∀ a : A, Commute (a : G) x → a = 1) :
    Function.Injective (hallDifferenceHom A x) := by
  intro a b hab
  have hker : hallDifferenceHom A x (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  exact mul_inv_eq_one.mp
    (hfixed (a * b⁻¹)
      ((hall_difference_commute A x (a * b⁻¹)).mp hker))

/-- A trivial intersection with the centralizer of `x` makes the Hall
difference endomorphism injective. -/
lemma inf_centralizer_bot
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G)
    (hcentralizer : A ⊓ Subgroup.centralizer {x} = ⊥) :
    Function.Injective (hallDifferenceHom A x) := by
  apply difference_injective_commute A x
  intro a ha
  apply Subtype.ext
  apply Subgroup.mem_bot.mp
  rw [← hcentralizer]
  exact ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr ha.eq⟩

/-- If an abelian minimal normal subgroup together with `x` generates
the ambient group and `x` acts nontrivially, then `x` has no nontrivial
fixed point in that subgroup. -/
lemma IMNormal.infcentsing_eqbotsup_zpowerseqtop
    {A : Subgroup G} (hA : IMNormal A) [IsMulCommutative A]
    (x : G) (hgenerate : A ⊔ Subgroup.zpowers x = ⊤)
    (hncentral : ¬ A ≤ Subgroup.centralizer {x}) :
    A ⊓ Subgroup.centralizer {x} = ⊥ := by
  let C : Subgroup G := A ⊓ Subgroup.centralizer {x}
  letI : A.Normal := hA.1
  letI : (C.subgroupOf A).Normal := by
    infer_instance
  have hAnormalizes : A ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf inf_le_left
  have hxnormalizes : x ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      have hcomm :
          c * x = x * c :=
        Subgroup.mem_centralizer_singleton_iff.mp hc.2
      have hconj : x * c * x⁻¹ = c := by
        calc
          x * c * x⁻¹ = c * x * x⁻¹ := by rw [← hcomm]
          _ = c := by group
      rwa [hconj]
    · intro hconjmem
      have hcomm :
          (x * c * x⁻¹) * x = x * (x * c * x⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp hconjmem.2
      have hconj : c = x * c * x⁻¹ := by
        apply mul_left_cancel (a := x)
        calc
          x * c = (x * c * x⁻¹) * x := by group
          _ = x * (x * c * x⁻¹) := hcomm
      rwa [hconj]
  have hCnormal : C.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgenerate]
    exact sup_le hAnormalizes (Subgroup.zpowers_le_of_mem hxnormalizes)
  by_contra hCne
  have hCA : C = A :=
    hA.2.2 C hCnormal inf_le_left hCne
  apply hncentral
  intro a ha
  have haC : a ∈ C := by
    rw [hCA]
    exact ha
  exact haC.2

/-- If an abelian minimal normal subgroup and an acting subgroup generate
the ambient group, and the action of `x` is central modulo the kernel of
the acting subgroup's action, then a nontrivial action by `x` is
fixed-point-free. -/
lemma IMNormal.infcen_eqbot_topco
    {A B : Subgroup G} (hA : IMNormal A) [IsMulCommutative A]
    (x : G) (hgenerate : A ⊔ B = ⊤)
    (hcomm :
      ∀ b ∈ B,
        x * b * x⁻¹ * b⁻¹ ∈ Subgroup.centralizer (A : Set G))
    (hncentral : ¬ A ≤ Subgroup.centralizer {x}) :
    A ⊓ Subgroup.centralizer {x} = ⊥ := by
  let C : Subgroup G :=
    A ⊓ Subgroup.centralizer {x}
  letI : A.Normal :=
    hA.1
  letI : (C.subgroupOf A).Normal := by
    infer_instance
  have hAnormalizes :
      A ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf inf_le_left
  have hconj_mem :
      ∀ b ∈ B, ∀ c ∈ C, b * (c : G) * b⁻¹ ∈ C := by
    intro b hb c hc
    have hconjA :
        b * (c : G) * b⁻¹ ∈ A :=
      hA.1.conj_mem c hc.1 b
    have hdcentral :
        x * b * x⁻¹ * b⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
      hcomm b hb
    have hdcomm :
        (b * (c : G) * b⁻¹) * (x * b * x⁻¹ * b⁻¹) =
          (x * b * x⁻¹ * b⁻¹) * (b * (c : G) * b⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hdcentral
        (b * (c : G) * b⁻¹) hconjA
    have hccomm :
        (c : G) * x = x * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hconjfixed :
        x * (b * (c : G) * b⁻¹) * x⁻¹ =
          b * (c : G) * b⁻¹ := by
      calc
        x * (b * (c : G) * b⁻¹) * x⁻¹ =
            (x * b * x⁻¹ * b⁻¹) *
              (b * (x * (c : G) * x⁻¹) * b⁻¹) *
                (x * b * x⁻¹ * b⁻¹)⁻¹ := by
                  group
        _ = (x * b * x⁻¹ * b⁻¹) *
              (b * (c : G) * b⁻¹) *
                (x * b * x⁻¹ * b⁻¹)⁻¹ := by
                  rw [show x * (c : G) * x⁻¹ = (c : G) by
                    calc
                      x * (c : G) * x⁻¹ = (c : G) * x * x⁻¹ := by
                        rw [← hccomm]
                      _ = (c : G) := by group]
        _ = b * (c : G) * b⁻¹ := by
          rw [← hdcomm]
          group
    refine ⟨hconjA, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (calc
        (b * (c : G) * b⁻¹) * x =
            (x * (b * (c : G) * b⁻¹) * x⁻¹) * x := by
              rw [hconjfixed]
        _ = x * (b * (c : G) * b⁻¹) := by
          group)
  have hBnormalizes :
      B ≤ Subgroup.normalizer (C : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hconj_mem b hb c
    · intro hc
      have hinv :=
        hconj_mem b⁻¹ (B.inv_mem hb)
          (b * c * b⁻¹) hc
      convert hinv using 1
      all_goals group
  have hCnormal : C.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgenerate]
    exact sup_le hAnormalizes hBnormalizes
  by_contra hCne
  have hCA : C = A :=
    hA.2.2 C hCnormal inf_le_left hCne
  apply hncentral
  intro a ha
  have haC : a ∈ C := by
    rw [hCA]
    exact ha
  exact haC.2

/-- Iterating the difference endomorphism gives Hall's iterated
right-commutator sequence. -/
lemma coe_difference_iterate
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A) :
    ∀ n : ℕ,
      ((hallDifferenceHom A x)^[n] a : G) =
        iteratedCommutatorRight (a : G) x n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', coe_difference_hom, ih]
      rfl

/-- The binomial product attached to the iterates of an endomorphism of
a commutative group. -/
def endomorphismBinomialProduct
    {A : Type*} [CommGroup A] (d : A →* A) (a : A) (w : ℕ) : A :=
  ∏ j ∈ Finset.range w, (d^[j] a) ^ Nat.choose w (j + 1)

/-- The binomial product satisfies the Pascal recurrence. -/
lemma endomorphism_binomial_succ
    {A : Type*} [CommGroup A] (d : A →* A) (a : A) (w : ℕ) :
    endomorphismBinomialProduct d a (w + 1) =
      endomorphismBinomialProduct d a w *
        (a * d (endomorphismBinomialProduct d a w)) := by
  simp only [endomorphismBinomialProduct, Finset.prod_range_succ,
    Nat.choose_self, pow_one, Nat.choose_succ_succ', pow_add,
    Finset.prod_mul_distrib, map_prod, map_pow, Nat.choose_succ_self,
    pow_zero, mul_one]
  have hshift :
      (∏ j ∈ Finset.range w, d^[j] a ^ Nat.choose w j) * d^[w] a =
        a * ∏ j ∈ Finset.range w,
          d (d^[j] a) ^ Nat.choose w (j + 1) := by
    calc
      (∏ j ∈ Finset.range w, d^[j] a ^ Nat.choose w j) * d^[w] a =
          (∏ j ∈ Finset.range w, d^[j] a ^ Nat.choose w j) *
            d^[w] a ^ Nat.choose w w := by simp
      _ = ∏ j ∈ Finset.range (w + 1), d^[j] a ^ Nat.choose w j := by
        rw [Finset.prod_range_succ]
      _ = a * ∏ j ∈ Finset.range w,
          d (d^[j] a) ^ Nat.choose w (j + 1) := by
        rw [Finset.prod_range_succ']
        simp only [Function.iterate_zero_apply, Nat.choose_zero_right, pow_one,
          Function.iterate_succ_apply']
        exact mul_comm _ _
  rw [hshift]
  exact mul_comm _ _

/-- The binomial product is the ordered product of the orbit of `a`
under the endomorphism `id * d`. -/
lemma endomorphism_binomial_orbit
    {A : Type*} [CommGroup A] (d : A →* A) (a : A) :
    ∀ w : ℕ,
      endomorphismBinomialProduct d a w =
        ∏ j ∈ Finset.range w, ((MonoidHom.id A * d)^[j] a) := by
  intro w
  have horbit :
      ∀ n : ℕ,
        (MonoidHom.id A * d)^[n] a =
          a * d (endomorphismBinomialProduct d a n) := by
    intro n
    induction n with
    | zero =>
        simp [endomorphismBinomialProduct]
    | succ n ih =>
        rw [Function.iterate_succ_apply', MonoidHom.mul_apply, MonoidHom.id_apply,
          ih, map_mul, endomorphism_binomial_succ]
        simp only [map_mul]
        rw [mul_assoc]
  induction w with
  | zero =>
      simp [endomorphismBinomialProduct]
  | succ w ih =>
      rw [endomorphism_binomial_succ, Finset.prod_range_succ, ← ih,
        horbit]

/-- The Hall difference family begins with `1`, then `a`, then the
successive commutators of `a` on the right by `x`. -/
noncomputable def hallDifferenceFamily
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A) :
    ℕ → A
  | 0 => 1
  | n + 1 => (hallDifferenceHom A x)^[n] a

@[simp]
lemma difference_family_zero
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A) :
    hallDifferenceFamily A x a 0 = 1 :=
  rfl

@[simp]
lemma difference_family_succ
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A)
    (n : ℕ) :
    hallDifferenceFamily A x a (n + 1) =
      (hallDifferenceHom A x)^[n] a :=
  rfl

/-- Conjugation by `x⁻¹` on an abelian normal subgroup is `id` times
the Hall difference endomorphism. -/
lemma monoid_id_difference
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) :
    (MulAut.conjNormal x⁻¹ : MulAut A).toMonoidHom =
      MonoidHom.id A * hallDifferenceHom A x := by
  ext a
  simp [hallDifferenceHom, mul_assoc]

/-- Iterated conjugation by `x⁻¹` has the expected ambient value. -/
lemma coe_inv_iterate
    (A : Subgroup G) [A.Normal] (x : G) (a : A) :
    ∀ n : ℕ,
      ((((MulAut.conjNormal x⁻¹ : MulAut A).toMonoidHom : A → A)^[n] a : A) : G) =
        (x ^ n)⁻¹ * (a : G) * x ^ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change
        (↑((MulAut.conjNormal x⁻¹ : MulAut A)
          (((MulAut.conjNormal x⁻¹ : MulAut A).toMonoidHom : A → A)^[n] a)) : G) =
            (x ^ (n + 1))⁻¹ * (a : G) * x ^ (n + 1)
      rw [MulAut.conjNormal_apply, ih]
      simp [pow_succ, mul_assoc]

/-- The product `(a x⁻¹)^w x^w` is the product of the conjugation orbit
of `a`. -/
lemma inv_normal_iterate
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A) :
    ∀ w : ℕ,
      ((a : G) * x⁻¹) ^ w * x ^ w =
        ((∏ j ∈ Finset.range w,
          ((MulAut.conjNormal x⁻¹ : MulAut A).toMonoidHom : A → A)^[j] a : A) : G) := by
  intro w
  induction w with
  | zero =>
      simp
  | succ w ih =>
      rw [pow_succ, pow_succ, Finset.prod_range_succ, Subgroup.coe_mul,
        coe_inv_iterate A x a w, ← ih]
      group

/-- Products over `Finset.range` agree with ordered products over
`List.range` in a commutative monoid. -/
lemma finset_range_list
    {A : Type*} [CommMonoid A] (f : ℕ → A) :
    ∀ w : ℕ,
      (∏ j ∈ Finset.range w, f j) = ((List.range w).map f).prod := by
  intro w
  induction w with
  | zero =>
      simp
  | succ w ih =>
      rw [Finset.prod_range_succ, List.range_succ, List.map_append,
        List.prod_append, ih]
      simp

/-- The Hall difference family is the Petresco family of the pair
`(a x⁻¹, x)` whenever `a` belongs to an abelian normal subgroup. -/
theorem difference_family_petresco
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A) :
    IPFam [(a : G) * x⁻¹, x]
      (fun n => (hallDifferenceFamily A x a n : G)) := by
  intro w
  rw [show ([(a : G) * x⁻¹, x].map fun g => g ^ w).prod =
      ((a : G) * x⁻¹) ^ w * x ^ w by simp]
  rw [inv_normal_iterate A x a]
  rw [monoid_id_difference]
  rw [← endomorphism_binomial_orbit (hallDifferenceHom A x) a w]
  rw [petresco_prod_range]
  rw [endomorphismBinomialProduct,
    finset_range_list]
  simp only [difference_family_succ]
  rw [Subgroup.val_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _hj
  rfl

/-- For the pair `(a x⁻¹, x)`, the canonical Petresco values are exactly
the iterated right commutators of `a` by `x`. -/
theorem petresco_inv_iterated
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A)
    (n : ℕ) :
    twoPetrescoValue (n + 1) ((a : G) * x⁻¹) x =
      iteratedCommutatorRight (a : G) x n := by
  have hfamily := difference_family_petresco A x a
  have hcanonical :=
    hfamily.eq_petresco_termpos (n + 1) (Nat.succ_pos n)
  rw [difference_family_succ, coe_difference_iterate] at hcanonical
  simpa [twoPetrescoValue, twoGeneratorPetresco,
    petrescoWordValue, word_eval_petresco, twoGeneratorAssignment] using
    hcanonical.symm

/-- An injective difference endomorphism keeps every nonidentity element
away from the identity throughout its Hall-commutator orbit. -/
lemma iterated_difference_injective
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A)
    (hinjective : Function.Injective (hallDifferenceHom A x))
    (ha : (a : G) ≠ 1) :
    ∀ n : ℕ, iteratedCommutatorRight (a : G) x n ≠ 1 := by
  intro n hone
  have hsubtype :
      (hallDifferenceHom A x)^[n] a =
        (hallDifferenceHom A x)^[n] 1 := by
    apply Subtype.ext
    rw [coe_difference_iterate, hone]
    simp
  have hiterate :
      Function.Injective ((hallDifferenceHom A x)^[n]) :=
    hinjective.iterate n
  exact ha (congrArg Subtype.val (hiterate hsubtype))

/-- An injective Hall difference endomorphism on an abelian normal
subgroup supplies Hall's two-generator Petresco separator explicitly. -/
theorem petresco_separator_injective
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A)
    (hinjective : Function.Injective (hallDifferenceHom A x))
    (ha : (a : G) ≠ 1) :
    ∃ f : Bool → G,
      ∀ n : ℕ, 0 < n →
        wordEval (twoGeneratorPetresco n) f ≠ 1 := by
  refine ⟨twoGeneratorAssignment ((a : G) * x⁻¹) x, ?_⟩
  intro n hn
  cases n with
  | zero =>
      omega
  | succ n =>
      change twoPetrescoValue (n + 1) ((a : G) * x⁻¹) x ≠ 1
      rw [petresco_inv_iterated]
      exact
        iterated_difference_injective
          A x a hinjective ha n

/-- Predicate form of the explicit Hall-difference separator
construction. -/
theorem petresco_separator_difference
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A)
    (hinjective : Function.Injective (hallDifferenceHom A x))
    (ha : (a : G) ≠ 1) :
    TPSepara G := by
  refine ⟨(a : G) * x⁻¹, x, ?_⟩
  intro n hn
  cases n with
  | zero =>
      omega
  | succ n =>
      rw [petresco_inv_iterated]
      exact
        iterated_difference_injective
          A x a hinjective ha n

/-- Fixed-point-free conjugation on a nontrivial abelian normal subgroup
supplies a Petresco separator. -/
theorem two_separator_commute
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A)
    (hfixed : ∀ b : A, Commute (b : G) x → b = 1)
    (ha : (a : G) ≠ 1) :
    TPSepara G :=
  petresco_separator_difference
    A x a (difference_injective_commute A x hfixed) ha

/-- A nontrivial abelian normal subgroup meeting the centralizer of `x`
trivially supplies a Petresco separator. -/
theorem separator_inf_centralizer
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (x : G) (a : A)
    (hcentralizer : A ⊓ Subgroup.centralizer {x} = ⊥)
    (ha : (a : G) ≠ 1) :
    TPSepara G :=
  petresco_separator_difference
    A x a
      (inf_centralizer_bot A x hcentralizer)
      ha

/-- An abelian minimal normal subgroup and a cyclic actor generating the
ambient group supply a Petresco separator as soon as the action is
nontrivial. -/
theorem petresco_separator_zpowers
    (A : Subgroup G) [IsMulCommutative A] (hA : IMNormal A)
    (x : G) (a : A) (hgenerate : A ⊔ Subgroup.zpowers x = ⊤)
    (hncentral : ¬ A ≤ Subgroup.centralizer {x}) (ha : (a : G) ≠ 1) :
    TPSepara G := by
  letI : A.Normal := hA.1
  apply separator_inf_centralizer A x a
  · exact
      hA.infcentsing_eqbotsup_zpowerseqtop
        x hgenerate hncentral
  · exact ha

/-- A fixed-point-free abelian normal section in a quotient supplies a
Petresco separator in the original group. -/
theorem petresco_separator_commute
    (N : Subgroup G) [N.Normal]
    (A : Subgroup (G ⧸ N)) [A.Normal] [IsMulCommutative A]
    (x : G ⧸ N) (a : A)
    (hfixed : ∀ b : A, Commute (b : G ⧸ N) x → b = 1)
    (ha : (a : G ⧸ N) ≠ 1) :
    TPSepara G :=
  (two_separator_commute
    A x a hfixed ha).of_quotient N

/-- An abelian minimal normal section in a quotient and a cyclic actor
generating that quotient supply a Petresco separator in the source. -/
theorem
    separator_minimal_zpowers
    (N : Subgroup G) [N.Normal]
    (A : Subgroup (G ⧸ N)) [IsMulCommutative A] (hA : IMNormal A)
    (x : G ⧸ N) (a : A) (hgenerate : A ⊔ Subgroup.zpowers x = ⊤)
    (hncentral : ¬ A ≤ Subgroup.centralizer {x})
    (ha : (a : G ⧸ N) ≠ 1) :
    TPSepara G :=
  (petresco_separator_zpowers
    A hA x a hgenerate hncentral ha).of_quotient N

/-- For a finite abelian normal subgroup, a surjective Hall difference
endomorphism supplies a Petresco separator. -/
theorem petresco_separator_surjective
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] [Finite A]
    (x : G) (a : A) (hsurjective : Function.Surjective (hallDifferenceHom A x))
    (ha : (a : G) ≠ 1) :
    TPSepara G := by
  apply petresco_separator_difference
    A x a _ ha
  exact Finite.injective_iff_surjective.mpr hsurjective

/-- Range form of the finite Hall-difference separator construction. -/
theorem petresco_separator_top
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] [Finite A]
    (x : G) (a : A) (hrange : (hallDifferenceHom A x).range = ⊤)
    (ha : (a : G) ≠ 1) :
    TPSepara G := by
  apply petresco_separator_surjective
    A x a _ ha
  intro b
  have hb : b ∈ (hallDifferenceHom A x).range := by
    rw [hrange]
    exact Subgroup.mem_top b
  exact hb

/-- A finite minimal nonnilpotent group has a two-generator Petresco
separator. This is the finite Schmidt-group structure step used in
Hall's Theorem 6.4. -/
theorem Group.IMNonnil.two_gen_petrescseparat
    [Finite G] (hG : Group.IMNonnil G) :
    TPSepara G := by
  classical
  obtain ⟨M, hMcoatom, hMnotnormal⟩ :=
    coatom_not_nilpotent (G := G) hG.1
  let N : Subgroup G :=
    M.normalCore
  let q : G →* G ⧸ N :=
    QuotientGroup.mk' N
  let B : Subgroup (G ⧸ N) :=
    M.map q
  have hqsurjective :
      Function.Surjective q :=
    QuotientGroup.mk'_surjective N
  have hqker :
      q.ker = N :=
    QuotientGroup.ker_mk' N
  have hNM :
      N ≤ M :=
    M.normalCore_le
  have hBcoatom :
      IsCoatom B :=
    Subgroup.coatom_mapsurj_kerle
      q hqsurjective hMcoatom (hqker.trans_le hNM)
  have hcomapB :
      B.comap q = M := by
    exact Subgroup.comap_map_eq_self (hqker.trans_le hNM)
  have hBnotnormal :
      ¬ B.Normal := by
    intro hBnormal
    apply hMnotnormal
    rw [← hcomapB]
    exact hBnormal.comap q
  have hquotientNotNilpotent :
      ¬ Group.IsNilpotent (G ⧸ N) := by
    intro hnilpotent
    apply hBnotnormal
    letI : Group.IsNilpotent (G ⧸ N) :=
      hnilpotent
    exact Subgroup.NormalizerCondition.normal_of_coatom
      B (Group.normalizerCondition_of_isNilpotent (G := G ⧸ N)) hBcoatom
  have hquotientMinimal :
      Group.IMNonnil (G ⧸ N) :=
    (Group.IMNonnil.quot_nilpo_minno
      hG N).resolve_left hquotientNotNilpotent
  have hBcore :
      B.normalCore = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc
      B.normalCore =
          (B.normalCore.comap q).map q :=
        (Subgroup.map_comap_eq_self_of_surjective
          hqsurjective B.normalCore).symm
      _ = ⊥ := by
        have hcomapCoreLeM :
            B.normalCore.comap q ≤ M :=
          (Subgroup.comap_mono B.normalCore_le).trans_eq hcomapB
        exact
          (Subgroup.map_eq_bot_iff (B.normalCore.comap q)).mpr
            ((Subgroup.normal_le_normalCore.mpr hcomapCoreLeM).trans_eq
              hqker.symm)
      _ ≤ ⊥ := le_rfl
  letI : Nontrivial (G ⧸ N) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsubsingleton
    apply hquotientNotNilpotent
    letI : Subsingleton (G ⧸ N) :=
      hsubsingleton
    infer_instance
  obtain ⟨A, hAminimal⟩ :=
    exists_is_minimal (G := G ⧸ N)
  letI : A.Normal :=
    hAminimal.1
  letI : IsMulCommutative A :=
    Group.IMNonnil.mul_comm_minnormal
      hquotientMinimal hAminimal
  have hAnleB :
      ¬ A ≤ B := by
    intro hAB
    have hAcore :
        A ≤ B.normalCore :=
      Subgroup.normal_le_normalCore.mpr hAB
    apply hAminimal.2.1
    exact le_bot_iff.mp (hAcore.trans_eq hBcore)
  have hABtop :
      A ⊔ B = ⊤ := by
    apply hBcoatom.2
    refine lt_of_le_of_ne le_sup_right ?_
    intro hBA
    apply hAnleB
    rw [hBA]
    exact le_sup_left
  let C : Subgroup (G ⧸ N) :=
    B ⊓ Subgroup.centralizer (A : Set (G ⧸ N))
  have hCltB :
      C < B := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hCB
    have hBcentral :
        B ≤ Subgroup.centralizer (A : Set (G ⧸ N)) := by
      rw [← hCB]
      exact inf_le_right
    apply hBnotnormal
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hABtop]
    apply sup_le ?_ B.le_normalizer
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have hcomm :
          a * b = b * a :=
        Subgroup.mem_centralizer_iff.mp (hBcentral hb) a ha
      have hconj :
          a * b * a⁻¹ = b := by
        calc
          a * b * a⁻¹ = b * a * a⁻¹ := by
            rw [hcomm]
          _ = b := by
            group
      rwa [hconj]
    · intro hconjmem
      have hcomm :
          a * (a * b * a⁻¹) = (a * b * a⁻¹) * a :=
        Subgroup.mem_centralizer_iff.mp (hBcentral hconjmem) a ha
      have hbEq :
          b = a * b * a⁻¹ := by
        calc
          b = a⁻¹ * (a * b * a⁻¹) * a := by
            group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by
            group
          _ = a⁻¹ * (a * (a * b * a⁻¹)) := by
            rw [← hcomm]
          _ = a * b * a⁻¹ := by
            group
      rwa [hbEq]
  let CB : Subgroup B :=
    C.subgroupOf B
  letI : CB.Normal := by
    simpa [CB, C] using
      (inferInstance :
        ((Subgroup.centralizer (A : Set (G ⧸ N))).subgroupOf B).Normal)
  have hCBneTop :
      CB ≠ ⊤ := by
    intro hCBtop
    apply hCltB.2
    exact Subgroup.subgroupOf_eq_top.mp hCBtop
  have hBnilpotent :
      Group.IsNilpotent B :=
    hquotientMinimal.2 B hBcoatom.lt_top
  letI : Group.IsNilpotent B :=
    hBnilpotent
  letI : Nontrivial (B ⧸ CB) :=
    QuotientGroup.nontrivial_iff.mpr hCBneTop
  have hcenterNeBot :
      Subgroup.center (B ⧸ CB) ≠ ⊥ :=
    center_nontrivial_nilpotent
  obtain ⟨z, hzcenter, hzbot⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hcenterNeBot)
  have hzne :
      z ≠ 1 := by
    simpa using hzbot
  obtain ⟨xB, hxB⟩ :=
    QuotientGroup.mk'_surjective CB z
  have hxBnotC :
      (xB : G ⧸ N) ∉ C := by
    intro hxBC
    apply hzne
    rw [← hxB]
    exact (QuotientGroup.eq_one_iff xB).mpr hxBC
  have hxBstep :
      xB ∈ Subgroup.upperCentralSeriesStep CB := by
    rw [Subgroup.upperCentralSeriesStep_eq_comap_center]
    change QuotientGroup.mk' CB xB ∈ Subgroup.center (B ⧸ CB)
    rwa [hxB]
  let x : G ⧸ N :=
    xB
  have hxcomm :
      ∀ b ∈ B,
        x * b * x⁻¹ * b⁻¹ ∈
          Subgroup.centralizer (A : Set (G ⧸ N)) := by
    intro b hb
    have hx :=
      (Subgroup.mem_upperCentralSeriesStep CB xB).mp hxBstep ⟨b, hb⟩
    exact hx.2
  have hxncentral :
      ¬ A ≤ Subgroup.centralizer {x} := by
    intro hAcentral
    apply hxBnotC
    refine ⟨xB.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hAcentral ha)
  have hfixed :
      A ⊓ Subgroup.centralizer {x} = ⊥ :=
    hAminimal.infcen_eqbot_topco
      x hABtop hxcomm hxncentral
  obtain ⟨a, haA, habot⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hAminimal.2.1)
  have hane :
      (⟨a, haA⟩ : A) ≠ 1 := by
    simpa using habot
  exact
    (separator_inf_centralizer
      A x ⟨a, haA⟩ hfixed (by simpa using hane)).of_quotient N

/-- Every finite nonnilpotent group has a two-generator Petresco
separator. -/
theorem petresco_separator_nilpotent
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    TPSepara G := by
  apply separator_minimal_nonnilpotent
    hnil
  intro H hH
  exact
    Group.IMNonnil.two_gen_petrescseparat
      (MNSubgro.to_group hH)

/-- **Hall, Theorem 6.4.** In a finite nonnilpotent group there is one
ordered pair on which every positive-weight canonical Petresco word is
nontrivial. -/
theorem two_petresco_separator
    [Finite G] (hnil : ¬ Group.IsNilpotent G) :
    ∃ x : Bool → G,
      ∀ n : ℕ, 0 < n → wordEval (twoGeneratorPetresco n) x ≠ 1 := by
  obtain ⟨x, y, hxy⟩ :=
    petresco_separator_nilpotent
      (G := G) hnil
  exact ⟨twoGeneratorAssignment x y, fun n hn ↦ hxy n hn⟩

/-- **Corollary to Hall's Theorem 6.4.** If a positive-weight canonical
Petresco verbal subgroup vanishes in a finite group, that group is
nilpotent. -/
theorem petresco_verbal_bot
    [Finite G] {n : ℕ} (hn : 0 < n)
    (htau : verbalSubgroup (twoGeneratorPetresco n) G = ⊥) :
    Group.IsNilpotent G := by
  apply nilpotent_petresco_verbal
    (tau := twoGeneratorPetresco) ?_ hn htau
  exact two_petresco_separator

end Edmonton
end Submission

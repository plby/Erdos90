import Towers.Group.Edmonton.LocallyNilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The Edmonton Notes on Nilpotent Groups: minimal normal subgroups

This file formalizes Hall's Theorem 2.9 and its corollary.
-/

namespace Towers
namespace Edmonton

open Group
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- A nontrivial normal subgroup with no smaller nontrivial normal subgroup. -/
def IMNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧
    ∀ N : Subgroup G, N.Normal → N ≤ M → N ≠ ⊥ → N = M

/-- A normal subgroup maximal among the proper normal subgroups lying
below `K`. -/
def MPBelow (N K : Subgroup G) : Prop :=
  N.Normal ∧ N < K ∧
    ∀ L : Subgroup G, L.Normal → N ≤ L → L < K → L = N

/-- A nontrivial subgroup of a finite group has a maximal proper ambient
normal subgroup below it. -/
lemma maximal_proper_below
    [Finite G] {K : Subgroup G} (hKne : K ≠ ⊥) :
    ∃ N : Subgroup G, MPBelow N K := by
  classical
  let S : Set (Subgroup G) := {N | N.Normal ∧ N < K}
  have hSne : S.Nonempty :=
    ⟨⊥, inferInstance, bot_lt_iff_ne_bot.mpr hKne⟩
  obtain ⟨N, hNS, hNmaximal⟩ := (Set.toFinite S).exists_maximal hSne
  refine ⟨N, hNS.1, hNS.2, ?_⟩
  intro L hLnormal hNL hLK
  exact le_antisymm (hNmaximal ⟨hLnormal, hLK⟩ hNL) hNL

/-- Quotienting a normal subgroup by a maximal proper ambient-normal
subgroup below it produces a minimal normal subgroup of the quotient. -/
lemma MPBelow.map_quot_minnormal
    {N K : Subgroup G} [N.Normal]
    (hN : MPBelow N K)
    (hKnormal : K.Normal) :
    IMNormal (K.map (QuotientGroup.mk' N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hqsurjective : Function.Surjective q :=
    QuotientGroup.mk'_surjective N
  have hqker : q.ker = N :=
    QuotientGroup.ker_mk' N
  have hNK : N ≤ K := hN.2.1.le
  have hAne : K.map q ≠ ⊥ := by
    intro hAbot
    have hKN : K ≤ N := by
      rw [← hqker]
      exact (Subgroup.map_eq_bot_iff K).mp hAbot
    exact hN.2.1.2 hKN
  refine ⟨hKnormal.map q hqsurjective, hAne, ?_⟩
  intro B hBnormal hBA hBne
  let L : Subgroup G := B.comap q
  have hLnormal : L.Normal :=
    hBnormal.comap q
  have hNL : N ≤ L := by
    change N ≤ B.comap q
    exact hqker.symm.le.trans (Subgroup.ker_le_comap q B)
  have hLK : L ≤ K := by
    change B.comap q ≤ K
    rw [← Subgroup.comap_map_eq_self (show q.ker ≤ K by rwa [hqker])]
    exact Subgroup.comap_mono hBA
  have hLeqK : L = K := by
    by_contra hLneK
    have hLlt : L < K :=
      lt_of_le_of_ne hLK hLneK
    have hLeqN : L = N :=
      hN.2.2 L hLnormal hNL hLlt
    apply hBne
    calc
      B = (B.comap q).map q :=
        (Subgroup.map_comap_eq_self_of_surjective hqsurjective B).symm
      _ = L.map q := rfl
      _ = N.map q := congrArg (Subgroup.map q) hLeqN
      _ = ⊥ := (Subgroup.map_eq_bot_iff N).mpr (by simp [hqker])
  calc
    B = (B.comap q).map q :=
      (Subgroup.map_comap_eq_self_of_surjective hqsurjective B).symm
    _ = L.map q := rfl
    _ = K.map q := congrArg (Subgroup.map q) hLeqK

/-- A commutator fixed point remains a commutator fixed point after
passing to a quotient. -/
lemma commutator_top_self
    {N K : Subgroup G} [N.Normal]
    (hKcomm : ⁅K, (⊤ : Subgroup G)⁆ = K) :
    ⁅K.map (QuotientGroup.mk' N), (⊤ : Subgroup (G ⧸ N))⁆ =
      K.map (QuotientGroup.mk' N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  calc
    ⁅K.map q, (⊤ : Subgroup (G ⧸ N))⁆ =
        ⁅K.map q, (⊤ : Subgroup G).map q⁆ := by
      rw [Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    _ = ⁅K, (⊤ : Subgroup G)⁆.map q := by
      rw [Subgroup.map_commutator]
    _ = K.map q := congrArg (Subgroup.map q) hKcomm

/-- A maximal proper normal quotient of a commutator fixed point is a
minimal normal commutator fixed point in the quotient. -/
lemma MPBelow.mapquot_minnormalcomm_topeqself
    {N K : Subgroup G} [N.Normal]
    (hN : MPBelow N K) (hKnormal : K.Normal)
    (hKcomm : ⁅K, (⊤ : Subgroup G)⁆ = K) :
    IMNormal (K.map (QuotientGroup.mk' N)) ∧
      ⁅K.map (QuotientGroup.mk' N), (⊤ : Subgroup (G ⧸ N))⁆ =
        K.map (QuotientGroup.mk' N) :=
  ⟨hN.map_quot_minnormal hKnormal,
    commutator_top_self hKcomm⟩

/-- If `[A, G] = A` and `A` is nontrivial, then some element of `G`
acts nontrivially on `A`. -/
lemma centralizer_singleton_self
    {A : Subgroup G} (hAne : A ≠ ⊥)
    (hAcomm : ⁅A, (⊤ : Subgroup G)⁆ = A) :
    ∃ x : G, ¬ A ≤ Subgroup.centralizer {x} := by
  by_contra h
  push Not at h
  have hcentral : A ≤ Subgroup.centralizer (⊤ : Subgroup G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x _
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h x ha)).symm
  have hbot : ⁅A, (⊤ : Subgroup G)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  rw [hAcomm] at hbot
  exact hAne hbot

/-- A chief-factor quotient of a commutator fixed point has a nontrivial
ambient actor. -/
lemma MPBelow.existsquot_actorcomm_fixedpoint
    {N K : Subgroup G} [N.Normal]
    (hN : MPBelow N K) (hKnormal : K.Normal)
    (hKcomm : ⁅K, (⊤ : Subgroup G)⁆ = K) :
    ∃ x : G ⧸ N,
      IMNormal (K.map (QuotientGroup.mk' N)) ∧
        ⁅K.map (QuotientGroup.mk' N), (⊤ : Subgroup (G ⧸ N))⁆ =
          K.map (QuotientGroup.mk' N) ∧
        ¬ (K.map (QuotientGroup.mk' N) ≤ Subgroup.centralizer {x}) := by
  have hchief :=
    hN.mapquot_minnormalcomm_topeqself
      hKnormal hKcomm
  obtain ⟨x, hx⟩ :=
    centralizer_singleton_self
      hchief.1.2.1 hchief.2
  exact ⟨x, hchief.1, hchief.2, hx⟩

/-- Every nontrivial normal subgroup of a finite group contains a
minimal normal subgroup of the ambient group. -/
lemma minimal_normal
    [Finite G] {K : Subgroup G} (hKnormal : K.Normal) (hKne : K ≠ ⊥) :
    ∃ M : Subgroup G, IMNormal M ∧ M ≤ K := by
  classical
  let S : Set (Subgroup G) := {M | M.Normal ∧ M ≠ ⊥ ∧ M ≤ K}
  have hSne : S.Nonempty :=
    ⟨K, hKnormal, hKne, le_rfl⟩
  obtain ⟨M, hMS, hMminimal⟩ := (Set.toFinite S).exists_minimal hSne
  refine ⟨M, ⟨hMS.1, hMS.2.1, ?_⟩, hMS.2.2⟩
  intro N hNnormal hNM hNne
  exact le_antisymm hNM
    (hMminimal ⟨hNnormal, hNne, hNM.trans hMS.2.2⟩ hNM)

/-- Every finite nontrivial group has a minimal normal subgroup. -/
lemma exists_is_minimal [Finite G] [Nontrivial G] :
    ∃ M : Subgroup G, IMNormal M := by
  obtain ⟨M, hM, _⟩ :=
    minimal_normal (G := G) (K := ⊤)
      (inferInstance : (⊤ : Subgroup G).Normal) top_ne_bot
  exact ⟨M, hM⟩

/-- The commutator of a minimal normal subgroup with the ambient group is
either trivial or the whole minimal normal subgroup. -/
lemma IMNormal.commtop_eqbot_oreqself
    {M : Subgroup G} (hM : IMNormal M) :
    ⁅M, (⊤ : Subgroup G)⁆ = ⊥ ∨ ⁅M, (⊤ : Subgroup G)⁆ = M := by
  letI : M.Normal := hM.1
  by_cases hbot : ⁅M, (⊤ : Subgroup G)⁆ = ⊥
  · exact Or.inl hbot
  · exact Or.inr (hM.2.2 _ inferInstance (Subgroup.commutator_le_left _ _) hbot)

/-- A locally soluble group is one whose finitely generated subgroups are
soluble. -/
def Group.IsLocallySolvable (G : Type u) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsSolvable H

/-- The normal closure of a nonidentity element of a minimal normal subgroup
is the whole minimal normal subgroup. -/
lemma IMNormal.normal_closure_singletoneq
    {M : Subgroup G} (hM : IMNormal M)
    {x : G} (hxM : x ∈ M) (hx : x ≠ 1) :
    Subgroup.normalClosure ({x} : Set G) = M := by
  letI : M.Normal := hM.1
  apply hM.2.2
  · infer_instance
  · exact Subgroup.normalClosure_le_normal (by simpa)
  · intro hbot
    have hxbot :
        x ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.subset_normalClosure (Set.mem_singleton x)
    exact hx (by simpa using hxbot)

/-- Solubility inherited by an ambient subgroup. -/
lemma is_of_le
    {H K : Subgroup G} (hKH : K ≤ H) (hH : IsSolvable H) :
    IsSolvable K := by
  letI : IsSolvable H := hH
  letI : IsSolvable (K.subgroupOf H) := inferInstance
  exact solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKH).surjective

/-- A finitely generated ambient subgroup contained in a locally soluble
subgroup is soluble. -/
lemma solvable_fg_locally
    {H K : Subgroup G} (hH : Group.IsLocallySolvable H)
    (hKfg : K.FG) (hKH : K ≤ H) :
    IsSolvable K := by
  let e : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  letI : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hKfg
  letI : Group.FG (K.subgroupOf H) :=
    Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hsubfg : (K.subgroupOf H).FG :=
    (Group.fg_iff_subgroup_fg (K.subgroupOf H)).mp inferInstance
  letI : IsSolvable (K.subgroupOf H) := hH _ hsubfg
  exact solvable_of_surjective (f := e.toMonoidHom) e.surjective

/-- Enlarging the acting subgroup enlarges a relative normal closure. -/
lemma relative_mono_right
    {S : Set G} {H K : Subgroup G} (hHK : H ≤ K) :
    relativeNormalClosure S H ≤ relativeNormalClosure S K :=
  relative_normal_closure (subset_relative_closure S K)
    (hHK.trans (normalizer_relative_closure S K))

/-- Membership in a singleton normal closure already uses conjugation by a
finitely generated subgroup containing the generator. -/
lemma fg_relative_singleton
    {c x : G} (hx : x ∈ Subgroup.normalClosure ({c} : Set G)) :
    ∃ H : Subgroup G, H.FG ∧ c ∈ H ∧
      x ∈ relativeNormalClosure ({c} : Set G) H := by
  classical
  change x ∈ Subgroup.closure (Group.conjugatesOfSet ({c} : Set G)) at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨d, hd, hdz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
      rw [Set.mem_singleton_iff.mp hd] at hdz
      obtain ⟨g, rfl⟩ := isConj_iff.mp hdz
      let H : Subgroup G := Subgroup.closure ({c, g} : Set G)
      have hcH : c ∈ H := Subgroup.subset_closure (by simp)
      have hgH : g ∈ H := Subgroup.subset_closure (by simp)
      refine ⟨H, ⟨{c, g}, by simp [H]⟩, hcH, ?_⟩
      exact conjugate_relative_closure hgH
        (subset_relative_closure ({c} : Set G) H (by simp))
  | one =>
      let H : Subgroup G := Subgroup.closure ({c} : Set G)
      exact ⟨H, ⟨{c}, by simp [H]⟩, Subgroup.subset_closure (by simp),
        (relativeNormalClosure ({c} : Set G) H).one_mem⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨A, hAfg, hcA, ha⟩ := iha
      obtain ⟨B, hBfg, hcB, hb⟩ := ihb
      refine ⟨A ⊔ B, hAfg.sup hBfg, Subgroup.mem_sup_left hcA, ?_⟩
      exact (relativeNormalClosure ({c} : Set G) (A ⊔ B)).mul_mem
        (relative_mono_right le_sup_left ha)
        (relative_mono_right le_sup_right hb)
  | inv a _ iha =>
      obtain ⟨A, hAfg, hcA, ha⟩ := iha
      exact ⟨A, hAfg, hcA,
        (relativeNormalClosure ({c} : Set G) A).inv_mem ha⟩

/-- If two ambient subgroups are normal in `H`, then their commutator is
normal in `H`. -/
lemma normal_commutator
    {H K L : Subgroup G} (hKH : K ≤ H) (hLH : L ≤ H)
    [(K.subgroupOf H).Normal] [(L.subgroupOf H).Normal] :
    (⁅K, L⁆.subgroupOf H).Normal := by
  have hcommH : ⁅K, L⁆ ≤ H :=
    (Subgroup.commutator_mono hKH hLH).trans H.commutator_le_self
  have heq :
      ⁅K, L⁆.subgroupOf H =
        ⁅K.subgroupOf H, L.subgroupOf H⁆ := by
    rw [← Subgroup.map_subtype_inj,
      Subgroup.map_subgroupOf_eq_of_le hcommH,
      Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hLH]
  rw [heq]
  infer_instance

/-- If `K` is normal in `H`, then its commutator with `H` is contained in
`K`. -/
lemma commutator_left_subgroup
    {H K : Subgroup G} (hKH : K ≤ H) [(K.subgroupOf H).Normal] :
    ⁅K, H⁆ ≤ K := by
  have hsub :
      ⁅K.subgroupOf H, (⊤ : Subgroup H)⁆ ≤ K.subgroupOf H :=
    Subgroup.commutator_le_left _ _
  have hmap := Subgroup.map_mono (f := H.subtype) hsub
  simpa [Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hKH,
    ← MonoidHom.range_eq_map, H.range_subtype] using hmap

/-- A nontrivial nilpotent group cannot contain a nontrivial subgroup
`K` satisfying `[K,H] = K`. -/
lemma bot_self_nilpotent
    {H K : Subgroup G} (hKH : K ≤ H) [Group.IsNilpotent H]
    (hcomm : ⁅K, H⁆ = K) :
    K = ⊥ := by
  have hKlower : ∀ n : ℕ, K ≤ ambientLowerSeries H n := by
    intro n
    induction n with
    | zero =>
        simpa using hKH
    | succ n ih =>
        rw [ambient_series_succ]
        rw [← hcomm]
        exact Subgroup.commutator_mono ih le_rfl
  apply le_bot_iff.mp
  have hlast := hKlower (Group.nilpotencyClass H)
  rw [ambientLowerSeries, Subgroup.lowerCentralSeries_nilpotencyClass,
    Subgroup.map_bot] at hlast
  exact hlast

/-- **Hall, Theorem 2.9(a).** A minimal normal subgroup of a locally
soluble group is abelian. -/
theorem minimal_locally_solvable
    (hG : Group.IsLocallySolvable G) {M : Subgroup G}
    (hM : IMNormal M) :
    ⁅M, M⁆ = ⊥ := by
  classical
  by_contra hcomm
  have hnle : ¬ ⁅M, M⁆ ≤ (⊥ : Subgroup G) :=
    fun h ↦ hcomm (le_bot_iff.mp h)
  rw [Subgroup.commutator_le] at hnle
  push Not at hnle
  obtain ⟨a, haM, b, hbM, hcnot⟩ := hnle
  let c : G := ⁅a, b⁆
  have hcne : c ≠ 1 := by
    simpa [c] using hcnot
  have hcM : c ∈ M :=
    M.commutator_le_self
      (Subgroup.commutator_mem_commutator haM hbM)
  have hnormalClosure :
      Subgroup.normalClosure ({c} : Set G) = M :=
    hM.normal_closure_singletoneq hcM hcne
  have haNC : a ∈ Subgroup.normalClosure ({c} : Set G) := by
    rw [hnormalClosure]
    exact haM
  have hbNC : b ∈ Subgroup.normalClosure ({c} : Set G) := by
    rw [hnormalClosure]
    exact hbM
  obtain ⟨A, hAfg, hcA, haA⟩ :=
    fg_relative_singleton haNC
  obtain ⟨B, hBfg, hcB, hbB⟩ :=
    fg_relative_singleton hbNC
  let H : Subgroup G := A ⊔ B
  let K : Subgroup G := relativeNormalClosure ({c} : Set G) H
  have hHfg : H.FG := hAfg.sup hBfg
  have hcH : c ∈ H := Subgroup.mem_sup_left hcA
  have haK : a ∈ K :=
    relative_mono_right le_sup_left haA
  have hbK : b ∈ K :=
    relative_mono_right le_sup_right hbB
  have hKH : K ≤ H :=
    relative_normal_closure (by simpa using hcH) Subgroup.le_normalizer
  letI : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    exact normalizer_relative_closure ({c} : Set G) H
  have hHsolv : IsSolvable H := hG H hHfg
  have hKsolv : IsSolvable K :=
    is_of_le hKH hHsolv
  have hccomm : c ∈ ⁅K, K⁆ :=
    Subgroup.commutator_mem_commutator haK hbK
  have hcommKH : ⁅K, K⁆ ≤ H :=
    K.commutator_le_self.trans hKH
  letI : (⁅K, K⁆.subgroupOf H).Normal :=
    normal_commutator hKH hKH
  have hHnormComm :
      H ≤ Subgroup.normalizer (⁅K, K⁆ : Subgroup G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hcommKH
  have hKleComm : K ≤ ⁅K, K⁆ :=
    relative_normal_closure (by simpa using hccomm) hHnormComm
  have hcommEq : ⁅K, K⁆ = K :=
    le_antisymm K.commutator_le_self hKleComm
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hcK :
        c ∈ K := subset_relative_closure ({c} : Set G) H (by simp)
    rw [hKbot] at hcK
    exact hcne (by simpa using hcK)
  letI : IsSolvable K := hKsolv
  have hlt : ⁅K, K⁆ < K := by
    rw [← K.nontrivial_iff_ne_bot] at hKne
    have hltSub :
        commutator K < (⊤ : Subgroup K) :=
      IsSolvable.commutator_lt_top_of_nontrivial K
    have hmaplt :
        (commutator K).map K.subtype <
          (⊤ : Subgroup K).map K.subtype :=
      Subgroup.map_subtype_lt_map_subtype.mpr hltSub
    rw [Subgroup.map_subtype_commutator,
      ← MonoidHom.range_eq_map, K.range_subtype] at hmaplt
    exact hmaplt
  rw [hcommEq] at hlt
  exact (lt_irrefl K) hlt

/-- **Hall, Theorem 2.9(b).** A minimal normal subgroup of a locally
nilpotent group lies in the center. -/
theorem minimal_center_locally
    (hG : Group.IsLocallyNilpotent G) {M : Subgroup G}
    (hM : IMNormal M) :
    M ≤ Subgroup.center G := by
  classical
  letI : M.Normal := hM.1
  have hcommBot : ⁅M, (⊤ : Subgroup G)⁆ = ⊥ := by
    by_contra hcomm
    have hnle : ¬ ⁅M, (⊤ : Subgroup G)⁆ ≤ (⊥ : Subgroup G) :=
      fun h ↦ hcomm (le_bot_iff.mp h)
    rw [Subgroup.commutator_le] at hnle
    push Not at hnle
    obtain ⟨a, haM, b, _, hcnot⟩ := hnle
    let c : G := ⁅a, b⁆
    have hcne : c ≠ 1 := by
      simpa [c] using hcnot
    have hcM : c ∈ M :=
      Subgroup.commutator_le_left M (⊤ : Subgroup G)
        (Subgroup.commutator_mem_commutator haM (Subgroup.mem_top b))
    have hnormalClosure :
        Subgroup.normalClosure ({c} : Set G) = M :=
      hM.normal_closure_singletoneq hcM hcne
    have haNC : a ∈ Subgroup.normalClosure ({c} : Set G) := by
      rw [hnormalClosure]
      exact haM
    obtain ⟨A, hAfg, hcA, haA⟩ :=
      fg_relative_singleton haNC
    let B : Subgroup G := Subgroup.closure ({b} : Set G)
    let H : Subgroup G := A ⊔ B
    let K : Subgroup G := relativeNormalClosure ({c} : Set G) H
    have hBfg : B.FG := ⟨{b}, by simp [B]⟩
    have hHfg : H.FG := hAfg.sup hBfg
    have hcH : c ∈ H := Subgroup.mem_sup_left hcA
    have hbH : b ∈ H :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have haK : a ∈ K :=
      relative_mono_right le_sup_left haA
    have hKH : K ≤ H :=
      relative_normal_closure (by simpa using hcH) Subgroup.le_normalizer
    letI : (K.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
      exact normalizer_relative_closure ({c} : Set G) H
    have hHnil : Group.IsNilpotent H := hG H hHfg
    have hccomm : c ∈ ⁅K, H⁆ :=
      Subgroup.commutator_mem_commutator haK hbH
    have hcommKH : ⁅K, H⁆ ≤ H :=
      (Subgroup.commutator_mono hKH le_rfl).trans H.commutator_le_self
    letI : (H.subgroupOf H).Normal := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    letI : (⁅K, H⁆.subgroupOf H).Normal :=
      normal_commutator hKH le_rfl
    have hHnormComm :
        H ≤ Subgroup.normalizer (⁅K, H⁆ : Subgroup G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hcommKH
    have hKleComm : K ≤ ⁅K, H⁆ :=
      relative_normal_closure (by simpa using hccomm) hHnormComm
    have hCommLeK : ⁅K, H⁆ ≤ K :=
      commutator_left_subgroup hKH
    have hcommEq : ⁅K, H⁆ = K :=
      le_antisymm hCommLeK hKleComm
    letI : Group.IsNilpotent H := hHnil
    have hKbot : K = ⊥ :=
      bot_self_nilpotent hKH hcommEq
    have hcK :
        c ∈ K := subset_relative_closure ({c} : Set G) H (by simp)
    rw [hKbot] at hcK
    exact hcne (by simpa using hcK)
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top,
    ← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hcommBot

/-- **Hall, Corollary after Theorem 2.9.** A simple locally soluble group is
cyclic of prime order. -/
theorem simple_locally_solvable [IsSimpleGroup G]
    (hG : Group.IsLocallySolvable G) :
    IsCyclic G ∧ (Nat.card G).Prime := by
  have htopMinimal : IMNormal (⊤ : Subgroup G) := by
    refine ⟨inferInstance, top_ne_bot, ?_⟩
    intro N hN _ hNne
    exact hN.eq_bot_or_eq_top.resolve_left hNne
  have hderived :
      ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊥ :=
    minimal_locally_solvable hG htopMinimal
  have hcomm : ∀ a b : G, a * b = b * a := by
    intro a b
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hab :
        ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hderived] at hab
    simpa using hab
  letI : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  have hprime : (Nat.card G).Prime :=
    Group.is_simple_iff_prime_card.mp (inferInstance : IsSimpleGroup G)
  letI : Fact (Nat.card G).Prime := ⟨hprime⟩
  exact ⟨isCyclic_of_prime_card (p := Nat.card G) rfl, hprime⟩

end Edmonton
end Towers

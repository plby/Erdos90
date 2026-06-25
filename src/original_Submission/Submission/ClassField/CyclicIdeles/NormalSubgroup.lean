import Submission.ClassField.CyclicIdeles.NormalSubgroupBridge

/-!
# Chapter VII, Section 5, Lemma 5.4: the normal subgroup step

This file supplies the elementary group-theoretic input in the induction:
every nontrivial finite `p`-group has a normal subgroup of index `p`.
-/

namespace Submission.CField.CIdeles

noncomputable section

universe u

private theorem quotient_simple_coatom
    {G : Type u} [Group G]
    {M : Subgroup G} [M.Normal] (hM : IsCoatom M) :
    IsSimpleGroup (G ⧸ M) := by
  refine
    { toNontrivial := (QuotientGroup.nontrivial_iff.mpr hM.1)
      eq_bot_or_eq_top_of_normal := ?_ }
  intro N hN
  have hle : M ≤ Subgroup.comap (QuotientGroup.mk' M) N :=
    QuotientGroup.le_comap_mk' M N
  by_cases hcomap : Subgroup.comap (QuotientGroup.mk' M) N = M
  · left
    calc
      N = (Subgroup.comap (QuotientGroup.mk' M) N).map
          (QuotientGroup.mk' M) := by
        symm
        exact Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective M) N
      _ = M.map (QuotientGroup.mk' M) := by rw [hcomap]
      _ = ⊥ := QuotientGroup.map_mk'_self M
  · right
    have htop : Subgroup.comap (QuotientGroup.mk' M) N = ⊤ :=
      hM.2 _ (lt_of_le_of_ne hle (Ne.symm hcomap))
    calc
      N = (Subgroup.comap (QuotientGroup.mk' M) N).map
          (QuotientGroup.mk' M) := by
        symm
        exact Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective M) N
      _ = ⊤ := by
        rw [htop]
        exact Subgroup.map_top_of_surjective _
          (QuotientGroup.mk'_surjective M)

private theorem coatom_prime
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    (hG : IsPGroup p G) {M : Subgroup G} [M.Normal]
    (hM : IsCoatom M) :
    M.index = p := by
  letI : IsSimpleGroup (G ⧸ M) :=
    quotient_simple_coatom hM
  letI : Group.IsNilpotent (G ⧸ M) := (hG.to_quotient M).isNilpotent
  have hprime : (Nat.card (G ⧸ M)).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hG.to_quotient M)
  rw [M.index_eq_card]
  exact ((Nat.Prime.pow_eq_iff hprime).mp hn.symm).1.symm

/-- A nontrivial finite `p`-group has a normal subgroup of index `p`. -/
theorem normalSubgroupBridge : NormalSubgroupBridge.{u} := by
  intro p hp G _ _ hG hcard
  letI : Fact p.Prime := ⟨hp⟩
  have hnontrivial : Nontrivial G := by
    by_contra htrivial
    letI : Subsingleton G :=
      not_nontrivial_iff_subsingleton.mp htrivial
    apply hcard
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  letI : Nontrivial G := hnontrivial
  rcases eq_top_or_exists_le_coatom (⊥ : Subgroup G) with
    htop | ⟨M, hM, _⟩
  · exact (bot_ne_top htop).elim
  · have hnormal : M.Normal := by
      letI : Group.IsNilpotent G := hG.isNilpotent
      exact Subgroup.NormalizerCondition.normal_of_coatom M
        Group.normalizerCondition_of_isNilpotent hM
    letI : M.Normal := hnormal
    exact ⟨M, hnormal, coatom_prime hG hM⟩

end

end Submission.CField.CIdeles

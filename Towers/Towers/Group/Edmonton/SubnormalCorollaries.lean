import Towers.Group.Edmonton.NormalizerTower
import Towers.Group.Edmonton.TorsionGeneratedGroups
import Mathlib.GroupTheory.Index

/-!
# The Edmonton Notes on Nilpotent Groups: consequences of subnormality

This file formalizes the corollaries following Hall's Lemma 2.6.
-/

namespace Towers
namespace Edmonton

open Group
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The derived subgroup of a nontrivial nilpotent group is proper. -/
lemma top_nontrivial_nilpotent
    [Nontrivial G] [Group.IsNilpotent G] :
    commutator G < ⊤ := by
  apply lt_of_le_of_ne le_top
  intro hcomm
  have hzero_succ :
      Subgroup.lowerCentralSeries G 0 = Subgroup.lowerCentralSeries G (0 + 1) := by
    simp [Subgroup.lowerCentralSeries_one, hcomm]
  have hconstant :
      Subgroup.lowerCentralSeries G 0 =
        Subgroup.lowerCentralSeries G (Group.nilpotencyClass G) :=
    lowerCentralSeries.eq_ge_succ
      (G := G) (Nat.zero_le _) hzero_succ
  have htop_bot : (⊤ : Subgroup G) = ⊥ := by
    calc
      ⊤ = Subgroup.lowerCentralSeries G 0 := Subgroup.lowerCentralSeries_zero.symm
      _ = Subgroup.lowerCentralSeries G (Group.nilpotencyClass G) := hconstant
      _ = ⊥ := Subgroup.lowerCentralSeries_nilpotencyClass
  exact top_ne_bot htop_bot

/-- If `K` is a proper normal subgroup of a nilpotent group, adjoining the
derived subgroup still gives a proper subgroup. -/
lemma sup_top_normal
    [Group.IsNilpotent G] (K : Subgroup G) [K.Normal] (hK : K < ⊤) :
    K ⊔ commutator G < ⊤ := by
  letI : Nontrivial (G ⧸ K) :=
    QuotientGroup.nontrivial_iff.mpr hK.ne
  let f : G →* G ⧸ K := QuotientGroup.mk' K
  have hquot :
      commutator (G ⧸ K) < (⊤ : Subgroup (G ⧸ K)) :=
    top_nontrivial_nilpotent
  have hmap :
      Subgroup.map f (commutator G) = commutator (G ⧸ K) := by
    rw [map_commutator_eq, f.range_eq_top_of_surjective
      (QuotientGroup.mk'_surjective K)]
    rfl
  have hcomap :
      Subgroup.comap f (commutator (G ⧸ K)) <
        Subgroup.comap f (⊤ : Subgroup (G ⧸ K)) :=
    (Subgroup.comap_lt_comap_of_surjective
      (QuotientGroup.mk'_surjective K)).mpr hquot
  rw [← hmap, QuotientGroup.comap_map_mk', Subgroup.comap_top] at hcomap
  exact hcomap

/-- **Hall, Corollary 1 after Lemma 2.6.** If `H` is proper in a nilpotent
group `G`, then `G' H` is proper in `G`.  The product is represented by the
subgroup supremum `G' ⊔ H`. -/
theorem sup_top
    [Group.IsNilpotent G] {H : Subgroup G} (hH : H < ⊤) :
    commutator G ⊔ H < ⊤ := by
  have hsubnormal : H.IsSubnormal :=
    subnormal_nilpotent H
  obtain ⟨K, hKnormal, hHK, hKproper⟩ :=
    hsubnormal.exists_normal_and_le_and_lt_top_of_ne hH.ne
  letI : K.Normal := hKnormal
  exact lt_of_le_of_lt
    (sup_le le_sup_right (hHK.trans le_sup_left))
    (sup_top_normal K hKproper)

/-- For a subnormal subgroup `H`, the relative index
`[K : H ∩ K]` divides `[G : H]`. -/
theorem Subgroup.IsSubnormal.rel_index_dvdindex
    {H : Subgroup G} (hH : H.IsSubnormal) (K : Subgroup G) :
    H.relIndex K ∣ H.index := by
  induction hH with
  | top =>
      simp
  | step H L hHL hLsub hHnormal ih =>
      letI : (H.subgroupOf L).Normal := hHnormal
      have hnormal :
          H.relIndex (L ⊓ K) ∣ H.relIndex L := by
        have hdiv :=
          Subgroup.relIndex_dvd_index_of_normal
            (H.subgroupOf L) ((L ⊓ K).subgroupOf L)
        rw [Subgroup.relIndex_subgroupOf inf_le_left] at hdiv
        exact hdiv
      have hmul := Nat.mul_dvd_mul hnormal ih
      rw [Subgroup.relIndex_inf_mul_relIndex, inf_of_le_left hHL,
        Subgroup.relIndex_mul_index hHL] at hmul
      exact hmul

/-- First clause of Hall's Corollary 2 after Lemma 2.6. -/
theorem rel_dvd_nilpotent
    [Group.IsNilpotent G] (H K : Subgroup G) :
    H.relIndex K ∣ H.index :=
  Subgroup.IsSubnormal.rel_index_dvdindex (subnormal_nilpotent H) K

/-- Second clause of Hall's Corollary 2 after Lemma 2.6. -/
theorem inf_indices_nilpotent
    [Group.IsNilpotent G] (H K : Subgroup G) :
    (H ⊓ K).index ∣ H.index * K.index := by
  have hmul := Nat.mul_dvd_mul
    (rel_dvd_nilpotent H K) (dvd_refl K.index)
  rw [← Subgroup.inf_relIndex_right H K,
    Subgroup.relIndex_mul_index inf_le_right] at hmul
  exact hmul

/-- In a nilpotent group, every prime divisor of the index of the normal
core of a finite-index subgroup already divides the index of the subgroup. -/
lemma core_index_subset
    [Group.IsNilpotent G] (H : Subgroup G) [H.FiniteIndex] :
    H.normalCore.index.primeFactors ⊆ H.index.primeFactors := by
  intro p hpCore
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpCore
  have hp_dvd_core : p ∣ H.normalCore.index :=
    Nat.dvd_of_mem_primeFactors hpCore
  let N : Subgroup G := H.normalCore
  let Q := G ⧸ N
  let f : G →* Q := QuotientGroup.mk' N
  let S : Subgroup Q := H.map f
  letI : N.Normal := by
    dsimp [N]
    infer_instance
  letI : N.FiniteIndex := by
    dsimp [N]
    infer_instance
  letI : Finite Q := by
    dsimp [Q]
    infer_instance
  letI : Group.IsNilpotent Q := by
    dsimp [Q]
    infer_instance
  have hf : Function.Surjective f := by
    dsimp [f]
    exact QuotientGroup.mk'_surjective N
  have hker : f.ker ≤ H := by
    rw [show f.ker = N by
      dsimp [f]
      exact QuotientGroup.ker_mk' N]
    exact H.normalCore_le
  have hSindex : S.index = H.index := by
    dsimp [S]
    exact H.index_map_eq hf hker
  have hp_dvd_card : p ∣ Nat.card Q := by
    rw [← N.index_eq_card]
    exact hp_dvd_core
  by_contra hp_not_mem
  have hp_not_dvd_H : ¬ p ∣ H.index := by
    intro hp_dvd_H
    exact hp_not_mem (Nat.mem_primeFactors.mpr
      ⟨hp, hp_dvd_H, Subgroup.FiniteIndex.index_ne_zero⟩)
  have hp_not_dvd_S : ¬ p ∣ S.index := by
    rwa [hSindex]
  letI : Fact p.Prime := ⟨hp⟩
  let R : Sylow p S := default
  have hRmap_index : ¬ p ∣ (R.map S.subtype).index := by
    rw [Subgroup.index_map_subtype R.1]
    exact hp.not_dvd_mul R.not_dvd_index hp_not_dvd_S
  let P : Sylow p Q :=
    (R.isPGroup'.map S.subtype).toSylow hRmap_index
  have hallSylowNormal :
      ∀ (q : ℕ) (_hq : Fact q.Prime) (T : Sylow q Q),
        (T : Subgroup Q).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := Q)).out 0 3).mp
      (inferInstance : Group.IsNilpotent Q)
  have hPnormal : (P : Subgroup Q).Normal :=
    hallSylowNormal p inferInstance P
  letI : (P : Subgroup Q).Normal := hPnormal
  have hPS : (P : Subgroup Q) ≤ S := by
    exact Subgroup.map_subtype_le R.1
  have hcomap_le_H : P.comap f ≤ H := by
    rw [← Subgroup.comap_map_eq_self hker]
    exact Subgroup.comap_mono hPS
  have hcomap_le_N : P.comap f ≤ N := by
    exact Subgroup.normal_le_normalCore.mpr hcomap_le_H
  have hPbot : (P : Subgroup Q) = ⊥ := by
    rw [← Subgroup.map_comap_eq_self_of_surjective hf P,
      Subgroup.map_eq_bot_iff]
    rw [show f.ker = N by
      dsimp [f]
      exact QuotientGroup.ker_mk' N]
    exact hcomap_le_N
  exact P.ne_bot_of_dvd_card hp_dvd_card hPbot

/-- Third clause of Hall's Corollary 2 after Lemma 2.6. -/
theorem normal_core_dvd
    [Group.IsNilpotent G] (H : Subgroup G) [H.FiniteIndex] :
    ∃ k : ℕ, H.normalCore.index ∣ H.index ^ k := by
  apply dvd_factors_subset
  · exact Subgroup.FiniteIndex.index_ne_zero
  · exact Subgroup.FiniteIndex.index_ne_zero
  · exact core_index_subset H

end Edmonton
end Towers

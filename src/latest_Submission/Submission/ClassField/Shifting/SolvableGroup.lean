import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite

/-!
# Milne, Class Field Theory, Theorem II.3.10: solvable-group reduction

This file formalizes the group-theoretic reduction in Milne's solvable case:
a finite nontrivial solvable group has a proper normal subgroup with cyclic
quotient.  We choose a maximal subgroup containing the commutator subgroup.
-/

namespace Submission.CField.Shifting

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- A coatom containing the commutator subgroup is normal and has cyclic
quotient. -/
private theorem cyclic_coatom_commutator
    [Finite G] (H : Subgroup G) (hH : IsCoatom H)
    (hcomm : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le (G := G) hcomm
    IsCyclic (G ⧸ H) := by
  letI : H.Normal := Subgroup.Normal.of_commutator_le (G := G) hcomm
  letI : Nontrivial (G ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH.ne_top
  rw [isCyclic_iff_exists_zpowers_eq_top]
  obtain ⟨g, hg⟩ := exists_ne (1 : G ⧸ H)
  refine ⟨g, ?_⟩
  let e := QuotientGroup.comapMk'OrderIso H
  have hle : H ≤ (e (Subgroup.zpowers g)).1 := (e (Subgroup.zpowers g)).2
  rcases (hH.le_iff.mp hle) with htop | heq
  · apply e.injective
    apply Subtype.ext
    simpa [e] using htop
  · have hzbot : Subgroup.zpowers g = ⊥ := by
      apply e.injective
      apply Subtype.ext
      simpa [e] using heq
    exact ((Subgroup.zpowers_ne_bot.mpr hg) hzbot).elim

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem nat_ne_top [Finite G] (H : Subgroup G)
    (hH : H ≠ ⊤) : Nat.card H < Nat.card G := by
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective H.subtype H.subtype_injective
  intro hsurj
  apply hH
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, rfl⟩ := hsurj g
  exact h.property

/-- The group-theoretic reduction used in the solvable part of Theorem
II.3.10: a finite nontrivial solvable group admits a proper normal subgroup
with cyclic quotient. -/
theorem proper_normal_cyclic
    [Finite G] [Nontrivial G] [IsSolvable G] :
    ∃ H : Subgroup G, H ≠ ⊤ ∧ ∃ hnormal : H.Normal,
      letI : H.Normal := hnormal
      IsCyclic (G ⧸ H) := by
  letI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective
  have hcomm : commutator G ≠ ⊤ :=
    (IsSolvable.commutator_lt_top_of_nontrivial G).ne
  rcases eq_top_or_exists_le_coatom (commutator G) with htop | ⟨H, hH, hle⟩
  · exact (hcomm htop).elim
  · let hnormal : H.Normal := Subgroup.Normal.of_commutator_le (G := G) hle
    refine ⟨H, hH.ne_top, hnormal, ?_⟩
    exact cyclic_coatom_commutator H hH hle

end

end Submission.CField.Shifting

import Submission.Group.Petresco.DerivedSeries
import Mathlib.GroupTheory.Nilpotent

/-!
# Petresco's 1954 paper: lower-central-series results

This file formalizes the nilpotent analogue in Section 7. Petresco writes
`O¹(A) = A`; accordingly the Lean index is again one less than the printed
index.
-/

namespace Submission
namespace Edmonton
namespace P1954

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The lower central series of a subgroup, viewed in the ambient group. -/
def petrescoLowerSeries (H : Subgroup G) (n : ℕ) : Subgroup G :=
  (Subgroup.lowerCentralSeries H n).map H.subtype

@[simp]
lemma petresco_series_zero (H : Subgroup G) :
    petrescoLowerSeries H 0 = H := by
  simp [petrescoLowerSeries, ← MonoidHom.range_eq_map, H.range_subtype]

lemma petresco_lower_succ (H : Subgroup G) (n : ℕ) :
    petrescoLowerSeries H (n + 1) =
      ⁅petrescoLowerSeries H n, H⁆ := by
  change Subgroup.map H.subtype ⁅Subgroup.lowerCentralSeries H n, ⊤⁆ =
    ⁅(Subgroup.lowerCentralSeries H n).map H.subtype, H⁆
  rw [Subgroup.map_commutator]
  simp [← MonoidHom.range_eq_map, H.range_subtype]

lemma petresco_central_series (H : Subgroup G) (n : ℕ) :
    petrescoLowerSeries H n ≤ H := by
  rw [petrescoLowerSeries]
  exact Subgroup.map_subtype_le (Subgroup.lowerCentralSeries H n)

/-- Each lower-central term is normal in its original subgroup. -/
lemma petresco_series_subgroup (H : Subgroup G) (n : ℕ) :
    ((petrescoLowerSeries H n).subgroupOf H).Normal := by
  have heq :
      (petrescoLowerSeries H n).subgroupOf H =
        Subgroup.lowerCentralSeries H n := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le
      (petresco_central_series H n)]
    rfl
  rw [heq]
  infer_instance

lemma petresco_series_succ (H : Subgroup G) (n : ℕ) :
    petrescoLowerSeries H (n + 1) ≤
      petrescoLowerSeries H n := by
  rw [petresco_lower_succ]
  letI :
      ((petrescoLowerSeries H n).subgroupOf H).Normal :=
    petresco_series_subgroup H n
  exact commutator_left_subgroup
    (petresco_central_series H n)

lemma petresco_series_antitone (H : Subgroup G) :
    Antitone (petrescoLowerSeries H) :=
  antitone_nat_of_succ_le (petresco_series_succ H)

/-- Once a lower-central term is stable, every later term is equal to it. -/
lemma petresco_stable_add
    (H : Subgroup G) (n : ℕ)
    (hstable :
      petrescoLowerSeries H (n + 1) =
        petrescoLowerSeries H n) :
    ∀ m : ℕ,
      petrescoLowerSeries H (n + m) =
        petrescoLowerSeries H n
  | 0 => by simp
  | m + 1 => by
      rw [Nat.add_succ, petresco_lower_succ,
        petresco_stable_add H n hstable m,
        ← petresco_lower_succ H n]
      exact hstable

/-- Petresco's stable lower-central subgroup, defined intrinsically as the
intersection of all lower-central terms. -/
def nilpotentResidual (H : Subgroup G) : Subgroup G :=
  ⨅ n : ℕ, petrescoLowerSeries H n

lemma nilpotent_residual_series
    (H : Subgroup G) (n : ℕ) :
    nilpotentResidual H ≤ petrescoLowerSeries H n :=
  iInf_le _ n

/-- A stabilized lower-central term equals the nilpotent residual. -/
theorem petresco_nilpotent_stable
    (H : Subgroup G) (n : ℕ)
    (hstable :
      petrescoLowerSeries H (n + 1) =
        petrescoLowerSeries H n) :
    petrescoLowerSeries H n = nilpotentResidual H := by
  apply le_antisymm
  · rw [nilpotentResidual]
    refine le_iInf fun m => ?_
    rcases le_total m n with hmn | hnm
    · exact petresco_series_antitone H hmn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact (petresco_stable_add H n hstable d).ge
  · exact nilpotent_residual_series H n

/-- Under the descending chain condition, every lower-central series has a
stable term. -/
lemma petresco_series_stable
    [WellFoundedLT (Subgroup G)] (H : Subgroup G) :
    ∃ n : ℕ,
      petrescoLowerSeries H (n + 1) =
        petrescoLowerSeries H n := by
  by_contra h
  push Not at h
  have hstrict : StrictAnti (petrescoLowerSeries H) :=
    strictAnti_nat_of_succ_lt fun n =>
      lt_of_le_of_ne
        (petresco_series_succ H n)
        (h n)
  exact
    (not_strictAnti_of_wellFoundedLT
      (petrescoLowerSeries H)) hstrict

/-- **Petresco, Section 7.** The lower-central term of a join is contained
in the product of the corresponding terms of the two inputs and their mixed
commutator subgroup. -/
theorem lower_series_join (A B : Subgroup G) :
    ∀ n : ℕ,
      petrescoLowerSeries (A ⊔ B) n ≤
        (petrescoLowerSeries A n ⊔ ⁅A, B⁆) ⊔
          petrescoLowerSeries B n
  | 0 => by
      rw [petresco_series_zero,
        petresco_series_zero,
        petresco_series_zero]
      exact (sup_commutator_join A B).ge
  | n + 1 => by
      rw [petresco_lower_succ]
      have ih := lower_series_join A B n
      have hmono :
          ⁅petrescoLowerSeries (A ⊔ B) n, A ⊔ B⁆ ≤
            ⁅(petrescoLowerSeries A n ⊔ ⁅A, B⁆) ⊔
                petrescoLowerSeries B n,
              A ⊔ B⁆ :=
        Subgroup.commutator_mono ih le_rfl
      apply hmono.trans
      letI :
          ((petrescoLowerSeries A n).subgroupOf A).Normal :=
        petresco_series_subgroup A n
      letI :
          ((petrescoLowerSeries B n).subgroupOf B).Normal :=
        petresco_series_subgroup B n
      simpa [petresco_lower_succ] using
        commutator_mixed_product
          (Astar := petrescoLowerSeries A n) (A := A)
          (Bstar := petrescoLowerSeries B n) (B := B)
          (petresco_central_series A n)
          (petresco_central_series B n)

/-- **Petresco, Section 7, stable form.** Under the descending chain
condition, the nilpotent residual of a join is bounded by the two residuals
and the mixed commutator subgroup. -/
theorem nilpotent_residual_join
    [WellFoundedLT (Subgroup G)] (A B : Subgroup G) :
    nilpotentResidual (A ⊔ B) ≤
      (nilpotentResidual A ⊔ ⁅A, B⁆) ⊔
        nilpotentResidual B := by
  obtain ⟨j, hj⟩ := petresco_series_stable A
  obtain ⟨k, hk⟩ := petresco_series_stable B
  have hA :
      petrescoLowerSeries A (j + k) =
        nilpotentResidual A := by
    rw [petresco_stable_add A j hj k,
      petresco_nilpotent_stable A j hj]
  have hB :
      petrescoLowerSeries B (j + k) =
        nilpotentResidual B := by
    rw [Nat.add_comm,
      petresco_stable_add B k hk j,
      petresco_nilpotent_stable B k hk]
  calc
    nilpotentResidual (A ⊔ B) ≤
        petrescoLowerSeries (A ⊔ B) (j + k) :=
      nilpotent_residual_series (A ⊔ B) (j + k)
    _ ≤
        (petrescoLowerSeries A (j + k) ⊔ ⁅A, B⁆) ⊔
          petrescoLowerSeries B (j + k) :=
      lower_series_join A B (j + k)
    _ =
        (nilpotentResidual A ⊔ ⁅A, B⁆) ⊔
          nilpotentResidual B := by rw [hA, hB]

end P1954
end Edmonton
end Submission

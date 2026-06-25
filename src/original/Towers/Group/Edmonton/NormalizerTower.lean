import Towers.Group.Edmonton.Fitting
import Mathlib.GroupTheory.IsSubnormal

/-!
# The Edmonton Notes on Nilpotent Groups: the normalizer tower

This file formalizes Hall's Lemma 2.6 and its subnormality consequence.
-/

namespace Towers
namespace Edmonton

open Group
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The iterated normalizer tower starting from `H`. -/
def normalizerTower (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => Subgroup.normalizer (normalizerTower H n : Set G)

@[simp]
lemma normalizerTower_zero (H : Subgroup G) :
    normalizerTower H 0 = H :=
  rfl

@[simp]
lemma normalizerTower_succ (H : Subgroup G) (n : ℕ) :
    normalizerTower H (n + 1) =
      Subgroup.normalizer (normalizerTower H n : Set G) :=
  rfl

/-- The normalizer tower is increasing. -/
lemma normalizerTower_monotone (H : Subgroup G) :
    Monotone (normalizerTower H) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [normalizerTower_succ]
  exact Subgroup.le_normalizer

/-- Every tower stage is normal in the next stage. -/
lemma normalizer_tower_succ (H : Subgroup G) (n : ℕ) :
    ((normalizerTower H n).subgroupOf (normalizerTower H (n + 1))).Normal := by
  rw [normalizerTower_succ]
  exact Subgroup.normal_in_normalizer

/-- If `H` contains `Z_n(G)`, then its normalizer contains `Z_{n+1}(G)`. -/
lemma upper_succ_normalizer
    (H : Subgroup G) {n : ℕ} (h : Subgroup.upperCentralSeries G n ≤ H) :
    Subgroup.upperCentralSeries G (n + 1) ≤ Subgroup.normalizer (H : Set G) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  have preserve :
      ∀ w ∈ Subgroup.upperCentralSeries G (n + 1), ∀ x ∈ H,
        w * x * w⁻¹ ∈ H := by
    intro w hw x hx
    have hcomm : ⁅w, x⁆ ∈ H :=
      h (Subgroup.mem_upperCentralSeries_succ_iff.mp hw x)
    rw [show w * x * w⁻¹ = ⁅w, x⁆ * x by
      simp [commutatorElement_def, mul_assoc]]
    exact H.mul_mem hcomm hx
  intro x
  constructor
  · exact preserve z hz x
  · intro hx
    have hback :=
      preserve z⁻¹ ((Subgroup.upperCentralSeries G (n + 1)).inv_mem hz)
        (z * x * z⁻¹) hx
    simpa [mul_assoc] using hback

/-- The `n`th upper-central term lies in the `n`th normalizer-tower stage. -/
lemma upper_normalizer_tower (H : Subgroup G) :
    ∀ n : ℕ, Subgroup.upperCentralSeries G n ≤ normalizerTower H n
  | 0 => by simp
  | n + 1 => by
      rw [normalizerTower_succ]
      exact upper_succ_normalizer (normalizerTower H n)
        (upper_normalizer_tower H n)

/-- **Hall, Lemma 2.6.** In a nilpotent group of class `c`, the normalizer
tower of a proper subgroup reaches the whole group after at most `c` strict
steps. -/
theorem strict_normalizer_tower
    {c : ℕ} (hG : NilpotentClass G c) {H : Subgroup G} (hH : H < ⊤) :
    ∃ r : ℕ, r ≤ c ∧ 0 < r ∧ normalizerTower H r = ⊤ ∧
      ∀ i < r, normalizerTower H i < normalizerTower H (i + 1) := by
  classical
  letI : Group.IsNilpotent G := hG.1
  have hc : normalizerTower H c = ⊤ := by
    apply top_unique
    have hupper : Subgroup.upperCentralSeries G c = ⊤ := by
      simpa [hG.2] using (Subgroup.upperCentralSeries_nilpotencyClass (G := G))
    rw [← hupper]
    exact upper_normalizer_tower H c
  let hex : ∃ n : ℕ, normalizerTower H n = ⊤ := ⟨c, hc⟩
  let r := Nat.find hex
  have hr_top : normalizerTower H r = ⊤ :=
    Nat.find_spec hex
  have hr_le : r ≤ c :=
    Nat.find_min' hex hc
  have hr_pos : 0 < r := by
    by_contra hr
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    rw [hr0, normalizerTower_zero] at hr_top
    exact hH.ne hr_top
  refine ⟨r, hr_le, hr_pos, hr_top, ?_⟩
  intro i hi
  have hi_find : i < Nat.find hex := by
    simpa [r] using hi
  have hi_ne_top : normalizerTower H i ≠ ⊤ :=
    Nat.find_min hex hi_find
  simpa [normalizerTower_succ] using
    (Group.normalizerCondition_of_isNilpotent (G := G)
      (normalizerTower H i) hi_ne_top.lt_top)

/-- Every subgroup of a nilpotent group is subnormal. -/
theorem subnormal_nilpotent
    [Group.IsNilpotent G] (H : Subgroup G) :
    H.IsSubnormal := by
  by_cases hH : H = ⊤
  · subst H
    exact Subgroup.IsSubnormal.top
  · have hproper : H < ⊤ := lt_top_iff_ne_top.mpr hH
    have hclass : NilpotentClass G (Group.nilpotencyClass G) :=
      ⟨inferInstance, rfl⟩
    obtain ⟨r, _, _, hr_top, _⟩ := strict_normalizer_tower hclass hproper
    rw [Subgroup.IsSubnormal.isSubnormal_iff]
    exact
      ⟨r, normalizerTower H, normalizerTower_monotone H,
        normalizer_tower_succ H, rfl, hr_top⟩

end Edmonton
end Towers

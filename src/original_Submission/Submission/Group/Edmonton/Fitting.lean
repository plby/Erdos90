import Submission.Group.Edmonton.BasicCommutators
import Mathlib.Data.Bool.Count
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The Edmonton Notes on Nilpotent Groups: Fitting's theorem

This file formalizes Hall's Theorem 2.5.
-/

namespace Submission
namespace Edmonton

open Group
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- The lower central series of a subgroup, viewed inside the ambient group. -/
def ambientLowerSeries (H : Subgroup G) (n : ℕ) : Subgroup G :=
  (Subgroup.lowerCentralSeries H n).map H.subtype

@[simp]
lemma ambient_series_zero (H : Subgroup G) :
    ambientLowerSeries H 0 = H := by
  simp [ambientLowerSeries, ← MonoidHom.range_eq_map, H.range_subtype]

lemma ambient_series_succ (H : Subgroup G) (n : ℕ) :
    ambientLowerSeries H (n + 1) =
      ⁅ambientLowerSeries H n, H⁆ := by
  change Subgroup.map H.subtype ⁅Subgroup.lowerCentralSeries H n, ⊤⁆ =
    ⁅(Subgroup.lowerCentralSeries H n).map H.subtype, H⁆
  rw [Subgroup.map_commutator]
  simp [← MonoidHom.range_eq_map, H.range_subtype]

instance ambient_series_normal (H : Subgroup G) [H.Normal] (n : ℕ) :
    (ambientLowerSeries H n).Normal := by
  change ((Subgroup.lowerCentralSeries H n).map H.subtype).Normal
  infer_instance

/-- If the entries tagged `b` lie in a normal subgroup `H`, then a left-normed
commutator containing `r > 0` such entries lies in the `(r - 1)`st lower
central term of `H`, viewed in the ambient group. -/
theorem normed_tag_pos
    (H : Subgroup G) [H.Normal] :
    ∀ (n : ℕ) (a : Fin (n + 1) → G) (tag : Fin (n + 1) → Bool) (b : Bool),
      (∀ i, tag i = b → a i ∈ H) →
      0 < List.count b (List.ofFn tag) →
      leftNormedValue n a ∈
        ambientLowerSeries H (List.count b (List.ofFn tag) - 1) := by
  intro n
  induction n with
  | zero =>
      intro a tag b ha hpos
      have htag : tag 0 = b := by
        cases htag : tag 0 <;> cases b <;>
          simp [List.ofFn_succ, htag] at hpos ⊢
      simpa [leftNormedValue, htag] using ha 0 htag
  | succ n ih =>
      intro a tag b ha hpos
      let a' : Fin (n + 1) → G := fun i ↦ a i.castSucc
      let tag' : Fin (n + 1) → Bool := fun i ↦ tag i.castSucc
      let r := List.count b (List.ofFn tag')
      by_cases hlast : tag (Fin.last (n + 1)) = b
      · by_cases hr : r = 0
        · have hcount :
              List.count b (List.ofFn tag) = r + 1 := by
            rw [List.ofFn_succ', hlast, List.count_concat]
          have hlast_mem : a (Fin.last (n + 1)) ∈ H :=
            ha _ hlast
          have hcomm :
              leftNormedValue (n + 1) a ∈ H := by
            change
              ⁅leftNormedValue n a',
                a (Fin.last (n + 1))⁆ ∈ H
            exact Subgroup.commutator_le_right (⊤ : Subgroup G) H
              (Subgroup.commutator_mem_commutator
                (Subgroup.mem_top _) hlast_mem)
          simpa only [hcount, hr, zero_add, Nat.sub_self,
            ambient_series_zero] using hcomm
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
          have hcount :
              List.count b (List.ofFn tag) = r + 1 := by
            rw [List.ofFn_succ', hlast, List.count_concat]
          have hprefix :
              leftNormedValue n a' ∈
                ambientLowerSeries H (r - 1) := by
            apply ih a' tag' b
            · intro i hi
              exact ha i.castSucc hi
            · exact hrpos
          have hcomm :
              leftNormedValue (n + 1) a ∈
                ambientLowerSeries H ((r - 1) + 1) := by
            rw [ambient_series_succ]
            exact Subgroup.commutator_mem_commutator hprefix (ha _ hlast)
          simpa only [hcount, Nat.add_sub_cancel,
            Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr)] using hcomm
      · have hcount :
            List.count b (List.ofFn tag) = r := by
          rw [List.ofFn_succ', List.concat_eq_append, List.count_append,
            List.count_singleton]
          simp [r, tag', hlast]
        have hrpos : 0 < r := by
          simpa only [hcount] using hpos
        have hprefix :
            leftNormedValue n a' ∈
              ambientLowerSeries H (r - 1) := by
          apply ih a' tag' b
          · intro i hi
            exact ha i.castSucc hi
          · exact hrpos
        have hcomm :
            leftNormedValue (n + 1) a ∈
              ambientLowerSeries H (r - 1) := by
          change
            ⁅leftNormedValue n a',
              a (Fin.last (n + 1))⁆ ∈ ambientLowerSeries H (r - 1)
          exact Subgroup.commutator_le_left
            (ambientLowerSeries H (r - 1)) (⊤ : Subgroup G)
            (Subgroup.commutator_mem_commutator hprefix (Subgroup.mem_top _))
        simpa only [hcount] using hcomm

/-- The carrier union of two subgroups, viewed inside their supremum. -/
def supGeneratorSet (H K : Subgroup G) : Set (H ⊔ K : Subgroup G) :=
  {x | (x : G) ∈ H ∨ (x : G) ∈ K}

/-- The carrier union of `H` and `K` generates `H ⊔ K`. -/
lemma closure_sup_top (H K : Subgroup G) :
    Subgroup.closure (supGeneratorSet H K) = ⊤ := by
  change
    Subgroup.closure
      (((H.subgroupOf (H ⊔ K : Subgroup G) :
          Subgroup (H ⊔ K : Subgroup G)) : Set (H ⊔ K : Subgroup G)) ∪
        ((K.subgroupOf (H ⊔ K : Subgroup G) :
          Subgroup (H ⊔ K : Subgroup G)) : Set (H ⊔ K : Subgroup G))) = ⊤
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
    ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]

/-- Coercion from a subgroup preserves left-normed commutator values. -/
@[simp]
lemma coe_normed_value
    {J : Subgroup G} :
    ∀ (n : ℕ) (a : Fin (n + 1) → J),
      ((leftNormedValue n a : J) : G) =
        leftNormedValue n (fun i ↦ (a i : G))
  | 0, _ => rfl
  | n + 1, a => by
      simp only [leftNormedValue]
      change J.subtype ⁅leftNormedValue n (fun i ↦ a i.castSucc),
        a (Fin.last (n + 1))⁆ = _
      rw [map_commutatorElement]
      congr 1
      exact coe_normed_value n (fun i ↦ a i.castSucc)

/-- A mixed left-normed commutator of length `c + d + 1` vanishes when
`H` and `K` are normal and their `c`th and `d`th lower-central terms vanish. -/
lemma mixed_normed_value
    (H K : Subgroup G) [H.Normal] [K.Normal] {c d : ℕ}
    (hH : Subgroup.lowerCentralSeries H c = ⊥) (hK : Subgroup.lowerCentralSeries K d = ⊥)
    (a : Fin (c + d + 1) → (H ⊔ K : Subgroup G))
    (ha : ∀ i, a i ∈ supGeneratorSet H K) :
    leftNormedValue (c + d) a = 1 := by
  classical
  let tag : Fin (c + d + 1) → Bool :=
    fun i ↦ if (a i : G) ∈ H then false else true
  have hfalse : ∀ i, tag i = false → (a i : G) ∈ H := by
    intro i hi
    by_cases hiH : (a i : G) ∈ H
    · exact hiH
    · simp [tag, hiH] at hi
  have htrue : ∀ i, tag i = true → (a i : G) ∈ K := by
    intro i hi
    have hgen := ha i
    change (a i : G) ∈ H ∨ (a i : G) ∈ K at hgen
    by_cases hiH : (a i : G) ∈ H
    · simp [tag, hiH] at hi
    · exact hgen.resolve_left hiH
  let r := List.count false (List.ofFn tag)
  let s := List.count true (List.ofFn tag)
  have hrs : r + s = c + d + 1 := by
    dsimp [r, s]
    simp [List.count_false_add_count_true]
  have hlarge : c < r ∨ d < s := by omega
  apply Subtype.ext
  change
    ((leftNormedValue (c + d) a : (H ⊔ K : Subgroup G)) : G) = 1
  rw [coe_normed_value]
  rcases hlarge with hcr | hds
  · have hmem :
        leftNormedValue (c + d) (fun i ↦ (a i : G)) ∈
          ambientLowerSeries H (r - 1) := by
      apply normed_tag_pos
        H (c + d) (fun i ↦ (a i : G)) tag false hfalse
      omega
    have hterm : ambientLowerSeries H (r - 1) = ⊥ := by
      rw [ambientLowerSeries]
      have hlower : Subgroup.lowerCentralSeries H (r - 1) = ⊥ := by
        apply le_bot_iff.mp
        rw [← hH]
        exact Subgroup.lowerCentralSeries_antitone (Nat.le_sub_one_of_lt hcr)
      rw [hlower, Subgroup.map_bot]
    rw [hterm] at hmem
    simpa using hmem
  · have hmem :
        leftNormedValue (c + d) (fun i ↦ (a i : G)) ∈
          ambientLowerSeries K (s - 1) := by
      apply normed_tag_pos
        K (c + d) (fun i ↦ (a i : G)) tag true htrue
      omega
    have hterm : ambientLowerSeries K (s - 1) = ⊥ := by
      rw [ambientLowerSeries]
      have hlower : Subgroup.lowerCentralSeries K (s - 1) = ⊥ := by
        apply le_bot_iff.mp
        rw [← hK]
        exact Subgroup.lowerCentralSeries_antitone (Nat.le_sub_one_of_lt hds)
      rw [hlower, Subgroup.map_bot]
    rw [hterm] at hmem
    simpa using hmem

/-- Lower-central-series form of Fitting's theorem. -/
theorem fitting_series_bot
    (H K : Subgroup G) [H.Normal] [K.Normal] {c d : ℕ}
    (hH : Subgroup.lowerCentralSeries H c = ⊥) (hK : Subgroup.lowerCentralSeries K d = ⊥) :
    Subgroup.lowerCentralSeries (H ⊔ K : Subgroup G) (c + d) = ⊥ := by
  rw [lower_normed_set
    (closure_sup_top H K)]
  apply le_bot_iff.mp
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨a, ha, rfl⟩
  change leftNormedValue (c + d) a = 1
  exact mixed_normed_value H K hH hK a ha

/-- Fitting's theorem, stated using the actual nilpotency classes. -/
theorem fitting_nilpotent
    (H K : Subgroup G) [H.Normal] [K.Normal]
    [Group.IsNilpotent H] [Group.IsNilpotent K] :
    Group.IsNilpotent (H ⊔ K : Subgroup G) ∧
      Group.nilpotencyClass (H ⊔ K : Subgroup G) ≤
        Group.nilpotencyClass H + Group.nilpotencyClass K := by
  have hlower :
      Subgroup.lowerCentralSeries (H ⊔ K : Subgroup G)
          (Group.nilpotencyClass H + Group.nilpotencyClass K) = ⊥ :=
    fitting_series_bot H K
      Subgroup.lowerCentralSeries_nilpotencyClass Subgroup.lowerCentralSeries_nilpotencyClass
  have hnil : Group.IsNilpotent (H ⊔ K : Subgroup G) :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨_, hlower⟩
  letI : Group.IsNilpotent (H ⊔ K : Subgroup G) := hnil
  exact ⟨hnil, Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hlower⟩

/-- **Hall, Theorem 2.5 (Fitting).** If `H` and `K` are normal nilpotent
subgroups of classes `c` and `d`, then `H K` is nilpotent of class at most
`c + d`. -/
theorem sup_normal_nilpotent
    (H K : Subgroup G) [H.Normal] [K.Normal] {c d : ℕ}
    (hH : NilpotentClass H c) (hK : NilpotentClass K d) :
    Group.IsNilpotent (H ⊔ K : Subgroup G) ∧
      Group.nilpotencyClass (H ⊔ K : Subgroup G) ≤ c + d := by
  letI : Group.IsNilpotent H := hH.1
  letI : Group.IsNilpotent K := hK.1
  simpa [hH.2, hK.2] using fitting_nilpotent H K

end Edmonton
end Submission

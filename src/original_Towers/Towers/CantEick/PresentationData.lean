import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Cant--Eick nilpotent presentation data

This file records the semantic objects used in Cant--Eick, Sections 1--2:
ordered normal words, parameter indices `T_{i,j,k}`, and the consistency
condition that the ordered words give unique coordinates.

The paper defines an abstract presentation `G(t)`.  For the formalization
below we use a semantic realization of that presentation: a group with chosen
generators satisfying the displayed relations and with bijective normal-form
coordinates.  This is the part of the presentation used in the Hall-polynomial
and consistency arguments before Section 5.
-/

open scoped BigOperators

namespace Towers
namespace CantEick

variable {n : ℕ}

/-- The parameter index for `T_{i,j,k}`, using zero-based `Fin n` indices. -/
abbrev ParameterIndex (n : ℕ) : Type :=
  { ijk : Fin n × Fin n × Fin n // ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2 }

/-- The relation index for pairs `i < j`. -/
abbrev RelationIndex (n : ℕ) : Type :=
  { ij : Fin n × Fin n // ij.1 < ij.2 }

/-- Inserting a skipped index into `Fin n` is strictly order-preserving. -/
lemma succ_above_mono {n : ℕ} (p : Fin (n + 1)) :
    StrictMono p.succAbove := by
  intro i j hij
  rcases Fin.succ_le_or_le_castSucc p i with hi | hi
  · rw [Fin.succAbove_of_succ_le p i hi]
    rcases Fin.succ_le_or_le_castSucc p j with hj | hj
    · rw [Fin.succAbove_of_succ_le p j hj]
      exact Fin.castSucc_lt_castSucc_iff.mpr hij
    · rw [Fin.succAbove_of_le_castSucc p j hj]
      exact Fin.castSucc_lt_succ_iff.mpr (le_of_lt hij)
  · rw [Fin.succAbove_of_le_castSucc p i hi]
    have hijle : i.castSucc ≤ j.castSucc :=
      Fin.castSucc_le_castSucc_iff.mpr (le_of_lt hij)
    have hj : p ≤ j.castSucc := le_trans hi hijle
    rw [Fin.succAbove_of_le_castSucc p j hj]
    exact Fin.succ_lt_succ_iff.mpr hij

/--
Embed the parameter indices for a length-`n` presentation into those for
length `n + 1` by skipping the generator index `p`.
-/
def parameterSuccAbove {n : ℕ} (p : Fin (n + 1)) :
    ParameterIndex n → ParameterIndex (n + 1)
  | ⟨(i, j, k), hij, hjk⟩ =>
      ⟨(p.succAbove i, p.succAbove j, p.succAbove k),
        succ_above_mono p hij, succ_above_mono p hjk⟩

/-- A parameter triple avoids the deleted generator slot `p`. -/
def ParameterIndexAvoids {n : ℕ} (p : Fin (n + 1))
    (I : ParameterIndex (n + 1)) : Prop :=
  I.1.1 ≠ p ∧ I.1.2.1 ≠ p ∧ I.1.2.2 ≠ p

lemma parameter_index_avoids {n : ℕ} (p : Fin (n + 1))
    (I : ParameterIndex n) :
    ParameterIndexAvoids p (parameterSuccAbove p I) := by
  rcases I with ⟨⟨i, j, k⟩, hij, hjk⟩
  simp [ParameterIndexAvoids, parameterSuccAbove]

lemma parameter_above_injective {n : ℕ} (p : Fin (n + 1)) :
    Function.Injective
      (parameterSuccAbove p : ParameterIndex n → ParameterIndex (n + 1)) := by
  intro I J h
  rcases I with ⟨⟨i, j, k⟩, hij, hjk⟩
  rcases J with ⟨⟨i', j', k'⟩, hij', hjk'⟩
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  have hcoords :
      i = i' ∧ j = j' ∧ k = k' := by
    simpa [parameterSuccAbove] using hval
  rcases hcoords with ⟨rfl, rfl, rfl⟩
  rfl

/--
The parameters obtained after deleting generator `p` are exactly the old
parameter triples whose three indices all avoid `p`.
-/
theorem parameter_above_avoids {n : ℕ}
    (p : Fin (n + 1)) (J : ParameterIndex (n + 1)) :
    (∃ I : ParameterIndex n, parameterSuccAbove p I = J) ↔
      ParameterIndexAvoids p J := by
  constructor
  · rintro ⟨I, rfl⟩
    exact parameter_index_avoids p I
  · intro h
    rcases J with ⟨⟨a, b, c⟩, hab, hbc⟩
    rcases h with ⟨ha, hb, hc⟩
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq ha
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hb
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hc
    have hij : i < j := by
      by_contra hnot
      have hji : j ≤ i := le_of_not_gt hnot
      have himage : p.succAbove j ≤ p.succAbove i :=
        (succ_above_mono p).monotone hji
      rw [hj, hi] at himage
      exact not_lt_of_ge himage hab
    have hjk : j < k := by
      by_contra hnot
      have hkj : k ≤ j := le_of_not_gt hnot
      have himage : p.succAbove k ≤ p.succAbove j :=
        (succ_above_mono p).monotone hkj
      rw [hk, hj] at himage
      exact not_lt_of_ge himage hbc
    refine ⟨⟨(i, j, k), hij, hjk⟩, ?_⟩
    apply Subtype.ext
    simp [parameterSuccAbove, hi, hj, hk]

theorem parameter_range_avoids {n : ℕ}
    (p : Fin (n + 1)) :
    Set.range (parameterSuccAbove p : ParameterIndex n → ParameterIndex (n + 1)) =
      {J | ParameterIndexAvoids p J} := by
  ext J
  exact parameter_above_avoids p J

@[simp]
lemma parameter_index_val {n : ℕ} (I : ParameterIndex n) :
    (parameterSuccAbove (0 : Fin (n + 1)) I).1 =
      (Fin.succ I.1.1, Fin.succ I.1.2.1, Fin.succ I.1.2.2) := by
  rcases I with ⟨⟨i, j, k⟩, hij, hjk⟩
  rfl

@[simp]
lemma parameter_above_val {n : ℕ} (I : ParameterIndex n) :
    (parameterSuccAbove (Fin.last n) I).1 =
      (Fin.castSucc I.1.1, Fin.castSucc I.1.2.1, Fin.castSucc I.1.2.2) := by
  rcases I with ⟨⟨i, j, k⟩, hij, hjk⟩
  simp [parameterSuccAbove]

/--
Delete one generator slot from a parameter tuple.  This is the uniform
zero-based version of the paper's `T_u`, `T_v`, and `T_w` reindexings.
-/
def deleteParameterTuple {n : ℕ} (p : Fin (n + 1))
    (T : ParameterIndex (n + 1) → ℤ) :
    ParameterIndex n → ℤ :=
  fun I => T (parameterSuccAbove p I)

@[simp]
lemma parameter_tuple {n : ℕ} (p : Fin (n + 1))
    (T : ParameterIndex (n + 1) → ℤ) (I : ParameterIndex n) :
    deleteParameterTuple p T I = T (parameterSuccAbove p I) :=
  rfl

/-- Parameters for the subgroup obtained by deleting the first generator. -/
def firstParameterTuple {n : ℕ}
    (T : ParameterIndex (n + 1) → ℤ) :
    ParameterIndex n → ℤ :=
  deleteParameterTuple 0 T

/-- Parameters for the subgroup obtained by deleting the second generator. -/
def secondParameterTuple {n : ℕ}
    (T : ParameterIndex (n + 2) → ℤ) :
    ParameterIndex (n + 1) → ℤ :=
  deleteParameterTuple 1 T

/-- Parameters for the quotient/reindexing obtained by deleting the last generator. -/
def lastParameterTuple {n : ℕ}
    (T : ParameterIndex (n + 1) → ℤ) :
    ParameterIndex n → ℤ :=
  deleteParameterTuple (Fin.last n) T

/-- Section 3.1: `T_u` keeps exactly the parameter triples avoiding the first generator. -/
theorem delete_parameter_range {n : ℕ} :
    Set.range
        (parameterSuccAbove (0 : Fin (n + 1)) :
          ParameterIndex n → ParameterIndex (n + 1)) =
      {I | ParameterIndexAvoids (0 : Fin (n + 1)) I} :=
  parameter_range_avoids (0 : Fin (n + 1))

/-- Section 3.1: `T_v` keeps exactly the parameter triples avoiding the second generator. -/
theorem parameter_tuple_range {n : ℕ} :
    Set.range
        (parameterSuccAbove (1 : Fin (n + 2)) :
          ParameterIndex (n + 1) → ParameterIndex (n + 2)) =
      {I | ParameterIndexAvoids (1 : Fin (n + 2)) I} :=
  parameter_range_avoids (1 : Fin (n + 2))

/-- Section 3.1: `T_w` keeps exactly the parameter triples avoiding the last generator. -/
theorem delete_last_parameter {n : ℕ} :
    Set.range
        (parameterSuccAbove (Fin.last n) :
          ParameterIndex n → ParameterIndex (n + 1)) =
      {I | ParameterIndexAvoids (Fin.last n) I} :=
  parameter_range_avoids (Fin.last n)

/-- For `n ≤ 2` there are no parameter triples `i < j < k`. -/
theorem parameter_empty_two {n : ℕ} (hn : n ≤ 2) :
    IsEmpty (ParameterIndex n) := by
  refine ⟨?_⟩
  rintro ⟨⟨i, j, k⟩, hij, hjk⟩
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  have hk : (k : ℕ) < n := k.isLt
  have hij' : (i : ℕ) < j := hij
  have hjk' : (j : ℕ) < k := hjk
  omega

/-- Consequently, the parameter tuple is unique in the base cases `n ≤ 2`. -/
theorem parameter_tuple_subsingleton {n : ℕ} (hn : n ≤ 2) :
    Subsingleton (ParameterIndex n → ℤ) := by
  refine ⟨?_⟩
  intro T U
  funext I
  have hI : IsEmpty (ParameterIndex n) := parameter_empty_two hn
  exact False.elim (IsEmpty.false I)

theorem parameter_tuple_two {n : ℕ} (hn : n ≤ 2)
    (T U : ParameterIndex n → ℤ) :
    T = U :=
  (parameter_tuple_subsingleton hn).elim T U

/-- The coordinate tuple with value `z` at `i` and zero elsewhere. -/
def singleCoord {n : ℕ} (i : Fin n) (z : ℤ) : Fin n → ℤ :=
  fun j => if j = i then z else 0

/-- The ordered list of indices strictly above `j`. -/
def upperIndices {n : ℕ} (j : Fin n) : List { k : Fin n // j < k } :=
  (List.finRange n).filterMap fun k =>
    if h : j < k then some ⟨k, h⟩ else none

/-- Ordered product `a₁^{x₁} ... aₙ^{xₙ}`, with zero-based indices. -/
def orderedZPow {G : Type*} [Group G] {n : ℕ}
    (a : Fin n → G) (x : Fin n → ℤ) : G :=
  ((List.finRange n).map fun i => a i ^ x i).prod

lemma ordered_z_single {G : Type*} [Group G] {n : ℕ}
    (a : Fin n → G) (i : Fin n) (z : ℤ) :
    orderedZPow a (singleCoord i z) = a i ^ z := by
  unfold orderedZPow singleCoord
  rw [List.prod_map_eq_pow_single i]
  · rw [List.count_finRange]
    simp
  · intro a' ha' _ha_mem
    simp [ha']

@[simp]
lemma ordered_z_pow {G : Type*} [Group G] {n : ℕ}
    (a : Fin n → G) :
    orderedZPow a (fun _ => 0) = 1 := by
  simp [orderedZPow]

/-- The tail `a_{j+1}^{T_{i,j,j+1}} ... a_n^{T_{i,j,n}}` in a defining relation. -/
def relationTail {G : Type*} [Group G] {n : ℕ}
    (a : Fin n → G) (T : ParameterIndex n → ℤ)
    (i j : Fin n) (hij : i < j) : G :=
  ((upperIndices j).map fun k =>
    a k.1 ^ T ⟨(i, j, k.1), hij, k.2⟩).prod

lemma list_filter_dite {α β M : Type*} [Monoid M]
    (p : α → Prop) [DecidablePred p]
    (f : ∀ a, p a → β) (g : β → M) (l : List α) :
    ((l.filterMap fun a => if h : p a then some (f a h) else none).map g).prod =
      (l.map fun a => if h : p a then g (f a h) else 1).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : p a <;> simp [h, ih]

set_option linter.flexible false in
lemma upperIndices_zero {n : ℕ} :
    upperIndices (0 : Fin (n + 1)) =
      (List.finRange n).map (fun k => (⟨Fin.succ k, Fin.succ_pos k⟩ :
        {k : Fin (n + 1) // (0 : Fin (n + 1)) < k})) := by
  unfold upperIndices
  rw [List.finRange_succ]
  simp [Fin.succ_pos]

lemma upperIndices_succ {n : ℕ} (j : Fin n) :
    upperIndices (Fin.succ j) =
      (upperIndices j).map (fun k => (⟨Fin.succ k.1, Fin.strictMono_succ k.2⟩ :
        {k : Fin (n + 1) // Fin.succ j < k})) := by
  have hfilter :
      List.filterMap
          (fun x : Fin n =>
            if h : Fin.succ j < Fin.succ x then
              some (⟨Fin.succ x, h⟩ : {k : Fin (n + 1) // Fin.succ j < k})
            else none)
          (List.finRange n) =
        (List.filterMap
            (fun x : Fin n =>
              if h : j < x then some (⟨x, h⟩ : {k : Fin n // j < k}) else none)
            (List.finRange n)).map
          (fun k => (⟨Fin.succ k.1, Fin.strictMono_succ k.2⟩ :
            {k : Fin (n + 1) // Fin.succ j < k})) := by
    generalize List.finRange n = l
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [Fin.succ_lt_succ_iff] at ih
        by_cases hx : j < x <;> simp [hx, ih, Fin.succ_lt_succ_iff]
  unfold upperIndices
  rw [List.finRange_succ]
  simp only [List.filterMap_cons, Fin.not_lt_zero, ↓reduceDIte, List.filterMap_map,
    Function.comp_apply]
  simpa only [Fin.succ_lt_succ_iff] using hfilter

set_option linter.flexible false in
lemma list_single_upper {G : Type*} [Monoid G] :
    ∀ {n : ℕ} (j : Fin n) (b : G) (c : ∀ k : Fin n, j < k → G),
    ((List.finRange n).map fun k =>
      if _hEq : k = j then b else if h : j < k then c k h else 1).prod =
      b * ((upperIndices j).map fun k => c k.1 k.2).prod
  | 0, j, _b, _c => by exact Fin.elim0 j
  | n + 1, j, b, c => by
      cases j using Fin.cases with
      | zero =>
          rw [upperIndices_zero]
          rw [List.finRange_succ]
          simp
          apply congrArg (fun tail : G => b * tail)
          apply congrArg List.prod
          apply List.map_congr_left
          intro k _hk
          simp [Fin.succ_pos]
      | succ j' =>
          have ih := list_single_upper (n := n) j' b
            (fun k h => c (Fin.succ k) (Fin.strictMono_succ h))
          rw [upperIndices_succ j']
          rw [List.finRange_succ]
          simp only [List.map_cons, List.prod_cons, List.map_map]
          have hfirst :
              (if _hEq : (0 : Fin (n + 1)) = Fin.succ j' then b
                else if h : Fin.succ j' < 0 then c 0 h else 1) = 1 := by
            have hzero : ¬ (0 : Fin (n + 1)) = Fin.succ j' :=
              (Fin.succ_ne_zero j').symm
            simp [hzero]
          rw [hfirst, one_mul]
          have hleft :
              (List.map ((fun k => if _hEq : k = Fin.succ j' then b
                else if h : Fin.succ j' < k then c k h else 1) ∘ Fin.succ)
                (List.finRange n)).prod =
              (List.map (fun k => if _hEq : k = j' then b
                else if h : j' < k then c (Fin.succ k) (Fin.strictMono_succ h) else 1)
                (List.finRange n)).prod := by
            apply congrArg List.prod
            apply List.map_congr_left
            intro k _hk
            by_cases heq : k = j'
            · subst k
              simp
            · by_cases hlt : j' < k
              · have hs : Fin.succ j' < Fin.succ k := Fin.strictMono_succ hlt
                have hne : Fin.succ k ≠ Fin.succ j' := by
                  intro hbad
                  exact heq ((Fin.succ_injective n) hbad)
                simp [heq, hlt, hs, hne]
              · have hs : ¬ Fin.succ j' < Fin.succ k := by
                  simpa [Fin.succ_lt_succ_iff] using hlt
                have hne : Fin.succ k ≠ Fin.succ j' := by
                  intro hbad
                  exact heq ((Fin.succ_injective n) hbad)
                simp [heq, hlt, hs, hne]
          rw [hleft]
          exact ih

/--
The coordinate tuple represented by a relation tail.  It has precisely the
parameters above `j` and zero in all coordinates `≤ j`.
-/
def relationTailTuple {n : ℕ} (T : ParameterIndex n → ℤ)
    (i j : Fin n) (hij : i < j) : Fin n → ℤ :=
  fun k => if h : j < k then T ⟨(i, j, k), hij, h⟩ else 0

/--
The coordinate tuple represented by `a_j · relationTail(i,j)`: it has a
single `1` in coordinate `j`, the displayed relation parameters above `j`,
and zero below `j`.
-/
def relationProductTuple {n : ℕ} (T : ParameterIndex n → ℤ)
    (i j : Fin n) (hij : i < j) : Fin n → ℤ :=
  fun k => if _hk : k = j then 1 else if h : j < k then T ⟨(i, j, k), hij, h⟩ else 0

@[simp]
lemma relation_tuple_self {n : ℕ} (T : ParameterIndex n → ℤ)
    (i j : Fin n) (hij : i < j) :
    relationProductTuple T i j hij j = 1 := by
  simp [relationProductTuple]

@[simp]
lemma relation_tuple {n : ℕ} (T : ParameterIndex n → ℤ)
    (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    relationProductTuple T i j hij k = T ⟨(i, j, k), hij, hjk⟩ := by
  simp [relationProductTuple, ne_of_gt hjk, hjk]

lemma relation_tuple_not {n : ℕ} (T : ParameterIndex n → ℤ)
    (i j k : Fin n) (hij : i < j) (hkj : k ≠ j) (hjk : ¬ j < k) :
    relationProductTuple T i j hij k = 0 := by
  simp [relationProductTuple, hkj, hjk]

lemma fin_add_two {n : ℕ} :
    (0 : Fin (n + 2)) < 1 := by
  norm_num [Fin.lt_def]

lemma succSucc_pos {n : ℕ} (k : Fin n) :
    (1 : Fin (n + 2)) < Fin.succ (Fin.succ k) := by
  rw [Fin.lt_def]
  simp

/--
The normal-coordinate tuple for the displayed product
`a_1 · relationTail(0,1)`.  This is the one-step relation product used in
the paper's first nontrivial conjugation recursion.
-/
def zeroRelationTuple {n : ℕ}
    (T : ParameterIndex (n + 2) → ℤ) : Fin (n + 2) → ℤ :=
  Fin.cases 0 (Fin.cases 1 (fun k : Fin n =>
    T ⟨((0 : Fin (n + 2)), (1 : Fin (n + 2)),
        Fin.succ (Fin.succ k)), fin_add_two,
      succSucc_pos k⟩))

@[simp]
lemma relation_product_tuple {n : ℕ}
    (T : ParameterIndex (n + 2) → ℤ) :
    zeroRelationTuple T 0 = 0 :=
  rfl

@[simp]
lemma zero_product_tuple {n : ℕ}
    (T : ParameterIndex (n + 2) → ℤ) :
    zeroRelationTuple T 1 = 1 :=
  rfl

@[simp]
lemma relation_tuple_succ {n : ℕ}
    (T : ParameterIndex (n + 2) → ℤ) (k : Fin n) :
    zeroRelationTuple T (Fin.succ (Fin.succ k)) =
      T ⟨((0 : Fin (n + 2)), (1 : Fin (n + 2)),
        Fin.succ (Fin.succ k)), fin_add_two,
        succSucc_pos k⟩ :=
  rfl

@[simp]
lemma zero_relation_tuple {n : ℕ}
    (T : ParameterIndex (n + 2) → ℤ) :
    zeroRelationTuple T =
      relationProductTuple T 0 1 fin_add_two := by
  funext k
  cases k using Fin.cases with
  | zero =>
      simp [relationProductTuple]
  | succ k =>
      cases k using Fin.cases with
      | zero =>
          simp [relationProductTuple]
      | succ k =>
          have hne : (Fin.succ (Fin.succ k) : Fin (n + 2)) ≠ 1 := by
            intro h
            have hval := congrArg Fin.val h
            simp at hval
          simp [relationProductTuple, hne, succSucc_pos]

/-- Homomorphisms commute with relation-tail products. -/
theorem map_relationTail {G H : Type*} [Group G] [Group H] {n : ℕ}
    (φ : G →* H) (a : Fin n → G) (T : ParameterIndex n → ℤ)
    (i j : Fin n) (hij : i < j) :
    φ (relationTail a T i j hij) =
      relationTail (fun k => φ (a k)) T i j hij := by
  unfold relationTail
  rw [map_list_prod φ]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k _hk
  simp [map_zpow]

/--
The relation tail for `T_u` is exactly the old relation tail after reindexing
the generators by deleting the first generator.
-/
theorem delete_parameter_tuple {G : Type*} [Group G] {n : ℕ}
    (a : Fin (n + 1) → G) (T : ParameterIndex (n + 1) → ℤ)
    (i j : Fin n) (hij : i < j) :
    relationTail (fun k : Fin n => a (Fin.succ k)) (firstParameterTuple T)
        i j hij =
      relationTail a T (Fin.succ i) (Fin.succ j) (Fin.strictMono_succ hij) := by
  have hfilter :
      List.filterMap
          (fun x : Fin n =>
            if h : j < x then
              some (⟨Fin.succ x, Fin.strictMono_succ h⟩ :
                {k : Fin (n + 1) // Fin.succ j < k})
            else none)
          (List.finRange n) =
        (List.filterMap
            (fun x : Fin n =>
              if h : j < x then some (⟨x, h⟩ : {k : Fin n // j < k}) else none)
            (List.finRange n)).map
          (fun k => (⟨Fin.succ k.1, Fin.strictMono_succ k.2⟩ :
            {k : Fin (n + 1) // Fin.succ j < k})) := by
    generalize List.finRange n = l
    induction l with
    | nil => simp
    | cons x xs ih =>
        by_cases hx : j < x <;> simp [hx, ih]
  unfold relationTail upperIndices firstParameterTuple deleteParameterTuple
  rw [List.finRange_succ]
  simp only [Fin.not_lt_zero, ↓reduceDIte, List.filterMap_cons_none, List.filterMap_map,
    Function.comp_apply, Fin.succ_lt_succ_iff]
  rw [hfilter]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k _hk
  rcases k with ⟨k, hk⟩
  change
    a (Fin.succ k) ^
        T (parameterSuccAbove (0 : Fin (n + 1)) ⟨(i, j, k), hij, hk⟩) =
      a (Fin.succ k) ^
        T ⟨(Fin.succ i, Fin.succ j, Fin.succ k),
          Fin.strictMono_succ hij, Fin.strictMono_succ hk⟩
  rw [show
      parameterSuccAbove (0 : Fin (n + 1)) ⟨(i, j, k), hij, hk⟩ =
        ⟨(Fin.succ i, Fin.succ j, Fin.succ k),
          Fin.strictMono_succ hij, Fin.strictMono_succ hk⟩ by
    apply Subtype.ext
    rfl]

/--
The relation tail for `T_v` is the old relation tail after deleting the
second generator.  The assumption `i < j` forces the tail indices above the
second generator, so only the first relation index may remain unchanged.
-/
theorem relation_parameter_tuple {G : Type*} [Group G] {n : ℕ}
    (a : Fin (n + 2) → G) (T : ParameterIndex (n + 2) → ℤ)
    (i j : Fin (n + 1)) (hij : i < j) :
    relationTail
        (fun k : Fin (n + 1) => a ((1 : Fin (n + 2)).succAbove k))
        (secondParameterTuple T) i j hij =
      relationTail a T ((1 : Fin (n + 2)).succAbove i)
        ((1 : Fin (n + 2)).succAbove j)
        (succ_above_mono (1 : Fin (n + 2)) hij) := by
  have hjpos : (0 : Fin (n + 1)) < j :=
    lt_of_le_of_lt (Fin.zero_le i) hij
  have hsj : (1 : Fin (n + 2)).succAbove j = Fin.succ j := by
    rw [Fin.succAbove_of_le_castSucc]
    rw [Fin.le_def]
    change (1 : ℕ) ≤ j
    omega
  have hfilter :
      List.filterMap
          (fun x : Fin (n + 1) =>
            if h : j < x then
              some (⟨Fin.succ x, Fin.strictMono_succ h⟩ :
                {k : Fin (n + 2) // Fin.succ j < k})
            else none)
          (List.finRange (n + 1)) =
        (List.filterMap
            (fun x : Fin (n + 1) =>
              if h : j < x then some (⟨x, h⟩ : {k : Fin (n + 1) // j < k}) else none)
            (List.finRange (n + 1))).map
          (fun k => (⟨Fin.succ k.1, Fin.strictMono_succ k.2⟩ :
            {k : Fin (n + 2) // Fin.succ j < k})) := by
    generalize List.finRange (n + 1) = l
    induction l with
    | nil => simp
    | cons x xs ih =>
        by_cases hx : j < x <;> simp [hx, ih]
  have htarget :
      relationTail
          (fun k : Fin (n + 1) => a ((1 : Fin (n + 2)).succAbove k))
          (secondParameterTuple T) i j hij =
        relationTail a T ((1 : Fin (n + 2)).succAbove i) (Fin.succ j)
          (by simpa [hsj] using succ_above_mono (1 : Fin (n + 2)) hij) := by
    unfold relationTail upperIndices secondParameterTuple deleteParameterTuple
    conv_rhs =>
      rw [List.finRange_succ]
    simp only [Fin.not_lt_zero, ↓reduceDIte, List.filterMap_cons_none, List.filterMap_map,
      Function.comp_apply, Fin.succ_lt_succ_iff]
    rw [hfilter]
    simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro k _hk
    rcases k with ⟨k, hk⟩
    have hsk : (1 : Fin (n + 2)).succAbove k = Fin.succ k := by
      rw [Fin.succAbove_of_le_castSucc]
      rw [Fin.le_def]
      change (1 : ℕ) ≤ k
      omega
    rw [hsk]
    congr 1
    apply congrArg T
    apply Subtype.ext
    rw [show
        (parameterSuccAbove (1 : Fin (n + 2)) ⟨(i, j, k), hij, hk⟩).1 =
          ((1 : Fin (n + 2)).succAbove i,
            (1 : Fin (n + 2)).succAbove j,
            (1 : Fin (n + 2)).succAbove k) by
      rfl]
    simp [hsj, hsk]
  simpa [hsj] using htarget

/--
If the last generator maps to `1`, then the relation tail for `T_w` is the
image of the old relation tail after deleting the final parameter index.
This is the relation-tail calculation used for the quotient `W(T)`.
-/
theorem last_parameter_tuple {G : Type*} [Group G]
    {n : ℕ} (a : Fin (n + 1) → G) (T : ParameterIndex (n + 1) → ℤ)
    (hlast : a (Fin.last n) = 1)
    (i j : Fin n) (hij : i < j) :
    relationTail (fun k : Fin n => a (Fin.castSucc k))
        (lastParameterTuple T) i j hij =
      relationTail a T (Fin.castSucc i) (Fin.castSucc j)
        (Fin.castSucc_lt_castSucc_iff.mpr hij) := by
  have hfilter :
      List.filterMap
          (fun x : Fin n =>
            if h : j < x then
              some (⟨Fin.castSucc x, Fin.castSucc_lt_castSucc_iff.mpr h⟩ :
                {k : Fin (n + 1) // Fin.castSucc j < k})
            else none)
          (List.finRange n) =
        (List.filterMap
            (fun x : Fin n =>
              if h : j < x then some (⟨x, h⟩ : {k : Fin n // j < k}) else none)
            (List.finRange n)).map
          (fun k => (⟨Fin.castSucc k.1, Fin.castSucc_lt_castSucc_iff.mpr k.2⟩ :
            {k : Fin (n + 1) // Fin.castSucc j < k})) := by
    generalize List.finRange n = l
    induction l with
    | nil => simp
    | cons x xs ih =>
        by_cases hx : j < x <;> simp [hx, ih]
  unfold relationTail upperIndices lastParameterTuple deleteParameterTuple
  rw [List.finRange_succ_last]
  simp only [List.filterMap_append, List.filterMap_map, Function.comp_apply,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, ↓reduceDIte,
    List.filterMap_cons, List.filterMap_nil, List.map_append,
    List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil]
  rw [hlast]
  simp only [one_zpow, mul_one]
  rw [hfilter]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k _hk
  rcases k with ⟨k, hk⟩
  congr 1
  apply congrArg T
  rw [show
      parameterSuccAbove (Fin.last n) ⟨(i, j, k), hij, hk⟩ =
        ⟨(Fin.castSucc i, Fin.castSucc j, Fin.castSucc k),
          Fin.castSucc_lt_castSucc_iff.mpr hij,
          Fin.castSucc_lt_castSucc_iff.mpr hk⟩ by
    apply Subtype.ext
    simp]

/-- A chosen ordered coordinate system for a group. -/
structure NCSystem (G : Type*) [Group G] (n : ℕ) where
  gen : Fin n → G
  normalForm_bijective : Function.Bijective (orderedZPow gen)

namespace NCSystem

variable {G : Type} [Group G] (S : NCSystem G n)

/-- The equivalence between integer coordinate tuples and group elements. -/
noncomputable def normalFormEquiv : (Fin n → ℤ) ≃ G :=
  Equiv.ofBijective (orderedZPow S.gen) S.normalForm_bijective

/-- Coordinates of a group element in the chosen normal form. -/
noncomputable def coord (g : G) : Fin n → ℤ :=
  (S.normalFormEquiv).symm g

@[simp]
lemma normal_form_equiv (x : Fin n → ℤ) :
    S.normalFormEquiv x = orderedZPow S.gen x :=
  rfl

lemma ordered_z_coord (g : G) :
    orderedZPow S.gen (S.coord g) = g :=
  (S.normalFormEquiv).apply_symm_apply g

lemma coord_z_product (x : Fin n → ℤ) :
    S.coord (orderedZPow S.gen x) = x :=
  (S.normalFormEquiv).symm_apply_apply x

/--
The correction factor that rewrites `a_j a_i` into `a_i a_j` in a chosen
normal coordinate system.
-/
def swapCorrection (i j : Fin n) : G :=
  (S.gen i * S.gen j)⁻¹ * (S.gen j * S.gen i)

/--
The parameter tuple read from the normal coordinates of the swap corrections.
For a triple `i < j < k`, this is the `k`th coordinate of the correction
factor for swapping `a_j a_i` past `a_i a_j`.
-/
noncomputable def parameterTuple : ParameterIndex n → ℤ
  | ⟨(i, j, k), _hij, _hjk⟩ => S.coord (S.swapCorrection i j) k

/--
The support condition saying that each swap correction is represented by the
tail coordinates strictly above the swapped pair.  This is the semantic form
of choosing the integers `t_{i,j,k}` from a central coordinate series.
-/
noncomputable def swapCorrectionsAbove : Prop :=
  ∀ (i j : Fin n) (hij : i < j),
    relationTail S.gen S.parameterTuple i j hij = S.swapCorrection i j

end NCSystem

/--
A semantic realization of Cant--Eick's nilpotent presentation `G(t)`.

The `relation` field is the displayed relation
`a_j a_i = a_i a_j a_{j+1}^{t_{i,j,j+1}} ... a_n^{t_{i,j,n}}`.
The `coords` field records consistency: every element has a unique ordered
normal form.
-/
structure CPres (n : ℕ) (T : ParameterIndex n → ℤ) where
  G : Type
  [group : Group G]
  coords : NCSystem G n
  relation :
    ∀ (i j : Fin n) (hij : i < j),
      coords.gen j * coords.gen i =
        coords.gen i * coords.gen j * relationTail coords.gen T i j hij

attribute [instance] CPres.group

namespace CPres

variable {T : ParameterIndex n → ℤ} (M : CPres n T)

/-- The chosen generators of a consistent presentation. -/
def gen : Fin n → M.G :=
  M.coords.gen

/-- The normal word associated to a coordinate tuple. -/
def normalWord (x : Fin n → ℤ) : M.G :=
  orderedZPow M.gen x

/-- Coordinates of an element in the chosen normal form. -/
noncomputable def coord (g : M.G) : Fin n → ℤ :=
  M.coords.coord g

@[simp]
lemma normalWord_zero :
    M.normalWord (fun _ => 0) = 1 := by
  simp [normalWord, gen]

lemma normalWord_coord (g : M.G) :
    M.normalWord (M.coord g) = g :=
  M.coords.ordered_z_coord g

lemma coord_normalWord (x : Fin n → ℤ) :
    M.coord (M.normalWord x) = x :=
  M.coords.coord_z_product x

/-- Relation tails are already normal words with support strictly above `j`. -/
lemma normal_tail_tuple (i j : Fin n) (hij : i < j) :
    M.normalWord (relationTailTuple T i j hij) =
      relationTail M.gen T i j hij := by
  change orderedZPow M.gen (relationTailTuple T i j hij) =
    relationTail M.gen T i j hij
  unfold orderedZPow relationTail relationTailTuple upperIndices
  rw [list_filter_dite (fun k : Fin n => j < k)
    (fun k h => (⟨k, h⟩ : {k : Fin n // j < k}))
    (fun k => M.gen k.1 ^ T ⟨(i, j, k.1), hij, k.2⟩)]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k _hk
  by_cases h : j < k <;> simp [h]

/-- Coordinates of a relation tail are exactly its displayed tail tuple. -/
lemma coord_relationTail (i j : Fin n) (hij : i < j) :
    M.coord (relationTail M.gen T i j hij) =
      relationTailTuple T i j hij := by
  rw [← M.normal_tail_tuple i j hij]
  exact M.coord_normalWord _

lemma coord_relation_not (i j k : Fin n) (hij : i < j)
    (hjk : ¬ j < k) :
    M.coord (relationTail M.gen T i j hij) k = 0 := by
  rw [M.coord_relationTail]
  simp [relationTailTuple, hjk]

lemma coord_pos_right {m : ℕ}
    {U : ParameterIndex (m + 1) → ℤ}
    (N : CPres (m + 1) U)
    (i j : Fin (m + 1)) (hij : i < j)
    (_h0j : (0 : Fin (m + 1)) < j) :
    N.coord (relationTail N.gen U i j hij) 0 = 0 :=
  N.coord_relation_not i j 0 hij (not_lt_of_ge (Fin.zero_le j))

/-- The product `a_j · relationTail(i,j)` is already in normal form. -/
lemma normal_product_tuple (i j : Fin n) (hij : i < j) :
    M.normalWord (relationProductTuple T i j hij) =
      M.gen j * relationTail M.gen T i j hij := by
  change orderedZPow M.gen (relationProductTuple T i j hij) =
    M.gen j * relationTail M.gen T i j hij
  unfold orderedZPow relationTail relationProductTuple
  rw [← list_single_upper j (M.gen j)
    (fun k h => M.gen k ^ T ⟨(i, j, k), hij, h⟩)]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k _hk
  by_cases hk : k = j
  · subst k
    simp
  · by_cases hjk : j < k
    · simp [hk, hjk]
    · simp [hk, hjk]

/-- Coordinates of `a_j · relationTail(i,j)` are the displayed relation-product tuple. -/
lemma coord_relationProduct (i j : Fin n) (hij : i < j) :
    M.coord (M.gen j * relationTail M.gen T i j hij) =
      relationProductTuple T i j hij := by
  rw [← M.normal_product_tuple i j hij]
  exact M.coord_normalWord _

set_option linter.flexible false in
/-- The product `a_1 · relationTail(0,1)` is already in normal form. -/
lemma normal_relation_tuple {m : ℕ}
    {U : ParameterIndex (m + 2) → ℤ}
    (N : CPres (m + 2) U) :
    N.normalWord (zeroRelationTuple U) =
      N.gen 1 * relationTail N.gen U 0 1 fin_add_two := by
  change orderedZPow N.gen (zeroRelationTuple U) =
      N.gen 1 * relationTail N.gen U 0 1 fin_add_two
  unfold orderedZPow relationTail upperIndices zeroRelationTuple
  rw [List.finRange_succ]
  rw [List.finRange_succ]
  simp [Fin.lt_def]
  change N.gen (1 : Fin (m + 2)) ^ (1 : ℤ) * _ = N.gen 1 * _
  rw [zpow_one]
  congr 1

/--
Coordinate form of `normal_relation_tuple`: multiplying
`a_1` by the `(0,1)` relation tail has the displayed normal coordinates.
-/
lemma coord_relation_product {m : ℕ}
    {U : ParameterIndex (m + 2) → ℤ}
    (N : CPres (m + 2) U) :
    N.coord (N.gen 1 * relationTail N.gen U 0 1 fin_add_two) =
      zeroRelationTuple U := by
  rw [← N.normal_relation_tuple]
  exact N.coord_normalWord _

/-- Every element has an ordered normal form. -/
theorem normalWord_surjective :
    Function.Surjective M.normalWord := by
  intro g
  exact ⟨M.coord g, M.normalWord_coord g⟩

/-- Ordered normal forms are unique. -/
theorem normalWord_injective :
    Function.Injective M.normalWord := by
  intro x y hxy
  rw [← M.coord_normalWord x, ← M.coord_normalWord y, hxy]

/-- Paper-style unique normal form statement for a consistent presentation. -/
theorem unique_normal_word (g : M.G) :
    ∃! x : Fin n → ℤ, M.normalWord x = g := by
  refine ⟨M.coord g, M.normalWord_coord g, ?_⟩
  intro x hx
  exact M.normalWord_injective (by rw [hx, M.normalWord_coord])

/-- The Cant--Eick consistency locus `C_n`, as semantic realizability. -/
def IsConsistent (T : ParameterIndex n → ℤ) : Prop :=
  Nonempty (CPres n T)

/-- The Cant--Eick set `C_n` of consistent parameter tuples. -/
def consistencyLocus (n : ℕ) : Set (ParameterIndex n → ℤ) :=
  {T | IsConsistent T}

/-- A zero-based formal counterpart of Lemma `HLGt`: a coordinate `T`-group
determines a point of the consistency locus. -/
theorem mem_consistency_locus (M : CPres n T) :
    IsConsistent T :=
  ⟨M⟩

/-- Set-membership form for the Cant--Eick consistency locus `C_n`. -/
theorem mem_consistencyLocus (M : CPres n T) :
    T ∈ consistencyLocus n :=
  ⟨M⟩

namespace NCSystem

variable {G : Type} [Group G] (S : NCSystem G n)

/--
Semantic constructor behind Lemma `HLGt`: a normal coordinate system whose
swap corrections are supported in the appropriate tails determines a
consistent Cant--Eick presentation with the parameter tuple read from those
corrections.
-/
noncomputable def consis_prese_corre
    (hS : S.swapCorrectionsAbove) :
    CPres n S.parameterTuple where
  G := G
  coords := S
  relation := by
    intro i j hij
    rw [hS i j hij]
    unfold NCSystem.swapCorrection
    group

/--
Set-level form of the semantic `HLGt` constructor: the parameter tuple read
from supported swap corrections lies in `C_n`.
-/
theorem consistency_locus_above
    (hS : S.swapCorrectionsAbove) :
    S.parameterTuple ∈ consistencyLocus n :=
  mem_consistencyLocus
    (NCSystem.consis_prese_corre S hS)

/--
Existence form of the semantic `HLGt` constructor: a coordinate group with
supported swap corrections supplies some point of the consistency locus.
-/
theorem parameter_locus_above
    (hS : S.swapCorrectionsAbove) :
    ∃ T : ParameterIndex n → ℤ, T ∈ consistencyLocus n :=
  ⟨S.parameterTuple,
    NCSystem.consistency_locus_above
      S hS⟩

end NCSystem

/--
Relation-level part of the Section 3.1 induction approach for `U(T)`:
after deleting the first generator, the remaining generators satisfy the
defining relations with parameter tuple `T_u`.
-/
theorem first_parameter_tuple {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    (i j : Fin n) (hij : i < j) :
    M.gen (Fin.succ j) * M.gen (Fin.succ i) =
      M.gen (Fin.succ i) * M.gen (Fin.succ j) *
        relationTail (fun k : Fin n => M.gen (Fin.succ k))
          (firstParameterTuple T) i j hij := by
  rw [delete_parameter_tuple M.gen T i j hij]
  exact M.relation (Fin.succ i) (Fin.succ j) (Fin.strictMono_succ hij)

/--
Relation-level part of the Section 3.1 induction approach for `V(T)`:
after deleting the second generator, the reindexed generators satisfy the
defining relations with parameter tuple `T_v`.
-/
theorem relation_second_parameter {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    (i j : Fin (n + 1)) (hij : i < j) :
    M.gen ((1 : Fin (n + 2)).succAbove j) *
        M.gen ((1 : Fin (n + 2)).succAbove i) =
      M.gen ((1 : Fin (n + 2)).succAbove i) *
        M.gen ((1 : Fin (n + 2)).succAbove j) *
          relationTail
            (fun k : Fin (n + 1) => M.gen ((1 : Fin (n + 2)).succAbove k))
            (secondParameterTuple T) i j hij := by
  rw [relation_parameter_tuple M.gen T i j hij]
  exact M.relation ((1 : Fin (n + 2)).succAbove i)
    ((1 : Fin (n + 2)).succAbove j)
    (succ_above_mono (1 : Fin (n + 2)) hij)

/--
Relation-level part of the Section 3.1 induction approach for `W(T)`:
after applying a homomorphism that kills the last generator, the images of
the remaining generators satisfy the defining relations with parameter tuple
`T_w`.
-/
theorem relation_last_parameter {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    {H : Type*} [Group H] (φ : M.G →* H)
    (hlast : φ (M.gen (Fin.last n)) = 1)
    (i j : Fin n) (hij : i < j) :
    φ (M.gen (Fin.castSucc j)) * φ (M.gen (Fin.castSucc i)) =
      φ (M.gen (Fin.castSucc i)) * φ (M.gen (Fin.castSucc j)) *
        relationTail (fun k : Fin n => φ (M.gen (Fin.castSucc k)))
          (lastParameterTuple T) i j hij := by
  have htailMap :
      φ (relationTail M.coords.gen T (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_lt_castSucc_iff.mpr hij)) =
        relationTail (fun k : Fin (n + 1) => φ (M.gen k)) T
          (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_lt_castSucc_iff.mpr hij) := by
    unfold relationTail
    rw [map_list_prod φ]
    simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro k _hk
    simp [gen, map_zpow]
  have htailDelete :=
    last_parameter_tuple
      (fun k : Fin (n + 1) => φ (M.gen k)) T hlast i j hij
  have hrel := congrArg φ
    (M.relation (Fin.castSucc i) (Fin.castSucc j)
      (Fin.castSucc_lt_castSucc_iff.mpr hij))
  simp only [map_mul] at hrel
  rw [htailMap, ← htailDelete] at hrel
  simpa [gen] using hrel

/--
Section 3.1 transfer for `U(T)`: an injective homomorphic copy of the
subgroup generated by `a₂, ..., aₙ`, equipped with normal coordinates, gives
a consistent presentation for `T_u`.
-/
theorem consistent_first_parameter {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    {H : Type} [Group H] (coords : NCSystem H n)
    (φ : H →* M.G) (hφ : Function.Injective φ)
    (hgen : ∀ k : Fin n, φ (coords.gen k) = M.gen (Fin.succ k)) :
    IsConsistent (firstParameterTuple T) := by
  refine ⟨{
    G := H
    coords := coords
    relation := ?_
  }⟩
  intro i j hij
  apply hφ
  simpa [map_mul, hgen, map_relationTail] using
    first_parameter_tuple M i j hij

/--
Section 3.1 transfer for `V(T)`: an injective homomorphic copy of the
subgroup generated by `a₁, a₃, ..., aₙ`, equipped with normal coordinates,
gives a consistent presentation for `T_v`.
-/
theorem consistent_parameter_hom {n : ℕ}
    {T : ParameterIndex (n + 2) → ℤ}
    (M : CPres (n + 2) T)
    {H : Type} [Group H] (coords : NCSystem H (n + 1))
    (φ : H →* M.G) (hφ : Function.Injective φ)
    (hgen : ∀ k : Fin (n + 1),
      φ (coords.gen k) = M.gen ((1 : Fin (n + 2)).succAbove k)) :
    IsConsistent (secondParameterTuple T) := by
  refine ⟨{
    G := H
    coords := coords
    relation := ?_
  }⟩
  intro i j hij
  apply hφ
  simpa [map_mul, hgen, map_relationTail] using
    relation_second_parameter M i j hij

/--
Section 3.1 transfer for `W(T)`: a quotient-like homomorphism that kills
`aₙ`, together with normal coordinates on the images of the remaining
generators, gives a consistent presentation for `T_w`.
-/
theorem consistent_parameter_killing {n : ℕ}
    {T : ParameterIndex (n + 1) → ℤ}
    (M : CPres (n + 1) T)
    {H : Type} [Group H] (coords : NCSystem H n)
    (φ : M.G →* H) (hlast : φ (M.gen (Fin.last n)) = 1)
    (hgen : ∀ k : Fin n, coords.gen k = φ (M.gen (Fin.castSucc k))) :
    IsConsistent (lastParameterTuple T) := by
  refine ⟨{
    G := H
    coords := coords
    relation := ?_
  }⟩
  intro i j hij
  have hcoords : coords.gen = fun k : Fin n => φ (M.gen (Fin.castSucc k)) := by
    funext k
    exact hgen k
  simpa [hcoords] using
    relation_last_parameter M φ hlast i j hij

end CPres

end CantEick
end Towers

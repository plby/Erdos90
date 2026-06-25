import Towers.Group.HallBasic.Word

/-!
# Powering one leaf occurrence of a Hall tree

This file contains the lower-central calculation used both by Struik's
top-weight order argument and by the polynomial-coordinate proof of Lemma H2.
It is kept separate from the finite-order conclusions so the Magnus argument
does not depend on finite-group collection machinery.
-/

namespace Struik
namespace P1960

open Towers
open Towers.HallTree
open scoped commutatorElement

universe u v

namespace HallTree

/-- One specified leaf occurrence of a Hall tree. -/
inductive LOccur {α : Type u} : HallTree α → Type u
  | atom (a : α) : LOccur (.atom a)
  | left {left right : HallTree α} :
      LOccur left → LOccur (.commutator left right)
  | right {left right : HallTree α} :
      LOccur right → LOccur (.commutator left right)

/-- The generator labelling a specified leaf occurrence. -/
def LOccur.label {α : Type u} :
    {tree : HallTree α} → LOccur tree → α
  | .atom _, .atom a => a
  | .commutator _ _, .left leaf => leaf.label
  | .commutator _ _, .right leaf => leaf.label

/-- Evaluate a Hall tree after replacing one specified leaf value by its
`m`th power. -/
def leafOccurrencePow
    {α : Type u} {G : Type v} [Group G]
    (value : α → G) (m : ℕ) :
    (tree : HallTree α) → LOccur tree → G
  | .atom a, .atom _ => value a ^ m
  | .commutator left right, .left leaf =>
      ⁅leafOccurrencePow value m left leaf,
        right.toCWord.eval value⁆
  | .commutator left right, .right leaf =>
      ⁅left.toCWord.eval value,
        leafOccurrencePow value m right leaf⁆

/-- Evaluate a Hall tree after replacing one specified leaf value by its
`m`th integer power. -/
def leafOccurrenceZ
    {α : Type u} {G : Type v} [Group G]
    (value : α → G) (m : ℤ) :
    (tree : HallTree α) → LOccur tree → G
  | .atom a, .atom _ => value a ^ m
  | .commutator left right, .left leaf =>
      ⁅leafOccurrenceZ value m left leaf,
        right.toCWord.eval value⁆
  | .commutator left right, .right leaf =>
      ⁅left.toCWord.eval value,
        leafOccurrenceZ value m right leaf⁆

@[simp] theorem leaf_z_cast
    {α : Type u} {G : Type v} [Group G]
    (value : α → G) (m : ℕ)
    {tree : HallTree α} (leaf : LOccur tree) :
    leafOccurrenceZ value (m : ℤ) tree leaf =
      leafOccurrencePow value m tree leaf := by
  induction leaf with
  | atom =>
      simp [leafOccurrenceZ, leafOccurrencePow]
  | left leaf ih =>
      simp [leafOccurrenceZ, leafOccurrencePow, ih]
  | right leaf ih =>
      simp [leafOccurrenceZ, leafOccurrencePow, ih]

@[simp] theorem eval_leaf_pow
    {α : Type u} {G : Type v} {H : Type*}
    [Group G] [Group H]
    (f : G →* H) (value : α → G) (m : ℕ)
    {tree : HallTree α} (leaf : LOccur tree) :
    f (leafOccurrencePow value m tree leaf) =
      leafOccurrencePow (fun a => f (value a)) m tree leaf := by
  induction leaf with
  | atom =>
      simp [leafOccurrencePow]
  | left leaf ih =>
      rw [leafOccurrencePow, leafOccurrencePow,
        map_commutatorElement, ih, CWord.map_eval]
  | right leaf ih =>
      rw [leafOccurrencePow, leafOccurrencePow,
        map_commutatorElement, ih, CWord.map_eval]

@[simp] theorem leaf_z_pow
    {α : Type u} {G : Type v} {H : Type*}
    [Group G] [Group H]
    (f : G →* H) (value : α → G) (m : ℤ)
    {tree : HallTree α} (leaf : LOccur tree) :
    f (leafOccurrenceZ value m tree leaf) =
      leafOccurrenceZ (fun a => f (value a)) m tree leaf := by
  induction leaf with
  | atom =>
      simp [leafOccurrenceZ]
  | left leaf ih =>
      rw [leafOccurrenceZ, leafOccurrenceZ,
        map_commutatorElement, ih, CWord.map_eval]
  | right leaf ih =>
      rw [leafOccurrenceZ, leafOccurrenceZ,
        map_commutatorElement, ih, CWord.map_eval]

@[simp] theorem leaf_occurrence_one
    {α : Type u} {G : Type v} [Group G]
    (value : α → G)
    {tree : HallTree α} (leaf : LOccur tree) :
    leafOccurrencePow value 1 tree leaf =
      tree.toCWord.eval value := by
  induction leaf with
  | atom =>
      simp [leafOccurrencePow, HallTree.toCWord]
  | left leaf ih =>
      simp [leafOccurrencePow, HallTree.toCWord, ih]
  | right leaf ih =>
      simp [leafOccurrencePow, HallTree.toCWord, ih]

@[simp] theorem eval_leaf_occurrence
    {α : Type u} {G : Type v} [Group G]
    (value : α → G) (m : ℕ)
    {tree : HallTree α} (leaf : LOccur tree)
    (hpow : value leaf.label ^ m = 1) :
    leafOccurrencePow value m tree leaf = 1 := by
  induction leaf with
  | atom =>
      simpa [leafOccurrencePow] using hpow
  | left leaf ih =>
      have ih' := ih (by simpa [LOccur.label] using hpow)
      simp [leafOccurrencePow, ih']
  | right leaf ih =>
      have ih' := ih (by simpa [LOccur.label] using hpow)
      simp [leafOccurrencePow, ih']

@[simp] theorem leaf_z_zpow
    {α : Type u} {G : Type v} [Group G]
    (value : α → G) (m : ℤ)
    {tree : HallTree α} (leaf : LOccur tree)
    (hpow : value leaf.label ^ m = 1) :
    leafOccurrenceZ value m tree leaf = 1 := by
  induction leaf with
  | atom =>
      simpa [leafOccurrenceZ] using hpow
  | left leaf ih =>
      have ih' := ih (by simpa [LOccur.label] using hpow)
      simp [leafOccurrenceZ, ih']
  | right leaf ih =>
      have ih' := ih (by simpa [LOccur.label] using hpow)
      simp [leafOccurrenceZ, ih']

private theorem mul_inv_trans
    {G : Type v} [Group G]
    (K : Subgroup G) [K.Normal]
    {x y z : G}
    (hxy : x * y⁻¹ ∈ K)
    (hyz : y * z⁻¹ ∈ K) :
    x * z⁻¹ ∈ K := by
  rw [mul_inv_quotient K] at hxy hyz ⊢
  exact hxy.trans hyz

private theorem element_lower_series
    {G : Type v} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
  lower_commutator_succ i j
    (Subgroup.commutator_mem_commutator hx hy)

private theorem congr_inv_series
    {G : Type v} [Group G]
    {i j : ℕ}
    {x y z : G}
    (hxy : x * y⁻¹ ∈ Subgroup.lowerCentralSeries G i)
    (hz : z ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, z⁆ * ⁅y, z⁆⁻¹ ∈ Subgroup.lowerCentralSeries G (i + j + 1) := by
  let L : Subgroup G := Subgroup.lowerCentralSeries G (i + j + 1)
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  let k : G := x * y⁻¹
  have hkz : ⁅k, z⁆ ∈ L := by
    simpa [L, k] using
      element_lower_series hxy hz
  have hyz :
      ⁅y, z⁆ ∈ Subgroup.lowerCentralSeries G (j + 1) := by
    simpa using
      element_lower_series
        (i := 0) (j := j) (x := y) (y := z) (by simp) hz
  have hkyz : ⁅k, ⁅y, z⁆⁆ ∈ L := by
    have hmem :
        ⁅k, ⁅y, z⁆⁆ ∈ Subgroup.lowerCentralSeries G (i + (j + 1) + 1) :=
      element_lower_series hxy hyz
    exact Subgroup.lowerCentralSeries_antitone (by omega) hmem
  have hkzComm : Commute (q k) (q z) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅k, z⁆).mpr hkz
  have hkyzComm : Commute (q k) ⁅q y, q z⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅k, ⁅y, z⁆⁆).mpr hkyz
  have hx : q x = q k * q y := by
    simp [q, k]
  rw [mul_inv_quotient L]
  calc
    q ⁅x, z⁆ = ⁅q x, q z⁆ := by rw [map_commutatorElement]
    _ = ⁅q k * q y, q z⁆ := by rw [hx]
    _ = q k * ⁅q y, q z⁆ * (q k)⁻¹ * ⁅q k, q z⁆ := by
      rw [element_mul_left]
    _ = ⁅q y, q z⁆ := by
      rw [commutatorElement_eq_one_iff_commute.mpr hkzComm, mul_one,
        hkyzComm.eq, mul_inv_cancel_right]
    _ = q ⁅y, z⁆ := by rw [map_commutatorElement]

private theorem element_congr_series
    {G : Type v} [Group G]
    {i j : ℕ}
    {x y z : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hyz : y * z⁻¹ ∈ Subgroup.lowerCentralSeries G j) :
    ⁅x, y⁆ * ⁅x, z⁆⁻¹ ∈ Subgroup.lowerCentralSeries G (i + j + 1) := by
  let L : Subgroup G := Subgroup.lowerCentralSeries G (i + j + 1)
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  let k : G := y * z⁻¹
  have hxk : ⁅x, k⁆ ∈ L := by
    simpa [L, k] using
      element_lower_series hx hyz
  have hxz :
      ⁅x, z⁆ ∈ Subgroup.lowerCentralSeries G (i + 1) := by
    simpa using
      element_lower_series
        (i := i) (j := 0) (x := x) (y := z) hx (by simp)
  have hkhxz : ⁅k, ⁅x, z⁆⁆ ∈ L := by
    have hmem :
        ⁅k, ⁅x, z⁆⁆ ∈ Subgroup.lowerCentralSeries G (j + (i + 1) + 1) :=
      element_lower_series hyz hxz
    exact Subgroup.lowerCentralSeries_antitone (by omega) hmem
  have hxkComm : Commute (q x) (q k) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅x, k⁆).mpr hxk
  have hkhxzComm : Commute (q k) ⁅q x, q z⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅k, ⁅x, z⁆⁆).mpr hkhxz
  have hy : q y = q k * q z := by
    simp [q, k]
  rw [mul_inv_quotient L]
  calc
    q ⁅x, y⁆ = ⁅q x, q y⁆ := by rw [map_commutatorElement]
    _ = ⁅q x, q k * q z⁆ := by rw [hy]
    _ = ⁅q x, q k⁆ * q k * ⁅q x, q z⁆ * (q k)⁻¹ := by
      rw [element_mul_right]
    _ = ⁅q x, q z⁆ := by
      rw [commutatorElement_eq_one_iff_commute.mpr hxkComm, one_mul,
        hkhxzComm.eq, mul_inv_cancel_right]
    _ = q ⁅x, z⁆ := by rw [map_commutatorElement]

private theorem commutator_zpow_commute
    {G : Type v} [Group G]
    {x y : G}
    (hcomm : Commute x ⁅x, y⁆) :
    ∀ m : ℤ, ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m
  | .ofNat m => by
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
        element_left_commute hcomm m
  | .negSucc m => by
      have hinv :
          ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
        calc
          ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
            simp only [commutatorElement_def, inv_inv, mul_inv_rev]
            group
          _ = ⁅x, y⁆⁻¹ := by
            rw [(hcomm.inv_left.inv_right).eq]
            simp
      have hcommInv :
          Commute x⁻¹ ⁅x⁻¹, y⁆ := by
        rw [hinv]
        exact hcomm.inv_left.inv_right
      simpa only [zpow_negSucc, ← inv_pow, hinv] using
        element_left_commute hcommInv (m + 1)

private theorem element_zpow_commute
    {G : Type v} [Group G]
    {x y : G}
    (hcomm : Commute y ⁅x, y⁆) :
    ∀ m : ℤ, ⁅x, y ^ m⁆ = ⁅x, y⁆ ^ m
  | .ofNat m => by
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
        commutator_element_commute hcomm m
  | .negSucc m => by
      have hinv :
          ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
        calc
          ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            simp only [commutatorElement_def, inv_inv, mul_inv_rev]
            group
          _ = ⁅x, y⁆⁻¹ := by
            rw [(hcomm.inv_left.inv_right).eq]
            simp
      have hcommInv :
          Commute y⁻¹ ⁅x, y⁻¹⁆ := by
        rw [hinv]
        exact hcomm.inv_left.inv_right
      simpa only [zpow_negSucc, ← inv_pow, hinv] using
        commutator_element_commute hcommInv (m + 1)

private theorem
    inv_zpow_series
    {G : Type v} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (m : ℤ) :
    ⁅x ^ m, y⁆ * (⁅x, y⁆ ^ m)⁻¹ ∈
      Subgroup.lowerCentralSeries G (2 * i + j + 2) := by
  let K : Subgroup G := Subgroup.lowerCentralSeries G (2 * i + j + 2)
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    element_lower_series hx hy
  have hnested :
      ⁅x, ⁅x, y⁆⁆ ∈ K := by
    have hmem :
        ⁅x, ⁅x, y⁆⁆ ∈
          Subgroup.lowerCentralSeries G (i + (i + j + 1) + 1) :=
      element_lower_series hx hxy
    simpa [K, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  have hcomm :
      Commute (q x) ⁅q x, q y⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅x, ⁅x, y⁆⁆).mpr hnested
  rw [mul_inv_quotient K]
  simpa only [map_commutatorElement, map_zpow] using
    commutator_zpow_commute hcomm m

private theorem
    element_zpow_series
    {G : Type v} [Group G]
    {i j : ℕ}
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i)
    (hy : y ∈ Subgroup.lowerCentralSeries G j)
    (m : ℤ) :
    ⁅x, y ^ m⁆ * (⁅x, y⁆ ^ m)⁻¹ ∈
      Subgroup.lowerCentralSeries G (i + 2 * j + 2) := by
  let K : Subgroup G := Subgroup.lowerCentralSeries G (i + 2 * j + 2)
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries G (i + j + 1) :=
    element_lower_series hx hy
  have hnested :
      ⁅y, ⁅x, y⁆⁆ ∈ K := by
    have hmem :
        ⁅y, ⁅x, y⁆⁆ ∈
          Subgroup.lowerCentralSeries G (j + (i + j + 1) + 1) :=
      element_lower_series hy hxy
    simpa [K, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem
  have hcomm :
      Commute (q y) ⁅q x, q y⁆ := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅y, ⁅x, y⁆⁆).mpr hnested
  rw [mul_inv_quotient K]
  simpa only [map_commutatorElement, map_zpow] using
    element_zpow_commute hcomm m

/-- Powering one leaf occurrence scales the leading lower-central class of
the whole tree.  The error lies one lower-central level beyond the tree's
ordinary weight. -/
theorem leaf_occurrence_series
    {α : Type u} {G : Type v} [Group G]
    (value : α → G) :
    ∀ (tree : HallTree α) (leaf : LOccur tree) (m : ℕ),
      leafOccurrencePow value m tree leaf *
          (tree.toCWord.eval value ^ m)⁻¹ ∈
        Subgroup.lowerCentralSeries G tree.weight := by
  intro tree leaf m
  induction leaf with
  | atom =>
      simp [leafOccurrencePow, HallTree.toCWord]
  | @left left right leaf ih =>
      have hleftPos := left.weight_pos
      have hrightPos := right.weight_pos
      have hright :
          right.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (right.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            right.toCWord)
      have hcongr :
          ⁅leafOccurrencePow value m left leaf,
              right.toCWord.eval value⁆ *
              ⁅left.toCWord.eval value ^ m,
                right.toCWord.eval value⁆⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) := by
        have hindex :
            left.weight + (right.weight - 1) + 1 =
              left.weight + right.weight := by
          omega
        simpa only [hindex] using
          congr_inv_series
            ih hright
      have hleft :
          left.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (left.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            left.toCWord)
      have hpowerRaw :
          ⁅left.toCWord.eval value ^ m,
              right.toCWord.eval value⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G
              (2 * (left.weight - 1) + (right.weight - 1) + 2) :=
        inv_commutator_series
          hleft hright m
      have hpower :
          ⁅left.toCWord.eval value ^ m,
              right.toCWord.eval value⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) :=
        Subgroup.lowerCentralSeries_antitone (by omega) hpowerRaw
      simpa [leafOccurrencePow, HallTree.toCWord] using
        mul_inv_trans
          (Subgroup.lowerCentralSeries G (left.weight + right.weight))
          hcongr hpower
  | @right left right leaf ih =>
      have hleftPos := left.weight_pos
      have hrightPos := right.weight_pos
      have hleft :
          left.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (left.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            left.toCWord)
      have hcongr :
          ⁅left.toCWord.eval value,
              leafOccurrencePow value m right leaf⁆ *
              ⁅left.toCWord.eval value,
                right.toCWord.eval value ^ m⁆⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) := by
        have hindex :
            (left.weight - 1) + right.weight + 1 =
              left.weight + right.weight := by
          omega
        simpa only [hindex] using
          element_congr_series
            hleft ih
      have hright :
          right.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (right.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            right.toCWord)
      have hpowerRaw :
          ⁅left.toCWord.eval value,
              right.toCWord.eval value ^ m⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G
              ((left.weight - 1) + 2 * (right.weight - 1) + 2) :=
        inv_element_series
          hleft hright m
      have hpower :
          ⁅left.toCWord.eval value,
              right.toCWord.eval value ^ m⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) :=
        Subgroup.lowerCentralSeries_antitone (by omega) hpowerRaw
      simpa [leafOccurrencePow, HallTree.toCWord] using
        mul_inv_trans
          (Subgroup.lowerCentralSeries G (left.weight + right.weight))
          hcongr hpower

/-- Powering one leaf occurrence by an arbitrary integer scales the leading
lower-central class of the whole tree.  The error lies one lower-central
level beyond the tree's ordinary weight. -/
theorem leaf_occurrence_z
    {α : Type u} {G : Type v} [Group G]
    (value : α → G) :
    ∀ (tree : HallTree α) (leaf : LOccur tree) (m : ℤ),
      leafOccurrenceZ value m tree leaf *
          (tree.toCWord.eval value ^ m)⁻¹ ∈
        Subgroup.lowerCentralSeries G tree.weight := by
  intro tree leaf m
  induction leaf with
  | atom =>
      simp [leafOccurrenceZ, HallTree.toCWord]
  | @left left right leaf ih =>
      have hleftPos := left.weight_pos
      have hrightPos := right.weight_pos
      have hright :
          right.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (right.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            right.toCWord)
      have hcongr :
          ⁅leafOccurrenceZ value m left leaf,
              right.toCWord.eval value⁆ *
              ⁅left.toCWord.eval value ^ m,
                right.toCWord.eval value⁆⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) := by
        have hindex :
            left.weight + (right.weight - 1) + 1 =
              left.weight + right.weight := by
          omega
        simpa only [hindex] using
          congr_inv_series
            ih hright
      have hleft :
          left.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (left.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            left.toCWord)
      have hpowerRaw :
          ⁅left.toCWord.eval value ^ m,
              right.toCWord.eval value⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G
              (2 * (left.weight - 1) + (right.weight - 1) + 2) :=
        inv_zpow_series
          hleft hright m
      have hpower :
          ⁅left.toCWord.eval value ^ m,
              right.toCWord.eval value⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) :=
        Subgroup.lowerCentralSeries_antitone (by omega) hpowerRaw
      simpa [leafOccurrenceZ, HallTree.toCWord] using
        mul_inv_trans
          (Subgroup.lowerCentralSeries G (left.weight + right.weight))
          hcongr hpower
  | @right left right leaf ih =>
      have hleftPos := left.weight_pos
      have hrightPos := right.weight_pos
      have hleft :
          left.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (left.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            left.toCWord)
      have hcongr :
          ⁅left.toCWord.eval value,
              leafOccurrenceZ value m right leaf⁆ *
              ⁅left.toCWord.eval value,
                right.toCWord.eval value ^ m⁆⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) := by
        have hindex :
            (left.weight - 1) + right.weight + 1 =
              left.weight + right.weight := by
          omega
        simpa only [hindex] using
          element_congr_series
            hleft ih
      have hright :
          right.toCWord.eval value ∈
            Subgroup.lowerCentralSeries G (right.weight - 1) := by
        simpa using
          (CWord.eval_lower_series
            value (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
            right.toCWord)
      have hpowerRaw :
          ⁅left.toCWord.eval value,
              right.toCWord.eval value ^ m⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G
              ((left.weight - 1) + 2 * (right.weight - 1) + 2) :=
        element_zpow_series
          hleft hright m
      have hpower :
          ⁅left.toCWord.eval value,
              right.toCWord.eval value ^ m⁆ *
              (⁅left.toCWord.eval value,
                right.toCWord.eval value⁆ ^ m)⁻¹ ∈
            Subgroup.lowerCentralSeries G (left.weight + right.weight) :=
        Subgroup.lowerCentralSeries_antitone (by omega) hpowerRaw
      simpa [leafOccurrenceZ, HallTree.toCWord] using
        mul_inv_trans
          (Subgroup.lowerCentralSeries G (left.weight + right.weight))
          hcongr hpower

end HallTree

end P1960
end Struik

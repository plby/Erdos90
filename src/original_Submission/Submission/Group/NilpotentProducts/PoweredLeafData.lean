import Submission.Group.NilpotentProducts.ArbitraryCutoffCover

open scoped IsMulCommutative


/-!
# Struik's Lemma 1 from powered-leaf Hall coordinates

The downward induction in Lemma 1 uses only the following consequence of
Lemma H2.  After one leaf of a weight-`r` Hall commutator is replaced by its
`a`th power:

* all coordinates below weight `r` vanish;
* the weight-`r` coordinate is `a` on the original factor and zero elsewhere;
* every higher coordinate is divisible by `a`;
* a higher coordinate vanishes unless its Hall tree still uses the replaced
  leaf.

This file packages those assertions and proves that they imply the recursive
Hall-factor order bound used in Theorem 3.
-/

namespace Struik
namespace P1960

open Submission
open Submission.HallTree
open Submission.TCTex

universe u

/-- The powered-leaf coordinate statement extracted from Lemma H2, in the
canonical Hall basis of the free nilpotent truncation. -/
def PoweredLeafHall
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (_hr : 1 ≤ r) (_hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i)),
    let a := order leaf.label.down
    let y :=
      HallTree.leafOccurrencePow
        (freeTruncationValue t n) a
        (concreteBasicTree i) leaf
    (∀ (s : ℕ), 1 ≤ s → s < r → s < n →
      standardHallCoordinates t n (by omega) y s = 0) ∧
    (∀ j : (standardHallFamily.{u} t r).index,
      standardHallCoordinates t n (by omega) y r j =
        if j = i then (a : ℤ) else 0) ∧
    (∀ (s : ℕ), r < s → s < n →
      ∀ j : (standardHallFamily.{u} t s).index,
        (a : ℤ) ∣ standardHallCoordinates t n (by omega) y s j) ∧
    (∀ (s : ℕ), r < s → s < n →
      ∀ j : (standardHallFamily.{u} t s).index,
        ¬hallTreeUses leaf.label (concreteBasicTree j) →
          standardHallCoordinates t n (by omega) y s j = 0)

/-- The genuinely higher-weight part of Lemma H2 needed by Lemma 1.  The
below-weight vanishing and leading coordinate will be derived separately
from the powered-leaf congruence. -/
def PoweredLeafHigher
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (_hr : 1 ≤ r) (_hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i)),
    let a := order leaf.label.down
    let y :=
      HallTree.leafOccurrencePow
        (freeTruncationValue t n) a
        (concreteBasicTree i) leaf
    (∀ (s : ℕ), r < s → s < n →
      ∀ j : (standardHallFamily.{u} t s).index,
        (a : ℤ) ∣ standardHallCoordinates t n (by omega) y s j) ∧
    (∀ (s : ℕ), r < s → s < n →
      ∀ j : (standardHallFamily.{u} t s).index,
        ¬hallTreeUses leaf.label (concreteBasicTree j) →
          standardHallCoordinates t n (by omega) y s j = 0)

/-- Polynomial degree part of Lemma H2 for the powered-leaf coordinates.
Struik's degree is the target weight minus `r - 1`. -/
def PoweredLeafCoordinate
    (t n : ℕ) : Prop :=
  ∀ (r : ℕ) (_hr : 1 ≤ r) (_hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (s : ℕ) (_hrs : r < s) (_hsn : s < n)
    (j : (standardHallFamily.{u} t s).index),
    IVMost
      (fun q : ℕ =>
        standardHallCoordinates t n (by omega)
          (HallTree.leafOccurrencePow
            (freeTruncationValue t n) q
            (concreteBasicTree i) leaf)
          s j)
      (s - (r - 1))

/-- Support part of Lemma H2: every nonzero higher correction still uses the
leaf occurrence that was powered. -/
def PoweredSupportData
    (t n : ℕ) : Prop :=
  ∀ (r : ℕ) (_hr : 1 ≤ r) (_hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (q s : ℕ) (_hrs : r < s) (_hsn : s < n)
    (j : (standardHallFamily.{u} t s).index),
    ¬hallTreeUses leaf.label (concreteBasicTree j) →
      standardHallCoordinates t n (by omega)
        (HallTree.leafOccurrencePow
          (freeTruncationValue t n) q
          (concreteBasicTree i) leaf)
        s j =
      0

/-- Polynomial part of Lemma H2 for an arbitrary parenthesized commutator
tree, rather than only for a standard Hall basis tree. -/
def TreePoweredLeaf
    (t n : ℕ) : Prop :=
  ∀ (tree : HallTree (FreeGenerator.{u} t))
    (_hrn : tree.weight < n)
    (leaf : HallTree.LOccur tree)
    (s : ℕ) (_hrs : tree.weight < s) (_hsn : s < n)
    (j : (standardHallFamily.{u} t s).index),
    IVMost
      (fun q : ℕ =>
        standardHallCoordinates t n (by omega)
          (HallTree.leafOccurrencePow
            (freeTruncationValue t n) q tree leaf)
          s j)
      (s - (tree.weight - 1))

/-- Support part of Lemma H2 for an arbitrary parenthesized commutator tree.
Every nonzero higher correction still uses the powered leaf's generator. -/
def PoweredLeafSupport
    (t n : ℕ) : Prop :=
  ∀ (tree : HallTree (FreeGenerator.{u} t))
    (_hrn : tree.weight < n)
    (leaf : HallTree.LOccur tree)
    (q s : ℕ) (_hrs : tree.weight < s) (_hsn : s < n)
    (j : (standardHallFamily.{u} t s).index),
    ¬hallTreeUses leaf.label (concreteBasicTree j) →
      standardHallCoordinates t n (by omega)
        (HallTree.leafOccurrencePow
          (freeTruncationValue t n) q tree leaf)
        s j =
      0

private theorem zpow_cast_dvd
    {G : Type*} [Group G] (g : G) {m : ℕ} {e : ℤ}
    (hdvd : (m : ℤ) ∣ e)
    (hm : g ^ m = 1) :
    g ^ e = 1 := by
  rcases hdvd with ⟨k, rfl⟩
  rw [zpow_mul, zpow_natCast, hm, one_zpow]

theorem list_prod_except
    {ι : Type*} {G : Type*} [Group G]
    (l : List ι) (f : ι → G) (i : ι)
    (hi : i ∈ l) (hnodup : l.Nodup)
    (hother : ∀ j ∈ l, j ≠ i → f j = 1) :
    (l.map f).prod = f i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hi
      rcases hi with hij | hi
      · subst j
        have htail : (l.map f).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          rcases List.mem_map.mp hx with ⟨k, hk, rfl⟩
          exact hother k (by simp [hk]) (by
            intro hki
            exact hnodup.1 (hki ▸ hk))
        simp [htail]
      · have hj : f j = 1 :=
          hother j (by simp) (by
            intro hji
            subst j
            exact hnodup.1 hi)
        rw [hj, one_mul]
        exact ih hi hnodup.2
          (fun k hk hki => hother k (by simp [hk]) hki)

theorem mapped_standard_single
    {t n r : ℕ} (order : Fin t → ℕ)
    (e : (standardHallFamily.{u} t r).index → ℤ)
    (i : (standardHallFamily.{u} t r).index)
    (hother :
      ∀ j : (standardHallFamily.{u} t r).index, j ≠ i →
        inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t r).commutator j
              |>.freeLowerTruncation (n := n)) ^ e j =
          1) :
    inverseFreeTruncation.{u} order n
        ((standardHallFamily.{u} t r).collectedWeightProduct
          (n := n) e) =
      inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := n)) ^ e i := by
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  simp only [List.map_map]
  let f : (standardHallFamily.{u} t r).index →
      NilpotentCyclicProduct order n :=
    fun j =>
      inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator j
            |>.freeLowerTruncation (n := n)) ^ e j
  have hresult :
      ((Finset.univ.sort fun j k :
        (standardHallFamily.{u} t r).index => j ≤ k).map f).prod =
        f i := by
    apply list_prod_except
    · simp
    · exact Finset.sort_nodup _ _
    · intro j _hj hji
      exact hother j hji
  rw [show
      (List.map
        (⇑(inverseFreeTruncation.{u} order n) ∘
          Subtype.val ∘ fun j =>
            ((standardHallFamily.{u} t r).commutator j
              |>.evalin_freelower_centtrunterm (n := n)) ^ e j)
        (Finset.univ.sort fun j k :
          (standardHallFamily.{u} t r).index => j ≤ k)).prod =
        ((Finset.univ.sort fun j k :
          (standardHallFamily.{u} t r).index => j ≤ k).map f).prod by
      apply congrArg List.prod
      apply List.map_congr_left
      intro j _hj
      change
        inverseFreeTruncation.{u} order n
            (((standardHallFamily.{u} t r).commutator j
              |>.freeLowerTruncation (n := n)) ^ e j) =
          f j
      simp [f, map_zpow]]
  exact hresult

private theorem mapped_standard_factors
    {t n r : ℕ} (order : Fin t → ℕ)
    (e : (standardHallFamily.{u} t r).index → ℤ)
    (hfactor :
      ∀ j : (standardHallFamily.{u} t r).index,
        inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t r).commutator j
              |>.freeLowerTruncation (n := n)) ^ e j =
          1) :
    inverseFreeTruncation.{u} order n
        ((standardHallFamily.{u} t r).collectedWeightProduct
          (n := n) e) =
      1 := by
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  simp only [List.map_map]
  apply List.prod_eq_one
  intro x hx
  rcases List.mem_map.mp hx with ⟨j, _hj, rfl⟩
  change
    inverseFreeTruncation.{u} order n
        (((standardHallFamily.{u} t r).commutator j
          |>.freeLowerTruncation (n := n)) ^ e j) =
      1
  rw [map_zpow]
  exact hfactor j

private theorem mapped_standard_weight
    {t n r : ℕ} (order : Fin t → ℕ)
    (e : StandardExponentFamily.{u} t)
    (hr : 1 ≤ r) (hrn : r < n)
    (hother :
      ∀ s : ℕ, 1 ≤ s → s < n → s ≠ r →
        inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t s).collectedWeightProduct
              (n := n) (e s)) =
          1) :
    inverseFreeTruncation.{u} order n
        (standardHallProduct t n e) =
      inverseFreeTruncation.{u} order n
        ((standardHallFamily.{u} t r).collectedWeightProduct
          (n := n) (e r)) := by
  unfold standardHallProduct collectedHallProduct
  rw [collectedPrefixProduct, map_list_prod]
  simp only [List.map_map]
  let f : ℕ → NilpotentCyclicProduct order n :=
    fun j =>
      inverseFreeTruncation.{u} order n
        ((standardHallFamily.{u} t (j + 1)).collectedWeightProduct
          (n := n) (e (j + 1)))
  have hrsub : r - 1 + 1 = r := by omega
  have hresult :
      ((List.range (n - 1)).map f).prod = f (r - 1) := by
    apply list_prod_except
    · simp
      omega
    · exact List.nodup_range
    · intro j hj hjr
      have hjlt : j < n - 1 := List.mem_range.mp hj
      have hweightNe : j + 1 ≠ r := by omega
      exact hother (j + 1) (by omega) (by omega) hweightNe
  rw [← hrsub]
  simpa only [f, Function.comp_apply] using hresult

theorem leaf_occurrence_uses
    {α : Type*} {a : α} :
    ∀ {tree : HallTree α}, hallTreeUses a tree →
      ∃ leaf : HallTree.LOccur tree, leaf.label = a
  | .atom b, huses => by
      exact ⟨.atom b, huses⟩
  | .commutator left right, huses => by
      rcases huses with hleft | hright
      · obtain ⟨leaf, hleaf⟩ :=
          leaf_occurrence_uses hleft
        exact ⟨.left leaf, hleaf⟩
      · obtain ⟨leaf, hleaf⟩ :=
          leaf_occurrence_uses hright
        exact ⟨.right leaf, hleaf⟩

/-- Congruence modulo the next lower-central layer forces equality of the
coordinates in the current layer. -/
theorem coordinates_inv_next
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (x y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hxy :
      x * y⁻¹ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r) :
    normalFormCoordinates hn H hH x r =
      normalFormCoordinates hn H hH y r := by
  let N :=
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  have hyInv :
      y⁻¹ ∈ Subgroup.lowerCentralSeries N (r - 1) :=
    (Subgroup.lowerCentralSeries N (r - 1)).inv_mem hy
  have hxyAdd :=
    normal_form_coordinates
      hn H hH hr hrn x y⁻¹ hx hyInv
  have hyyAdd :=
    normal_form_coordinates
      hn H hH hr hrn y y⁻¹ hy hyInv
  funext i
  have hxyZero :
      normalFormCoordinates hn H hH (x * y⁻¹) r i = 0 :=
    lower_central_series
      (r := r + 1) (s := r) hn H hH (x * y⁻¹)
      (by simpa using hxy) hr (by omega) hrn i
  have hyyZero :
      normalFormCoordinates hn H hH (y * y⁻¹) r i = 0 := by
    rw [mul_inv_cancel]
    exact coordinate_one_zero hn H hH hr hrn i
  have hxyAddAt := congrFun hxyAdd i
  have hyyAddAt := congrFun hyyAdd i
  omega

/-- For an arbitrary commutator tree, powering one selected leaf occurrence
does not change coordinates below the tree weight, and multiplies the whole
leading coordinate vector by the power.  This is the arbitrary-parenthesis
leading term in Struik's Lemma H2. -/
theorem powered_leaf_leading
    {t n : ℕ}
    (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (hrn : tree.weight < n)
    (leaf : HallTree.LOccur tree)
    (m : ℕ) :
    let y :=
      HallTree.leafOccurrencePow
        (freeTruncationValue t n) m tree leaf
    let base :=
      tree.toCWord.eval
        (freeTruncationValue t n)
    (∀ (s : ℕ), 1 ≤ s → s < tree.weight → s < n →
      standardHallCoordinates t n hn y s = 0) ∧
    standardHallCoordinates t n hn y tree.weight =
      fun j =>
        (m : ℤ) *
          standardHallCoordinates t n hn base tree.weight j := by
  let H := standardHallFamily.{u} t
  let hH :
      ∀ s : ℕ, 1 ≤ s → s < n →
        (H s).FormsAssocGradedbasis (n := n) :=
    fun s _hs hsn =>
      standard_forms_associated t n s (by omega) hsn
  let y :=
    HallTree.leafOccurrencePow
      (freeTruncationValue t n) m tree leaf
  let base :=
    tree.toCWord.eval
      (freeTruncationValue t n)
  have hr : 1 ≤ tree.weight := tree.weight_pos
  have hscaled :
      y * (base ^ m)⁻¹ ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          tree.weight := by
    exact
      HallTree.leaf_occurrence_series
        (freeTruncationValue t n) tree leaf m
  have hbase :
      base ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
        (tree.weight - 1) := by
    simpa [base] using
      (CWord.eval_lower_series
        (freeTruncationValue t n)
        (fun _ => 1) (fun _ => by simp) (fun _ => by simp)
        tree.toCWord)
  have hpow :
      base ^ m ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
        (tree.weight - 1) :=
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
      (tree.weight - 1)).pow_mem hbase m
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
        (tree.weight - 1) := by
    have hscaled' :
        y * (base ^ m)⁻¹ ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
            (tree.weight - 1) :=
      Subgroup.lowerCentralSeries_antitone (by omega) hscaled
    rw [show y = (y * (base ^ m)⁻¹) * base ^ m by group]
    exact
      (Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
        (tree.weight - 1)).mul_mem hscaled' hpow
  constructor
  · intro s hs hsr hsn
    funext j
    exact lower_central_series
      hn H hH y hy hs hsr hsn j
  · calc
      standardHallCoordinates t n hn y tree.weight =
          standardHallCoordinates t n hn (base ^ m) tree.weight := by
            exact coordinates_inv_next
              hn H hH hr hrn y (base ^ m) hy hpow hscaled
      _ = fun j =>
          (m : ℤ) *
            standardHallCoordinates t n hn base tree.weight j := by
              exact
                form_coordinates_series
                  hn H hH hr hrn base hbase m

/-- Replacing one leaf occurrence by an `m`th power has no coordinates below
the original weight and has leading coordinate `m` on the original Hall
factor. -/
theorem powered_coordinates_leading
    {t n r : ℕ}
    (hn : 2 ≤ n)
    (hr : 1 ≤ r) (hrn : r < n)
    (i : (standardHallFamily.{u} t r).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (m : ℕ) :
    let y :=
      HallTree.leafOccurrencePow
        (freeTruncationValue t n) m
        (concreteBasicTree i) leaf
    (∀ (s : ℕ), 1 ≤ s → s < r → s < n →
      standardHallCoordinates t n hn y s = 0) ∧
    ∀ j : (standardHallFamily.{u} t r).index,
      standardHallCoordinates t n hn y r j =
        if j = i then (m : ℤ) else 0 := by
  let H := standardHallFamily.{u} t
  let hH :
      ∀ s : ℕ, 1 ≤ s → s < n →
        (H s).FormsAssocGradedbasis (n := n) :=
    fun s _hs hsn =>
      standard_forms_associated t n s (by omega) hsn
  let tree := concreteBasicTree i
  let y :=
    HallTree.leafOccurrencePow
      (freeTruncationValue t n) m tree leaf
  let base :=
    (standardHallFamily.{u} t r).commutator i
      |>.freeLowerTruncation (n := n)
  have hscaled :
      y * (base ^ m)⁻¹ ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n) r := by
    simpa [y, base, tree,
      BCWt.freeLowerTruncation,
      concrete_basic_word,
      concrete_tree_weight] using
      HallTree.leaf_occurrence_series
        (freeTruncationValue t n)
        (concreteBasicTree i) leaf m
  have hbase :
      base ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n) (r - 1) :=
    (standardHallFamily.{u} t r).commutator i
      |>.free_truncation_series
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n) (r - 1) := by
    have hscaled' :
        y * (base ^ m)⁻¹ ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
              (r - 1) :=
      Subgroup.lowerCentralSeries_antitone (by omega) hscaled
    have hpow :
        base ^ m ∈ Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
            (r - 1) :=
      (Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          (r - 1)).pow_mem hbase m
    rw [show y = (y * (base ^ m)⁻¹) * base ^ m by group]
    exact
      (Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n)
          (r - 1)).mul_mem hscaled' hpow
  constructor
  · intro s hs hsr hsn
    funext j
    exact lower_central_series
      hn H hH y hy hs hsr hsn j
  · let leading : (H r).index → ℤ :=
      fun j => if j = i then (m : ℤ) else 0
    let N : Type u :=
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} t)) n
    let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
    let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
    let q : A →* A ⧸ B := QuotientGroup.mk' B
    letI : IsMulCommutative (AssociatedGradedLayer N r) :=
      associated_graded_commutative r
    letI : CommGroup (AssociatedGradedLayer N r) :=
      { (inferInstance : Group (AssociatedGradedLayer N r)) with
        mul_comm := mul_comm' }
    let yTerm : A := ⟨y, hy⟩
    let baseTerm : A := ⟨base, hbase⟩
    have hyClass : q yTerm = q (baseTerm ^ m) := by
      apply (mul_inv_quotient B).mp
      exact hscaled
    have hsegmentClass :
        q ((H r).collected_lower_centralterm (n := n) leading) =
          q (baseTerm ^ m) := by
      rw [(H r).collectedlower_centtermclas_eqmulsum
        (n := n) leading]
      have hsum :
          (∑ j,
              leading j •
                ((H r).commutator j).associatedGradedClass (n := n)) =
            (m : ℤ) •
              ((H r).commutator i).associatedGradedClass (n := n) := by
        classical
        simp [leading]
      rw [hsum]
      change
        Additive.toMul ((m : ℤ) • Additive.ofMul (q baseTerm)) =
          q (baseTerm ^ m)
      rw [map_pow]
      rfl
    have hsegmentInvY :
        ((H r).collectedWeightProduct (n := n) leading)⁻¹ * y ∈
          Subgroup.lowerCentralSeries N r := by
      apply (QuotientGroup.eq_one_iff
        (N := B)
        (((H r).collected_lower_centralterm (n := n) leading)⁻¹ *
          yTerm)).mp
      change
        q (((H r).collected_lower_centralterm (n := n) leading)⁻¹ *
          yTerm) = 1
      rw [map_mul, map_inv, hsegmentClass, hyClass, inv_mul_cancel]
    have hcoordinates :
        normalFormCoordinates hn H hH y r = leading :=
      form_coordinates_next
        hn H hH hr hrn y hy leading hsegmentInvY
    intro j
    change normalFormCoordinates hn H hH y r j =
      if j = i then (m : ℤ) else 0
    rw [hcoordinates]

/-- The powered-leaf congruence supplies the low and leading coordinates, so
only the higher divisibility and support clauses of Lemma H2 need to be
provided separately. -/
theorem powered_leaf_higher
    {t n : ℕ} (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hhigher : PoweredLeafHigher.{u} order n) :
    PoweredLeafHall.{u} order n := by
  intro r hr hrn i leaf
  let a := order leaf.label.down
  let y :=
    HallTree.leafOccurrencePow
      (freeTruncationValue t n) a
      (concreteBasicTree i) leaf
  obtain ⟨hbelow, hleading⟩ :=
    powered_coordinates_leading
      hn hr hrn i leaf a
  obtain ⟨hdivisible, hsupported⟩ :=
    hhigher r hr hrn i leaf
  exact ⟨hbelow, hleading, hdivisible, hsupported⟩

/-- Struik's tame-prime arithmetic converts the polynomial and support
statements in Lemma H2 into the higher-coordinate data used by Lemma 1. -/
theorem powered_leaf_support
    {t n : ℕ} (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (hpolynomial : PoweredLeafCoordinate.{u} t n)
    (hsupport : PoweredSupportData.{u} t n) :
    PoweredLeafHigher.{u} order n := by
  intro r hr hrn i leaf
  let a := order leaf.label.down
  let y :=
    HallTree.leafOccurrencePow
      (freeTruncationValue t n) a
      (concreteBasicTree i) leaf
  constructor
  · intro s hrs hsn j
    have hf :
        IVMost
          (fun q : ℕ =>
            standardHallCoordinates t n hn
              (HallTree.leafOccurrencePow
                (freeTruncationValue t n) q
                (concreteBasicTree i) leaf)
              s j)
          (s - (r - 1)) :=
      hpolynomial r hr hrn i leaf s hrs hsn j
    have hf0 :
        standardHallCoordinates t n hn
            (HallTree.leafOccurrencePow
              (freeTruncationValue t n) 0
              (concreteBasicTree i) leaf)
            s j =
          0 := by
      have hy0 :
          HallTree.leafOccurrencePow
              (freeTruncationValue t n) 0
              (concreteBasicTree i) leaf =
            1 :=
        HallTree.eval_leaf_occurrence
          (freeTruncationValue t n) 0 leaf (by simp)
      rw [hy0]
      simpa [standardHallCoordinates] using
        coordinate_one_zero
          hn (standardHallFamily.{u} t)
          (fun q _hq hqn =>
            standard_forms_associated
              t n q (by omega) hqn)
          (by omega) hsn j
    have hdegree : s - (r - 1) ≤ n - 1 := by omega
    exact tame_valued_degree
      (htame leaf.label.down) hdegree hf hf0
  · intro s hrs hsn j hnotUses
    exact hsupport r hr hrn i leaf a s hrs hsn j hnotUses

/-- Struik's downward induction: the powered-leaf coordinate data from
Lemma H2 implies the recursive Hall-factor order assertion of Lemma 1. -/
theorem powered_leaf_data
    {t n : ℕ} (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hdata : PoweredLeafHall.{u} order n) :
    FactorOrderBound.{u} order n := by
  let P : ℕ → Prop := fun k =>
    ∀ (r : ℕ), 1 ≤ r → r < n → n - r = k →
      ∀ i : (standardHallFamily.{u} t r).index,
        inverseFreeTruncation.{u} order n
              ((standardHallFamily.{u} t r).commutator i
                |>.freeLowerTruncation (n := n)) ^
            generalStandardOrder order i =
          1
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro r hr hrn hkr i
        let tree := concreteBasicTree i
        let g :=
          inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t r).commutator i
              |>.freeLowerTruncation (n := n))
        change
          g ^ hallTreeOrder
              (fun j : FreeGenerator.{u} t => order j.down) tree =
            1
        apply tree_order_uses
        intro generator hgenerator
        obtain ⟨leaf, hleaf⟩ :=
          leaf_occurrence_uses hgenerator
        let a := order leaf.label.down
        let y :=
          HallTree.leafOccurrencePow
            (freeTruncationValue t n) a tree leaf
        let e := standardHallCoordinates t n hn y
        have hcoordinates := hdata r hr hrn i leaf
        change
          (∀ (s : ℕ), 1 ≤ s → s < r → s < n → e s = 0) ∧
            (∀ j : (standardHallFamily.{u} t r).index,
              e r j = if j = i then (a : ℤ) else 0) ∧
            (∀ (s : ℕ), r < s → s < n →
              ∀ j : (standardHallFamily.{u} t s).index,
                (a : ℤ) ∣ e s j) ∧
            (∀ (s : ℕ), r < s → s < n →
              ∀ j : (standardHallFamily.{u} t s).index,
                ¬hallTreeUses leaf.label (concreteBasicTree j) →
                  e s j = 0) at hcoordinates
        rcases hcoordinates with
          ⟨hbelow, hleading, hdivisible, hsupported⟩
        have hmapY :
            inverseFreeTruncation.{u} order n y = 1 := by
          rw [show
              inverseFreeTruncation.{u} order n y =
                HallTree.leafOccurrencePow
                  (fun j =>
                    inverseFreeTruncation.{u} order n
                      (freeTruncationValue t n j))
                  a tree leaf by
                simp [y]]
          apply HallTree.eval_leaf_occurrence
          change
            inverseFreeTruncation.{u} order n
                (lowerCentralTruncation
                  (FreeGroup (FreeGenerator.{u} t)) n
                  (FreeGroup.of leaf.label)) ^ a =
              1
          rw [inverse_truncation_generator]
          simpa [a] using congrArg Inv.inv
            (nilpotent_cyclic_generator
              order n leaf.label.down)
        have hotherWeight :
            ∀ s : ℕ, 1 ≤ s → s < n → s ≠ r →
              inverseFreeTruncation.{u} order n
                  ((standardHallFamily.{u} t s).collectedWeightProduct
                    (n := n) (e s)) =
                1 := by
          intro s hs hsn hsr
          rcases lt_or_gt_of_ne hsr with hlt | hgt
          · have hes : e s = 0 := hbelow s hs hlt hsn
            rw [hes,
              BCWta.collected_weight_productzero,
              map_one]
          · apply mapped_standard_factors
            intro j
            by_cases huses :
                hallTreeUses leaf.label (concreteBasicTree j)
            · have hhigher :
                  inverseFreeTruncation.{u} order n
                        ((standardHallFamily.{u} t s).commutator j
                          |>.freeLowerTruncation (n := n)) ^
                      generalStandardOrder order j =
                    1 := by
                exact ih (n - s) (by omega) s hs hsn rfl j
              have hfactorDvd :
                  generalStandardOrder order j ∣ a :=
                general_standard_uses
                  order j leaf.label huses
              have hcastDvd :
                  (generalStandardOrder order j : ℤ) ∣
                    e s j :=
                (Int.natCast_dvd_natCast.mpr hfactorDvd).trans
                  (hdivisible s hgt hsn j)
              exact zpow_cast_dvd
                _ hcastDvd hhigher
            · rw [hsupported s hgt hsn j huses, zpow_zero]
        have hmapProductWeight :
            inverseFreeTruncation.{u} order n
                (standardHallProduct t n e) =
              inverseFreeTruncation.{u} order n
                ((standardHallFamily.{u} t r).collectedWeightProduct
                  (n := n) (e r)) :=
          mapped_standard_weight
            order e hr hrn hotherWeight
        have hmapWeight :
            inverseFreeTruncation.{u} order n
                ((standardHallFamily.{u} t r).collectedWeightProduct
                  (n := n) (e r)) =
              g ^ (a : ℤ) := by
          rw [mapped_standard_single order (e r) i]
          · rw [hleading i, if_pos rfl]
          · intro j hji
            rw [hleading j, if_neg hji, zpow_zero]
        have heval : standardHallProduct t n e = y :=
          standard_product_coordinates t n hn y
        have hga : g ^ a = 1 := by
          rw [← zpow_natCast, ← hmapWeight, ← hmapProductWeight, heval,
            hmapY]
        simpa [a, hleaf] using hga
  intro r hr hrn i
  exact hP (n - r) r hr hrn rfl i

/-- Lemma 1's Hall-factor order bound follows from the polynomial and support
parts of Lemma H2 under the tame-prime hypothesis. -/
theorem bound_powered_leaf
    {t n : ℕ} (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (hpolynomial : PoweredLeafCoordinate.{u} t n)
    (hsupport : PoweredSupportData.{u} t n) :
    FactorOrderBound.{u} order n :=
  powered_leaf_data
    order hn
      (powered_leaf_higher
        order hn
          (powered_leaf_support
            order hn htame hpolynomial hsupport))

end P1960
end Struik

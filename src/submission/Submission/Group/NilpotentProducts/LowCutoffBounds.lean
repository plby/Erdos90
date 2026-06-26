import Submission.Group.NilpotentProducts.Support
import Submission.Group.NilpotentProducts.LowWeightBasis
import Submission.Group.NilpotentProducts.FreeTruncationCollection
import Submission.Group.Zassenhaus.SignedCorrectionSemantics

/-!
# The polynomial clause of Lemma H2 through cutoff four

Below the class-four cutoff, the only nontrivial higher-coordinate case is a
weight-two basic commutator with one powered leaf.  Struik's Lemma 2 writes
that element as its weight-two factor to the powered exponent followed by one
weight-three factor to a binomial exponent.
-/

namespace Struik
namespace P1960

open Submission
open Submission.HallTree
open Submission.TCTex
open scoped commutatorElement

universe u

private noncomputable def singleExponentFamily
    {t r : ℕ}
    (i : (standardHallFamily.{u} t r).index)
    (z : ℤ) :
    StandardExponentFamily.{u} t :=
  Function.update (0 : StandardExponentFamily.{u} t) r
    (fun j => if j = i then z else 0)

@[simp] private theorem single_exponent_same
    {t r : ℕ}
    (i : (standardHallFamily.{u} t r).index)
    (z : ℤ) :
    singleExponentFamily i z r =
      fun j => if j = i then z else 0 := by
  simp [singleExponentFamily]

private theorem single_exponent_ne
    {t r s : ℕ}
    (i : (standardHallFamily.{u} t r).index)
    (z : ℤ)
    (hsr : s ≠ r) :
    singleExponentFamily i z s = 0 := by
  simp [singleExponentFamily, hsr]

/-- A Hall exponent family supported at one canonical factor evaluates to
that factor's integer power. -/
private theorem standard_single_family
    {t n r : ℕ}
    (i : (standardHallFamily.{u} t r).index)
    (z : ℤ)
    (hr : 1 ≤ r)
    (hrn : r < n) :
    standardHallProduct t n (singleExponentFamily i z) =
      ((standardHallFamily.{u} t r).commutator i
        |>.freeLowerTruncation (n := n)) ^ z := by
  unfold standardHallProduct collectedHallProduct collectedPrefixProduct
  rw [show
      ((List.range (n - 1)).map fun j =>
        (standardHallFamily.{u} t (j + 1)).collectedWeightProduct
          (n := n) (singleExponentFamily i z (j + 1))).prod =
        ((List.range (n - 1)).map fun j =>
          if j = r - 1 then
            ((standardHallFamily.{u} t r).commutator i
              |>.freeLowerTruncation (n := n)) ^ z
          else
            1).prod by
      congr 1
      apply List.map_congr_left
      intro j hj
      by_cases hjr : j = r - 1
      · subst j
        have hsucc : r - 1 + 1 = r := by omega
        rw [hsucc]
        rw [single_exponent_same]
        simpa using
          (standardHallFamily.{u} t r).collectedweight_productite_eqzpow
            i z
      · have hweight : j + 1 ≠ r := by omega
        rw [single_exponent_ne i z hweight,
          BCWta.collected_weight_productzero,
          if_neg hjr]]
  exact
    List.prodmap_iteeq_nodupmem
      (List.range (n - 1))
      (r - 1)
      (((standardHallFamily.{u} t r).commutator i
        |>.freeLowerTruncation (n := n)) ^ z)
      List.nodup_range
      (by simp; omega)

/-- Away from its own weight, one canonical Hall factor to an arbitrary
integer power has zero Hall coordinate. -/
private theorem standard_zpow_ne
    {t n r s : ℕ}
    (hn : 2 ≤ n)
    (i : (standardHallFamily.{u} t r).index)
    (z : ℤ)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (hsr : s ≠ r) :
    standardHallCoordinates t n hn
        (((standardHallFamily.{u} t r).commutator i
          |>.freeLowerTruncation (n := n)) ^ z)
        s =
      0 := by
  have hcoordinates :=
    standard_coordinates_product
      t n hn (singleExponentFamily i z)
      (((standardHallFamily.{u} t r).commutator i
        |>.freeLowerTruncation (n := n)) ^ z)
      (standard_single_family i z hr hrn)
      s hs hsn
  rw [hcoordinates]
  exact single_exponent_ne i z hsr

private theorem HallTree.evalleaf_occurpow_weightone
    {α : Type*} {G : Type*} [Group G]
    (value : α → G) (q : ℕ) :
    ∀ (tree : HallTree α), tree.weight = 1 →
      ∀ leaf : HallTree.LOccur tree,
        HallTree.leafOccurrencePow value q tree leaf =
          tree.toCWord.eval value ^ q
  | .atom _, _, .atom _ => rfl
  | .commutator left right, hweight, _ => by
      have hleft := left.weight_pos
      have hright := right.weight_pos
      simp only [HallTree.weight_commutator] at hweight
      omega

/-- Powering the unique leaf of a weight-one Hall tree is just powering the
corresponding canonical Hall factor. -/
private theorem leaf_occurrence_pow
    {t n : ℕ}
    (i : (standardHallFamily.{u} t 1).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (q : ℕ) :
    HallTree.leafOccurrencePow
        (freeTruncationValue t n) q
        (concreteBasicTree i) leaf =
      ((standardHallFamily.{u} t 1).commutator i
        |>.freeLowerTruncation (n := n)) ^ q := by
  rw [HallTree.evalleaf_occurpow_weightone
    (freeTruncationValue t n) q
    (concreteBasicTree i) (concrete_tree_weight i) leaf]
  rfl

/-- The polynomial clause of Lemma H2 is automatic for a powered
weight-one Hall factor: all higher coordinates vanish. -/
private theorem powered_leaf_coordinate
    {t n s : ℕ}
    (hn : 2 ≤ n)
    (i : (standardHallFamily.{u} t 1).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (hs : 1 < s)
    (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index) :
    IVMost
      (fun q : ℕ =>
        standardHallCoordinates t n hn
          (HallTree.leafOccurrencePow
            (freeTruncationValue t n) q
            (concreteBasicTree i) leaf)
          s j)
      s := by
  have hzero :
      (fun q : ℕ =>
        standardHallCoordinates t n hn
          (HallTree.leafOccurrencePow
            (freeTruncationValue t n) q
            (concreteBasicTree i) leaf)
          s j) =
        0 := by
    funext q
    rw [leaf_occurrence_pow]
    have hcoordinates :=
      standard_zpow_ne
        hn i (q : ℤ) (by omega) (by omega) (by omega) hsn (by omega)
    simpa only [zpow_natCast] using congrFun hcoordinates j
  rw [hzero]
  exact IVMost.zero s

private theorem element_zpow_three
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (z : ℤ) :
    ⁅x ^ z, y⁆ =
      ⁅x, y⁆ ^ z *
        ⁅⁅x, y⁆, x⁆ ^ (-Ring.choose z 2) := by
  let C := ⁅x, y⁆
  let D := ⁅C, x⁆
  have hx : x ∈ Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hy : y ∈ Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hC : C ∈ Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa [C] using
      element_lower_series hx hy
  have hD : D ∈ Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa [D] using
      element_lower_series hC hx
  have hcentralD : Commute C D :=
    HCThree.commute_series_four
      hn4 C hD
  have hraw :=
    HCThree.element_zpow_class
      hn4 x y z 1
  have hswap : ⁅x, C⁆ = D⁻¹ := by
    simpa only [D] using (commutatorElement_inv C x).symm
  change
    ⁅x ^ z, y⁆ =
      C ^ z * D ^ (-Ring.choose z 2)
  norm_num at hraw
  rw [hraw, hswap, inv_zpow, ← zpow_neg]
  exact (hcentralD.zpow_zpow z (-Ring.choose z 2)).eq.symm

private theorem element_zpow_standard
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (z : ℤ) :
    ⁅x, y ^ z⁆ =
      ⁅x, y⁆ ^ z *
        ⁅⁅x, y⁆, y⁆ ^ (-Ring.choose z 2) := by
  let C := ⁅x, y⁆
  let E := ⁅C, y⁆
  have hraw :=
    HCThree.element_zpow_class
      hn4 x y 1 z
  have hswap : ⁅y, C⁆ = E⁻¹ := by
    simpa only [E] using (commutatorElement_inv C y).symm
  change
    ⁅x, y ^ z⁆ =
      C ^ z * E ^ (-Ring.choose z 2)
  norm_num at hraw
  rw [hraw, hswap, inv_zpow, ← zpow_neg]

/-- Through cutoff four, powering one leaf of a weight-two basic Hall tree
introduces exactly one weight-three Hall correction. -/
private theorem HallTree.evalleaf_occurpow_weighttwo
    {d n : ℕ}
    (hn4 : n ≤ 4)
    (value :
      FreeGenerator.{u} d →
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (tree : HallTree (FreeGenerator.{u} d))
    (hbasic : tree.IsBasic)
    (hweight : tree.weight = 2)
    (leaf : HallTree.LOccur tree) :
    ∃ correction : HallTree (FreeGenerator.{u} d),
      correction.IsBasic ∧
        correction.weight = 3 ∧
        ∀ q : ℕ,
        HallTree.leafOccurrencePow value q tree leaf =
          tree.toCWord.eval value ^ (q : ℤ) *
            correction.toCWord.eval value ^
              (-Ring.choose (q : ℤ) 2) := by
  cases tree with
  | atom a =>
      simp at hweight
  | commutator left right =>
      have hleftWeight : left.weight = 1 := by
        simp only [HallTree.weight_commutator] at hweight
        have := left.weight_pos
        have := right.weight_pos
        omega
      have hrightWeight : right.weight = 1 := by
        simp only [HallTree.weight_commutator] at hweight
        have := left.weight_pos
        have := right.weight_pos
        omega
      have hleftBasic : left.IsBasic := hbasic.1
      have hrightBasic : right.IsBasic := hbasic.2.1
      have hrightLeft : right < left := hbasic.2.2.1
      cases leaf with
      | left leaf =>
          let correction :=
            HallTree.commutator (HallTree.commutator left right) left
          have hcorrectionBasic : correction.IsBasic := by
            exact HallTree.basic_commutator_admissible
              hbasic hleftBasic
              (HallTree.lt_weight_lt (by
                simp only [HallTree.weight_commutator]
                omega))
              hrightLeft.le
          have hcorrectionWeight : correction.weight = 3 := by
            simp only [correction, HallTree.weight_commutator]
            omega
          refine ⟨correction, hcorrectionBasic, hcorrectionWeight, ?_⟩
          intro q
          simp only [HallTree.leafOccurrencePow,
            HallTree.to_commutator_commutator,
            CWord.eval_commutator]
          rw [HallTree.evalleaf_occurpow_weightone
            value q left hleftWeight leaf]
          simpa only [zpow_natCast, correction] using
            element_zpow_three
              hn4
              (left.toCWord.eval value)
              (right.toCWord.eval value)
              (q : ℤ)
      | right leaf =>
          let correction :=
            HallTree.commutator (HallTree.commutator left right) right
          have hcorrectionBasic : correction.IsBasic := by
            exact HallTree.basic_commutator_admissible
              hbasic hrightBasic
              (HallTree.lt_weight_lt (by
                simp only [HallTree.weight_commutator]
                omega))
              le_rfl
          have hcorrectionWeight : correction.weight = 3 := by
            simp only [correction, HallTree.weight_commutator]
            omega
          refine ⟨correction, hcorrectionBasic, hcorrectionWeight, ?_⟩
          intro q
          simp only [HallTree.leafOccurrencePow,
            HallTree.to_commutator_commutator,
            CWord.eval_commutator]
          rw [HallTree.evalleaf_occurpow_weightone
            value q right hrightWeight leaf]
          simpa only [zpow_natCast, correction] using
            element_zpow_standard
              hn4
              (left.toCWord.eval value)
              (right.toCWord.eval value)
              (q : ℤ)

private noncomputable def weightExponentFamily
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (a : ℤ)
    (k : (standardHallFamily.{u} t 3).index)
    (b : ℤ) :
    StandardExponentFamily.{u} t :=
  Function.update
    (Function.update (0 : StandardExponentFamily.{u} t) 2
      (fun j => if j = i then a else 0))
    3
    (fun j => if j = k then b else 0)

@[simp] private theorem exponent_family_one
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (a : ℤ)
    (k : (standardHallFamily.{u} t 3).index)
    (b : ℤ) :
    weightExponentFamily i a k b 1 = 0 := by
  simp [weightExponentFamily]

@[simp] private theorem two_exponent_family
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (a : ℤ)
    (k : (standardHallFamily.{u} t 3).index)
    (b : ℤ) :
    weightExponentFamily i a k b 2 =
      fun j => if j = i then a else 0 := by
  simp [weightExponentFamily]

@[simp] private theorem weight_exponent_family
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (a : ℤ)
    (k : (standardHallFamily.{u} t 3).index)
    (b : ℤ) :
    weightExponentFamily i a k b 3 =
      fun j => if j = k then b else 0 := by
  simp [weightExponentFamily]

private theorem standard_exponent_family
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (a : ℤ)
    (k : (standardHallFamily.{u} t 3).index)
    (b : ℤ) :
    standardHallProduct t 4
        (weightExponentFamily i a k b) =
      ((standardHallFamily.{u} t 2).commutator i
        |>.freeLowerTruncation (n := 4)) ^ a *
        ((standardHallFamily.{u} t 3).commutator k
          |>.freeLowerTruncation (n := 4)) ^ b := by
  norm_num [standardHallProduct, collectedHallProduct,
    collectedPrefixProduct, List.range_succ,
    weightExponentFamily,
    BCWta.collected_weight_productzero,
    (standardHallFamily.{u} t 2).collectedweight_productite_eqzpow,
    (standardHallFamily.{u} t 3).collectedweight_productite_eqzpow]

/-- Canonical form of the weight-two powered-leaf identity at cutoff four. -/
private theorem leaf_occurrence_two
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (leaf : HallTree.LOccur (concreteBasicTree i)) :
    ∃ k : (standardHallFamily.{u} t 3).index,
      ∀ q : ℕ,
      HallTree.leafOccurrencePow
          (freeTruncationValue t 4) q
          (concreteBasicTree i) leaf =
        ((standardHallFamily.{u} t 2).commutator i
          |>.freeLowerTruncation (n := 4)) ^ (q : ℤ) *
          ((standardHallFamily.{u} t 3).commutator k
            |>.freeLowerTruncation (n := 4)) ^
              (-Ring.choose (q : ℤ) 2) := by
  obtain ⟨correction, hcorrectionBasic, hcorrectionWeight, hformula⟩ :=
    HallTree.evalleaf_occurpow_weighttwo
      (d := t) (n := 4) (by omega)
      (freeTruncationValue t 4)
      (concreteBasicTree i)
      (concrete_hall_tree i)
      (concrete_tree_weight i)
      leaf
  obtain ⟨k, hk⟩ :=
    concrete_basic_tree
      hcorrectionBasic hcorrectionWeight
  refine ⟨k, ?_⟩
  intro q
  rw [BCWt.freeLowerTruncation,
    BCWt.freeLowerTruncation]
  change
    HallTree.leafOccurrencePow
        (freeTruncationValue t 4) q
        (concreteBasicTree i) leaf =
      (concreteBasicTree i).toCWord.eval
          (freeTruncationValue t 4) ^ (q : ℤ) *
        (concreteBasicTree k).toCWord.eval
            (freeTruncationValue t 4) ^
              (-Ring.choose (q : ℤ) 2)
  rw [hk]
  exact hformula q

/-- The weight-three Hall coordinates of a powered leaf in a weight-two
factor are supported at one fixed correction index. -/
private theorem powered_leaf_weight
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (leaf : HallTree.LOccur (concreteBasicTree i)) :
    ∃ k : (standardHallFamily.{u} t 3).index,
      ∀ (q : ℕ) (j : (standardHallFamily.{u} t 3).index),
        standardHallCoordinates t 4 (by omega)
            (HallTree.leafOccurrencePow
              (freeTruncationValue t 4) q
              (concreteBasicTree i) leaf)
            3 j =
          if j = k then -Ring.choose (q : ℤ) 2 else 0 := by
  obtain ⟨k, hformula⟩ :=
    leaf_occurrence_two i leaf
  refine ⟨k, ?_⟩
  intro q j
  let e :=
    weightExponentFamily i (q : ℤ) k
      (-Ring.choose (q : ℤ) 2)
  have hproduct :
      standardHallProduct t 4 e =
        HallTree.leafOccurrencePow
          (freeTruncationValue t 4) q
          (concreteBasicTree i) leaf := by
    exact
      (standard_exponent_family
        i (q : ℤ) k (-Ring.choose (q : ℤ) 2)).trans
        (hformula q).symm
  have hcoordinates :=
    standard_coordinates_product
      t 4 (by omega) e
      (HallTree.leafOccurrencePow
        (freeTruncationValue t 4) q
        (concreteBasicTree i) leaf)
      hproduct 3 (by omega) (by omega)
  simpa [e, weightExponentFamily] using
    congrFun hcoordinates j

private theorem neg_choose_cast :
    IVMost
      (fun q : ℕ => -Ring.choose (q : ℤ) 2)
      2 := by
  let m : NBMono 2 :=
    ⟨[2], by simp⟩
  have hm :
      IVMost m.eval 2 :=
    m.integerValuedMost
  have hscaled :
      IVMost ((-1 : ℤ) • m.eval) 2 :=
    IVMost.smul (-1) hm
  have heq :
      (fun q : ℕ => -Ring.choose (q : ℤ) 2) =
        (-1 : ℤ) • m.eval := by
    funext q
    simp [m, NBMono.eval, Ring.choose_natCast]
  rw [heq]
  exact hscaled

/-- The nontrivial low-cutoff case of Struik's Lemma H2 has degree at most
two. -/
private theorem powered_leaf_two
    {t : ℕ}
    (i : (standardHallFamily.{u} t 2).index)
    (leaf : HallTree.LOccur (concreteBasicTree i))
    (j : (standardHallFamily.{u} t 3).index) :
    IVMost
      (fun q : ℕ =>
        standardHallCoordinates t 4 (by omega)
          (HallTree.leafOccurrencePow
            (freeTruncationValue t 4) q
            (concreteBasicTree i) leaf)
          3 j)
      2 := by
  obtain ⟨k, hcoordinates⟩ :=
    powered_leaf_weight i leaf
  have hfunction :
      (fun q : ℕ =>
        standardHallCoordinates t 4 (by omega)
          (HallTree.leafOccurrencePow
            (freeTruncationValue t 4) q
            (concreteBasicTree i) leaf)
          3 j) =
        fun q : ℕ =>
          if j = k then -Ring.choose (q : ℤ) 2 else 0 := by
    funext q
    exact hcoordinates q j
  rw [hfunction]
  by_cases hjk : j = k
  · simpa [hjk] using neg_choose_cast
  · simpa [hjk] using IVMost.zero 2

/-- Struik's powered-leaf Hall-coordinate degree bound holds unconditionally
for every truncation cutoff through four. -/
theorem powered_leaf_four
    (t n : ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    PoweredLeafCoordinate.{u} t n := by
  intro r hr hrn i leaf s hrs hsn j
  have hrCases : r = 1 ∨ r = 2 := by
    omega
  rcases hrCases with rfl | rfl
  · simpa using
      powered_leaf_coordinate
        hn i leaf hrs hsn j
  · have hs : s = 3 := by
      omega
    have hnEq : n = 4 := by
      omega
    subst s
    subst n
    simpa using
      powered_leaf_two
        i leaf j

/-- Through nilpotency class three, the recursive order bound in Struik's
Lemma 1 follows from the tame-order assumptions alone. -/
theorem bound_n_four
    {t n : ℕ}
    (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (htame : TameOrdersCutoff order n) :
    FactorOrderBound.{u} order n :=
  powered_leaf_polynomial
    order hn htame
      (powered_leaf_four
        t n hn hn4)

end P1960
end Struik

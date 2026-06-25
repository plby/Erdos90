import Towers.Group.NilpotentProducts.PoweredLeafData


/-!
# The support clause in Struik's Lemma H2

Set one free generator equal to the identity.  A Hall tree using that
generator vanishes, while a Hall tree omitting it is fixed.  Applying this
endomorphism to a canonical Hall normal form and using uniqueness shows that
every coordinate of a powered-leaf commutator still uses the powered leaf.
-/

namespace Struik
namespace P1960

open Towers
open Towers.HallTree
open Towers.TCTex

universe u

private def eraseValue
    {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (a : α) (value : α → G) (b : α) : G :=
  if b = a then 1 else value b

private theorem HallTree.evalerase_valueeq_oneuses
    {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (a : α) (value : α → G) :
    ∀ {tree : HallTree α}, hallTreeUses a tree →
      tree.toCWord.eval (eraseValue a value) = 1
  | .atom b, huses => by
      subst b
      simp [eraseValue]
  | .commutator left right, huses => by
      rcases huses with hleft | hright
      · rw [HallTree.to_commutator_commutator,
          CWord.eval_commutator,
          HallTree.evalerase_valueeq_oneuses a value hleft]
        simp
      · rw [HallTree.to_commutator_commutator,
          CWord.eval_commutator,
          HallTree.evalerase_valueeq_oneuses a value hright]
        simp

private theorem HallTree.evalerase_valueeq_notuses
    {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (a : α) (value : α → G) :
    ∀ {tree : HallTree α}, ¬hallTreeUses a tree →
      tree.toCWord.eval (eraseValue a value) =
        tree.toCWord.eval value
  | .atom b, huses => by
      have hba : b ≠ a := by
        simpa [hallTreeUses] using huses
      simp [eraseValue, hba]
  | .commutator left right, huses => by
      have hleft : ¬hallTreeUses a left :=
        fun h => huses (Or.inl h)
      have hright : ¬hallTreeUses a right :=
        fun h => huses (Or.inr h)
      simp [HallTree.to_commutator_commutator,
        HallTree.evalerase_valueeq_notuses a value hleft,
        HallTree.evalerase_valueeq_notuses a value hright]

private theorem HallTree.evalleafoccur_powerasevalue_eqoneuses
    {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (a : α) (value : α → G) (q : ℕ) :
    ∀ {tree : HallTree α} (leaf : HallTree.LOccur tree),
      hallTreeUses a tree →
        HallTree.leafOccurrencePow (eraseValue a value) q tree leaf = 1
  | .atom b, .atom _, huses => by
      subst b
      simp [HallTree.leafOccurrencePow, eraseValue]
  | .commutator left right, .left leaf, huses => by
      rcases huses with hleft | hright
      · rw [HallTree.leafOccurrencePow]
        simp [HallTree.evalleafoccur_powerasevalue_eqoneuses
          a value q leaf hleft]
      · rw [HallTree.leafOccurrencePow,
          HallTree.evalerase_valueeq_oneuses a value hright]
        simp
  | .commutator left right, .right leaf, huses => by
      rcases huses with hleft | hright
      · rw [HallTree.leafOccurrencePow,
          HallTree.evalerase_valueeq_oneuses a value hleft]
        simp
      · rw [HallTree.leafOccurrencePow]
        simp [HallTree.evalleafoccur_powerasevalue_eqoneuses
          a value q leaf hright]

private theorem HallTree.evalle_zpowe_value
    {α : Type*} [DecidableEq α] {G : Type*} [Group G]
    (a : α) (value : α → G) (q : ℤ) :
    ∀ {tree : HallTree α} (leaf : HallTree.LOccur tree),
      hallTreeUses a tree →
        HallTree.leafOccurrenceZ (eraseValue a value) q tree leaf = 1
  | .atom b, .atom _, huses => by
      subst b
      simp [HallTree.leafOccurrenceZ, eraseValue]
  | .commutator left right, .left leaf, huses => by
      rcases huses with hleft | hright
      · rw [HallTree.leafOccurrenceZ]
        simp [HallTree.evalle_zpowe_value
          a value q leaf hleft]
      · rw [HallTree.leafOccurrenceZ,
          HallTree.evalerase_valueeq_oneuses a value hright]
        simp
  | .commutator left right, .right leaf, huses => by
      rcases huses with hleft | hright
      · rw [HallTree.leafOccurrenceZ,
          HallTree.evalerase_valueeq_oneuses a value hleft]
        simp
      · rw [HallTree.leafOccurrenceZ]
        simp [HallTree.evalle_zpowe_value
          a value q leaf hright]

private theorem uses_label_leaf
    {α : Type*} :
    ∀ {tree : HallTree α} (leaf : HallTree.LOccur tree),
      hallTreeUses leaf.label tree
  | .atom _, .atom _ => rfl
  | .commutator _ _, .left leaf =>
      Or.inl (uses_label_leaf leaf)
  | .commutator _ _, .right leaf =>
      Or.inr (uses_label_leaf leaf)

/-- Endomorphism of the free nilpotent truncation obtained by sending one
free generator to the identity and fixing all other free generators. -/
noncomputable def eraseTruncationGenerator
    (t n : ℕ) (a : FreeGenerator.{u} t) :
    LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n →*
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n := by
  let value : FreeGenerator.{u} t →
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n :=
    eraseValue a (freeTruncationValue t n)
  let f : FreeGroup (FreeGenerator.{u} t) →*
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n :=
    FreeGroup.lift value
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} t)) (n - 1)) f
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n) (n - 1) :=
    Subgroup.lowerCentralSeries.map f (n - 1)
      (Subgroup.mem_map_of_mem f hx)
  have hbot :
      Subgroup.lowerCentralSeries
          (LowerCentralTruncation
            (FreeGroup (FreeGenerator.{u} t)) n) (n - 1) =
        ⊥ := by
    simpa [LowerCentralTruncation] using
      (lower_last_bot
        (G := FreeGroup (FreeGenerator.{u} t)) (c := n))
  rw [hbot] at hxmap
  exact hxmap

@[simp] theorem erase_truncation_generator
    (t n : ℕ) (a b : FreeGenerator.{u} t) :
    eraseTruncationGenerator t n a
        (freeTruncationValue t n b) =
      eraseValue a (freeTruncationValue t n) b := by
  simp [eraseTruncationGenerator,
    freeTruncationValue]

theorem erase_truncation_uses
    (t n : ℕ)
    (a : FreeGenerator.{u} t)
    (tree : HallTree (FreeGenerator.{u} t))
    (huses : hallTreeUses a tree) :
    eraseTruncationGenerator t n a
        (tree.toCWord.eval
          (freeTruncationValue t n)) =
      1 := by
  rw [CWord.map_eval]
  simp_rw [erase_truncation_generator]
  exact
    HallTree.evalerase_valueeq_oneuses
      a (freeTruncationValue t n) huses

theorem erase_tree_uses
    (t n : ℕ)
    (a : FreeGenerator.{u} t)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (q : ℕ)
    (huses : hallTreeUses a tree) :
    eraseTruncationGenerator t n a
        (HallTree.leafOccurrencePow
          (freeTruncationValue t n) q tree leaf) =
      1 := by
  rw [HallTree.eval_leaf_pow]
  simp_rw [erase_truncation_generator]
  exact
    HallTree.evalleafoccur_powerasevalue_eqoneuses
      a (freeTruncationValue t n) q leaf huses

theorem erase_powered_uses
    (t n : ℕ)
    (a : FreeGenerator.{u} t)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (q : ℤ)
    (huses : hallTreeUses a tree) :
    eraseTruncationGenerator t n a
        (HallTree.leafOccurrenceZ
          (freeTruncationValue t n) q tree leaf) =
      1 := by
  rw [HallTree.leaf_z_pow]
  simp_rw [erase_truncation_generator]
  exact
    HallTree.evalle_zpowe_value
      a (freeTruncationValue t n) q leaf huses

theorem erase_truncation_factor
    (t n r : ℕ) (a : FreeGenerator.{u} t)
    (i : (standardHallFamily.{u} t r).index) :
    eraseTruncationGenerator t n a
        ((standardHallFamily.{u} t r).commutator i
          |>.freeLowerTruncation (n := n)) =
      if hallTreeUses a (concreteBasicTree i) then
        1
      else
        (standardHallFamily.{u} t r).commutator i
          |>.freeLowerTruncation (n := n) := by
  classical
  rw [BCWt.freeLowerTruncation]
  have hword :
      ((standardHallFamily.{u} t r).commutator i).word =
        (concreteBasicTree i).toCWord := by
    rfl
  rw [hword, CWord.map_eval]
  simp_rw [erase_truncation_generator]
  by_cases huses : hallTreeUses a (concreteBasicTree i)
  · rw [if_pos huses,
      HallTree.evalerase_valueeq_oneuses a
        (freeTruncationValue t n) huses]
  · rw [if_neg huses,
      HallTree.evalerase_valueeq_notuses a
        (freeTruncationValue t n) huses]

private noncomputable def eraseUsedCoordinates
    {t : ℕ} (a : FreeGenerator.{u} t)
    (e : StandardExponentFamily.{u} t) :
    StandardExponentFamily.{u} t :=
  fun r i =>
    if hallTreeUses a (concreteBasicTree i) then 0 else e r i

private theorem erase_free_truncation
    (t n r : ℕ) (a : FreeGenerator.{u} t)
    (e : StandardExponentFamily.{u} t) :
    eraseTruncationGenerator t n a
        ((standardHallFamily.{u} t r).collectedWeightProduct
          (n := n) (e r)) =
      (standardHallFamily.{u} t r).collectedWeightProduct
        (n := n) ((eraseUsedCoordinates a e) r) := by
  classical
  unfold BCWta.collectedWeightProduct
    BCWta.collected_lower_centralterm
  rw [SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod,
    map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _hi
  change
    eraseTruncationGenerator t n a
        (((standardHallFamily.{u} t r).commutator i
          |>.freeLowerTruncation (n := n)) ^ e r i) =
      ((standardHallFamily.{u} t r).commutator i
        |>.evalin_freelower_centtrunterm (n := n)) ^
        eraseUsedCoordinates a e r i
  rw [map_zpow, erase_truncation_factor]
  by_cases huses : hallTreeUses a (concreteBasicTree i)
  · simp [huses, eraseUsedCoordinates,
      BCWt.evalin_freelower_centtrunterm]
  · simp [huses, eraseUsedCoordinates,
      BCWt.evalin_freelower_centtrunterm]

private theorem erase_truncation_standard
    (t n : ℕ) (a : FreeGenerator.{u} t)
    (e : StandardExponentFamily.{u} t) :
    eraseTruncationGenerator t n a
        (standardHallProduct t n e) =
      standardHallProduct t n (eraseUsedCoordinates a e) := by
  unfold standardHallProduct collectedHallProduct
  rw [collectedPrefixProduct, collectedPrefixProduct, map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro r _hr
  exact erase_free_truncation
    t n (r + 1) a e

/-- If erasing one free generator kills an element, every nonzero standard
Hall coordinate of that element uses the erased generator. -/
theorem standard_erase_uses
    (t n : ℕ) (hn : 2 ≤ n)
    (a : FreeGenerator.{u} t)
    (y : LowerCentralTruncation
      (FreeGroup (FreeGenerator.{u} t)) n)
    (hmap : eraseTruncationGenerator t n a y = 1)
    (s : ℕ) (hs : 1 ≤ s) (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index)
    (hnotUses :
      ¬hallTreeUses a (concreteBasicTree j)) :
    standardHallCoordinates t n hn y s j = 0 := by
  let e := standardHallCoordinates t n hn y
  have heval : standardHallProduct t n e = y :=
    standard_product_coordinates t n hn y
  have herasedProduct :
      standardHallProduct t n (eraseUsedCoordinates a e) = 1 := by
    rw [← erase_truncation_standard,
      heval, hmap]
  have hzero :
      eraseUsedCoordinates a e s = 0 :=
    collected_imp_coordinates
      hn (standardHallFamily.{u} t)
      (fun w _hw hwn =>
        standard_forms_associated
          t n w (by omega) hwn)
      (eraseUsedCoordinates a e)
      herasedProduct s hs hsn
  have hzeroj := congrFun hzero j
  simpa [eraseUsedCoordinates, hnotUses, e] using hzeroj

/-- Every coordinate of a powered-leaf Hall tree still uses the powered
generator.  No comparison between the coordinate weight and the source-tree
weight is needed for this support statement. -/
theorem powered_leaf_uses
    (t n : ℕ) (hn : 2 ≤ n)
    (tree : HallTree (FreeGenerator.{u} t))
    (leaf : HallTree.LOccur tree)
    (q s : ℕ) (hs : 1 ≤ s) (hsn : s < n)
    (j : (standardHallFamily.{u} t s).index)
    (hnotUses :
      ¬hallTreeUses leaf.label (concreteBasicTree j)) :
    standardHallCoordinates t n hn
        (HallTree.leafOccurrencePow
          (freeTruncationValue t n) q tree leaf)
        s j =
      0 := by
  let a := leaf.label
  let y :=
    HallTree.leafOccurrencePow
      (freeTruncationValue t n) q
      tree leaf
  let e := standardHallCoordinates t n hn y
  have hmapY :
      eraseTruncationGenerator t n a y = 1 := by
    rw [show
        eraseTruncationGenerator t n a y =
          HallTree.leafOccurrencePow
            (fun b =>
              eraseTruncationGenerator t n a
                (freeTruncationValue t n b))
            q tree leaf by
          simp [y]]
    apply HallTree.eval_leaf_occurrence
    simp [eraseValue, a]
  have heval : standardHallProduct t n e = y :=
    standard_product_coordinates t n hn y
  have herasedProduct :
      standardHallProduct t n (eraseUsedCoordinates a e) = 1 := by
    rw [← erase_truncation_standard,
      heval, hmapY]
  have hzero :
      eraseUsedCoordinates a e s = 0 :=
    collected_imp_coordinates
      hn (standardHallFamily.{u} t)
      (fun w _hw hwn =>
        standard_forms_associated
          t n w (by omega) hwn)
      (eraseUsedCoordinates a e)
      herasedProduct s (by omega) hsn
  have hzeroj := congrFun hzero j
  simpa [eraseUsedCoordinates, a, hnotUses, e] using hzeroj

/-- The support assertion in Lemma H2 for an arbitrary commutator tree
follows from the all-weight support theorem. -/
theorem treePoweredLeaf
    (t n : ℕ) (hn : 2 ≤ n) :
    PoweredLeafSupport.{u} t n := by
  intro tree _hrn leaf q s hrs hsn j hnotUses
  exact powered_leaf_uses
    t n hn tree leaf q s (by omega) hsn j hnotUses

/-- The arbitrary-tree support theorem specializes to the canonical standard
Hall basis used by Lemma 1. -/
theorem poweredLeafData
    (t n : ℕ) (hn : 2 ≤ n) :
    PoweredSupportData.{u} t n := by
  intro r _hr hrn i leaf q s hrs hsn j hnotUses
  exact
    treePoweredLeaf t n hn
      (concreteBasicTree i)
      (by simpa [concrete_tree_weight] using hrn)
      leaf q s (by simpa [concrete_tree_weight] using hrs)
      hsn j hnotUses

/-- With support now proved, the polynomial degree statement is the only
remaining Lemma H2 input needed for Struik's Hall-factor order bound. -/
theorem powered_leaf_polynomial
    {t n : ℕ} (order : Fin t → ℕ)
    (hn : 2 ≤ n)
    (htame : TameOrdersCutoff order n)
    (hpolynomial : PoweredLeafCoordinate.{u} t n) :
    FactorOrderBound.{u} order n :=
  bound_powered_leaf
    order hn htame hpolynomial
      (poweredLeafData t n hn)

end P1960
end Struik

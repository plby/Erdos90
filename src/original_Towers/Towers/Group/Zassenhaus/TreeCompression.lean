import Towers.Group.HallBasic.ExplicitReductionCoordinates
import Towers.Group.Zassenhaus.Factors
import Towers.Group.HallBasic.ConcreteBasisBridge

/-!
# Concrete Hall-tree expansion of symbolic power words

A symbolic Hall power word is a commutator word whose atoms are Hall-coordinate
addresses.  For the canonical concrete Hall family, every such atom has an
underlying basic Hall tree in the original free generators.  Replacing address
atoms by those trees turns weighted symbolic words into ordinary Hall trees.

This file proves that expansion preserves the relevant weight and evaluation,
then applies explicit Hall-tree reduction to obtain a next-stratum residual in
the lower-central truncation.  It is the group-level compression primitive
needed before a symbolic collector can recurse on the higher residual.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace HEWord

universe u

/-- Evaluate one canonical Hall-coordinate address in the original free group. -/
def evalFreeAddress
    {d : ℕ}
    (address :
      HEAddres (concreteBasicCommutators.{u} d)) :
    FreeGroup (FreeGenerator.{u} d) :=
  ((concreteBasicCommutators.{u} d address.1).commutator
    address.2).eval_in_freegroup

/--
Replace every canonical Hall-coordinate address by its underlying concrete
basic Hall tree.
-/
def tree
    {d : ℕ} :
    CWord (HEAddres (concreteBasicCommutators.{u} d)) →
      HallTree (FreeGenerator.{u} d)
  | .atom address => concreteBasicTree address.2
  | .commutator left right => .commutator (tree left) (tree right)

@[simp]
theorem tree_atom
    {d : ℕ}
    (address :
      HEAddres (concreteBasicCommutators.{u} d)) :
    tree (.atom address) = concreteBasicTree address.2 :=
  rfl

@[simp]
theorem tree_commutator
    {d : ℕ}
    (left right :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d))) :
    tree (.commutator left right) =
      .commutator (tree left) (tree right) :=
  rfl

/-- Expansion turns weighted symbolic degree into ordinary Hall-tree weight. -/
@[simp]
theorem tree_weight
    {d : ℕ}
    (word :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d))) :
    (tree word).weight =
      word.weight PEAddres.weight := by
  induction word with
  | atom address =>
      simp [tree, PEAddres.weight]
  | commutator left right ihLeft ihRight =>
      simp [tree, ihLeft, ihRight]

/-- The expanded tree evaluates to the free-group value of the address word. -/
@[simp]
theorem tree_commutator_eval
    {d : ℕ}
    (word :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d))) :
    (tree word).toCWord.eval FreeGroup.of =
      word.eval evalFreeAddress := by
  induction word with
  | atom address =>
      rfl
  | commutator left right ihLeft ihRight =>
      simp [tree, ihLeft, ihRight]

/-- Truncation carries free-group address evaluation to symbolic address evaluation. -/
@[simp]
theorem lower_truncation_address
    {d n : ℕ}
    (address :
      HEAddres (concreteBasicCommutators.{u} d)) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (evalFreeAddress address) =
      PEAddres.freeLowerTruncation address :=
  ((concreteBasicCommutators.{u} d address.1).commutator
    address.2).mapevalinfree_groupeqevalin_frelowcentru

/-- Truncation carries free-group address-word evaluation to symbolic evaluation. -/
@[simp]
theorem lower_truncation_group
    {d n : ℕ}
    (word :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d))) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (word.eval evalFreeAddress) =
      word.eval PEAddres.freeLowerTruncation := by
  rw [CWord.map_eval]
  simp only [lower_truncation_address]

/--
Truncation carries the expanded Hall-tree value to the original symbolic word
value.
-/
@[simp]
theorem lower_truncation_tree
    {d n : ℕ}
    (word :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d))) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        ((tree word).toCWord.eval FreeGroup.of) =
      word.eval PEAddres.freeLowerTruncation := by
  rw [tree_commutator_eval, lower_truncation_group]

/--
Before truncation, explicit Hall-tree compression leaves a residual one
lower-central stratum above the weighted symbolic word.
-/
theorem basic_inv_series
    {d : ℕ}
    (word :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d))) :
    (HallTree.basicReductionProduct (tree word))⁻¹ *
        word.eval evalFreeAddress ∈
      Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d))
        (word.weight PEAddres.weight) := by
  simpa only [tree_weight, tree_commutator_eval] using
    HallTree.basic_reduction_series
      (tree word)

/--
After lower-central truncation, explicit Hall-tree compression still leaves a
residual one stratum above the symbolic word.
-/
theorem
    truncation_inv_series
    {d n : ℕ}
    (word :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d))) :
    (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.basicReductionProduct (tree word)))⁻¹ *
        word.eval PEAddres.freeLowerTruncation ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (word.weight PEAddres.weight) := by
  have h :=
    basic_inv_series word
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) h)
  simpa only [map_mul, map_inv,
    lower_truncation_group] using hmap

/--
Raising the explicit compression product to a symbolic factor's polynomial
exponent still leaves a residual one stratum above the factor.
-/
theorem zpow_inv_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    ((lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.basicReductionProduct (tree factor.word))) ^
          factor.exponent q)⁻¹ *
        factor.eval (n := n) q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  let N : Type u :=
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let K : Subgroup N :=
    Subgroup.lowerCentralSeries N
      (factor.word.weight PEAddres.weight)
  let quotientMap : N →* N ⧸ K := QuotientGroup.mk' K
  let compressed : N :=
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
      (HallTree.basicReductionProduct (tree factor.word))
  change
    (compressed ^ factor.exponent q)⁻¹ * factor.eval (n := n) q ∈ K
  have hresidual :
      compressed⁻¹ * factor.wordValue (n := n) ∈ K := by
    simpa only [compressed, K, SPFactora.wordValue] using
      truncation_inv_series
        factor.word
  have hclass :
      quotientMap compressed =
        quotientMap (factor.wordValue (n := n)) := by
    have hone :
        quotientMap (compressed⁻¹ * factor.wordValue (n := n)) = 1 :=
      (QuotientGroup.eq_one_iff
        (N := K) (compressed⁻¹ * factor.wordValue (n := n))).mpr hresidual
    rw [map_mul, map_inv] at hone
    exact inv_mul_eq_one.mp hone
  apply (QuotientGroup.eq_one_iff
    (N := K) ((compressed ^ factor.exponent q)⁻¹ *
      factor.eval (n := n) q)).mp
  change
    quotientMap ((compressed ^ factor.exponent q)⁻¹ *
      factor.eval (n := n) q) = 1
  rw [SPFactora.eval, map_mul, map_inv, map_zpow, hclass,
    map_zpow, inv_mul_cancel]

end HEWord
end TCTex
end Towers

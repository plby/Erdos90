import Towers.Group.HallBasic.ConcreteBasisBridge

/-!
# Concrete recursive Hall families

`ConcreteHallFamilies` adapts the canonical sorted Hall-tree enumeration to
the collection-layer carrier.  This file exposes the equivalent intrinsic
recursive construction directly: weight-one generator leaves are inserted at
every stage, and the next stage adds every admissible bracket of previously
constructed Hall trees.

The resulting finite ordered family is equivalent to the canonical adapter,
so downstream code may keep using the latter without hiding the recursive
construction theorem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
The finite ordered index type cut out directly by the recursive Hall family
in ordinary weight `r`.
-/
abbrev RecursiveConcreteIndex
    (d r : ℕ) :
    Type u :=
  ULift.{u}
    {w : HallTree (FreeGenerator.{u} d) //
      w ∈ HallTree.recursiveTreesWeight r}

noncomputable instance recursiveConcreteFintype
    (d r : ℕ) :
    Fintype (RecursiveConcreteIndex.{u} d r) := by
  classical
  letI :
      Fintype
        {w : HallTree (FreeGenerator.{u} d) //
          w ∈ HallTree.recursiveTreesWeight r} :=
    Fintype.ofFinset (HallTree.recursiveTreesWeight r) fun _ => Iff.rfl
  infer_instance

/--
The collection-layer Hall family obtained directly from the intrinsic
recursive Hall-tree construction.
-/
noncomputable def recursiveConcreteCommutators
    (d r : ℕ) :
    BCWta.{u} d r where
  index := RecursiveConcreteIndex.{u} d r
  commutator i :=
    { word := i.down.1.toCWord
      word_weight := by
        rw [HallTree.commutator_weight_one]
        exact
          (HallTree.recursive_trees_weight.mp i.down.2).2 }

/-- Recover the Hall tree represented by one direct recursive-family index. -/
noncomputable def recursiveConcreteTree
    {d r : ℕ}
    (i : RecursiveConcreteIndex.{u} d r) :
    HallTree (FreeGenerator.{u} d) :=
  i.down.1

@[simp] theorem recursive_basic_tree
    {d r : ℕ}
    (i : RecursiveConcreteIndex.{u} d r) :
    (recursiveConcreteTree i).IsBasic :=
  (HallTree.recursive_trees_weight.mp i.down.2).1

@[simp] theorem recursive_tree_weight
    {d r : ℕ}
    (i : RecursiveConcreteIndex.{u} d r) :
    (recursiveConcreteTree i).weight = r :=
  (HallTree.recursive_trees_weight.mp i.down.2).2

@[simp] theorem recursive_concrete_word
    {d r : ℕ}
    (i : RecursiveConcreteIndex.{u} d r) :
    ((recursiveConcreteCommutators.{u} d r).commutator i).word =
      (recursiveConcreteTree i).toCWord :=
  rfl

/--
Every directly recursive Hall-tree index is represented by the canonical
concrete family.
-/
theorem concrete_tree_recursive
    {d r : ℕ}
    (i : RecursiveConcreteIndex.{u} d r) :
    ∃ j : (concreteCommutatorsWeight.{u} d r).index,
      concreteBasicTree j = recursiveConcreteTree i :=
  concrete_basic_tree
    (recursive_basic_tree i)
    (recursive_tree_weight i)

/--
Every canonical concrete Hall-tree index is represented by the direct
recursive family.
-/
theorem recursive_concrete_tree
    {d r : ℕ}
    (i : (concreteCommutatorsWeight.{u} d r).index) :
    ∃ j : RecursiveConcreteIndex.{u} d r,
      recursiveConcreteTree j = concreteBasicTree i := by
  refine ⟨ULift.up ⟨concreteBasicTree i, ?_⟩, rfl⟩
  exact
    HallTree.recursive_trees_weight.mpr
      ⟨concrete_hall_tree i, concrete_tree_weight i⟩

/-- Choose the canonical concrete index of one direct recursive Hall tree. -/
noncomputable def recursiveConcreteIndex
    {d r : ℕ}
    (i : RecursiveConcreteIndex.{u} d r) :
    (concreteCommutatorsWeight.{u} d r).index :=
  Classical.choose
    (concrete_tree_recursive i)

@[simp] theorem tree_recursive_index
    {d r : ℕ}
    (i : (recursiveConcreteCommutators.{u} d r).index) :
    concreteBasicTree (recursiveConcreteIndex i) =
      recursiveConcreteTree i :=
  Classical.choose_spec
    (concrete_tree_recursive i)

theorem concrete_tree_injective
    {d r : ℕ} :
    Function.Injective
      (concreteBasicTree :
        (concreteCommutatorsWeight.{u} d r).index →
          HallTree (FreeGenerator.{u} d)) := by
  intro i j hij
  apply ULift.down_injective
  exact HallTree.indexed_tree_injective hij

theorem recursive_concrete_bijective
    {d r : ℕ} :
    Function.Bijective
      (recursiveConcreteIndex :
        RecursiveConcreteIndex.{u} d r →
          (concreteCommutatorsWeight.{u} d r).index) := by
  constructor
  · intro i j hij
    apply ULift.down_injective
    apply Subtype.ext
    calc
      i.down.1 =
          concreteBasicTree (recursiveConcreteIndex i) :=
        (tree_recursive_index i).symm
      _ =
          concreteBasicTree (recursiveConcreteIndex j) :=
        congrArg concreteBasicTree hij
      _ = j.down.1 :=
        tree_recursive_index j
  · intro i
    obtain ⟨j, hj⟩ :=
      recursive_concrete_tree i
    refine ⟨j, ?_⟩
    apply concrete_tree_injective
    rw [tree_recursive_index, hj]

/--
The direct recursive family and the canonical collection-layer family have
equivalent finite ordered index sets.
-/
noncomputable def recursiveConcreteBasic
    (d r : ℕ) :
    RecursiveConcreteIndex.{u} d r ≃
      (concreteCommutatorsWeight.{u} d r).index :=
  Equiv.ofBijective recursiveConcreteIndex
    recursive_concrete_bijective

end TCTex
end Towers

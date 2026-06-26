import Submission.Group.NilpotentProducts.ClassThreeCover
import Mathlib.Tactic.FinCases


/-!
# Hall basic trees of rank three and weight at most three
-/

namespace Struik
namespace P1960

open Submission
open Submission.HallTree
open Submission.TCTex
open Submission.TCTex

abbrev RankThreeGenerator := FreeGenerator 3

def rankThreeGenerator (i : Fin 3) : RankThreeGenerator :=
  ULift.up i

def rankThreeAtom (i : Fin 3) : HallTree RankThreeGenerator :=
  .atom (rankThreeGenerator i)

def rankPairTree (i j : Fin 3) :
    HallTree RankThreeGenerator :=
  .commutator (rankThreeAtom j) (rankThreeAtom i)

def rankTripleTree (i j k : Fin 3) :
    HallTree RankThreeGenerator :=
  .commutator (rankPairTree i j) (rankThreeAtom k)

@[simp] theorem rank_atom
    (i j : Fin 3) :
    rankThreeAtom i < rankThreeAtom j ↔ i < j := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem rank_three_atom
    (i j : Fin 3) :
    rankThreeAtom i ≤ rankThreeAtom j ↔ i ≤ j := by
  fin_cases i <;> fin_cases j <;> decide

theorem rank_three_cases
    (tree : HallTree RankThreeGenerator)
    (hweight : tree.weight = 1) :
    tree = rankThreeAtom 0 ∨
      tree = rankThreeAtom 1 ∨
        tree = rankThreeAtom 2 := by
  obtain ⟨i, rfl⟩ := HallTree.weight_eq_iff.mp hweight
  cases i with
  | up i =>
      fin_cases i <;>
        simp [rankThreeAtom, rankThreeGenerator]

theorem rank_two_cases
    (tree : HallTree RankThreeGenerator)
    (hbasic : tree.IsBasic)
    (hweight : tree.weight = 2) :
    tree = rankPairTree 0 1 ∨
      tree = rankPairTree 0 2 ∨
        tree = rankPairTree 1 2 := by
  cases tree with
  | atom i => simp at hweight
  | commutator left right =>
      have hleftPos := left.weight_pos
      have hrightPos := right.weight_pos
      have hleftWeight : left.weight = 1 := by
        simp only [HallTree.weight_commutator] at hweight
        omega
      have hrightWeight : right.weight = 1 := by
        simp only [HallTree.weight_commutator] at hweight
        omega
      obtain ⟨leftIndex, rfl⟩ :=
        HallTree.weight_eq_iff.mp hleftWeight
      obtain ⟨rightIndex, rfl⟩ :=
        HallTree.weight_eq_iff.mp hrightWeight
      cases leftIndex with
      | up leftIndex =>
          cases rightIndex with
          | up rightIndex =>
              have horder :=
                hbasic.2.2.1
              change
                rankThreeAtom rightIndex <
                  rankThreeAtom leftIndex at horder
              fin_cases leftIndex <;>
                fin_cases rightIndex <;>
                  simp at horder <;>
                  simp [rankPairTree, rankThreeAtom,
                    rankThreeGenerator]

theorem rank_basic_cases
    (tree : HallTree RankThreeGenerator)
    (hbasic : tree.IsBasic)
    (hweight : tree.weight = 3) :
    tree = rankTripleTree 0 1 0 ∨
      tree = rankTripleTree 0 1 1 ∨
      tree = rankTripleTree 0 1 2 ∨
      tree = rankTripleTree 0 2 0 ∨
      tree = rankTripleTree 0 2 1 ∨
      tree = rankTripleTree 0 2 2 ∨
      tree = rankTripleTree 1 2 1 ∨
      tree = rankTripleTree 1 2 2 := by
  cases tree with
  | atom i => simp at hweight
  | commutator left right =>
      have hleftPos := left.weight_pos
      have hrightPos := right.weight_pos
      have hsum : left.weight + right.weight = 3 := hweight
      have hrightLtLeft : right < left := hbasic.2.2.1
      have hleftWeight : left.weight = 2 := by
        by_contra hne
        have hl : left.weight = 1 := by omega
        have hr : right.weight = 2 := by omega
        exact (not_lt_of_ge
          (HallTree.lt_weight_lt (by omega : left.weight < right.weight)).le)
          hrightLtLeft
      have hrightWeight : right.weight = 1 := by omega
      obtain ⟨rightIndex, rfl⟩ :=
        HallTree.weight_eq_iff.mp hrightWeight
      cases left with
      | atom i => simp at hleftWeight
      | commutator leftLeft leftRight =>
          have hleftLeftPos := leftLeft.weight_pos
          have hleftRightPos := leftRight.weight_pos
          have hleftLeftWeight : leftLeft.weight = 1 := by
            simp only [HallTree.weight_commutator] at hleftWeight
            omega
          have hleftRightWeight : leftRight.weight = 1 := by
            simp only [HallTree.weight_commutator] at hleftWeight
            omega
          obtain ⟨leftIndex, rfl⟩ :=
            HallTree.weight_eq_iff.mp hleftLeftWeight
          obtain ⟨middleIndex, rfl⟩ :=
            HallTree.weight_eq_iff.mp hleftRightWeight
          cases leftIndex with
          | up leftIndex =>
              cases middleIndex with
              | up middleIndex =>
                  cases rightIndex with
                  | up rightIndex =>
                      have hmiddleLtLeft :
                          rankThreeAtom middleIndex <
                            rankThreeAtom leftIndex := by
                        simpa [rankThreeAtom, rankThreeGenerator] using
                          hbasic.1.2.2.1
                      have hmiddleLeRight :
                          rankThreeAtom middleIndex ≤
                            rankThreeAtom rightIndex := by
                        simpa [rankThreeAtom, rankThreeGenerator] using
                          hbasic.2.2.2
                      fin_cases leftIndex <;>
                        fin_cases middleIndex <;>
                          fin_cases rightIndex <;>
                            simp at hmiddleLtLeft hmiddleLeRight <;>
                            simp [rankTripleTree,
                              rankPairTree, rankThreeAtom,
                              rankThreeGenerator]

inductive RankTwoIndex
  | c12
  | c13
  | c23
  deriving DecidableEq, Fintype

inductive RankThreeIndex
  | c121
  | c122
  | c123
  | c131
  | c132
  | c133
  | c232
  | c233
  deriving DecidableEq, Fintype

def rankTwoTree :
    RankTwoIndex → HallTree RankThreeGenerator
  | .c12 => rankPairTree 0 1
  | .c13 => rankPairTree 0 2
  | .c23 => rankPairTree 1 2

def rankThreeTree :
    RankThreeIndex → HallTree RankThreeGenerator
  | .c121 => rankTripleTree 0 1 0
  | .c122 => rankTripleTree 0 1 1
  | .c123 => rankTripleTree 0 1 2
  | .c131 => rankTripleTree 0 2 0
  | .c132 => rankTripleTree 0 2 1
  | .c133 => rankTripleTree 0 2 2
  | .c232 => rankTripleTree 1 2 1
  | .c233 => rankTripleTree 1 2 2

theorem rank_three_basic (i : Fin 3) :
    (rankThreeAtom i).IsBasic := by
  simp [rankThreeAtom]

theorem rank_one_tree (i : Fin 3) :
    (rankThreeAtom i).weight = 1 := rfl

theorem rank_tree_basic
    {i j : Fin 3} (hij : i < j) :
    (rankPairTree i j).IsBasic := by
  exact HallTree.basic_commutator_admissible
    (u := rankThreeAtom j) (v := rankThreeAtom i)
    (rank_three_basic j)
    (rank_three_basic i)
    ((rank_atom i j).2 hij)
    trivial

theorem rank_triple_tree
    {i j k : Fin 3} (hij : i < j) (hik : i ≤ k) :
    (rankTripleTree i j k).IsBasic := by
  exact HallTree.basic_commutator_admissible
    (u := rankPairTree i j) (v := rankThreeAtom k)
    (rank_tree_basic hij)
    (rank_three_basic k)
    (HallTree.lt_weight_lt (by
      simp [rankPairTree, rankThreeAtom]))
    ((rank_three_atom i k).2 hik)

theorem two_tree_basic
    (i : RankTwoIndex) :
    (rankTwoTree i).IsBasic := by
  cases i
  · exact rank_tree_basic (by decide)
  · exact rank_tree_basic (by decide)
  · exact rank_tree_basic (by decide)

theorem rank_two_tree
    (i : RankTwoIndex) :
    (rankTwoTree i).weight = 2 := by
  cases i <;> rfl

theorem rank_weight_tree
    (i : RankThreeIndex) :
    (rankThreeTree i).IsBasic := by
  cases i
  · exact rank_triple_tree (by decide) (by decide)
  · exact rank_triple_tree (by decide) (by decide)
  · exact rank_triple_tree (by decide) (by decide)
  · exact rank_triple_tree (by decide) (by decide)
  · exact rank_triple_tree (by decide) (by decide)
  · exact rank_triple_tree (by decide) (by decide)
  · exact rank_triple_tree (by decide) (by decide)
  · exact rank_triple_tree (by decide) (by decide)

theorem rank_three_tree
    (i : RankThreeIndex) :
    (rankThreeTree i).weight = 3 := by
  cases i <;> rfl

theorem rank_atom_injective :
    Function.Injective rankThreeAtom := by
  intro i j hij
  simpa [rankThreeAtom, rankThreeGenerator] using hij

theorem two_tree_injective :
    Function.Injective rankTwoTree := by
  intro i j hij
  cases i <;> cases j <;>
    simp [rankTwoTree, rankPairTree,
      rankThreeAtom, rankThreeGenerator] at hij ⊢

theorem rank_tree_injective :
    Function.Injective rankThreeTree := by
  intro i j hij
  cases i <;> cases j <;>
    simp [rankThreeTree, rankTripleTree,
      rankPairTree, rankThreeAtom, rankThreeGenerator] at hij ⊢

theorem concrete_tree_injective
    {d r : ℕ} :
    Function.Injective
      (fun i : (standardHallFamily d r).index =>
        concreteBasicTree i) := by
  intro i j hij
  apply concrete_basic_injective
  simpa [concrete_basic_word] using
    congrArg HallTree.toCWord hij

noncomputable def rankWeightCanonical
    (i : Fin 3) :
    (standardHallFamily 3 1).index :=
  Classical.choose
    (concrete_basic_tree
      (rank_three_basic i)
      (rank_one_tree i))

noncomputable def rankTwoCanonical
    (i : RankTwoIndex) :
    (standardHallFamily 3 2).index :=
  Classical.choose
    (concrete_basic_tree
      (two_tree_basic i)
      (rank_two_tree i))

noncomputable def rankThreeCanonical
    (i : RankThreeIndex) :
    (standardHallFamily 3 3).index :=
  Classical.choose
    (concrete_basic_tree
      (rank_weight_tree i)
      (rank_three_tree i))

@[simp] theorem concrete_tree_rank
    (i : Fin 3) :
    concreteBasicTree (rankWeightCanonical i) =
      rankThreeAtom i :=
  Classical.choose_spec
    (concrete_basic_tree
      (rank_three_basic i)
      (rank_one_tree i))

@[simp] theorem tree_rank_canonical
    (i : RankTwoIndex) :
    concreteBasicTree (rankTwoCanonical i) =
      rankTwoTree i :=
  Classical.choose_spec
    (concrete_basic_tree
      (two_tree_basic i)
      (rank_two_tree i))

@[simp] theorem concrete_tree_canonical
    (i : RankThreeIndex) :
    concreteBasicTree (rankThreeCanonical i) =
      rankThreeTree i :=
  Classical.choose_spec
    (concrete_basic_tree
      (rank_weight_tree i)
      (rank_three_tree i))

noncomputable def rankThreeIndex :
    Fin 3 ≃ (standardHallFamily 3 1).index :=
  Equiv.ofBijective rankWeightCanonical ⟨by
    intro i j hij
    apply rank_atom_injective
    rw [← concrete_tree_rank i,
      ← concrete_tree_rank j, hij], by
    intro j
    rcases rank_three_cases
      (concreteBasicTree j)
      (concrete_tree_weight j) with h | h | h
    · exact ⟨0, concrete_tree_injective
        ((concrete_tree_rank 0).trans h.symm)⟩
    · exact ⟨1, concrete_tree_injective
        ((concrete_tree_rank 1).trans h.symm)⟩
    · exact ⟨2, concrete_tree_injective
        ((concrete_tree_rank 2).trans h.symm)⟩⟩

noncomputable def rankTwoIndex :
    RankTwoIndex ≃
      (standardHallFamily 3 2).index :=
  Equiv.ofBijective rankTwoCanonical ⟨by
    intro i j hij
    apply two_tree_injective
    rw [← tree_rank_canonical i,
      ← tree_rank_canonical j, hij], by
    intro j
    rcases rank_two_cases
      (concreteBasicTree j)
      (concrete_hall_tree j)
      (concrete_tree_weight j) with h | h | h
    · exact ⟨.c12, concrete_tree_injective
        ((tree_rank_canonical .c12).trans
          h.symm)⟩
    · exact ⟨.c13, concrete_tree_injective
        ((tree_rank_canonical .c13).trans
          h.symm)⟩
    · exact ⟨.c23, concrete_tree_injective
        ((tree_rank_canonical .c23).trans
          h.symm)⟩⟩

noncomputable def rankIndexEquiv :
    RankThreeIndex ≃
      (standardHallFamily 3 3).index :=
  Equiv.ofBijective rankThreeCanonical ⟨by
    intro i j hij
    apply rank_tree_injective
    rw [← concrete_tree_canonical i,
      ← concrete_tree_canonical j, hij], by
    intro j
    rcases rank_basic_cases
      (concreteBasicTree j)
      (concrete_hall_tree j)
      (concrete_tree_weight j) with
      h | h | h | h | h | h | h | h
    · exact ⟨.c121, concrete_tree_injective
        ((concrete_tree_canonical .c121).trans
          h.symm)⟩
    · exact ⟨.c122, concrete_tree_injective
        ((concrete_tree_canonical .c122).trans
          h.symm)⟩
    · exact ⟨.c123, concrete_tree_injective
        ((concrete_tree_canonical .c123).trans
          h.symm)⟩
    · exact ⟨.c131, concrete_tree_injective
        ((concrete_tree_canonical .c131).trans
          h.symm)⟩
    · exact ⟨.c132, concrete_tree_injective
        ((concrete_tree_canonical .c132).trans
          h.symm)⟩
    · exact ⟨.c133, concrete_tree_injective
        ((concrete_tree_canonical .c133).trans
          h.symm)⟩
    · exact ⟨.c232, concrete_tree_injective
        ((concrete_tree_canonical .c232).trans
          h.symm)⟩
    · exact ⟨.c233, concrete_tree_injective
        ((concrete_tree_canonical .c233).trans
          h.symm)⟩⟩

/-- The recursive Hall order of a weight-one rank-three factor. -/
@[simp] theorem standard_order_rank
    (order : Fin 3 → ℕ) (i : Fin 3) :
    standardFactorOrder order
        (rankThreeIndex i) =
      order i := by
  change
    hallTreeOrder (fun j : FreeGenerator 3 => order j.down)
        (concreteBasicTree (rankWeightCanonical i)) =
      order i
  rw [concrete_tree_rank]
  rfl

/-- The pairwise gcd attached to a weight-two rank-three Hall factor. -/
def rankTwoOrder
    (order : Fin 3 → ℕ) :
    RankTwoIndex → ℕ
  | .c12 => Nat.gcd (order 0) (order 1)
  | .c13 => Nat.gcd (order 0) (order 2)
  | .c23 => Nat.gcd (order 1) (order 2)

/-- The recursive Hall order agrees with the expected pairwise gcd. -/
@[simp] theorem standard_rank_two
    (order : Fin 3 → ℕ) (i : RankTwoIndex) :
    standardFactorOrder order
        (rankTwoIndex i) =
      rankTwoOrder order i := by
  change
    hallTreeOrder (fun j : FreeGenerator 3 => order j.down)
        (concreteBasicTree (rankTwoCanonical i)) =
      rankTwoOrder order i
  rw [tree_rank_canonical]
  cases i <;>
    simp [rankTwoTree, rankPairTree, rankThreeAtom,
      rankThreeGenerator, rankTwoOrder, hallTreeOrder,
      Nat.gcd_comm]

/-- The pairwise or three-way gcd attached to a weight-three factor. -/
def rankThreeOrder
    (order : Fin 3 → ℕ) :
    RankThreeIndex → ℕ
  | .c121 | .c122 => Nat.gcd (order 0) (order 1)
  | .c123 | .c132 => Nat.gcd (Nat.gcd (order 0) (order 1)) (order 2)
  | .c131 | .c133 => Nat.gcd (order 0) (order 2)
  | .c232 | .c233 => Nat.gcd (order 1) (order 2)

/-- The recursive Hall order agrees with the gcd prescribed in Theorem 1. -/
@[simp] theorem standard_rank_weight
    (order : Fin 3 → ℕ) (i : RankThreeIndex) :
    standardFactorOrder order
        (rankIndexEquiv i) =
      rankThreeOrder order i := by
  change
    hallTreeOrder (fun j : FreeGenerator 3 => order j.down)
        (concreteBasicTree (rankThreeCanonical i)) =
      rankThreeOrder order i
  rw [concrete_tree_canonical]
  cases i <;>
    simp [rankThreeTree, rankTripleTree,
      rankPairTree, rankThreeAtom, rankThreeGenerator,
      rankThreeOrder, hallTreeOrder, Nat.gcd_comm,
      Nat.gcd_left_comm, Nat.gcd_assoc]

end P1960
end Struik

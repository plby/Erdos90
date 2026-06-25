import Towers.Group.NilpotentProducts.ClassThreeCover
import Towers.Group.NilpotentProducts.GeneralResidues
import Mathlib.Data.Finset.Sort


/-!
# Hall basic commutators of weights at most three in arbitrary rank

The canonical Hall factors below the class-four cutoff are indexed by:

* one generator index in weight one;
* one strictly increasing pair in weight two;
* two factors for every increasing pair and two factors for every
  increasing triple in weight three.
-/

namespace Struik
namespace P1960

open Towers
open Towers.HallTree
open Towers.TCTex
open Towers.TCTex

universe u

abbrev LowWeightGenerator (t : ℕ) := FreeGenerator.{u} t

def lowWeightGenerator {t : ℕ} (i : Fin t) :
    LowWeightGenerator.{u} t :=
  ULift.up i

def lowWeightAtom {t : ℕ} (i : Fin t) :
    HallTree (LowWeightGenerator.{u} t) :=
  .atom (lowWeightGenerator i)

def lowPairTree {t : ℕ} (i j : Fin t) :
    HallTree (LowWeightGenerator.{u} t) :=
  .commutator (lowWeightAtom j) (lowWeightAtom i)

def lowTripleTree {t : ℕ} (i j k : Fin t) :
    HallTree (LowWeightGenerator.{u} t) :=
  .commutator (lowPairTree i j) (lowWeightAtom k)

/-- Two distinct generator positions, oriented by the Hall order on atoms. -/
@[ext]
structure LowPairIndex (t : ℕ) where
  i : Fin t
  j : Fin t
  lt : lowWeightAtom.{u} i < lowWeightAtom j
  deriving DecidableEq

/-- The Hall-oriented pair index as a subtype of the finite type of ordered
pairs. -/
def lowPairSubtype (t : ℕ) :
    LowPairIndex.{u} t ≃
      {p : Fin t × Fin t //
        lowWeightAtom.{u} p.1 < lowWeightAtom p.2} where
  toFun q := ⟨(q.i, q.j), q.lt⟩
  invFun q := ⟨q.1.1, q.1.2, q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

noncomputable instance lowPairFintype (t : ℕ) :
    Fintype (LowPairIndex.{u} t) :=
  Fintype.ofEquiv
    {p : Fin t × Fin t //
      lowWeightAtom.{u} p.1 < lowWeightAtom p.2}
    (lowPairSubtype t).symm

/-- Three distinct generator positions in increasing Hall-atom order. -/
@[ext]
structure LowTripleIndex (t : ℕ) where
  i : Fin t
  j : Fin t
  k : Fin t
  lt_ij : lowWeightAtom.{u} i < lowWeightAtom j
  lt_jk : lowWeightAtom.{u} j < lowWeightAtom k
  deriving DecidableEq

theorem low_weight_cases
    {t : ℕ}
    (tree : HallTree (LowWeightGenerator.{u} t))
    (hweight : tree.weight = 1) :
    ∃ i : Fin t, tree = lowWeightAtom i := by
  obtain ⟨i, rfl⟩ := HallTree.weight_eq_iff.mp hweight
  cases i with
  | up i => exact ⟨i, rfl⟩

theorem low_two_cases
    {t : ℕ}
    (tree : HallTree (LowWeightGenerator.{u} t))
    (hbasic : tree.IsBasic)
    (hweight : tree.weight = 2) :
    ∃ q : LowPairIndex.{u} t,
      tree = lowPairTree q.i q.j := by
  cases tree with
  | atom i => simp at hweight
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
      obtain ⟨leftIndex, rfl⟩ :=
        HallTree.weight_eq_iff.mp hleftWeight
      obtain ⟨rightIndex, rfl⟩ :=
        HallTree.weight_eq_iff.mp hrightWeight
      cases leftIndex with
      | up leftIndex =>
          cases rightIndex with
          | up rightIndex =>
              have horder :
                  lowWeightAtom rightIndex <
                    lowWeightAtom leftIndex := by
                simpa [lowWeightAtom, lowWeightGenerator] using
                  hbasic.2.2.1
              exact
                ⟨⟨rightIndex, leftIndex, horder⟩, rfl⟩

/-- The leaf triples satisfying Hall's weight-three admissibility
condition. -/
abbrev LowThreeIndex (t : ℕ) :=
  {p : Fin t × Fin t × Fin t //
    lowWeightAtom.{u} p.1 < lowWeightAtom.{u} p.2.1 ∧
      lowWeightAtom.{u} p.1 ≤ lowWeightAtom.{u} p.2.2}

/-- The three leaf positions of an explicit weight-three Hall factor. -/
def lowThreeLeaves {t : ℕ}
    (q : LowThreeIndex.{u} t) :
    Fin t × Fin t × Fin t :=
  q.1

/-- The Hall tree represented by an explicit weight-three index. -/
def lowThreeTree {t : ℕ} (q : LowThreeIndex t) :
    HallTree (LowWeightGenerator.{u} t) :=
  lowTripleTree
    (lowThreeLeaves q).1
    (lowThreeLeaves q).2.1
    (lowThreeLeaves q).2.2

theorem low_atom_basic {t : ℕ} (i : Fin t) :
    (lowWeightAtom.{u} i).IsBasic := by
  simp [lowWeightAtom]

theorem low_pair_basic
    {t : ℕ} (q : LowPairIndex.{u} t) :
    (lowPairTree.{u} q.i q.j).IsBasic := by
  exact HallTree.basic_commutator_admissible
    (u := lowWeightAtom q.j) (v := lowWeightAtom q.i)
    (low_atom_basic q.j)
    (low_atom_basic q.i)
    q.lt
    trivial

theorem low_triple_tree
    {t : ℕ} {i j k : Fin t}
    (hij : lowWeightAtom.{u} i < lowWeightAtom j)
    (hik : lowWeightAtom.{u} i ≤ lowWeightAtom k) :
    (lowTripleTree.{u} i j k).IsBasic := by
  exact HallTree.basic_commutator_admissible
    (u := lowPairTree i j) (v := lowWeightAtom k)
    (HallTree.basic_commutator_admissible
      (u := lowWeightAtom j) (v := lowWeightAtom i)
      (low_atom_basic j) (low_atom_basic i)
      hij trivial)
    (low_atom_basic k)
    (HallTree.lt_weight_lt (by
      simp [lowPairTree, lowWeightAtom]))
    hik

theorem low_tree_basic
    {t : ℕ} (q : LowThreeIndex t) :
    (lowThreeTree.{u} q).IsBasic := by
  exact low_triple_tree q.2.1 q.2.2

@[simp] theorem low_weight_atom
    {t : ℕ} (i : Fin t) :
    (lowWeightAtom.{u} i).weight = 1 :=
  rfl

theorem low_atom_injective {t : ℕ} :
    Function.Injective (lowWeightAtom.{u} : Fin t →
      HallTree (LowWeightGenerator.{u} t)) := by
  intro i j hij
  simpa [lowWeightAtom, lowWeightGenerator] using hij

/-- The finite set of weight-one Hall atoms. -/
noncomputable def lowAtomFinset (t : ℕ) :
    Finset (HallTree (LowWeightGenerator.{u} t)) :=
  Finset.univ.image lowWeightAtom

@[simp] theorem low_atom_finset (t : ℕ) :
    (lowAtomFinset.{u} t).card = t := by
  rw [lowAtomFinset,
    Finset.card_image_of_injective _ low_atom_injective]
  simp

/-- Enumerate the generator atoms in increasing Hall order. -/
noncomputable def lowAtomIso (t : ℕ) :
    Fin t ≃o
      {w : HallTree (LowWeightGenerator.{u} t) //
        w ∈ lowAtomFinset.{u} t} :=
  Finset.orderIsoOfFin (lowAtomFinset.{u} t)
    (low_atom_finset.{u} t)

/-- The numeric position of a generator atom in increasing Hall order. -/
noncomputable def lowHallRank
    {t : ℕ} (i : Fin t) : Fin t :=
  (lowAtomIso.{u} t).symm
    ⟨lowWeightAtom i, by
      simp [lowAtomFinset]⟩

theorem low_rank_bijective (t : ℕ) :
    Function.Bijective (lowHallRank.{u} : Fin t → Fin t) := by
  constructor
  · intro i j hij
    have hsubtype :=
      congrArg (lowAtomIso.{u} t) hij
    simp only [lowHallRank,
      OrderIso.apply_symm_apply] at hsubtype
    exact low_atom_injective
      (congrArg Subtype.val hsubtype)
  · intro r
    let w := lowAtomIso.{u} t r
    obtain ⟨i, _, hi⟩ :=
      Finset.mem_image.mp w.property
    refine ⟨i, ?_⟩
    have hsubtype :
        (⟨lowWeightAtom i, by
          simp [lowAtomFinset]⟩ :
          {w : HallTree (LowWeightGenerator.{u} t) //
            w ∈ lowAtomFinset.{u} t}) =
          w := by
      apply Subtype.ext
      exact hi
    change
      (lowAtomIso.{u} t).symm
          ⟨lowWeightAtom i, _⟩ =
        r
    rw [hsubtype]
    exact (lowAtomIso.{u} t).symm_apply_apply r

/-- Generator positions, permuted into increasing Hall-atom order. -/
noncomputable def lowWeightRank (t : ℕ) :
    Fin t ≃ Fin t :=
  Equiv.ofBijective lowHallRank
    (low_rank_bijective.{u} t)

@[simp] theorem low_rank_equiv
    {t : ℕ} (i : Fin t) :
    lowWeightRank.{u} t i =
      lowHallRank.{u} i :=
  rfl

@[simp] theorem low_rank_symm
    {t : ℕ} (i : Fin t) :
    (lowWeightRank.{u} t).symm
        (lowHallRank.{u} i) =
      i := by
  change
    (lowWeightRank.{u} t).symm
        (lowWeightRank.{u} t i) =
      i
  exact (lowWeightRank.{u} t).symm_apply_apply i

@[simp] theorem low_weight_symm
    {t : ℕ} (i : Fin t) :
    lowHallRank.{u}
        ((lowWeightRank.{u} t).symm i) =
      i := by
  change
    lowWeightRank.{u} t
        ((lowWeightRank.{u} t).symm i) =
      i
  exact (lowWeightRank.{u} t).apply_symm_apply i

theorem low_hall_rank
    {t : ℕ} (i j : Fin t) :
    lowHallRank.{u} i < lowHallRank.{u} j ↔
      lowWeightAtom.{u} i < lowWeightAtom.{u} j := by
  unfold lowHallRank
  simpa only [Subtype.mk_lt_mk] using
    ((lowAtomIso.{u} t).symm.lt_iff_lt :
      (lowAtomIso.{u} t).symm
          ⟨lowWeightAtom.{u} i, by simp [lowAtomFinset]⟩ <
        (lowAtomIso.{u} t).symm
          ⟨lowWeightAtom.{u} j, by simp [lowAtomFinset]⟩ ↔
      (⟨lowWeightAtom.{u} i, by simp [lowAtomFinset]⟩ :
          {w : HallTree (LowWeightGenerator.{u} t) //
            w ∈ lowAtomFinset.{u} t}) <
        ⟨lowWeightAtom.{u} j, by simp [lowAtomFinset]⟩)

theorem low_weight_rank
    {t : ℕ} (i j : Fin t) :
    lowHallRank.{u} i ≤ lowHallRank.{u} j ↔
      lowWeightAtom.{u} i ≤ lowWeightAtom.{u} j := by
  unfold lowHallRank
  simpa only [Subtype.mk_le_mk] using
    ((lowAtomIso.{u} t).symm.le_iff_le :
      (lowAtomIso.{u} t).symm
          ⟨lowWeightAtom.{u} i, by simp [lowAtomFinset]⟩ ≤
        (lowAtomIso.{u} t).symm
          ⟨lowWeightAtom.{u} j, by simp [lowAtomFinset]⟩ ↔
      (⟨lowWeightAtom.{u} i, by simp [lowAtomFinset]⟩ :
          {w : HallTree (LowWeightGenerator.{u} t) //
            w ∈ lowAtomFinset.{u} t}) ≤
        ⟨lowWeightAtom.{u} j, by simp [lowAtomFinset]⟩)

@[simp] theorem low_weight_pair
    {t : ℕ} (i j : Fin t) :
    (lowPairTree.{u} i j).weight = 2 :=
  rfl

@[simp] theorem low_weight_tree
    {t : ℕ} (q : LowThreeIndex t) :
    (lowThreeTree.{u} q).weight = 3 :=
  rfl

theorem low_basic_cases
    {t : ℕ}
    (tree : HallTree (LowWeightGenerator.{u} t))
    (hbasic : tree.IsBasic)
    (hweight : tree.weight = 3) :
    ∃ q : LowThreeIndex t,
      tree = lowThreeTree q := by
  cases tree with
  | atom i => simp at hweight
  | commutator left right =>
      have hleftPos := left.weight_pos
      have hrightPos := right.weight_pos
      have hrightLtLeft : right < left := hbasic.2.2.1
      have hleftWeight : left.weight = 2 := by
        simp only [HallTree.weight_commutator] at hweight
        by_contra hne
        have hl : left.weight = 1 := by omega
        have hr : right.weight = 2 := by omega
        exact (not_lt_of_ge
          (HallTree.lt_weight_lt (by omega : left.weight < right.weight)).le)
          hrightLtLeft
      have hrightWeight : right.weight = 1 := by
        simp only [HallTree.weight_commutator] at hweight
        omega
      obtain ⟨rightIndex, rfl⟩ :=
        HallTree.weight_eq_iff.mp hrightWeight
      cases left with
      | atom i => simp at hleftWeight
      | commutator leftLeft leftRight =>
          have hleftLeftWeight : leftLeft.weight = 1 := by
            simp only [HallTree.weight_commutator] at hleftWeight
            have := leftLeft.weight_pos
            have := leftRight.weight_pos
            omega
          have hleftRightWeight : leftRight.weight = 1 := by
            simp only [HallTree.weight_commutator] at hleftWeight
            have := leftLeft.weight_pos
            have := leftRight.weight_pos
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
                          lowWeightAtom middleIndex <
                            lowWeightAtom leftIndex := by
                        simpa [lowWeightAtom, lowWeightGenerator] using
                          hbasic.1.2.2.1
                      have hmiddleLeRight :
                          lowWeightAtom middleIndex ≤
                            lowWeightAtom rightIndex := by
                        simpa [lowWeightAtom, lowWeightGenerator] using
                          hbasic.2.2.2
                      exact
                        ⟨⟨(middleIndex, leftIndex, rightIndex),
                            hmiddleLtLeft, hmiddleLeRight⟩, rfl⟩

theorem low_pair_tree {t : ℕ} :
    Function.Injective
      (fun q : LowPairIndex.{u} t =>
        lowPairTree.{u} q.i q.j) := by
  rintro ⟨i, j, hij⟩ ⟨i', j', hij'⟩ h
  have hparts := HallTree.commutator.inj
    (show HallTree.commutator (lowWeightAtom j) (lowWeightAtom i) =
      HallTree.commutator (lowWeightAtom j') (lowWeightAtom i') from h)
  have hjUp := HallTree.atom.inj hparts.1
  have hiUp := HallTree.atom.inj hparts.2
  change ULift.up j = ULift.up j' at hjUp
  change ULift.up i = ULift.up i' at hiUp
  have hj : j = j' := ULift.up.inj hjUp
  have hi : i = i' := ULift.up.inj hiUp
  subst i'
  subst j'
  rfl

theorem low_leaves_injective {t : ℕ} :
    Function.Injective (lowThreeLeaves : LowThreeIndex t →
      Fin t × Fin t × Fin t) := by
  exact Subtype.val_injective

theorem low_tree_injective {t : ℕ} :
    Function.Injective
      (fun q : Fin t × Fin t × Fin t =>
        lowTripleTree.{u} q.1 q.2.1 q.2.2) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have houter := HallTree.commutator.inj
    (show HallTree.commutator (lowPairTree i j) (lowWeightAtom k) =
      HallTree.commutator (lowPairTree i' j') (lowWeightAtom k') from h)
  have hinner := HallTree.commutator.inj houter.1
  have hjUp := HallTree.atom.inj hinner.1
  have hiUp := HallTree.atom.inj hinner.2
  have hkUp := HallTree.atom.inj houter.2
  change ULift.up j = ULift.up j' at hjUp
  change ULift.up i = ULift.up i' at hiUp
  change ULift.up k = ULift.up k' at hkUp
  have hj : j = j' := ULift.up.inj hjUp
  have hi : i = i' := ULift.up.inj hiUp
  have hk : k = k' := ULift.up.inj hkUp
  subst i'
  subst j'
  subst k'
  rfl

theorem low_three_tree {t : ℕ} :
    Function.Injective
      (lowThreeTree.{u} :
        LowThreeIndex t →
          HallTree (LowWeightGenerator.{u} t)) :=
  low_tree_injective.comp low_leaves_injective

theorem tree_injective_low
    {t r : ℕ} :
    Function.Injective
      (fun i : (standardHallFamily.{u} t r).index =>
        concreteBasicTree i) := by
  intro i j hij
  apply concrete_basic_injective
  simpa [concrete_basic_word] using
    congrArg HallTree.toCWord hij

noncomputable def lowWeightCanonical
    {t : ℕ} (i : Fin t) :
    (standardHallFamily.{u} t 1).index :=
  Classical.choose
    (concrete_basic_tree
      (low_atom_basic i) (low_weight_atom i))

noncomputable def lowTwoCanonical
    {t : ℕ} (q : LowPairIndex.{u} t) :
    (standardHallFamily.{u} t 2).index :=
  Classical.choose
    (concrete_basic_tree
      (low_pair_basic q)
      (low_weight_pair q.i q.j))

noncomputable def lowThreeCanonical
    {t : ℕ} (q : LowThreeIndex t) :
    (standardHallFamily.{u} t 3).index :=
  Classical.choose
    (concrete_basic_tree
      (low_tree_basic q)
      (low_weight_tree q))

@[simp] theorem tree_low_canonical
    {t : ℕ} (i : Fin t) :
    concreteBasicTree (lowWeightCanonical.{u} i) =
      lowWeightAtom i :=
  Classical.choose_spec
    (concrete_basic_tree
      (low_atom_basic i) (low_weight_atom i))

@[simp] theorem concrete_low_canonical
    {t : ℕ} (q : LowPairIndex.{u} t) :
    concreteBasicTree (lowTwoCanonical.{u} q) =
      lowPairTree q.i q.j :=
  Classical.choose_spec
    (concrete_basic_tree
      (low_pair_basic q)
      (low_weight_pair q.i q.j))

@[simp] theorem concrete_tree_low
    {t : ℕ} (q : LowThreeIndex t) :
    concreteBasicTree (lowThreeCanonical.{u} q) =
      lowThreeTree q :=
  Classical.choose_spec
    (concrete_basic_tree
      (low_tree_basic q)
      (low_weight_tree q))

noncomputable def lowWeightIndex
    (t : ℕ) :
    Fin t ≃ (standardHallFamily.{u} t 1).index :=
  Equiv.ofBijective lowWeightCanonical ⟨by
    intro i j hij
    apply low_atom_injective
    rw [← tree_low_canonical i,
      ← tree_low_canonical j, hij], by
    intro j
    obtain ⟨i, hi⟩ :=
      low_weight_cases
        (concreteBasicTree j)
        (concrete_tree_weight j)
    exact ⟨i, tree_injective_low
      ((tree_low_canonical i).trans hi.symm)⟩⟩

noncomputable def lowTwoIndex
    (t : ℕ) :
    LowPairIndex.{u} t ≃
      (standardHallFamily.{u} t 2).index :=
  Equiv.ofBijective lowTwoCanonical ⟨by
    intro q r hqr
    apply low_pair_tree
    change lowPairTree q.i q.j =
      lowPairTree r.i r.j
    rw [← concrete_low_canonical q,
      ← concrete_low_canonical r, hqr], by
    intro j
    obtain ⟨q, hq⟩ :=
      low_two_cases
        (concreteBasicTree j)
        (concrete_hall_tree j)
        (concrete_tree_weight j)
    exact ⟨q, tree_injective_low
      ((concrete_low_canonical q).trans hq.symm)⟩⟩

noncomputable def lowIndexEquiv
    (t : ℕ) :
    LowThreeIndex t ≃
      (standardHallFamily.{u} t 3).index :=
  Equiv.ofBijective lowThreeCanonical ⟨by
    intro q r hqr
    apply low_three_tree
    change lowThreeTree q = lowThreeTree r
    rw [← concrete_tree_low q,
      ← concrete_tree_low r, hqr], by
    intro j
    obtain ⟨q, hq⟩ :=
      low_basic_cases
        (concreteBasicTree j)
        (concrete_hall_tree j)
        (concrete_tree_weight j)
    exact ⟨q, tree_injective_low
      ((concrete_tree_low q).trans hq.symm)⟩⟩

/-- The recursive order of an explicit pair factor. -/
def lowPairOrder
    {t : ℕ} (order : Fin t → ℕ)
    (q : LowPairIndex.{u} t) : ℕ :=
  Nat.gcd (order q.i) (order q.j)

/-- The recursive order of an explicit weight-three factor. -/
def lowThreeOrder
    {t : ℕ} (order : Fin t → ℕ)
    (q : LowThreeIndex.{u} t) : ℕ :=
  Nat.gcd (Nat.gcd (order (lowThreeLeaves q).1)
    (order (lowThreeLeaves q).2.1))
    (order (lowThreeLeaves q).2.2)

@[simp] theorem standard_order_low
    {t : ℕ} (order : Fin t → ℕ) (i : Fin t) :
    standardFactorOrder order
        (lowWeightIndex.{u} t i) =
      order i := by
  change
    hallTreeOrder (fun j : FreeGenerator.{u} t => order j.down)
        (concreteBasicTree (lowWeightCanonical.{u} i)) =
      order i
  rw [tree_low_canonical]
  rfl

@[simp] theorem standard_low_two
    {t : ℕ} (order : Fin t → ℕ)
    (q : LowPairIndex.{u} t) :
    standardFactorOrder order
        (lowTwoIndex.{u} t q) =
      lowPairOrder order q := by
  change
    hallTreeOrder (fun j : FreeGenerator.{u} t => order j.down)
        (concreteBasicTree (lowTwoCanonical.{u} q)) =
      lowPairOrder order q
  rw [concrete_low_canonical]
  simp [lowPairTree, lowWeightAtom, lowWeightGenerator,
    hallTreeOrder, lowPairOrder, Nat.gcd_comm]

@[simp] theorem standard_low_three
    {t : ℕ} (order : Fin t → ℕ)
    (q : LowThreeIndex t) :
    standardFactorOrder order
        (lowIndexEquiv.{u} t q) =
      lowThreeOrder order q := by
  change
    hallTreeOrder (fun j : FreeGenerator.{u} t => order j.down)
        (concreteBasicTree (lowThreeCanonical.{u} q)) =
      lowThreeOrder order q
  rw [concrete_tree_low]
  rcases q with ⟨⟨i, j, k⟩, hq⟩
  simp [lowThreeTree, lowThreeLeaves,
    lowTripleTree, lowPairTree, lowWeightAtom,
    lowWeightGenerator, lowThreeOrder, hallTreeOrder,
    Nat.gcd_comm, Nat.gcd_left_comm]

end P1960
end Struik

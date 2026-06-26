import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex
import Towers.Group.HallWords
import Towers.Group.LowerMagnusMap
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace



namespace Towers

universe u

/--
A bracket tree before evaluation in a group.  Unlike `CWord`, this type
has a canonical weight-one grading built into its leaves.
-/
inductive HallTree (α : Type u) where
  | atom : α → HallTree α
  | commutator : HallTree α → HallTree α → HallTree α
  deriving DecidableEq, Encodable

namespace HallTree

variable {α : Type u}

/-- Forget the Hall-tree bookkeeping and retain the underlying commutator word. -/
def toCWord : HallTree α → CWord α
  | atom a => .atom a
  | commutator u v => .commutator u.toCWord v.toCWord

/-- Ordinary commutator weight: every free generator has weight one. -/
def weight : HallTree α → ℕ
  | atom _ => 1
  | commutator u v => u.weight + v.weight

/-- Tree height, used to produce a finite search space for each weight. -/
def height : HallTree α → ℕ
  | atom _ => 1
  | commutator u v => max u.height v.height + 1

@[simp] theorem commutator_word_atom (a : α) :
    (atom a).toCWord = .atom a := rfl

@[simp] theorem to_commutator_commutator (u v : HallTree α) :
    (commutator u v).toCWord =
      .commutator u.toCWord v.toCWord := rfl

theorem commutator_word_injective :
    Function.Injective (@toCWord α) := by
  intro u
  induction u with
  | atom a =>
      intro v huv
      cases v with
      | atom b =>
          simpa [toCWord] using huv
      | commutator v₁ v₂ =>
          simp [toCWord] at huv
  | commutator u₁ u₂ ih₁ ih₂ =>
      intro v huv
      cases v with
      | atom b =>
          simp [toCWord] at huv
      | commutator v₁ v₂ =>
          simp only [toCWord, CWord.commutator.injEq] at huv
          exact congrArg₂ commutator (ih₁ huv.1) (ih₂ huv.2)

@[simp] theorem weight_atom (a : α) : (atom a).weight = 1 := rfl

@[simp] theorem weight_commutator (u v : HallTree α) :
    (commutator u v).weight = u.weight + v.weight := rfl

@[simp] theorem height_atom (a : α) : (atom a).height = 1 := rfl

@[simp] theorem height_commutator (u v : HallTree α) :
    (commutator u v).height = max u.height v.height + 1 := rfl

theorem weight_pos : ∀ w : HallTree α, 0 < w.weight
  | atom _ => by simp
  | commutator u v => by
      simpa using Nat.add_pos_left u.weight_pos v.weight

theorem height_pos : ∀ w : HallTree α, 0 < w.height
  | atom _ => by simp
  | commutator u v => by simp

theorem height_le_weight : ∀ w : HallTree α, w.height ≤ w.weight
  | atom _ => by simp
  | commutator u v => by
      have hu := u.height_le_weight
      have hv := v.height_le_weight
      have huPos := u.weight_pos
      have hvPos := v.weight_pos
      simp only [height_commutator, weight_commutator]
      omega

theorem weight_eq_iff {w : HallTree α} :
    w.weight = 1 ↔ ∃ a : α, w = atom a := by
  constructor
  · intro hw
    cases w with
    | atom a => exact ⟨a, rfl⟩
    | commutator u v =>
        have hu := u.weight_pos
        have hv := v.weight_pos
        simp only [weight_commutator] at hw
        omega
  · rintro ⟨a, rfl⟩
    rfl

@[simp] theorem commutator_weight_one (w : HallTree α) :
    w.toCWord.weight (fun _ => 1) = w.weight := by
  induction w with
  | atom a => simp [toCWord, weight]
  | commutator u v ihu ihv =>
      simp [toCWord, weight, ihu, ihv]

/--
The Hall order first compares ordinary weight, then uses the encoding as a
deterministic tie-breaker.  Hall theory allows any ordering within a fixed
weight.
-/
def orderKey [Encodable α] (w : HallTree α) : ℕ ×ₗ ℕ :=
  toLex (w.weight, Encodable.encode w)

instance [Encodable α] : LinearOrder (HallTree α) :=
  LinearOrder.lift' orderKey (by
    intro u v h
    apply Encodable.encode_injective
    exact congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)

theorem lt_weight_lt [Encodable α] {u v : HallTree α}
    (h : u.weight < v.weight) : u < v := by
  change orderKey u < orderKey v
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

/--
The usual recursive Hall admissibility predicate.  A commutator `[u, v]` is
basic when `u` and `v` are basic, `v < u`, and, when `u = [u₁, u₂]`, one also
has `u₂ ≤ v`.
-/
def IsBasic [Encodable α] : HallTree α → Prop
  | atom _ => True
  | commutator u v =>
      u.IsBasic ∧ v.IsBasic ∧ v < u ∧
        match u with
        | atom _ => True
        | commutator _ u₂ => u₂ ≤ v

@[simp] theorem isBasic_atom [Encodable α] (a : α) :
    (atom a).IsBasic := trivial

@[simp] theorem isBasic_commutator [Encodable α] (u v : HallTree α) :
    (commutator u v).IsBasic ↔
      u.IsBasic ∧ v.IsBasic ∧ v < u ∧
        match u with
        | atom _ => True
        | commutator _ u₂ => u₂ ≤ v := by
  rfl

theorem basic_commutator_admissible [Encodable α] {u v : HallTree α}
    (hu : u.IsBasic) (hv : v.IsBasic) (hvu : v < u)
    (hadmissible :
      match u with
      | atom _ => True
      | commutator _ u₂ => u₂ ≤ v) :
    (commutator u v).IsBasic := by
  cases u with
  | atom a =>
      exact ⟨hu, hv, hvu, trivial⟩
  | commutator u₁ u₂ =>
      exact ⟨hu, hv, hvu, hadmissible⟩

/-- Whether all leaves of a tree belong to the given finite alphabet. -/
def UsesOnly (alphabet : List α) : HallTree α → Prop
  | atom a => a ∈ alphabet
  | commutator u v => u.UsesOnly alphabet ∧ v.UsesOnly alphabet

@[simp] theorem usesOnly_atom (alphabet : List α) (a : α) :
    (atom a).UsesOnly alphabet ↔ a ∈ alphabet := by
  rfl

@[simp] theorem usesOnly_commutator (alphabet : List α) (u v : HallTree α) :
    (commutator u v).UsesOnly alphabet ↔
      u.UsesOnly alphabet ∧ v.UsesOnly alphabet := by
  rfl

/--
A finite, cumulative enumeration of every bracket tree of height at most `n`
whose leaves occur in `alphabet`.
-/
def treesHeight (alphabet : List α) : ℕ → List (HallTree α)
  | 0 => []
  | n + 1 =>
      let previous := treesHeight alphabet n
      alphabet.map atom ++ previous ++
        previous.flatMap fun u => previous.map fun v => commutator u v

@[simp] theorem trees_up_zero (alphabet : List α) :
    treesHeight alphabet 0 = [] := rfl

theorem trees_up_succ (alphabet : List α) {n : ℕ}
    {w : HallTree α} (hw : w ∈ treesHeight alphabet n) :
    w ∈ treesHeight alphabet (n + 1) := by
  simp [treesHeight, hw]

theorem trees_height (alphabet : List α) {m n : ℕ}
    (hmn : m ≤ n) {w : HallTree α}
    (hw : w ∈ treesHeight alphabet m) :
    w ∈ treesHeight alphabet n := by
  induction hmn with
  | refl => exact hw
  | @step n hmn ih =>
      exact trees_up_succ alphabet ih

theorem trees_uses_only (alphabet : List α) :
    ∀ {w : HallTree α}, w.UsesOnly alphabet →
      w ∈ treesHeight alphabet w.height
  | atom a, ha => by
      simpa [treesHeight] using ha
  | commutator u v, huv => by
      rcases huv with ⟨hu, hv⟩
      have huMem : u ∈ treesHeight alphabet (max u.height v.height) :=
        trees_height alphabet (Nat.le_max_left _ _)
          (trees_uses_only alphabet hu)
      have hvMem : v ∈ treesHeight alphabet (max u.height v.height) :=
        trees_height alphabet (Nat.le_max_right _ _)
          (trees_uses_only alphabet hv)
      simp [treesHeight, huMem, hvMem]

theorem trees_up_only (alphabet : List α)
    {w : HallTree α} (hw : w.UsesOnly alphabet) :
    w ∈ treesHeight alphabet w.weight :=
  trees_height alphabet w.height_le_weight
    (trees_uses_only alphabet hw)

section FiniteAlphabet

variable [Fintype α]

/-- Every bracket tree up to a fixed height over a finite alphabet. -/
noncomputable def allTreesHeight (n : ℕ) : List (HallTree α) :=
  treesHeight Finset.univ.toList n

theorem usesOnly_univ : ∀ w : HallTree α, w.UsesOnly Finset.univ.toList
  | atom a => by simp
  | commutator u v => by
      simp [usesOnly_univ u, usesOnly_univ v]

theorem all_trees_height (w : HallTree α) :
    w ∈ allTreesHeight w.weight :=
  trees_up_only Finset.univ.toList (usesOnly_univ w)

variable [DecidableEq α] [Encodable α]

/--
The canonically ordered list of all Hall basic commutators of ordinary weight
`r` over the finite alphabet `α`.
-/
noncomputable def basicTreesWeight (r : ℕ) : List (HallTree α) :=
  by
    classical
    exact ((allTreesHeight r).toFinset.filter fun w =>
      w.IsBasic ∧ w.weight = r).sort

theorem basic_trees_weight {r : ℕ} {w : HallTree α} :
    w ∈ basicTreesWeight (α := α) r ↔ w.IsBasic ∧ w.weight = r := by
  classical
  constructor
  · simp [basicTreesWeight]
  · intro hw
    have hMem : w ∈ allTreesHeight r := by
      simpa [hw.2] using all_trees_height w
    simpa [basicTreesWeight, hMem] using hw

theorem basic_trees_nodup (r : ℕ) :
    (basicTreesWeight (α := α) r).Nodup := by
  classical
  exact Finset.sort_nodup _ _

theorem basic_trees_sorted (r : ℕ) :
    (basicTreesWeight (α := α) r).SortedLT := by
  classical
  exact Finset.sortedLT_sort _

@[simp] theorem basic_trees_zero :
    basicTreesWeight (α := α) 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro w hw
  have hweight := (basic_trees_weight (α := α)).mp hw |>.2
  exact Nat.ne_of_gt w.weight_pos hweight

/-- A finite linearly ordered index type for the Hall basic words of weight `r`. -/
abbrev BasicIndex (r : ℕ) : Type := Fin (basicTreesWeight (α := α) r).length

/-- The Hall basic tree represented by a canonical weight-`r` index. -/
noncomputable def indexedBasicTree {r : ℕ} (i : BasicIndex (α := α) r) :
    HallTree α :=
  (basicTreesWeight (α := α) r).get i

theorem indexed_tree {r : ℕ} (i : BasicIndex (α := α) r) :
    (indexedBasicTree i).IsBasic :=
  (basic_trees_weight (α := α)).mp (List.get_mem _ i) |>.1

theorem indexed_tree_weight {r : ℕ} (i : BasicIndex (α := α) r) :
    (indexedBasicTree i).weight = r :=
  (basic_trees_weight (α := α)).mp (List.get_mem _ i) |>.2

theorem indexed_tree_injective {r : ℕ} :
    Function.Injective (indexedBasicTree (α := α) (r := r)) := by
  classical
  exact (basic_trees_nodup (α := α) r).injective_get

theorem indexed_tree_mono {r : ℕ} :
    StrictMono (indexedBasicTree (α := α) (r := r)) := by
  classical
  exact (basic_trees_sorted (α := α) r).strictMono_get

theorem indexed_basic_tree {r : ℕ} {w : HallTree α}
    (hw : w.IsBasic) (hweight : w.weight = r) :
    ∃ i : BasicIndex (α := α) r, indexedBasicTree i = w := by
  classical
  simpa [indexedBasicTree] using
    List.get_of_mem ((basic_trees_weight (α := α)).2 ⟨hw, hweight⟩)

theorem indexed_tree_atom (a : α) :
    ∃ i : BasicIndex (α := α) 1, indexedBasicTree i = atom a :=
  indexed_basic_tree (isBasic_atom a) (weight_atom a)

theorem indexed_tree_admissible
    {u v : HallTree α}
    (hu : u.IsBasic) (hv : v.IsBasic) (hvu : v < u)
    (hadmissible :
      match u with
      | atom _ => True
      | commutator _ u₂ => u₂ ≤ v) :
    ∃ i : BasicIndex (α := α) (u.weight + v.weight),
      indexedBasicTree i = commutator u v :=
  indexed_basic_tree
    (basic_commutator_admissible hu hv hvu hadmissible)
    (weight_commutator u v)

/--
The canonical index type enumerates exactly the Hall basic trees of the chosen
weight, with no repetitions.
-/
noncomputable def basicIndexEquiv (r : ℕ) :
    BasicIndex (α := α) r ≃ {w : HallTree α // w.IsBasic ∧ w.weight = r} :=
  Equiv.ofBijective
    (fun i => ⟨indexedBasicTree i, indexed_tree i,
      indexed_tree_weight i⟩)
    ⟨fun i j hij => indexed_tree_injective (Subtype.ext_iff.mp hij),
      fun w => by
        obtain ⟨i, hi⟩ := indexed_basic_tree w.property.1 w.property.2
        exact ⟨i, Subtype.ext hi⟩⟩

/-- The underlying `CWord` represented by a canonical Hall index. -/
noncomputable def indexedCommutatorWord {r : ℕ} (i : BasicIndex (α := α) r) :
    CWord α :=
  (indexedBasicTree i).toCWord

theorem indexed_commutator_injective {r : ℕ} :
    Function.Injective (indexedCommutatorWord (α := α) (r := r)) :=
  commutator_word_injective.comp indexed_tree_injective

theorem indexed_commutator_atom (a : α) :
    ∃ i : BasicIndex (α := α) 1, indexedCommutatorWord i = .atom a := by
  obtain ⟨i, hi⟩ := indexed_tree_atom a
  exact ⟨i, by simp [indexedCommutatorWord, hi]⟩

@[simp] theorem indexed_commutator_weight {r : ℕ}
    (i : BasicIndex (α := α) r) :
    (indexedCommutatorWord i).weight (fun _ => 1) = r := by
  simp [indexedCommutatorWord, indexed_tree_weight]

end FiniteAlphabet

end HallTree

end Towers


namespace Towers

universe u

namespace HallTree

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The intrinsic recursive Hall construction through height `n`.  Stage zero is
empty.  At the next stage, insert the free generators and every admissible
bracket of trees from the preceding stage.
-/
noncomputable def treesUpHeight : ℕ → Finset (HallTree α)
  | 0 => ∅
  | n + 1 => by
      classical
      let previous := treesUpHeight n
      exact Finset.univ.image atom ∪
        ((previous ×ˢ previous).image fun uv => commutator uv.1 uv.2).filter
          IsBasic

theorem recursive_trees_up {n : ℕ} {w : HallTree α}
    (hw : w ∈ treesUpHeight (α := α) n) :
    w.IsBasic := by
  induction n with
  | zero =>
      simp [treesUpHeight] at hw
  | succ n ih =>
      classical
      simp only [treesUpHeight, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hw
      rcases hw with ⟨a, -, rfl⟩ | ⟨-, hw⟩
      · exact isBasic_atom a
      · exact hw

theorem recursive_up_height {n : ℕ} {w : HallTree α}
    (hw : w ∈ treesUpHeight (α := α) n) :
    w.height ≤ n := by
  induction n generalizing w with
  | zero =>
      simp [treesUpHeight] at hw
  | succ n ih =>
      classical
      simp only [treesUpHeight, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hw
      rcases hw with ⟨a, -, rfl⟩ | ⟨hcommutator, -⟩
      · simp
      · rcases hcommutator with ⟨⟨u, v⟩, huv, rfl⟩
        simp only [Finset.mem_product] at huv
        simp only [height_commutator, Nat.add_le_add_iff_right]
        exact Nat.max_le.2 ⟨ih huv.1, ih huv.2⟩

theorem recursive_trees_height :
    ∀ (n : ℕ) (w : HallTree α), w.IsBasic → w.height ≤ n →
      w ∈ treesUpHeight (α := α) n
  | 0, w, _, hw => by
      have := w.height_pos
      omega
  | n + 1, atom a, _, _ => by
      classical
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  | n + 1, commutator u v, hw, hheight => by
      classical
      have huBasic := (isBasic_commutator u v).mp hw |>.1
      have hvBasic := (isBasic_commutator u v).mp hw |>.2.1
      have hmax : max u.height v.height ≤ n := by
        simpa only [height_commutator, Nat.add_le_add_iff_right] using hheight
      have huHeight : u.height ≤ n :=
        (Nat.le_max_left u.height v.height).trans hmax
      have hvHeight : v.height ≤ n :=
        (Nat.le_max_right u.height v.height).trans hmax
      have huMem :=
        recursive_trees_height n u huBasic huHeight
      have hvMem :=
        recursive_trees_height n v hvBasic hvHeight
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr
        ⟨(u, v), Finset.mem_product.mpr ⟨huMem, hvMem⟩, rfl⟩, hw⟩

theorem basic_trees_height {n : ℕ} {w : HallTree α} :
    w ∈ treesUpHeight (α := α) n ↔
      w.IsBasic ∧ w.height ≤ n :=
  ⟨fun hw => ⟨recursive_trees_up hw,
      recursive_up_height hw⟩,
    fun hw =>
      recursive_trees_height n w hw.1 hw.2⟩

/--
The intrinsic recursive Hall family in one ordinary weight.  Height `r`
suffices because the height of every bracket tree is bounded by its weight.
-/
noncomputable def recursiveTreesWeight (r : ℕ) : Finset (HallTree α) := by
  classical
  exact (treesUpHeight (α := α) r).filter fun w => w.weight = r

theorem recursive_trees_weight {r : ℕ} {w : HallTree α} :
    w ∈ recursiveTreesWeight (α := α) r ↔
      w.IsBasic ∧ w.weight = r := by
  classical
  constructor
  · intro hw
    have hw := (Finset.mem_filter.mp hw)
    exact ⟨recursive_trees_up hw.1, hw.2⟩
  · rintro ⟨hwBasic, hwWeight⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hwWeight⟩
    exact recursive_trees_height r w hwBasic <| by
      simpa only [hwWeight] using w.height_le_weight

/--
The intrinsic recursive construction agrees with the canonical sorted Hall
list used to define `BasicIndex`.
-/
theorem recursive_trees_finset (r : ℕ) :
    recursiveTreesWeight (α := α) r =
      (basicTreesWeight (α := α) r).toFinset := by
  classical
  ext w
  rw [List.mem_toFinset]
  exact recursive_trees_weight.trans basic_trees_weight.symm

end HallTree

end Towers


namespace Towers
namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/--
The associative bracket polynomial attached to a Hall tree.  Its leaves are
the augmentation differences of the corresponding free generators.
-/
noncomputable def associativeLeadingPolynomial
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    MonoidAlgebra R (FreeGroup α) :=
  freeLeadingPolynomial R α w.toCWord

@[simp] theorem associative_leading_atom
    (R : Type*) [CommRing R]
    (a : α) :
    (atom a).associativeLeadingPolynomial R =
      augmentationDifference R (FreeGroup α) (FreeGroup.of a) :=
  rfl

@[simp] theorem associative_leading_commutator
    (R : Type*) [CommRing R]
    (u v : HallTree α) :
    (commutator u v).associativeLeadingPolynomial R =
      u.associativeLeadingPolynomial R * v.associativeLeadingPolynomial R -
        v.associativeLeadingPolynomial R * u.associativeLeadingPolynomial R :=
  rfl

/-- A Hall tree's associative bracket polynomial has its expected degree. -/
theorem associative_leading_pow
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    w.associativeLeadingPolynomial R ∈
      (GShafar.augmentationIdeal R (FreeGroup α)) ^ w.weight := by
  simpa [associativeLeadingPolynomial] using
    free_leading_pow R α w.toCWord

/--
The evaluated Hall commutator agrees with its associative bracket polynomial
modulo the next augmentation power.
-/
theorem difference_associative_leading
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    augmentationDifference R (FreeGroup α)
          (w.toCWord.eval FreeGroup.of) -
        w.associativeLeadingPolynomial R ∈
      (GShafar.augmentationIdeal R (FreeGroup α)) ^
        (w.weight + 1) := by
  simpa [associativeLeadingPolynomial] using
    difference_leading_succ
      R α w.toCWord

/-- The augmentation-layer class of a Hall tree's associative polynomial. -/
noncomputable def associativeLeadingLayer
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    GroupAlgebra.augmentationLayer R (FreeGroup α) w.weight :=
  Submodule.Quotient.mk
    ⟨w.associativeLeadingPolynomial R, by
      simpa [GroupAlgebra.augmentationPower,
        ← golod_shafarevich_algebra] using
          w.associative_leading_pow R⟩

/--
A Hall tree evaluated in the free group, represented in its expected
lower-central term.
-/
def freeCentralRep
    (w : HallTree α) :
    Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1) :=
  ⟨w.toCWord.eval FreeGroup.of, by
    simpa using
      (CWord.eval_lower_series
        FreeGroup.of
        (fun _ : α => 1)
        (fun _ => by simp)
        (fun _ => by simp)
        w.toCWord)⟩

/-- The lower-central associated-graded class represented by a Hall tree. -/
def freeCentralLayer
    (w : HallTree α) :
    Additive
      (LowerGradedLayer (FreeGroup α) (w.weight - 1)) :=
  Additive.ofMul
    (QuotientGroup.mk'
      ((Subgroup.lowerCentralSeries (FreeGroup α) ((w.weight - 1) + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) (w.weight - 1)))
      w.freeCentralRep)

private theorem associated_graded_magnus
    (R : Type*) [CommRing R]
    (w : HallTree α)
    (n : ℕ)
    (hweight : w.toCWord.weight (fun _ => 1) = n) :
    GroupAlgebra.augmentationLayerReindex R (FreeGroup α)
        (Nat.sub_add_cancel
          (hweight ▸
            CWord.weight_pos
              (fun _ : α => 1) (fun _ => by simp) w.toCWord))
        (lowerAssociatedGraded R (FreeGroup α)
          (n - 1)
          (cast
            (congrArg
              (fun m =>
                Additive
                  (LowerGradedLayer
                    (FreeGroup α) (m - 1)))
              hweight)
            (freeLowerLayer
              α w.toCWord))) =
      cast
        (congrArg
          (fun m => GroupAlgebra.augmentationLayer R (FreeGroup α) m)
          hweight)
        (freeLeadingLayer
          R α w.toCWord) := by
  subst n
  exact
    associated_graded_layer
      R α w.toCWord

/--
The Magnus map sends the lower-central class of a Hall tree to the
augmentation-layer class of its associative bracket polynomial.
-/
theorem lower_associated_graded
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    GroupAlgebra.augmentationLayerReindex R (FreeGroup α)
        (Nat.sub_add_cancel w.weight_pos)
        (lowerAssociatedGraded R (FreeGroup α)
          (w.weight - 1) w.freeCentralLayer) =
      w.associativeLeadingLayer R := by
  rw [freeCentralLayer,
    graded_magnus_mk,
    GroupAlgebra.augmentation_reindex_mk]
  apply
    (Submodule.Quotient.eq
      (GroupAlgebra.augmentationLayerDenom R (FreeGroup α) w.weight)).mpr
  change
    augmentationDifference R (FreeGroup α)
          (w.toCWord.eval FreeGroup.of) -
        w.associativeLeadingPolynomial R ∈
      GroupAlgebra.augmentationPower R (FreeGroup α) (w.weight + 1)
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra] using
      w.difference_associative_leading R

end HallTree
end Towers


noncomputable section

namespace Towers
namespace TBluepr

universe u

/--
Concatenating two right-boundary-first augmentation words reverses the order
of the corresponding products in the group algebra.
-/
theorem free_augmentation_append
    (R α : Type*) [CommRing R]
    (u v : List α) :
    freeAugmentationWord R α (u ++ v) =
      freeAugmentationWord R α v *
        freeAugmentationWord R α u := by
  induction u with
  | nil => simp
  | cons a u ih =>
      simp [ih, mul_assoc]

/--
The forward-reading augmentation word.  Reversing the stored list compensates
for the right-boundary-first convention used by the Fox-coordinate engine.
-/
def freeForwardWord
    (R α : Type*) [CommRing R]
    (w : FreeMonoid α) :
    MonoidAlgebra R (FreeGroup α) :=
  freeAugmentationWord R α w.toList.reverse

@[simp] theorem free_forward_nil
    (R α : Type*) [CommRing R] :
    freeForwardWord R α 1 = 1 := by
  simp [freeForwardWord]

@[simp] theorem free_forward_singleton
    (R α : Type*) [CommRing R]
    (a : α) :
    freeForwardWord R α (FreeMonoid.of a) =
      augmentationDifference R (FreeGroup α) (FreeGroup.of a) := by
  simp [freeForwardWord]

@[simp] theorem free_forward_append
    (R α : Type*) [CommRing R]
    (u v : FreeMonoid α) :
    freeForwardWord R α (u * v) =
      freeForwardWord R α u *
        freeForwardWord R α v := by
  simp [freeForwardWord, free_augmentation_append]

/-- Forward augmentation words form a monoid homomorphism under concatenation. -/
def freeForwardMonoid
    (R α : Type*) [CommRing R] :
    FreeMonoid α →* MonoidAlgebra R (FreeGroup α) where
  toFun := freeForwardWord R α
  map_one' := free_forward_nil R α
  map_mul' := free_forward_append R α

/--
Substitute the augmentation difference of a free generator into a polynomial
in noncommuting words.
-/
def freeAssociativeRealization
    (R α : Type*) [CommRing R] :
    MonoidAlgebra R (FreeMonoid α) →ₐ[R] MonoidAlgebra R (FreeGroup α) :=
  MonoidAlgebra.lift R (MonoidAlgebra R (FreeGroup α)) (FreeMonoid α)
    (freeForwardMonoid R α)

@[simp] theorem free_realization_single
    (R α : Type*) [CommRing R]
    (w : FreeMonoid α)
    (r : R) :
    freeAssociativeRealization R α (MonoidAlgebra.single w r) =
      algebraMap R (MonoidAlgebra R (FreeGroup α)) r *
        freeForwardWord R α w := by
  simp [freeAssociativeRealization, Algebra.smul_def,
    freeForwardMonoid]

@[simp] theorem associative_realization_single
    (R α : Type*) [CommRing R]
    (w : FreeMonoid α) :
    freeAssociativeRealization R α (MonoidAlgebra.single w 1) =
      freeForwardWord R α w := by
  rw [free_realization_single]
  rw [map_one, one_mul]

end TBluepr

namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/-- A finite noncommutative polynomial in words of free generators. -/
abbrev AssociativeWordPolynomial
    (R α : Type*) [CommRing R] :=
  MonoidAlgebra R (FreeMonoid α)

/--
The recursive associative bracket polynomial of a Hall tree, before
substitution into the free-group algebra.
-/
noncomputable def associativeWordPolynomial
    (R : Type*) [CommRing R] :
    HallTree α → AssociativeWordPolynomial R α
  | atom a => MonoidAlgebra.single (FreeMonoid.of a) 1
  | commutator u v =>
      u.associativeWordPolynomial R * v.associativeWordPolynomial R -
        v.associativeWordPolynomial R * u.associativeWordPolynomial R

@[simp] theorem associative_word_atom
    (R : Type*) [CommRing R]
    (a : α) :
    (atom a).associativeWordPolynomial R =
      MonoidAlgebra.single (FreeMonoid.of a) 1 :=
  rfl

@[simp] theorem associative_word_commutator
    (R : Type*) [CommRing R]
    (u v : HallTree α) :
    (commutator u v).associativeWordPolynomial R =
      u.associativeWordPolynomial R * v.associativeWordPolynomial R -
        v.associativeWordPolynomial R * u.associativeWordPolynomial R :=
  rfl

/-- Every word occurring in the bracket polynomial has the tree's weight. -/
theorem associative_word_length
    (R : Type*) [CommRing R]
    (w : HallTree α)
    {word : FreeMonoid α}
    (hword : word ∈ (w.associativeWordPolynomial R).support) :
    word.length = w.weight := by
  classical
  induction w generalizing word with
  | atom a =>
      have hsingleton :
          word ∈ ({FreeMonoid.of a} : Finset (FreeMonoid α)) :=
        Finsupp.support_single_subset hword
      have hwordEq : word = FreeMonoid.of a := Finset.mem_singleton.mp hsingleton
      simp [hwordEq]
  | commutator u v ihu ihv =>
      have hunion :
          word ∈
            (u.associativeWordPolynomial R *
                v.associativeWordPolynomial R).support ∪
              (v.associativeWordPolynomial R *
                u.associativeWordPolynomial R).support :=
        Finsupp.support_sub hword
      rcases Finset.mem_union.mp hunion with huv | hvu
      · have hmul :=
          MonoidAlgebra.support_mul
            (u.associativeWordPolynomial R)
            (v.associativeWordPolynomial R) huv
        obtain ⟨wu, hwu, wv, hwv, rfl⟩ := Finset.mem_mul.mp hmul
        simp [ihu hwu, ihv hwv]
      · have hmul :=
          MonoidAlgebra.support_mul
            (v.associativeWordPolynomial R)
            (u.associativeWordPolynomial R) hvu
        obtain ⟨wv, hwv, wu, hwu, rfl⟩ := Finset.mem_mul.mp hmul
        simp [ihu hwu, ihv hwv, Nat.add_comm]

/-- A coefficient outside the tree's homogeneous degree vanishes. -/
theorem associative_word_ne
    (R : Type*) [CommRing R]
    (w : HallTree α)
    (word : FreeMonoid α)
    (hlength : word.length ≠ w.weight) :
    w.associativeWordPolynomial R word = 0 := by
  rw [← Finsupp.notMem_support_iff]
  intro hword
  exact hlength (associative_word_length R w hword)

/--
Realizing the word polynomial in the free-group algebra recovers the
associative leading polynomial used by the Magnus map.
-/
theorem associative_realization_polynomial
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    freeAssociativeRealization R α (w.associativeWordPolynomial R) =
      w.associativeLeadingPolynomial R := by
  induction w with
  | atom a =>
      rw [associative_word_atom,
        associative_realization_single,
        associative_leading_atom,
        free_forward_singleton]
  | commutator u v ihu ihv =>
      simp [ihu, ihv]

end HallTree
end Towers


noncomputable section

namespace Towers
namespace TBluepr

universe u

/-- Free-monoid words of a fixed length. -/
abbrev AssociativeWordsLength
    (α : Type u)
    (n : ℕ) :=
  { w : FreeMonoid α // w.length = n }

/--
Forward-reading words correspond to the reversed vectors used by the
right-boundary-first Fox-coordinate basis.
-/
def associativeVectorEquiv
    (α : Type u)
    (n : ℕ) :
    AssociativeWordsLength α n ≃ List.Vector α n where
  toFun w :=
    ⟨w.1.toList.reverse, by
      simpa [FreeMonoid.length] using w.2⟩
  invFun v :=
    ⟨FreeMonoid.ofList v.toList.reverse, by
      simp [FreeMonoid.length]⟩
  left_inv w := by
    apply Subtype.ext
    apply FreeMonoid.toList.injective
    simp
  right_inv v := by
    apply List.Vector.toList_injective
    simp

/-- A fixed-length forward word, viewed in the corresponding augmentation layer. -/
def freeAssociativeVector
    (R α : Type*) [CommRing R]
    (n : ℕ)
    (w : AssociativeWordsLength α n) :
    GroupAlgebra.augmentationLayer R (FreeGroup α) n :=
  freeVectorLayer R α
    (associativeVectorEquiv α n w)

/-- Fixed-length forward words are linearly independent in the augmentation layer. -/
theorem associative_vector_independent
    (R α : Type*) [CommRing R] [Finite α]
    (n : ℕ) :
    LinearIndependent R (freeAssociativeVector R α n) := by
  letI := Fintype.ofFinite α
  classical
  change
    LinearIndependent R
      ((freeVectorLayer R α) ∘
        associativeVectorEquiv α n)
  exact
    (linearIndependent_equiv (associativeVectorEquiv α n)).mpr
      (free_vector_independent R α n)

/-- Word polynomials supported in one homogeneous length. -/
abbrev AssociativeHomogeneousWords
    (R α : Type*) [CommRing R]
    (n : ℕ) :=
  Finsupp.supported R R
    { w : FreeMonoid α | w.length = n }

/-- The single-word basis of the homogeneous word-polynomial module. -/
noncomputable def associativeHomogeneousWords
    (R α : Type*) [CommRing R]
    (n : ℕ) :
    Module.Basis (AssociativeWordsLength α n) R
      (AssociativeHomogeneousWords R α n) :=
  Finsupp.basisSingleOne.map
    (Finsupp.supportedEquivFinsupp
      (R := R) { w : FreeMonoid α | w.length = n }).symm

@[simp] theorem homogeneous_words_basis
    (R α : Type*) [CommRing R]
    (n : ℕ)
    (w : AssociativeWordsLength α n) :
    associativeHomogeneousWords R α n w =
      ⟨Finsupp.single w.1 1,
        Finsupp.single_mem_supported R 1 w.2⟩ := by
  apply Subtype.ext
  simpa [associativeHomogeneousWords] using
    (Finsupp.supportedEquivFinsupp_symm_single
      (R := R) { w : FreeMonoid α | w.length = n } w (1 : R))

/--
Evaluate a homogeneous word polynomial in the fixed-degree augmentation
layer by taking the corresponding linear combination of word classes.
-/
def freeAssociativeHomogeneous
    (R α : Type*) [CommRing R]
    (n : ℕ) :
    AssociativeHomogeneousWords R α n →ₗ[R]
      GroupAlgebra.augmentationLayer R (FreeGroup α) n :=
  (Finsupp.linearCombination R (freeAssociativeVector R α n)).comp
    (Finsupp.supportedEquivFinsupp
      (R := R) { w : FreeMonoid α | w.length = n }).toLinearMap

/--
Distinct homogeneous word polynomials remain distinct in the free-group
augmentation layer.
-/
theorem associative_homogeneous_injective
    (R α : Type*) [CommRing R] [Finite α]
    (n : ℕ) :
    Function.Injective (freeAssociativeHomogeneous R α n) := by
  letI := Fintype.ofFinite α
  classical
  intro p q hpq
  apply
    (Finsupp.supportedEquivFinsupp
      (R := R) { w : FreeMonoid α | w.length = n }).injective
  apply associative_vector_independent R α n
  exact hpq

end TBluepr

namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/-- A Hall polynomial, packaged in its homogeneous word submodule. -/
def associativeWordRep
    (R : Type*) [CommRing R]
    (w : HallTree α) :
    AssociativeHomogeneousWords R α w.weight :=
  ⟨w.associativeWordPolynomial R, by
    intro word hword
    exact associative_word_length R w hword⟩

/-- Reindex a Hall polynomial into any explicitly equal weight. -/
def associativeRepWeight
    (R : Type*) [CommRing R]
    {n : ℕ}
    (w : HallTree α)
    (hweight : w.weight = n) :
    AssociativeHomogeneousWords R α n :=
  ⟨w.associativeWordPolynomial R, by
    intro word hword
    simpa [← hweight] using
      associative_word_length R w hword⟩

end HallTree
end Towers


noncomputable section

namespace Towers
namespace TBluepr

universe u

/-- A forward augmentation word lies in the augmentation power given by its length. -/
theorem free_forward_pow
    (R α : Type*) [CommRing R]
    (w : FreeMonoid α) :
    freeForwardWord R α w ∈
      (GShafar.augmentationIdeal R (FreeGroup α)) ^ w.length := by
  simpa [freeForwardWord, FreeMonoid.length] using
    free_ideal_pow
      R α w.toList.reverse

/-- The forward word and reversed Fox-coordinate vector give the same monomial. -/
theorem free_forward_vector
    (R α : Type*) [CommRing R]
    (n : ℕ)
    (w : AssociativeWordsLength α n) :
    freeForwardWord R α w =
      freeVectorWord R α
        (associativeVectorEquiv α n w) :=
  rfl

/-- Realizing a homogeneous word polynomial lands in its expected augmentation power. -/
theorem free_associative_realization
    (R α : Type*) [CommRing R]
    {n : ℕ}
    (p : AssociativeHomogeneousWords R α n) :
    freeAssociativeRealization R α
        p.1 ∈
      (GShafar.augmentationIdeal R (FreeGroup α)) ^ n := by
  classical
  rw [← p.1.sum_single]
  change
    (freeAssociativeRealization R α).toLinearMap
        (p.1.sum Finsupp.single) ∈
      (GShafar.augmentationIdeal R (FreeGroup α)) ^ n
  rw [map_finsuppSum]
  apply Ideal.sum_mem
  intro word hword
  change
    freeAssociativeRealization R α
        (MonoidAlgebra.single word (p.1 word)) ∈
      (GShafar.augmentationIdeal R (FreeGroup α)) ^ n
  rw [free_realization_single]
  apply Ideal.mul_mem_left
  have hlength : word.length = n := p.2 hword
  simpa [hlength] using
    free_forward_pow R α word

/--
Realize a homogeneous word polynomial as an element of its augmentation-power
submodule.
-/
def homogeneousRealizationRep
    (R α : Type*) [CommRing R]
    (n : ℕ) :
    AssociativeHomogeneousWords R α n →ₗ[R]
      GroupAlgebra.augmentationPowerSubmodule R (FreeGroup α) n :=
  (((freeAssociativeRealization R α).toLinearMap.domRestrict
    (AssociativeHomogeneousWords R α n)).codRestrict
      (GroupAlgebra.augmentationPowerSubmodule R (FreeGroup α) n) (by
        intro p
        change
          freeAssociativeRealization R α
              p.1 ∈
            GroupAlgebra.augmentationPower R (FreeGroup α) n
        simpa [GroupAlgebra.augmentationPower,
          ← golod_shafarevich_algebra] using
            free_associative_realization R α p))

/--
Realize a homogeneous word polynomial in the corresponding associated-graded
augmentation layer.
-/
def associativeHomogeneousRealization
    (R α : Type*) [CommRing R]
    (n : ℕ) :
    AssociativeHomogeneousWords R α n →ₗ[R]
      GroupAlgebra.augmentationLayer R (FreeGroup α) n :=
  (GroupAlgebra.augmentationLayerDenom R (FreeGroup α) n).mkQ.comp
    (homogeneousRealizationRep R α n)

/-- The coefficient-level homogeneous map sends a basis word to its word class. -/
@[simp] theorem associative_homogeneous_basis
    (R α : Type*) [CommRing R]
    (n : ℕ)
    (w : AssociativeWordsLength α n) :
    freeAssociativeHomogeneous R α n
        (associativeHomogeneousWords R α n w) =
      freeAssociativeVector R α n w := by
  rw [homogeneous_words_basis]
  change
    Finsupp.linearCombination R (freeAssociativeVector R α n)
        ((Finsupp.supportedEquivFinsupp
          (R := R) { w : FreeMonoid α | w.length = n })
          ⟨Finsupp.single w.1 (1 : R),
            Finsupp.single_mem_supported R (1 : R) w.2⟩) =
      freeAssociativeVector R α n w
  have hsingle :
      (Finsupp.supportedEquivFinsupp
        (R := R) { w : FreeMonoid α | w.length = n })
          ⟨Finsupp.single w.1 (1 : R),
            Finsupp.single_mem_supported R (1 : R) w.2⟩ =
        Finsupp.single w (1 : R) := by
    apply
      (Finsupp.supportedEquivFinsupp
        (R := R) { w : FreeMonoid α | w.length = n }).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    exact
      (Finsupp.supportedEquivFinsupp_symm_single
        (R := R) { w : FreeMonoid α | w.length = n } w (1 : R)).symm
  rw [hsingle, Finsupp.linearCombination_single, one_smul]

/-- The natural quotient realization sends a basis word to its word class. -/
@[simp] theorem homogeneous_realization_basis
    (R α : Type*) [CommRing R]
    (n : ℕ)
    (w : AssociativeWordsLength α n) :
    associativeHomogeneousRealization R α n
        (associativeHomogeneousWords R α n w) =
      freeAssociativeVector R α n w := by
  rw [homogeneous_words_basis]
  apply
    (Submodule.Quotient.eq
      (GroupAlgebra.augmentationLayerDenom R (FreeGroup α) n)).mpr
  change
    freeAssociativeRealization R α (Finsupp.single w.1 1) -
        freeVectorWord R α
          (associativeVectorEquiv α n w) ∈
      GroupAlgebra.augmentationPower R (FreeGroup α) (n + 1)
  rw [associative_realization_single,
    free_forward_vector]
  simp

/-- The natural realization and coefficient-level homogeneous maps agree. -/
theorem free_homogeneous_realization
    (R α : Type*) [CommRing R]
    (n : ℕ) :
    associativeHomogeneousRealization R α n =
      freeAssociativeHomogeneous R α n := by
  apply (associativeHomogeneousWords R α n).ext
  intro w
  rw [homogeneous_realization_basis,
    associative_homogeneous_basis]

/-- Homogeneous realization in the augmentation layer is injective. -/
theorem homogeneous_realization_injective
    (R α : Type*) [CommRing R] [Finite α]
    (n : ℕ) :
    Function.Injective
      (associativeHomogeneousRealization R α n) := by
  letI := Fintype.ofFinite α
  classical
  rw [free_homogeneous_realization]
  exact associative_homogeneous_injective R α n

end TBluepr
end Towers

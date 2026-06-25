import Submission.Group.HallBasic.LowerLieBridge
import Submission.Group.HallBasic.Weight
import Submission.Group.HallBasic.Word
import Submission.Group.HallBasic.ConcreteBasisBridge
import Submission.Group.HallBasic.TriangularStandardWords


open Submission.TCTex

noncomputable section

namespace Submission
namespace HallTree

open TBluepr
open scoped commutatorElement IsMulCommutative

universe u

variable {α : Type u}

/-- The span of the classes of all Hall trees in one ordinary weight. -/
def allTreeSpan
    (r : ℕ) :
    Submodule ℤ
      (Additive
        (LowerGradedLayer (FreeGroup α) (r - 1))) :=
  Submodule.span ℤ
    (Set.range fun w : {w : HallTree α // w.weight = r} =>
      w.1.freeLowerWeight w.2)

/-- Every fixed-weight Hall-tree class belongs to the span of all such trees. -/
theorem all_tree_span
    {r : ℕ}
    (w : HallTree α)
    (hweight : w.weight = r) :
    w.freeLowerWeight hweight ∈
      allTreeSpan (α := α) r := by
  apply Submodule.subset_span
  exact ⟨⟨w, hweight⟩, rfl⟩

/--
The graded bracket carries the span of all weight-`i` trees and the span of all
weight-`j` trees into the span of all weight-`i + j` trees.
-/
theorem bracket_tree_span
    {i j : ℕ}
    (hi : 0 < i)
    (hj : 0 < j)
    {x : Additive
      (LowerGradedLayer (FreeGroup α) (i - 1))}
    {y : Additive
      (LowerGradedLayer (FreeGroup α) (j - 1))}
    (hx : x ∈ allTreeSpan (α := α) i)
    (hy : y ∈ allTreeSpan (α := α) j) :
    lowerBracketClass
        (i - 1) (j - 1) (i + j - 1)
        (by omega) x y ∈
      allTreeSpan (α := α) (i + j) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨u, rfl⟩
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨v, rfl⟩
          rcases u with ⟨u, hu⟩
          rcases v with ⟨v, hv⟩
          subst i
          subst j
          change
            lowerBracketClass
                (u.weight - 1) (v.weight - 1)
                ((commutator u v).weight - 1)
                (lower_bracket_degree u v)
                u.freeCentralLayer v.freeCentralLayer ∈
              allTreeSpan (α := α) (commutator u v).weight
          rw [← free_central_commutator u v rfl]
          exact
            all_tree_span
              (commutator u v) rfl
      | zero =>
          simp
      | add y z _hy _hz ihy ihz =>
          rw [lower_central_bracket]
          exact (allTreeSpan (α := α) (i + j)).add_mem ihy ihz
      | smul c y _hy ihy =>
          rw [bracket_zsmul_right]
          exact (allTreeSpan (α := α) (i + j)).smul_mem c ihy
  | zero =>
      simp
  | add x z _hx _hz ihx ihz =>
      rw [central_bracket_left]
      exact (allTreeSpan (α := α) (i + j)).add_mem ihx ihz
  | smul c x _hx ihx =>
      rw [bracket_zsmul_left]
      exact (allTreeSpan (α := α) (i + j)).smul_mem c ihx

/-- Every degree-one free-group word class belongs to the weight-one tree span. -/
theorem weight_tree_span
    (x : FreeGroup α) :
    weightCentralClass x ∈
      allTreeSpan (α := α) 1 := by
  induction x using FreeGroup.induction_on with
  | C1 =>
      simp
  | of a =>
      rw [weight_central_class]
      exact
        all_tree_span
          (atom a) rfl
  | inv_of x hx =>
      rw [lower_central_inv]
      exact (allTreeSpan (α := α) 1).neg_mem hx
  | mul x y hx hy =>
      rw [lower_central_mul]
      exact (allTreeSpan (α := α) 1).add_mem hx hy

/-- Every class in the first lower-central layer belongs to the weight-one tree span. -/
theorem lower_tree_span
    (g : Subgroup.lowerCentralSeries (FreeGroup α) 0) :
    lowerCentralClass 0 g ∈ allTreeSpan (α := α) 1 := by
  change weightCentralClass (g : FreeGroup α) ∈
    allTreeSpan (α := α) 1
  exact weight_tree_span (g : FreeGroup α)

/-- Weight-one Hall trees span the first lower-central associated-graded layer. -/
theorem all_span_top :
    allTreeSpan (α := α) 1 = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective
      ((Subgroup.lowerCentralSeries (FreeGroup α) 1).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) 0)) z.toMul
  change Additive.ofMul z.toMul ∈ allTreeSpan (α := α) 1
  rw [← hg]
  change lowerCentralClass 0 g ∈ allTreeSpan (α := α) 1
  exact lower_tree_span g

/--
If all weight-`r` trees span their layer, then all weight-`r + 1` trees span
the next layer.
-/
theorem all_tree_top
    {r : ℕ}
    (hr : 0 < r)
    (hspan : allTreeSpan (α := α) r = ⊤) :
    allTreeSpan (α := α) (r + 1) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective
      ((Subgroup.lowerCentralSeries (FreeGroup α) (r + 1)).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) r)) z.toMul
  change Additive.ofMul z.toMul ∈ allTreeSpan (α := α) (r + 1)
  rw [← hg]
  change lowerCentralClass r g ∈ allTreeSpan (α := α) (r + 1)
  have hg' :
      (g : FreeGroup α) ∈
        Subgroup.closure
          {z : FreeGroup α |
            ∃ c ∈ Subgroup.lowerCentralSeries (FreeGroup α) (r - 1),
              ∃ x ∈ (⊤ : Subgroup (FreeGroup α)),
                c * x * c⁻¹ * x⁻¹ = z} := by
    have hgSeries :
        (g : FreeGroup α) ∈
          Subgroup.lowerCentralSeries (FreeGroup α) ((r - 1) + 1) := by
      rw [Nat.sub_add_cancel hr]
      exact g.property
    simpa only [Subgroup.lowerCentralSeries_succ] using hgSeries
  simpa only using
    (Subgroup.closure_induction
      (k :=
        {z : FreeGroup α |
          ∃ c ∈ Subgroup.lowerCentralSeries (FreeGroup α) (r - 1),
            ∃ x ∈ (⊤ : Subgroup (FreeGroup α)),
              c * x * c⁻¹ * x⁻¹ = z})
      (p := fun z hz =>
        lowerCentralClass r
            ⟨z, by
              rw [← Nat.sub_add_cancel hr]
              exact hz⟩ ∈
          allTreeSpan (α := α) (r + 1))
      (fun z hz => by
        rcases hz with ⟨c, hc, x, hx, rfl⟩
        have hleft :
            lowerCentralClass (r - 1)
                (⟨c, hc⟩ : Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)) ∈
              allTreeSpan (α := α) r := by
          rw [hspan]
          trivial
        have hright :
            lowerCentralClass 0
                  (⟨x, by simp [Subgroup.lowerCentralSeries_zero]⟩ :
                  Subgroup.lowerCentralSeries (FreeGroup α) 0) ∈
              allTreeSpan (α := α) 1 := by
          rw [all_span_top]
          trivial
        have hbracket :=
          bracket_tree_span
            (α := α) hr (by omega) hleft hright
        simpa only [lower_bracket_class,
          Nat.add_sub_cancel, commutatorElement_def] using hbracket)
      (by
        simpa using (allTreeSpan (α := α) (r + 1)).zero_mem)
      (fun _ _ _ _ hx hy => by
        simpa using (allTreeSpan (α := α) (r + 1)).add_mem hx hy)
      (fun _ _ hx => by
        simpa using (allTreeSpan (α := α) (r + 1)).neg_mem hx)
      hg')

/-- In every positive weight, all Hall-tree classes span the free-group layer. -/
theorem all_hall_top
    {r : ℕ}
    (hr : 0 < r) :
    allTreeSpan (α := α) r = ⊤ := by
  induction r with
  | zero =>
      omega
  | succ r ih =>
      cases r with
      | zero =>
          exact all_span_top
      | succ r =>
          exact all_tree_top (by omega) (ih (by omega))

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- The span of the indexed Hall basic classes in one ordinary weight. -/
def basicTreeSpan
    (r : ℕ) :
    Submodule ℤ
      (Additive
        (LowerGradedLayer (FreeGroup α) (r - 1))) :=
  Submodule.span ℤ
    (Set.range fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i))

/-- A basic Hall tree represents an element of the indexed basic-tree span. -/
theorem free_tree_span
    {r : ℕ}
    (w : HallTree α)
    (hw : w.IsBasic)
    (hweight : w.weight = r) :
    w.freeLowerWeight hweight ∈
      basicTreeSpan (α := α) r := by
  obtain ⟨i, hi⟩ := indexed_basic_tree hw hweight
  apply Submodule.subset_span
  refine ⟨i, ?_⟩
  exact
    free_lower_congr hi
      (indexed_tree_weight i) hweight

/-- The indexed basic-tree span is contained in the span of all Hall trees. -/
theorem tree_span_all
    (r : ℕ) :
    basicTreeSpan (α := α) r ≤ allTreeSpan (α := α) r := by
  apply Submodule.span_le.2
  rintro _ ⟨i, rfl⟩
  exact
    all_tree_span
      (indexedBasicTree i) (indexed_tree_weight i)

/--
To prove that the all-tree span lies in the basic-tree span, it is enough to
reduce one arbitrary fixed-weight Hall tree.
-/
theorem all_tree_forall
    {r : ℕ}
    (hreduce :
      ∀ (w : HallTree α) (hweight : w.weight = r),
        w.freeLowerWeight hweight ∈
          basicTreeSpan (α := α) r) :
    allTreeSpan (α := α) r ≤ basicTreeSpan (α := α) r := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨w, hweight⟩, rfl⟩
  exact hreduce w hweight

/--
At a positive weight, reduction of arbitrary Hall trees to basic trees is
enough to prove that the basic Hall classes span the whole layer.
-/
theorem tree_top_forall
    {r : ℕ}
    (hr : 0 < r)
    (hreduce :
      ∀ (w : HallTree α) (hweight : w.weight = r),
        w.freeLowerWeight hweight ∈
          basicTreeSpan (α := α) r) :
    basicTreeSpan (α := α) r = ⊤ := by
  rw [← all_hall_top (α := α) hr]
  exact le_antisymm
    (tree_span_all r)
    (all_tree_forall hreduce)

/-- An admissible bracket of basic Hall trees is already in the basic span. -/
theorem free_tree_admissible
    {r : ℕ}
    (u v : HallTree α)
    (hu : u.IsBasic)
    (hv : v.IsBasic)
    (hvu : v < u)
    (hadmissible :
      match u with
      | atom _ => True
      | commutator _ u₂ => u₂ ≤ v)
    (hweight : (commutator u v).weight = r) :
    (commutator u v).freeLowerWeight hweight ∈
      basicTreeSpan (α := α) r :=
  free_tree_span
    (commutator u v)
    (basic_commutator_admissible hu hv hvu hadmissible)
    hweight

/-- A reversed bracket reduces to the same basic span by skew-symmetry. -/
theorem free_tree_swap
    {r : ℕ}
    (u v : HallTree α)
    (hweight : (commutator u v).weight = r)
    (hswap :
      (commutator v u).freeLowerWeight
          (by
            simp only [weight_commutator] at hweight ⊢
            omega) ∈
        basicTreeSpan (α := α) r) :
    (commutator u v).freeLowerWeight hweight ∈
      basicTreeSpan (α := α) r := by
  rw [free_commutator_swap
    u v hweight]
  exact (basicTreeSpan (α := α) r).neg_mem hswap

/-- A self-bracket belongs to the basic span because its class vanishes. -/
theorem self_tree_span
    {r : ℕ}
    (u : HallTree α)
    (hweight : (commutator u u).weight = r) :
    (commutator u u).freeLowerWeight hweight ∈
      basicTreeSpan (α := α) r := by
  rw [free_commutator_self u hweight]
  exact (basicTreeSpan (α := α) r).zero_mem

/--
The Jacobi rewrite reduces a non-admissible left-normed bracket once both
resulting terms have been reduced.
-/
theorem free_tree_jacobi
    {r : ℕ}
    (u v w : HallTree α)
    (hweight : (commutator (commutator u v) w).weight = r)
    (huw :
      (commutator (commutator u w) v).freeLowerWeight
          (by
            simp only [weight_commutator] at hweight ⊢
            omega) ∈
        basicTreeSpan (α := α) r)
    (hvw :
      (commutator (commutator v w) u).freeLowerWeight
          (by
            simp only [weight_commutator] at hweight ⊢
            omega) ∈
        basicTreeSpan (α := α) r) :
    (commutator (commutator u v) w).freeLowerWeight
        hweight ∈
      basicTreeSpan (α := α) r := by
  rw [free_jacobi_rewrite
    u v w hweight]
  exact (basicTreeSpan (α := α) r).sub_mem huw hvw

/--
If brackets of indexed basic trees of weight `i` with one fixed tree of
weight `j` have been reduced, linearity in the left input reduces the bracket
of the whole basic-tree span with that fixed right tree.
-/
theorem bracket_tree_left
    {i j : ℕ}
    (hi : 0 < i)
    (hj : 0 < j)
    (v : HallTree α)
    (hvWeight : v.weight = j)
    (hcommutator :
      ∀ u : BasicIndex (α := α) i,
        (commutator (indexedBasicTree u) v).freeLowerWeight
            (by
              simp only [weight_commutator, indexed_tree_weight,
                hvWeight]) ∈
          basicTreeSpan (α := α) (i + j))
    {x : Additive
      (LowerGradedLayer (FreeGroup α) (i - 1))}
    (hx : x ∈ basicTreeSpan (α := α) i) :
    lowerBracketClass
        (i - 1) (j - 1) (i + j - 1)
        (by omega) x
        (v.freeLowerWeight hvWeight) ∈
      basicTreeSpan (α := α) (i + j) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨u, rfl⟩
      rw [← free_lower_weights
        (indexedBasicTree u) v (indexed_tree_weight u) hvWeight rfl]
      exact hcommutator u
  | zero =>
      simp
  | add x y _hx _hy ihx ihy =>
      rw [central_bracket_left]
      exact (basicTreeSpan (α := α) (i + j)).add_mem ihx ihy
  | smul c x _hx ihx =>
      rw [bracket_zsmul_left]
      exact (basicTreeSpan (α := α) (i + j)).smul_mem c ihx

/--
If brackets of indexed basic trees of weights `i` and `j` have been reduced,
bilinearity reduces the bracket of any two elements of their spans.
-/
theorem bracket_tree_indexed
    {i j : ℕ}
    (hi : 0 < i)
    (hj : 0 < j)
    (hcommutator :
      ∀ (u : BasicIndex (α := α) i) (v : BasicIndex (α := α) j),
        (commutator (indexedBasicTree u) (indexedBasicTree v)).freeLowerWeight
            (by
              simp only [weight_commutator, indexed_tree_weight]) ∈
          basicTreeSpan (α := α) (i + j))
    {x : Additive
      (LowerGradedLayer (FreeGroup α) (i - 1))}
    {y : Additive
      (LowerGradedLayer (FreeGroup α) (j - 1))}
    (hx : x ∈ basicTreeSpan (α := α) i)
    (hy : y ∈ basicTreeSpan (α := α) j) :
    lowerBracketClass
        (i - 1) (j - 1) (i + j - 1)
        (by omega) x y ∈
      basicTreeSpan (α := α) (i + j) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨u, rfl⟩
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨v, rfl⟩
          rw [← free_lower_weights
            (indexedBasicTree u) (indexedBasicTree v)
            (indexed_tree_weight u) (indexed_tree_weight v) rfl]
          exact hcommutator u v
      | zero =>
          simp
      | add y z _hy _hz ihy ihz =>
          rw [lower_central_bracket]
          exact (basicTreeSpan (α := α) (i + j)).add_mem ihy ihz
      | smul c y _hy ihy =>
          rw [bracket_zsmul_right]
          exact (basicTreeSpan (α := α) (i + j)).smul_mem c ihy
  | zero =>
      simp
  | add x z _hx _hz ihx ihz =>
      rw [central_bracket_left]
      exact (basicTreeSpan (α := α) (i + j)).add_mem ihx ihz
  | smul c x _hx ihx =>
      rw [bracket_zsmul_left]
      exact (basicTreeSpan (α := α) (i + j)).smul_mem c ihx

/--
Pointwise normalization of brackets of indexed basic trees recursively
reduces every Hall tree to the basic-tree span in its own weight.
-/
theorem tree_indexed_commutator
    (hcommutator :
      ∀ {i j : ℕ}
        (u : BasicIndex (α := α) i) (v : BasicIndex (α := α) j),
        (commutator (indexedBasicTree u) (indexedBasicTree v)).freeLowerWeight
            (by
              simp only [weight_commutator, indexed_tree_weight]) ∈
          basicTreeSpan (α := α) (i + j))
    (w : HallTree α) :
    w.freeCentralLayer ∈
      basicTreeSpan (α := α) w.weight := by
  induction w with
  | atom a =>
      exact
        free_tree_span
          (atom a) (isBasic_atom a) rfl
  | commutator u v ihu ihv =>
      rw [free_layer_commutator]
      exact
        bracket_tree_indexed
          u.weight_pos v.weight_pos (fun x y => hcommutator x y) ihu ihv

/--
Pointwise normalization of indexed basic-tree brackets proves spanning in
every positive weight.
-/
theorem tree_top_indexed
    (hcommutator :
      ∀ {i j : ℕ}
        (u : BasicIndex (α := α) i) (v : BasicIndex (α := α) j),
        (commutator (indexedBasicTree u) (indexedBasicTree v)).freeLowerWeight
            (by
              simp only [weight_commutator, indexed_tree_weight]) ∈
          basicTreeSpan (α := α) (i + j))
    {r : ℕ}
    (hr : 0 < r) :
    basicTreeSpan (α := α) r = ⊤ := by
  apply tree_top_forall hr
  intro w hweight
  subst r
  exact
    tree_indexed_commutator
      hcommutator w

end HallTree
end Submission


/-!
# From non-admissible Hall brackets to all-weight spanning

The all-tree spanning theorem and its bilinear reduction bridge leave one
classical local obligation.  It is enough to reduce ordered brackets of basic
Hall trees whose left input is itself a commutator and whose right input is
too small for Hall admissibility.

Admissible brackets are already basic, equal brackets vanish, and reversed
brackets reduce by skew-symmetry.  This file packages that final local
reduction boundary and feeds it into the all-weight spanning theorem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The remaining classical local case: an ordered basic bracket whose left input
is itself a commutator, but whose right input is too small for Hall
admissibility.
-/
structure NBRed : Prop where
  bracket_mem :
    ∀ (u₁ u₂ v : HallTree α)
      (_hu : (commutator u₁ u₂).IsBasic)
      (_hv : v.IsBasic)
      (_hvu : v < commutator u₁ u₂)
      (_hvu₂ : v < u₂)
      {r : ℕ}
      (hweight : (commutator (commutator u₁ u₂) v).weight = r),
      (commutator (commutator u₁ u₂) v).freeLowerWeight
          hweight ∈
        basicTreeSpan (α := α) r

namespace NBRed

/-- Resolve an ordered bracket of basic Hall trees. -/
theorem ordered_bracket_mem
    (kernel : NBRed (α := α))
    (u v : HallTree α)
    (hu : u.IsBasic)
    (hv : v.IsBasic)
    (hvu : v < u)
    {r : ℕ}
    (hweight : (commutator u v).weight = r) :
    (commutator u v).freeLowerWeight hweight ∈
      basicTreeSpan (α := α) r := by
  cases u with
  | atom a =>
      exact
        free_tree_admissible
          (atom a) v hu hv hvu trivial hweight
  | commutator u₁ u₂ =>
      rcases lt_or_ge v u₂ with hvu₂ | hu₂v
      · exact kernel.bracket_mem u₁ u₂ v hu hv hvu hvu₂ hweight
      · exact
          free_tree_admissible
            (commutator u₁ u₂) v hu hv hvu hu₂v hweight

/--
Admissibility, zero, skew-symmetry, and the non-admissible local kernel resolve
the bracket of every two basic Hall trees.
-/
theorem basic_bracket_mem
    (kernel : NBRed (α := α))
    (u v : HallTree α)
    (hu : u.IsBasic)
    (hv : v.IsBasic)
    {r : ℕ}
    (hweight : (commutator u v).weight = r) :
    (commutator u v).freeLowerWeight hweight ∈
      basicTreeSpan (α := α) r := by
  rcases lt_trichotomy v u with hvu | heq | huv
  · exact kernel.ordered_bracket_mem u v hu hv hvu hweight
  · subst v
    exact
      self_tree_span
        u hweight
  · apply
      free_tree_swap
        u v hweight
    exact kernel.ordered_bracket_mem v u hv hu huv
      (by simpa only [weight_commutator, Nat.add_comm] using hweight)

/-- Resolve the bracket of every two indexed basic Hall trees. -/
theorem indexed_tree_commutator
    (kernel : NBRed (α := α))
    {i j : ℕ}
    (u : BasicIndex (α := α) i)
    (v : BasicIndex (α := α) j) :
    (commutator (indexedBasicTree u) (indexedBasicTree v)).freeLowerWeight
        (by
          simp only [weight_commutator, indexed_tree_weight]) ∈
      basicTreeSpan (α := α) (i + j) :=
  kernel.basic_bracket_mem
    (indexedBasicTree u) (indexedBasicTree v)
    (indexed_tree u) (indexed_tree v)
    (by simp only [weight_commutator, indexed_tree_weight])

/--
Reducing only non-admissible ordered basic brackets suffices for all-weight
basic Hall spanning.
-/
theorem tree_span_top
    (kernel : NBRed (α := α))
    {r : ℕ}
    (hr : 0 < r) :
    basicTreeSpan (α := α) r = ⊤ :=
  tree_top_indexed
    (fun u v => kernel.indexed_tree_commutator u v) hr

end NBRed

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- The number of basic trees of bounded height that are at most `w`. -/
def treeUpHeight
    (n : ℕ)
    (w : HallTree α) :
    ℕ :=
  ((treesUpHeight (α := α) n).filter fun v => v ≤ w).card

/--
Reverse finite rank among basic trees of bounded height.  This is the
secondary recursion measure for Hall normalization at fixed total weight.
-/
def defectUpHeight
    (n : ℕ)
    (w : HallTree α) :
    ℕ :=
  (treesUpHeight (α := α) n).card -
    treeUpHeight n w

/-- A basic tree whose weight is at most `n` occurs in the bounded Hall family. -/
theorem trees_up_height
    {n : ℕ}
    {w : HallTree α}
    (hw : w.IsBasic)
    (hweight : w.weight ≤ n) :
    w ∈ treesUpHeight (α := α) n :=
  recursive_trees_height n w hw
    (w.height_le_weight.trans hweight)

/-- The bounded basic-tree rank never exceeds the size of the bounded family. -/
theorem up_height_card
    (n : ℕ)
    (w : HallTree α) :
    treeUpHeight (α := α) n w ≤
      (treesUpHeight (α := α) n).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- Strict Hall order gives strict bounded rank growth inside the finite family. -/
theorem rank_up_height
    {n : ℕ}
    {u v : HallTree α}
    (hv : v ∈ treesUpHeight (α := α) n)
    (huv : u < v) :
    treeUpHeight n u < treeUpHeight n v := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.trans huv.le⟩
  · intro heq
    have hvv :
        v ∈
          (treesUpHeight (α := α) n).filter
            (fun w => w ≤ v) := by
      simp only [Finset.mem_filter]
      exact ⟨hv, le_rfl⟩
    have hvu :
        v ∉
          (treesUpHeight (α := α) n).filter
            (fun w => w ≤ u) := by
      simp only [Finset.mem_filter, hv, true_and, not_le]
      exact huv
    rw [heq] at hvu
    exact hvu hvv

/-- Increasing a bounded basic tree strictly decreases its reverse rank. -/
theorem tree_up_height
    {n : ℕ}
    {u v : HallTree α}
    (hv : v ∈ treesUpHeight (α := α) n)
    (huv : u < v) :
    defectUpHeight n v <
      defectUpHeight n u := by
  have hrank := rank_up_height hv huv
  have hvBound := up_height_card (α := α) n v
  simp only [defectUpHeight]
  omega

/--
Increasing a basic tree of bounded weight strictly decreases its reverse
rank, without requiring explicit finite-family membership at the call site.
-/
theorem defect_up_height
    {n : ℕ}
    {u v : HallTree α}
    (hvBasic : v.IsBasic)
    (hvWeight : v.weight ≤ n)
    (huv : u < v) :
    defectUpHeight n v <
      defectUpHeight n u :=
  tree_up_height
    (trees_up_height
      hvBasic hvWeight)
    huv

/--
Secondary Hall-normalization measure for a bracket pair at fixed total
weight.  Taking the minimum makes the measure insensitive to skew swaps.
-/
def bracketRankDefect
    (n : ℕ)
    (u v : HallTree α) :
    ℕ :=
  defectUpHeight n (min u v)

/--
If both factors of a replacement bracket are larger than the original right
factor, the replacement has strictly smaller pair defect.
-/
theorem bracket_defect_both
    {n : ℕ}
    {u v x y : HallTree α}
    (hvu : v < u)
    (hvx : v < x)
    (hvy : v < y)
    (hxBasic : x.IsBasic)
    (hyBasic : y.IsBasic)
    (hxWeight : x.weight ≤ n)
    (hyWeight : y.weight ≤ n) :
    bracketRankDefect n x y <
      bracketRankDefect n u v := by
  have hminBasic : (min x y).IsBasic := by
    rcases min_choice x y with h | h
    · simpa only [h] using hxBasic
    · simpa only [h] using hyBasic
  have hminWeight : (min x y).weight ≤ n := by
    rcases min_choice x y with h | h
    · simpa only [h] using hxWeight
    · simpa only [h] using hyWeight
  have hvmin : v < min x y := lt_min hvx hvy
  simpa only [bracketRankDefect, min_eq_right hvu.le] using
    defect_up_height
      hminBasic hminWeight hvmin

omit [Fintype α] [DecidableEq α] in
/-- Adding a positive left weight makes a Hall tree strictly larger. -/
theorem weight_add_left
    (u v w : HallTree α)
    (hweight : w.weight = u.weight + v.weight) :
    v < w := by
  apply lt_weight_lt
  rw [hweight]
  have hu := u.weight_pos
  omega

omit [Fintype α] [DecidableEq α] in
/--
In the first Jacobi descendant `[[a,v],b]`, both possible eventual right
factors are strictly larger than the original right factor `v`.
-/
theorem both_jacobi_first
    (a b v t : HallTree α)
    (hvb : v < b)
    (htWeight : t.weight = a.weight + v.weight) :
    v < b ∧ v < t :=
  ⟨hvb, weight_add_left a v t htWeight⟩

omit [Fintype α] [DecidableEq α] in
/--
In the second Jacobi descendant `[[b,v],a]`, both possible eventual right
factors are strictly larger than the original right factor `v`.
-/
theorem both_jacobi_factors
    (a b v t : HallTree α)
    (hvb : v < b)
    (hba : b < a)
    (htWeight : t.weight = b.weight + v.weight) :
    v < a ∧ v < t :=
  ⟨hvb.trans hba, weight_add_left b v t htWeight⟩

end HallTree
end Submission


/-!
# Strict Hall reduction descent for Jacobi descendants

The non-admissible Hall reduction rewrites `[[a, b], v]` with `v < b` into
the two Jacobi descendants `[[a, v], b]` and `[[b, v], a]`.  Once either
inner bracket has been reduced to basic trees, every possible eventual right
factor is strictly larger than `v`.

This file turns that order progress into the reverse finite-rank inequalities
needed by a well-founded fixed-weight normalizer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
After reducing the inner bracket `[a, v]` to a basic tree `t`, both possible
right factors in the first Jacobi descendant have smaller reverse rank than
the original right factor `v`.
-/
theorem defect_up_both
    (a b v t : HallTree α)
    (hvb : v < b)
    (hbBasic : b.IsBasic)
    (htBasic : t.IsBasic)
    (htWeight : t.weight = a.weight + v.weight) :
    defectUpHeight ((a.weight + v.weight) + b.weight) b <
        defectUpHeight ((a.weight + v.weight) + b.weight) v ∧
      defectUpHeight ((a.weight + v.weight) + b.weight) t <
        defectUpHeight ((a.weight + v.weight) + b.weight) v := by
  rcases both_jacobi_first a b v t hvb htWeight with
    ⟨hvb, hvt⟩
  constructor
  · apply defect_up_height hbBasic
    · omega
    · exact hvb
  · apply defect_up_height htBasic
    · omega
    · exact hvt

/--
After reducing the inner bracket `[b, v]` to a basic tree `t`, both possible
right factors in the second Jacobi descendant have smaller reverse rank than
the original right factor `v`.
-/
theorem up_height_both
    (a b v t : HallTree α)
    (hvb : v < b)
    (hba : b < a)
    (haBasic : a.IsBasic)
    (htBasic : t.IsBasic)
    (htWeight : t.weight = b.weight + v.weight) :
    defectUpHeight ((b.weight + v.weight) + a.weight) a <
        defectUpHeight ((b.weight + v.weight) + a.weight) v ∧
      defectUpHeight ((b.weight + v.weight) + a.weight) t <
        defectUpHeight ((b.weight + v.weight) + a.weight) v := by
  rcases both_jacobi_factors a b v t hvb hba htWeight with
    ⟨hva, hvt⟩
  constructor
  · apply defect_up_height haBasic
    · omega
    · exact hva
  · apply defect_up_height htBasic
    · omega
    · exact hvt

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The bracket of two Hall trees has been reduced to the basic-tree span in an
explicitly chosen total weight.
-/
def BBRed
    (n : ℕ)
    (u v : HallTree α) :
    Prop :=
  ∀ hweight : (commutator u v).weight = n,
    (commutator u v).freeLowerWeight hweight ∈
      basicTreeSpan (α := α) n

/-- An admissible bracket of basic Hall trees is reduced. -/
theorem bracket_reduced_admissible
    {n : ℕ}
    {u v : HallTree α}
    (hu : u.IsBasic)
    (hv : v.IsBasic)
    (hvu : v < u)
    (hadmissible :
      match u with
      | atom _ => True
      | commutator _ u₂ => u₂ ≤ v) :
    BBRed n u v := by
  intro hweight
  exact
    free_tree_admissible
      u v hu hv hvu hadmissible hweight

/-- A self-bracket is reduced because its class vanishes. -/
theorem bracket_reduced_self
    {n : ℕ}
    (u : HallTree α) :
    BBRed n u u := by
  intro hweight
  exact
    self_tree_span
      u hweight

/-- Reversing a reduced bracket preserves reduction by skew-symmetry. -/
theorem BBRed.swap
    {n : ℕ}
    {u v : HallTree α}
    (h : BBRed n v u) :
    BBRed n u v := by
  intro hweight
  apply
    free_tree_swap
      u v hweight
  exact h (by
    simp only [weight_commutator] at hweight ⊢
    omega)

/--
Jacobi repairs a left-normed bracket once its two descendant brackets have
been reduced.
-/
theorem bracket_reduced_jacobi
    {n : ℕ}
    (u v w : HallTree α)
    (huw : BBRed n (commutator u w) v)
    (hvw : BBRed n (commutator v w) u) :
    BBRed n (commutator u v) w := by
  intro hweight
  apply
    free_tree_jacobi
      u v w hweight
  · exact huw (by
      simp only [weight_commutator] at hweight ⊢
      omega)
  · exact hvw (by
      simp only [weight_commutator] at hweight ⊢
      omega)

/--
Reduce an inner bracket to a span, then reduce each indexed replacement
against the unchanged outer right factor.
-/
theorem bracket_reduced_span
    (u v w : HallTree α)
    (hinner :
      BBRed (u.weight + v.weight) u v)
    (houter :
      ∀ t : BasicIndex (α := α) (u.weight + v.weight),
        BBRed
          ((u.weight + v.weight) + w.weight)
          (indexedBasicTree t) w) :
    BBRed
      ((u.weight + v.weight) + w.weight)
      (commutator u v) w := by
  intro hweight
  rw [free_central_commutator
    (commutator u v) w hweight]
  exact
    bracket_tree_left
      (commutator u v).weight_pos w.weight_pos w rfl
      (fun t => houter t (by
        simp only [weight_commutator, indexed_tree_weight]))
      (hinner rfl)

/--
The bracket of two basic Hall trees reduces to the basic-tree span.  The
outer induction is on total weight.  At fixed weight, Jacobi strictly
decreases the reverse finite rank of the smaller bracket factor.
-/
theorem basic_bracket_reduced
    (n : ℕ)
    (u v : HallTree α)
    (hu : u.IsBasic)
    (hv : v.IsBasic)
    (hweight : u.weight + v.weight = n) :
    BBRed n u v := by
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
      have ordered :
          ∀ fuel : ℕ,
            ∀ (u v : HallTree α),
              u.IsBasic →
              v.IsBasic →
              v < u →
              u.weight + v.weight = n →
              bracketRankDefect n u v = fuel →
              BBRed n u v := by
        intro fuel
        induction fuel using Nat.strong_induction_on with
        | h fuel ihFuel =>
            intro u v hu hv hvu huvWeight hfuel
            cases u with
            | atom a =>
                exact
                  bracket_reduced_admissible
                    hu hv hvu trivial
            | commutator a b =>
                rcases (isBasic_commutator a b).mp hu with
                  ⟨ha, hb, hba, hab⟩
                by_cases hbv : b ≤ v
                · exact
                    bracket_reduced_admissible
                      hu hv hvu hbv
                · have hvb : v < b := lt_of_not_ge hbv
                  have reduceOuter
                      (x y : HallTree α)
                      (hx : x.IsBasic)
                      (hy : y.IsBasic)
                      (hvx : v < x)
                      (hvy : v < y)
                      (hxyWeight : x.weight + y.weight = n) :
                      BBRed n x y := by
                    have hxWeight : x.weight ≤ n := by
                      have hyPos := y.weight_pos
                      omega
                    have hyWeight : y.weight ≤ n := by
                      have hxPos := x.weight_pos
                      omega
                    rcases lt_trichotomy y x with hyx | hyx | hxy
                    · apply ihFuel
                        (bracketRankDefect n x y)
                        (by
                          have hdesc :=
                            bracket_defect_both
                              hvu hvx hvy hx hy hxWeight hyWeight
                          omega)
                        x y hx hy hyx hxyWeight rfl
                    · subst y
                      exact bracket_reduced_self x
                    · apply BBRed.swap
                      apply ihFuel
                        (bracketRankDefect n y x)
                        (by
                          have hdesc :=
                            bracket_defect_both
                              hvu hvx hvy hx hy hxWeight hyWeight
                          have hdesc' :
                              bracketRankDefect n y x <
                                bracketRankDefect n
                                  (commutator a b) v := by
                            simpa only [bracketRankDefect, min_comm]
                              using hdesc
                          omega)
                        y x hy hx hxy
                        (by omega) rfl
                  apply
                    bracket_reduced_jacobi
                      a b v
                  · have htotal : a.weight + v.weight + b.weight = n := by
                      simp only [weight_commutator] at huvWeight
                      omega
                    rw [← htotal]
                    apply
                      bracket_reduced_span
                        a v b
                    · apply ih (a.weight + v.weight)
                      · simp only [weight_commutator] at huvWeight
                        have hbPos := b.weight_pos
                        omega
                      · exact ha
                      · exact hv
                      · rfl
                    · intro t
                      rw [htotal]
                      apply reduceOuter (indexedBasicTree t) b
                        (indexed_tree t) hb
                      · exact
                          weight_add_left a v (indexedBasicTree t)
                            (indexed_tree_weight t)
                      · exact hvb
                      · simp only [indexed_tree_weight,
                          weight_commutator] at huvWeight ⊢
                        omega
                  · have htotal : b.weight + v.weight + a.weight = n := by
                      simp only [weight_commutator] at huvWeight
                      omega
                    rw [← htotal]
                    apply
                      bracket_reduced_span
                        b v a
                    · apply ih (b.weight + v.weight)
                      · simp only [weight_commutator] at huvWeight
                        have haPos := a.weight_pos
                        omega
                      · exact hb
                      · exact hv
                      · rfl
                    · intro t
                      rw [htotal]
                      apply reduceOuter (indexedBasicTree t) a
                        (indexed_tree t) ha
                      · exact
                          weight_add_left b v (indexedBasicTree t)
                            (indexed_tree_weight t)
                      · exact hvb.trans hba
                      · simp only [indexed_tree_weight,
                          weight_commutator] at huvWeight ⊢
                        omega
      rcases lt_trichotomy v u with hvu | hvu | huv
      · exact
          ordered (bracketRankDefect n u v)
            u v hu hv hvu hweight rfl
      · subst v
        exact bracket_reduced_self u
      · apply BBRed.swap
        exact
          ordered (bracketRankDefect n v u)
            v u hv hu huv (by omega) rfl

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- Every bracket of indexed Hall basic trees reduces to the basic-tree span. -/
theorem indexed_tree_span
    {i j : ℕ}
    (u : BasicIndex (α := α) i)
    (v : BasicIndex (α := α) j) :
    (commutator (indexedBasicTree u) (indexedBasicTree v)).freeLowerWeight
        (by
          simp only [weight_commutator, indexed_tree_weight]) ∈
      basicTreeSpan (α := α) (i + j) := by
  apply
    basic_bracket_reduced
      (i + j) (indexedBasicTree u) (indexedBasicTree v)
      (indexed_tree u) (indexed_tree v)
      (by simp only [indexed_tree_weight])

/-- Every Hall-tree class reduces to the basic-tree span in its own weight. -/
theorem basic_tree_span
    (w : HallTree α) :
    w.freeCentralLayer ∈
      basicTreeSpan (α := α) w.weight :=
  tree_indexed_commutator
    indexed_tree_span w

/--
In every positive weight, the indexed Hall basic classes span the free-group
lower-central associated-graded layer.
-/
theorem tree_span_top
    {r : ℕ}
    (hr : 0 < r) :
    basicTreeSpan (α := α) r = ⊤ :=
  tree_top_indexed
    indexed_tree_span hr

/--
Expanded form of the all-weight Hall spanning theorem, ready for the existing
basis-input interface.
-/
theorem indexed_basic_top
    {r : ℕ}
    (hr : 0 < r) :
    Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) r =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) =
      ⊤ := by
  simpa only [basicTreeSpan] using
    tree_span_top (α := α) hr

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The generic basic-tree span agrees with the previously constructed spanning
results through weight three.
-/
theorem tree_top_pos
    {r : ℕ}
    (hrPos : 0 < r)
    (hr : r ≤ 3) :
    basicTreeSpan (α := α) r = ⊤ := by
  interval_cases r
  · simpa [basicTreeSpan] using
      indexed_span_top
        (α := α)
  · simpa [basicTreeSpan] using
      indexed_free_top
        (α := α)
  · simpa [basicTreeSpan] using
      indexed_tree_top
        (α := α)

/-- Every Hall tree through weight three reduces to the generic basic-tree span. -/
theorem free_tree_pos
    {r : ℕ}
    (hrPos : 0 < r)
    (hr : r ≤ 3)
    (w : HallTree α)
    (hweight : w.weight = r) :
    w.freeLowerWeight hweight ∈
      basicTreeSpan (α := α) r := by
  rw [tree_top_pos hrPos hr]
  trivial

/--
In total weight at most three, the pointwise indexed-commutator obligation of
the recursive reduction interface is already discharged.
-/
theorem indexed_tree_three
    {i j : ℕ}
    (u : BasicIndex (α := α) i)
    (v : BasicIndex (α := α) j)
    (hij : i + j ≤ 3) :
    (commutator (indexedBasicTree u) (indexedBasicTree v)).freeLowerWeight
        (by
          simp only [weight_commutator, indexed_tree_weight]) ∈
      basicTreeSpan (α := α) (i + j) := by
  rw [tree_top_pos
    (by
      have hi : 0 < i := by
        simpa only [← indexed_tree_weight u] using
          (indexedBasicTree u).weight_pos
      have hj : 0 < j := by
        simpa only [← indexed_tree_weight v] using
          (indexedBasicTree v).weight_pos
      omega)
    hij]
  trivial

end HallTree
end Submission


/-!
# All-weight concrete Hall basis reduced to signed triangularity

The well-founded Hall normalizer proves that indexed basic Hall classes span
every positive free-group lower-central layer.  Consequently the only
remaining classical input for the concrete graded Hall basis theorem is
signed standard-word triangularity of the recursive Hall polynomials.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped IsMulCommutative

/--
At one positive weight, signed standard-word triangularity now suffices for
the concrete free-group associated-graded Hall basis.
-/
theorem forms_graded_pivots
    {d r : ℕ}
    (pivots :
      HallTree.SSPivots
        (α := FreeGenerator.{u} d) ℤ r)
    (hr : 0 < r) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_associated_input
    { pivots := pivots
      span_eq_top :=
        HallTree.indexed_basic_top
          hr }
    hr

/--
An all-weight signed standard-word system supplies concrete free-group graded
Hall bases in every positive ordinary weight.
-/
theorem forms_associated_system
    (d : ℕ)
    (pivots :
      HallTree.SSSystem
        (α := FreeGenerator.{u} d) ℤ) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  fun r hr =>
    forms_graded_pivots
      (pivots.pivots r) hr

end TCTex
end Submission


/-!
# All-weight concrete Hall basis reduced to signed triangularity

The classical Hall leading-word theorem naturally gives a triangular
coefficient matrix.  This file combines that input with the all-weight
spanning theorem and packages the exact concrete basis predicate consumed by
the collection development.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

open TBluepr

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The triangularity and spanning inputs required to build a free-group
lower-central Hall basis in one weight.
-/
structure TBInput
    (r : ℕ) where
  words : STWords (α := α) ℤ r
  span_eq_top :
    Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) r =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) =
      ⊤

/-- Signed triangularity plus spanning constructs the fixed-weight basis. -/
noncomputable def TBInput.basis
    {r : ℕ}
    (P : TBInput (α := α) r)
    (hr : 0 < r) :
    Module.Basis (BasicIndex (α := α) r) ℤ
      (Additive
        (LowerGradedLayer (FreeGroup α) (r - 1))) :=
  Module.Basis.mk
    (P.words.freegr_lowec_weigh hr)
    (by rw [P.span_eq_top])

end HallTree

namespace TCTex

universe u

open scoped IsMulCommutative

/--
Map a triangular Magnus-side Hall basis to the one-based collection layer and
reindex it by the universe-lifted concrete Hall-family index.
-/
noncomputable def concreteTriangularInput
    {d r : ℕ}
    (P : HallTree.TBInput
      (α := FreeGenerator.{u} d) r)
    (hr : 0 < r) :
    Module.Basis (concreteCommutatorsWeight.{u} d r).index ℤ
      (Additive
        (AssociatedGradedLayer
          (FreeGroup (FreeGenerator.{u} d)) r)) :=
  ((P.basis hr).map
    (lowerGradedLinear
      (FreeGroup (FreeGenerator.{u} d)) r hr)).reindex Equiv.ulift.symm

/--
A triangular Magnus-side Hall basis packet supplies the classical free-group
basis predicate consumed by the collection development.
-/
theorem forms_triangular_input
    {d r : ℕ}
    (P : HallTree.TBInput
      (α := FreeGenerator.{u} d) r)
    (hr : 0 < r) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis := by
  refine ⟨concreteTriangularInput P hr, ?_⟩
  intro i
  rw [concreteTriangularInput,
    Module.Basis.reindex_apply, Module.Basis.map_apply]
  simpa [HallTree.TBInput.basis,
    Module.Basis.mk_apply] using
      graded_indexed_tree
        hr i.down

/--
At one positive weight, signed leading-word triangularity suffices for the
concrete free-group associated-graded Hall basis.
-/
theorem forms_triangular_words
    {d r : ℕ}
    (words :
      HallTree.STWords
        (α := FreeGenerator.{u} d) ℤ r)
    (hr : 0 < r) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  forms_triangular_input
    { words := words
      span_eq_top :=
        HallTree.indexed_basic_top
          hr }
    hr

/--
An all-weight signed triangular standard-word system supplies concrete
free-group graded Hall bases in every positive ordinary weight.
-/
theorem forms_triangular_system
    (d : ℕ)
    (words :
      HallTree.TriangularStandardSystem
        (α := FreeGenerator.{u} d) ℤ) :
    ∀ r : ℕ, 0 < r →
      (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  fun r hr =>
    forms_triangular_words
      (words.words r) hr

end TCTex
end Submission

import Towers.Group.HallBasic.Word
import Towers.Group.Zassenhaus.TriangularGHLaw
import Towers.Group.HallBasic.Weight

open Towers.TCTex
open scoped IsMulCommutative

namespace Towers

universe u

namespace TCTex

/--
The Hall basic commutators of fixed weight used by the collection layer,
constructed from the canonical Hall-tree enumeration.
-/
noncomputable def concreteCommutatorsWeight
    (d r : ℕ) :
    BCWta.{u} d r where
  index := ULift.{u} (HallTree.BasicIndex (α := FreeGenerator.{u} d) r)
  commutator i :=
    { word := HallTree.indexedCommutatorWord i.down
      word_weight := HallTree.indexed_commutator_weight i.down }

/-- The concrete Hall family in every ordinary weight. -/
noncomputable def concreteBasicCommutators
    (d : ℕ) :
    ∀ r : ℕ, BCWta.{u} d r :=
  fun r => concreteCommutatorsWeight.{u} d r

/-- Recover the bracket tree underlying a concrete Hall-family index. -/
noncomputable def concreteBasicTree
    {d r : ℕ}
    (i : (concreteCommutatorsWeight.{u} d r).index) :
    HallTree (FreeGenerator.{u} d) :=
  HallTree.indexedBasicTree i.down

@[simp] theorem concrete_hall_tree
    {d r : ℕ}
    (i : (concreteCommutatorsWeight.{u} d r).index) :
    (concreteBasicTree i).IsBasic :=
  HallTree.indexed_tree i.down

@[simp] theorem concrete_tree_weight
    {d r : ℕ}
    (i : (concreteCommutatorsWeight.{u} d r).index) :
    (concreteBasicTree i).weight = r :=
  HallTree.indexed_tree_weight i.down

@[simp] theorem concrete_basic_word
    {d r : ℕ}
    (i : (concreteCommutatorsWeight.{u} d r).index) :
    ((concreteCommutatorsWeight.{u} d r).commutator i).word =
      (concreteBasicTree i).toCWord :=
  rfl

theorem concrete_basic_injective
    {d r : ℕ} :
    Function.Injective
      (fun i : (concreteCommutatorsWeight.{u} d r).index =>
        ((concreteCommutatorsWeight.{u} d r).commutator i).word) := by
  intro i j hij
  apply ULift.down_injective
  exact HallTree.indexed_commutator_injective hij

theorem concrete_basic_tree
    {d r : ℕ}
    {w : HallTree (FreeGenerator.{u} d)}
    (hw : w.IsBasic) (hweight : w.weight = r) :
    ∃ i : (concreteCommutatorsWeight.{u} d r).index,
      concreteBasicTree i = w := by
  obtain ⟨i, hi⟩ := HallTree.indexed_basic_tree hw hweight
  exact ⟨ULift.up i, hi⟩

theorem concrete_commutator_word
    {d r : ℕ}
    {w : HallTree (FreeGenerator.{u} d)}
    (hw : w.IsBasic) (hweight : w.weight = r) :
    ∃ i : (concreteCommutatorsWeight.{u} d r).index,
      ((concreteCommutatorsWeight.{u} d r).commutator i).word =
        w.toCWord := by
  obtain ⟨i, hi⟩ := concrete_basic_tree hw hweight
  exact ⟨i, by rw [concrete_basic_word, hi]⟩

@[simp] theorem concrete_commutators_empty
    (d : ℕ) :
    IsEmpty (concreteCommutatorsWeight.{u} d 0).index := by
  constructor
  intro i
  simpa [concreteCommutatorsWeight, HallTree.BasicIndex] using
    i.down.isLt

end TCTex

end Towers

noncomputable section

namespace Towers
namespace TCTex

open TBluepr

universe u

/--
For a positive ordinary weight, the zero-based lower-central layer used by the
Magnus development is the one-based TeX layer used by collection.
-/
noncomputable def lowerCentralGraded
    (G : Type u) [Group G]
    (r : ℕ)
    (hr : 0 < r) :
    LowerGradedLayer G (r - 1) ≃*
      AssociatedGradedLayer G r := by
  apply QuotientGroup.quotientMulEquivOfEq
  rw [Nat.sub_add_cancel hr]

/-- Integer-linear additive form of the indexing-convention equivalence. -/
noncomputable def lowerGradedLinear
    (G : Type u) [Group G]
    (r : ℕ)
    (hr : 0 < r) :
    Additive (LowerGradedLayer G (r - 1)) ≃ₗ[ℤ]
      Additive (AssociatedGradedLayer G r) :=
  (MulEquiv.toAdditive
    (lowerCentralGraded G r hr)).toIntLinearEquiv

/--
The indexing-convention equivalence carries the Magnus-side Hall-tree class to
the one-based associated-graded class represented by the same commutator word.
-/
theorem lower_graded_group
    {α : Type u}
    {r : ℕ}
    (hr : 0 < r)
    (w : HallTree α)
    (hweight : w.weight = r) :
    lowerGradedLinear (FreeGroup α) r hr
        (w.freeLowerWeight hweight) =
      Additive.ofMul
        (QuotientGroup.mk'
          ((Subgroup.lowerCentralSeries (FreeGroup α) r).subgroupOf
            (Subgroup.lowerCentralSeries (FreeGroup α) (r - 1)))
          ⟨w.toCWord.eval FreeGroup.of, by
            simpa [hweight] using
              (CWord.eval_lower_series
                FreeGroup.of
                (fun _ : α => 1)
                (fun _ => by simp)
                (fun _ => by simp)
                w.toCWord)⟩) := by
  subst r
  simp [lowerGradedLinear,
    lowerCentralGraded,
    HallTree.freeLowerWeight,
    HallTree.freeCentralLayer,
    HallTree.freeCentralRep]

/--
For the concrete Hall family, the indexing-convention equivalence carries an
indexed Hall-tree class to the collection layer's free-group class.
-/
theorem graded_indexed_tree
    {d r : ℕ}
    (hr : 0 < r)
    (i : HallTree.BasicIndex (α := FreeGenerator.{u} d) r) :
    lowerGradedLinear
        (FreeGroup (FreeGenerator.{u} d)) r hr
        ((HallTree.indexedBasicTree i).freeLowerWeight
          (HallTree.indexed_tree_weight i)) =
      ((concreteCommutatorsWeight.{u} d r).commutator
        (ULift.up i)).free_groupassoc_gradedclass := by
  rw [
    lower_graded_group]
  rfl

/--
Map a Magnus-side Hall basis to the one-based collection layer and reindex it
by the universe-lifted concrete Hall-family index.
-/
noncomputable def concreteBasisInput
    {d r : ℕ}
    (P : HallTree.FBInput
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
A Magnus-side Hall basis packet supplies the exact classical free-group basis
predicate consumed by the collection development.
-/
theorem forms_associated_input
    {d r : ℕ}
    (P : HallTree.FBInput
      (α := FreeGenerator.{u} d) r)
    (hr : 0 < r) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis := by
  refine ⟨concreteBasisInput P hr, ?_⟩
  intro i
  rw [concreteBasisInput,
    Module.Basis.reindex_apply, Module.Basis.map_apply]
  simpa [HallTree.FBInput.basis, Module.Basis.mk_apply] using
    graded_indexed_tree
      hr i.down

end TCTex
end Towers

namespace Towers
namespace TCTex

universe u

/--
The concrete weight-one Hall family is a basis of the first lower-central
associated-graded layer of the free group.
-/
theorem forms_graded_basis
    (d : ℕ) :
    (concreteCommutatorsWeight.{u} d 1).FormsfreeGroupassocGradedbasis :=
  forms_associated_input
    (HallTree.weightBasisInput
      (α := FreeGenerator.{u} d))
    (by omega)

end TCTex
end Towers

namespace Towers
namespace TCTex

universe u

/--
The concrete weight-two Hall family is a basis of the second lower-central
associated-graded layer of the free group.
-/
theorem forms_associated_basis
    (d : ℕ) :
    (concreteCommutatorsWeight.{u} d 2).FormsfreeGroupassocGradedbasis :=
  forms_associated_input
    (HallTree.lowerBasisInput
      (α := FreeGenerator.{u} d))
    (by omega)

end TCTex
end Towers

namespace Towers
namespace TCTex

universe u

/--
The concrete weight-three Hall family is a basis of the third lower-central
associated-graded layer of the free group.
-/
theorem commutators_forms_graded
    (d : ℕ) :
    (concreteCommutatorsWeight.{u} d 3).FormsfreeGroupassocGradedbasis :=
  forms_associated_input
    (HallTree.freeBasisInput
      (α := FreeGenerator.{u} d))
    (by omega)

end TCTex
end Towers

namespace Towers
namespace TCTex

universe u

/--
The concrete Hall family has the required free-group associated-graded basis
property in each of the first two positive weights.
-/
theorem forms_associated_graded
    {d r : ℕ}
    (hr : r = 1 ∨ r = 2) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis := by
  rcases hr with rfl | rfl
  · exact
      forms_graded_basis d
  · exact
      forms_associated_basis d

/--
The concrete Hall family has the required free-group associated-graded basis
property in each of the first three positive weights.
-/
theorem commutators_forms_associated
    {d r : ℕ}
    (hrPos : 0 < r)
    (hr : r ≤ 3) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis := by
  interval_cases r
  · exact
      forms_graded_basis d
  · exact
      forms_associated_basis d
  · exact
      commutators_forms_graded d

end TCTex
end Towers

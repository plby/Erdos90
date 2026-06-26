import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.EquivFin

/-!
# Chapter VIII, Section 4: cardinality rigidity

Before Lemma 4.1, Milne uses a surjection from a subgroup `H^2(L/K)'` onto a cyclic group of
order `n`, together with the upper bound `|H^2(L/K)| <= n`, to conclude that the subgroup is the
whole group and that the surjection is an isomorphism.  This file isolates that finite argument.

Constructing the cohomology groups, the invariant map, and the fundamental exact sequence itself
requires the global idele-class cohomology and local Brauer invariant interfaces that are not yet
available in the project.
-/

namespace Towers.CField.GClass

/-- A surjection between finite types is injective when the source has no larger cardinality. -/
theorem injective_surjective_card
    {A B : Type*} [Fintype A] [Fintype B] (f : A → B)
    (hf : Function.Surjective f) (hcard : Fintype.card A ≤ Fintype.card B) :
    Function.Injective f := by
  exact ((Fintype.bijective_iff_surjective_and_card f).2
    ⟨hf, le_antisymm hcard (Fintype.card_le_of_surjective f hf)⟩).1

/-- The cardinality argument used for parts (a) and (b) before Lemma 4.1.  A subgroup which
surjects onto an `n`-element type, inside an ambient type of cardinality at most `n`, must be the
whole ambient type; all three cardinalities are `n`. -/
theorem top_surjective_card
    {A B : Type*} [Group A] [Fintype A] [Fintype B]
    (H : Subgroup A) (f : H → B) (hf : Function.Surjective f)
    (hcard : Fintype.card A ≤ Fintype.card B) :
    H = ⊤ ∧ Fintype.card A = Fintype.card B ∧ Function.Bijective f := by
  letI : Fintype H := Fintype.ofFinite H
  have hBA : Fintype.card B ≤ Fintype.card H :=
    Fintype.card_le_of_surjective f hf
  have hHA : Fintype.card H ≤ Fintype.card A :=
    Fintype.card_subtype_le (fun a : A ↦ a ∈ H)
  have hAH : Fintype.card A = Fintype.card H :=
    le_antisymm (hcard.trans hBA) hHA
  have hHtop : H = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top H).mp
    simpa [Nat.card_eq_fintype_card] using hAH.symm
  have hAB : Fintype.card A = Fintype.card B :=
    le_antisymm hcard (hBA.trans hHA)
  refine ⟨hHtop, hAB, ?_⟩
  exact (Fintype.bijective_iff_surjective_and_card f).2
    ⟨hf, hAH.symm.trans hAB⟩

end Towers.CField.GClass

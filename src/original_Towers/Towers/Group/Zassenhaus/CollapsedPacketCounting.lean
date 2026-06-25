import Towers.Group.Zassenhaus.SchedulingContracts

/-!
# Counting collapsed Hall-Petresco correction packets

For polynomial compression, a packet does not need to remember the exact order
of the canonical realization slots.  It needs a common erased Hall shape and
the realization count prescribed by its block family.  Pairwise correction of
two such closed packets again closes: its words have the correction shape and
its length is the product of the parent lengths.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace PCCounti

open HACoeff

/-- Every word in a list has one fixed erased Hall-pair shape. -/
def SCShape
    {M N : ℕ}
    (shape : CWord HPAtom)
    (words : List (CWord (LabelledAtom M N))) :
    Prop :=
  ∀ w ∈ words, collapseWord w = shape

/--
A closed collapsed packet has one family shape and the family realization
count.  Exact realization-slot identities are deliberately not required.
-/
structure CPFor
    {M N : ℕ}
    (F : BFam M N)
    (words : List (CWord (LabelledAtom M N))) :
    Prop where
  same_shape :
    SCShape F.recipe.erasedShape words
  length_eq :
    words.length = F.realizations.length

/-- Pair every word in the left packet with every word in the right packet. -/
def correctionWords
    {M N : ℕ}
    (left right : List (CWord (LabelledAtom M N))) :
    List (CWord (LabelledAtom M N)) :=
  left.flatMap fun b =>
    right.map fun a => .commutator b a

@[simp]
lemma correctionWords_realizations
    {M N : ℕ}
    (B A : BFam M N) :
    correctionWords B.realizations A.realizations =
      (B.correction A).realizations :=
  rfl

@[simp]
lemma length_correctionWords
    {M N : ℕ}
    (left right : List (CWord (LabelledAtom M N))) :
    (correctionWords left right).length = left.length * right.length := by
  simp [correctionWords, List.length_flatMap]

/-- Pairwise corrections of same-shape lists have the correction recipe shape. -/
lemma SCShape.correctionWords
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : SCShape B.recipe.erasedShape left)
    (hright : SCShape A.recipe.erasedShape right) :
    SCShape (B.correction A).recipe.erasedShape
      (correctionWords left right) := by
  intro w hw
  rcases List.mem_flatMap.mp hw with ⟨b, hb, hw⟩
  rcases List.mem_map.mp hw with ⟨a, ha, rfl⟩
  rw [BFam.recipe_correction, BRecipe.erasedShape_corr]
  change
    CWord.commutator (collapseWord b) (collapseWord a) =
      CWord.commutator B.recipe.erasedShape A.recipe.erasedShape
  rw [hleft b hb, hright a ha]

/-- Canonical family realizations form a closed collapsed packet. -/
lemma CPFor.realizations
    {M N : ℕ}
    (F : BFam M N) :
    CPFor F F.realizations where
  same_shape := F.collapse_word
  length_eq := rfl

/--
The Cartesian pairwise corrections of two closed collapsed packets close to
the complete correction family.
-/
lemma CPFor.correctionWords
    {M N : ℕ}
    {B A : BFam M N}
    {left right : List (CWord (LabelledAtom M N))}
    (hleft : CPFor B left)
    (hright : CPFor A right) :
    CPFor (B.correction A) (correctionWords left right) where
  same_shape :=
    hleft.same_shape.correctionWords hright.same_shape
  length_eq := by
    rw [length_correctionWords, hleft.length_eq, hright.length_eq]
    simp [BFam.correction, List.length_flatMap]

/--
A closed collapsed packet has the same product as the canonical realization
list of its family after evaluating at any Hall pair.
-/
lemma CPFor.collap_liste_eqrea
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {F : BFam M N}
    {words : List (CWord (LabelledAtom M N))}
    (hpacket : CPFor F words)
    (x y : G) :
    BFTrunc.collapsedList x y words =
      BFTrunc.collapsedList x y F.realizations := by
  let value :=
    F.recipe.erasedShape.eval (HPAtom.eval x y)
  have hwords :
      words.map
          (fun w => (collapseWord w).eval (HPAtom.eval x y)) =
        List.replicate words.length value := by
    simpa [value] using
      (List.eq_replicate_of_mem
        (a := value)
        (l := words.map
          fun w => (collapseWord w).eval (HPAtom.eval x y))
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [hpacket.same_shape w hw]))
  have hrealizations :
      F.realizations.map
          (fun w => (collapseWord w).eval (HPAtom.eval x y)) =
        List.replicate F.realizations.length value := by
    simpa [value] using
      (List.eq_replicate_of_mem
        (a := value)
        (l := F.realizations.map
          fun w => (collapseWord w).eval (HPAtom.eval x y))
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [F.collapse_word w hw]))
  rw [BFTrunc.collapsedList,
    BFTrunc.collapsedList,
    hwords, hrealizations, hpacket.length_eq]

/-- A list of closed collapsed packets, in canonical family order. -/
inductive CPBy
    {M N : ℕ} :
    List (BFam M N) →
      List (CWord (LabelledAtom M N)) →
        Prop where
  | nil :
      CPBy [] []
  | cons
      (F : BFam M N)
      (families : List (BFam M N))
      (packet rest : List (CWord (LabelledAtom M N)))
      (hpacket : CPFor F packet)
      (hrest : CPBy families rest) :
      CPBy (F :: families) (packet ++ rest)

namespace CPBy

/--
A closed collapsed packet decomposition evaluates exactly like the canonical
family realization list.
-/
lemma collapsed_list_realization
    {M N : ℕ}
    {G : Type*}
    [Group G]
    {families : List (BFam M N)}
    {words : List (CWord (LabelledAtom M N))}
    (hpacketed : CPBy families words)
    (x y : G) :
    BFTrunc.collapsedList x y words =
      BFTrunc.collapsedList x y
        (BFam.realizationList families) := by
  induction hpacketed with
  | nil =>
      simp [BFam.realizationList,
        BFTrunc.collapsedList]
  | cons F families packet rest hpacket hrest ih =>
      rw [BFTrunc.collapsed_list_append,
        hpacket.collap_liste_eqrea,
        ih, BFam.realizationList_cons,
        BFTrunc.collapsed_list_append]

end CPBy

end PCCounti
end TCTex
end Towers

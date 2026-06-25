import Towers.Group.Zassenhaus.InverseOrientedPackets

/-!
# Packet scheduling for the inverse-oriented Hall trace

The reusable Hall collector expands a powered commutator into
`inverseLeftTrace`.  The positive-positive nonterminal problem is to
rewrite that finite labelled trace into consecutive closed collapsed packets.
The packets are indexed by `PHistor`: direct leading corrections and
inverse-oriented conjugation corrections.

This file states that operational endpoint without assuming the direct binary
obstruction tree.  It also discharges both zero-input cases and isolates the
remaining positive-positive constructor.  This file is intentionally not
imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ITSched

open HACoeff
open BBSched
open HOPacket

/--
A finite operational schedule from the reusable inverse-oriented raw trace to
closed collapsed packets indexed by their exact Hall histories.
-/
structure CHSched
    (M N : ℕ) where
  histories :
    List (PHistor M N)
  words :
    List (CWord (LabelledAtom M N))
  rewrites :
    BBSched.LWRw
      (inverseLeftTrace
        (labelledLeftAtoms M N)
        (labelledRightAtoms M N))
      words
  packetedBy :
    PCCounti.CPBy
      (histories.map PHistor.family) words

namespace CHSched

/-- Complete endpoint families read from the history-indexed packet list. -/
def families
    {M N : ℕ}
    (schedule : CHSched M N) :
    List (BFam M N) :=
  schedule.histories.map PHistor.family

/-- Endpoint block recipes ready for polynomial specialization. -/
def recipes
    {M N : ℕ}
    (schedule : CHSched M N) :
    List BRecipe :=
  schedule.families.map BFam.recipe

/-- Closed history packets compress to their canonical realization lists. -/
lemma collapsed_list_realization
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (schedule : CHSched M N)
    (x y : G) :
    BFTrunc.collapsedList x y schedule.words =
      BFTrunc.collapsedList x y
        (BFam.realizationList schedule.families) := by
  exact schedule.packetedBy.collapsed_list_realization x y

/-- The concrete rewrite run preserves collapsed evaluation at every Hall pair. -/
lemma collapsed_list_source
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (schedule : CHSched M N)
    (x y : G) :
    BFTrunc.collapsedList x y schedule.words =
      BFTrunc.collapsedList x y
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) := by
  exact
    BFTrunc.collapsed_labelled_rewrites
      x y schedule.rewrites

/-- Canonical endpoint families have the same collapsed value as the raw trace. -/
lemma collapsed_realization_source
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (schedule : CHSched M N)
    (x y : G) :
    BFTrunc.collapsedList x y
        (BFam.realizationList schedule.families) =
      BFTrunc.collapsedList x y
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) := by
  exact
    (schedule.collapsed_list_realization x y).symm.trans
      (schedule.collapsed_list_source x y)

end CHSched

/-- The inverse-oriented raw trace is empty when the right input is empty. -/
lemma inverse_left_nil
    {M N : ℕ}
    (left : List (LabelledAtom M N)) :
    inverseLeftTrace left [] = [] := by
  induction left with
  | nil =>
      rfl
  | cons x left ih =>
      simp [inverseLeftTrace, inverseRightTrace, inverseTraceList, ih]

/-- The inverse-oriented raw trace is already packeted when no left labels exist. -/
def zeroLeft
    (N : ℕ) :
    CHSched 0 N where
  histories := []
  words := []
  rewrites := by
    simpa [labelledLeftAtoms, inverseLeftTrace] using
      (Relation.ReflTransGen.refl :
        BBSched.LWRw
          ([] : List (CWord (LabelledAtom 0 N))) [])
  packetedBy :=
    PCCounti.CPBy.nil

/-- The inverse-oriented raw trace is already packeted when no right labels exist. -/
def zeroRight
    (M : ℕ) :
    CHSched M 0 where
  histories := []
  words := []
  rewrites := by
    simpa [labelledRightAtoms,
      inverse_left_nil (labelledLeftAtoms M 0)] using
      (Relation.ReflTransGen.refl :
        BBSched.LWRw
          ([] : List (CWord (LabelledAtom M 0))) [])
  packetedBy :=
    PCCounti.CPBy.nil

/--
The remaining operational theorem: packetize every positive-positive
inverse-oriented raw trace into complete collapsed history packets.
-/
structure PPScheda :
    Prop where
  resolve :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          Nonempty (CHSched M N)

namespace PPScheda

/-- Zero cases plus one positive-positive kernel schedule every finite raw trace. -/
noncomputable def resolveAll
    (kernel : PPScheda)
    (M N : ℕ) :
    CHSched M N := by
  by_cases hM : M = 0
  · subst M
    exact zeroLeft N
  by_cases hN : N = 0
  · subst N
    exact zeroRight M
  exact Classical.choice
    (kernel.resolve M N (Nat.pos_of_ne_zero hM) (Nat.pos_of_ne_zero hN))

end PPScheda

end ITSched
end TCTex
end Towers

/-!
# Basic schedule for the inverse-oriented Hall trace

The raw inverse-oriented trace starts with basic Hall commutators before it
creates direct and conjugation correction histories.  This file constructs the
first positive-positive schedule explicitly.  It is intentionally not imported
by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ITSched

open HACoeff
open BBSched
open HOPacket

@[simp]
lemma basic_words_one :
    basicWords 1 1 =
      [.commutator (.atom (Sum.inl 0)) (.atom (Sum.inr 0))] := by
  simp [basicWords, labelledLeftAtoms, labelledRightAtoms]

/-- The first positive-positive inverse trace is exactly one basic packet. -/
def oneOne :
    CHSched 1 1 where
  histories := [.hallPair]
  words := basicWords 1 1
  rewrites := by
    simpa [basic_words_one, labelledLeftAtoms, labelledRightAtoms,
      inverseLeftTrace, inverseRightTrace, inverseTraceList,
      inverseConjTrace] using
      (Relation.ReflTransGen.refl :
        BBSched.LWRw
          (basicWords 1 1) (basicWords 1 1))
  packetedBy := by
    simpa using
      (PCCounti.CPBy.cons
        (basicFamily 1 1) []
        (basicWords 1 1) []
        (PCCounti.CPFor.realizations
          (basicFamily 1 1))
        PCCounti.CPBy.nil)

end ITSched
end TCTex
end Towers

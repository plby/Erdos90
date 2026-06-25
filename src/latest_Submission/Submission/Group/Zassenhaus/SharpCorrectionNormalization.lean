import Submission.Group.Zassenhaus.SemanticCorrectionDelegation

/-!
# Sharp semantic normalization of symbolic Hall-power corrections

The ordinary correction delegation interface exposes every correction emitted
from stratum `lowerWeight` at support `lowerWeight + 1`.  For recursive routing
through a higher tail, the useful invariant is stronger: a correction emitted
while crossing an actual parent of weight `parentWeight` can be normalized at
support `parentWeight + 1`.

This file packages exact-parent normalization and the weakening maps needed
when an older coarse-stratum interface consumes that sharper endpoint.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace CCExpans

/-- A stronger lower-support bound may be exposed at any weaker stratum. -/
lemma NTBelow.mono
    {d inputWeight lowerWeight strongerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {R : CCExpans H inputWeight}
    (hR : R.NTBelow strongerWeight)
    (hbound : lowerWeight ≤ strongerWeight) :
    R.NTBelow lowerWeight := by
  intro s i hs
  exact hR s i (hs.trans_le hbound)

end CCExpans

namespace TSNorma

/--
A sharply normalized correction endpoint may be exposed through an interface
requesting any weaker parent support bound.
-/
def weaken
    {d n inputWeight lowerWeight strongerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    {C : TCPkt n B A}
    (normalization :
      TSNorma
        strongerWeight C)
    (hbound : lowerWeight ≤ strongerWeight) :
    TSNorma
      lowerWeight C where
  coordinates := normalization.coordinates
  coordinates_no_below :=
    normalization.coordinates_no_below.mono
      (Nat.add_le_add_right hbound 1)
  list_eval_coordinates := normalization.list_eval_coordinates

end TSNorma

namespace TCPkt

/--
Normalize a correction packet at the exact weight of its left parent.  The
result retains the sharp support bound needed by recursive higher-tail routing.
-/
lemma nonempty_normalization_left
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            B.word.weight PEAddres.weight + 1) H) :
    Nonempty
      (TSNorma
        (B.word.weight PEAddres.weight) C) :=
  C.normalization_left (Nat.le_refl _) normalizer

/--
Normalize a correction packet at the exact weight of its right parent.  The
result retains the sharp support bound needed by recursive higher-tail routing.
-/
lemma nonempty_normalization_right
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            A.word.weight PEAddres.weight + 1) H) :
    Nonempty
      (TSNorma
        (A.word.weight PEAddres.weight) C) :=
  C.semantic_normalization (Nat.le_refl _) normalizer

/-- Choose the sharply normalized endpoint supported above the left parent. -/
noncomputable def normalization_left_weight
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            B.word.weight PEAddres.weight + 1) H) :
    TSNorma
      (B.word.weight PEAddres.weight) C :=
  Classical.choice
    (C.nonempty_normalization_left normalizer)

/-- Choose the sharply normalized endpoint supported above the right parent. -/
noncomputable def semantic_normalization_word
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            A.word.weight PEAddres.weight + 1) H) :
    TSNorma
      (A.word.weight PEAddres.weight) C :=
  Classical.choice
    (C.nonempty_normalization_right normalizer)

/--
Normalize sharply at the left parent, then expose the result through a weaker
parent-support interface.
-/
lemma nonempty_semantic_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            B.word.weight PEAddres.weight + 1) H) :
    Nonempty
      (TSNorma
        lowerWeight C) :=
  ⟨(C.normalization_left_weight normalizer).weaken hB⟩

/--
Normalize sharply at the right parent, then expose the result through a weaker
parent-support interface.
-/
lemma nonempty_normalization_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            A.word.weight PEAddres.weight + 1) H) :
    Nonempty
      (TSNorma
        lowerWeight C) :=
  ⟨(C.semantic_normalization_word normalizer).weaken hA⟩

/--
Choose a sharply normalized left-parent endpoint exposed at a weaker support
stratum.
-/
noncomputable def semantic_left_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            B.word.weight PEAddres.weight + 1) H) :
    TSNorma
      lowerWeight C :=
  Classical.choice (C.nonempty_semantic_sharp hB normalizer)

/--
Choose a sharply normalized right-parent endpoint exposed at a weaker support
stratum.
-/
noncomputable def normalization_right_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            A.word.weight PEAddres.weight + 1) H) :
    TSNorma
      lowerWeight C :=
  Classical.choice (C.nonempty_normalization_sharp hA normalizer)

end TCPkt

end TCTex
end Submission

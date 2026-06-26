import Towers.Group.Zassenhaus.ResidualBranch
import Towers.Group.Zassenhaus.BasicTreeReduction

/-!
# Leaf branches for Hall-ranked concrete residual recursion

Several concrete basic-reduction residuals recollect without recursive child
tasks: cutoff endpoints, basic expanded trees, self-commutators,
reversed-basic words, and weight-one factors.  This file packages those exact
recollections as leaf branches for the Hall-ranked residual scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora
namespace RCSrc

/-- The empty ranked source is a strict child source for every parent task. -/
def empty
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (parent : SPFactora H inputWeight)
    (parentRankDefect : ℕ) :
    RCSrc (n := n) parent parentRankDefect where
  tasks := []
  tasks_descend := by
    simp

@[simp]
theorem tasks_empty
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (parent : SPFactora H inputWeight)
    (parentRankDefect : ℕ) :
    (empty (n := n) parent parentRankDefect).tasks = [] :=
  rfl

@[simp]
theorem factorSource_empty
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (parent : SPFactora H inputWeight)
    (parentRankDefect : ℕ) :
    (empty (n := n) parent parentRankDefect).factorSource = [] :=
  rfl

end RCSrc
end SPFactora

namespace RRBrancha

open
  TSRecollb

/--
Compile an already recollected concrete residual into a Hall-ranked leaf
branch with no recursive child tasks.
-/
noncomputable def ofResidRecollect
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (residual :
      TSRecollb
        (n := n) factor) :
    RRBrancha
      (n := n) factor rankDefect where
  children := SPFactora.RCSrc.empty
    (n := n) factor rankDefect
  recollect := fun _ => residual

/-- The truncation endpoint is a Hall-ranked leaf branch. -/
noncomputable def leaf_of_terminal
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    RRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (of_terminal factor hcutoff)

/-- A basic expanded Hall tree is a Hall-ranked leaf branch. -/
noncomputable def leaf_tree_basic
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (htreeBasic : (HEWord.tree factor.word).IsBasic) :
    RRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (tree_basic factor htreeBasic)

/-- A symbolic self-commutator is a Hall-ranked leaf branch. -/
noncomputable def leaf_commutator_self
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word) :
    RRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (word_commutator_self factor word hword)

/-- A reversed-basic symbolic word is a Hall-ranked leaf branch. -/
noncomputable def leaf_reversed_basic
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hreversed : HEWord.IsReversedBasic factor.word) :
    RRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (reversed_basic factor hreversed)

/-- A weight-one symbolic factor is a Hall-ranked leaf branch. -/
noncomputable def leaf_weight_one
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1) :
    RRBrancha
      (n := n) factor rankDefect :=
  ofResidRecollect factor rankDefect
    (of_weight_one factor hfactorWeight)

end RRBrancha

/--
The concrete residual cases that close immediately, without any recursively
scheduled child residuals.
-/
inductive TruncatedLeafCase
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) : Type u
  | terminal
      (hcutoff :
        n ≤ factor.word.weight PEAddres.weight + 1)
  | tree_isBasic
      (htreeBasic : (HEWord.tree factor.word).IsBasic)
  | commutator_self
      (word :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)))
      (hword : factor.word = .commutator word word)
  | isReversedBasic
      (hreversed : HEWord.IsReversedBasic factor.word)
  | weight_one
      (hfactorWeight :
        factor.word.weight PEAddres.weight = 1)

namespace RRBrancha

/-- Compile any immediate concrete residual case into a Hall-ranked leaf. -/
noncomputable def ofLeafCase
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (leaf :
      TruncatedLeafCase
        (n := n) factor) :
    RRBrancha
      (n := n) factor rankDefect := by
  cases leaf with
  | terminal hcutoff =>
      exact leaf_of_terminal factor rankDefect hcutoff
  | tree_isBasic htreeBasic =>
      exact leaf_tree_basic factor rankDefect htreeBasic
  | commutator_self word hword =>
      exact leaf_commutator_self factor rankDefect word hword
  | isReversedBasic hreversed =>
      exact leaf_reversed_basic factor rankDefect hreversed
  | weight_one hfactorWeight =>
      exact leaf_weight_one factor rankDefect hfactorWeight

end RRBrancha

end TCTex
end Towers

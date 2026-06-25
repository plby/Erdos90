import Towers.Group.Zassenhaus.StrictPrincipalCompatibility
import Towers.Group.Zassenhaus.StrictTail
import Towers.Group.Zassenhaus.BasicTermSemantics
import Towers.Group.Zassenhaus.ConjugatedHigherRouting
import Towers.Group.Zassenhaus.FrontierRecollection
import Towers.Group.Zassenhaus.FrontierWeightDescent
import Towers.Group.Zassenhaus.ResidualContextualRecollection
import Towers.Group.Zassenhaus.ContextualRecursion
import Towers.Group.Zassenhaus.ContextualPacketRecursion
import Towers.Group.Zassenhaus.Contextual
import Towers.Group.Zassenhaus.ConjugatedHigherList

-- Merged from OrderedBasicSplitFromPrincipal.lean

/-!
# Ordered basic splits from principal packet inventory

The principal-recipe invariant identifies `basic` as the only recipe shape
with bidegree `(1, 1)`, but it does not by itself rule out duplicate
occurrences of `basic`.  For a duplicate-free packet, the invariant does
construct the ordered split needed by transient residual routing.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  PFSubsti.TAPkt.PBRecipea

open HACoeff
open BRSpec
open PTSubsti

/--
A duplicate-free packet with a principal basic recipe admits an ordered
decomposition around that recipe.  Every recipe in either tail is strict.
-/
noncomputable def ordered_split_nodup
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PBRecipea)
    (hnodup : packet.recipes.Nodup) :
    packet.OBSplit := by
  let hsplit := List.mem_iff_append.mp principal.basic_mem
  let beforeBasic := Classical.choose hsplit
  let afterBasic := Classical.choose (Classical.choose_spec hsplit)
  have hrecipes :
      packet.recipes = beforeBasic ++ hallPair :: afterBasic :=
    Classical.choose_spec (Classical.choose_spec hsplit)
  have hnodup' : (beforeBasic ++ hallPair :: afterBasic).Nodup := by
    simpa only [hrecipes] using hnodup
  have hbasicNotBefore : hallPair ∉ beforeBasic := by
    intro hbasic
    exact
      (List.nodup_append.mp hnodup').2.2 hallPair hbasic hallPair (by simp) rfl
  have hbasicNotAfter : hallPair ∉ afterBasic :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup').2.1).1
  refine
    { beforeBasic := beforeBasic
      afterBasic := afterBasic
      recipes_eq := hrecipes
      before_strict_tail := ?_
      after_strict_tail := ?_ }
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotBefore (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotAfter (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft

end
  PFSubsti.TAPkt.PBRecipea

end TCTex
end Towers

-- Merged from OrderedResidualSemantics.lean

/-!
# Ordered semantics of transient rewording residuals

An ordered split around the principal basic recipe leaves two strict inverse
tails.  The basic inverse evaluates to the inverse parent, but the strict
prefix still sits between it and the appended parent.  This file records that
noncommutative shape without commuting any factors.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TWExp

/-- Transient source evaluation preserves ordered concatenation. -/
@[simp]
lemma listValue_append
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (left right :
      List (TWExp H inputWeight)) :
    listValue (n := n) q (left ++ right) =
      listValue q left * listValue q right := by
  simp [listValue]

/-- Transient evaluation of a singleton is evaluation of its carrier. -/
@[simp]
lemma listValue_singleton
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansion :
      TWExp H inputWeight) :
    listValue (n := n) q [wordExpansion] =
      wordExpansion.value q := by
  simp [listValue]

end TWExp

namespace PFSubsti.TAPkt
namespace OBSplit

open PTSubsti

/-- Reverse-negated strict suffix emitted before the principal inverse. -/
def strictAfterSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (TWExp H inputWeight) :=
  TWExp.inverseList
    (wordExpansions hinputWeight split.afterBasic
      (outerExpansion.reword innerWord)
      (TWExp.wordUnit rightWord))

/-- Reverse-negated strict prefix emitted after the principal inverse. -/
def strictBeforeSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (TWExp H inputWeight) :=
  TWExp.inverseList
    (wordExpansions hinputWeight split.beforeBasic
      (outerExpansion.reword innerWord)
      (TWExp.wordUnit rightWord))

/-- Both strict inverse tails, forgetting the principal carrier between them. -/
def strictInverseSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (TWExp H inputWeight) :=
  split.strictAfterSource hinputWeight outerExpansion innerWord
      rightWord ++
    split.strictBeforeSource hinputWeight outerExpansion innerWord
      rightWord

/--
The residual source is the strict suffix, principal inverse, strict prefix,
and parent in that exact order.
-/
lemma transient_after_before
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    packet.transientInnerReduction hinputWeight
        outerExpansion innerWord rightWord =
      split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord ++
        [(rewordedBasicExpansion hinputWeight outerExpansion innerWord
          rightWord).neg] ++
        split.strictBeforeSource hinputWeight outerExpansion innerWord
            rightWord ++
          [outerExpansion] := by
  rw [split.inner_after_before]
  rfl

/-- Every carrier in the reverse-negated suffix is strictly heavier. -/
theorem outer_after_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord) :
    outerExpansion.word.weight PEAddres.weight <
      nextExpansion.word.weight PEAddres.weight := by
  apply
    expansions_reword_tail
      hinputWeight split.after_strict_tail outerExpansion innerWord
        rightWord hword nextExpansion
  exact hnext

/-- Every carrier in the reverse-negated prefix is strictly heavier. -/
theorem outer_before_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord) :
    outerExpansion.word.weight PEAddres.weight <
      nextExpansion.word.weight PEAddres.weight := by
  apply
    expansions_reword_tail
      hinputWeight split.before_strict_tail outerExpansion innerWord
        rightWord hword nextExpansion
  exact hnext

/-- Every carrier in either strict inverse tail is strictly heavier. -/
theorem outer_strict_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        split.strictInverseSource hinputWeight outerExpansion innerWord
          rightWord) :
    outerExpansion.word.weight PEAddres.weight <
      nextExpansion.word.weight PEAddres.weight := by
  rcases List.mem_append.mp hnext with hnext | hnext
  · exact split.outer_after_source
      hinputWeight outerExpansion innerWord rightWord hword nextExpansion hnext
  · exact split.outer_before_source
      hinputWeight outerExpansion innerWord rightWord hword nextExpansion hnext

/--
The ordered residual evaluates to a strict suffix, the parent inverse, the
strict prefix, and the parent.  The middle conjugation must be preserved.
-/
lemma raw_strict_tails
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) =
      TWExp.listValue q
          (split.strictAfterSource hinputWeight outerExpansion innerWord
            rightWord) *
        (outerExpansion.value q)⁻¹ *
        TWExp.listValue q
            (split.strictBeforeSource hinputWeight outerExpansion
              innerWord rightWord) *
          outerExpansion.value q := by
  rw [
    split.transient_after_before,
    TWExp.listValue_append,
    TWExp.listValue_append,
    TWExp.listValue_append,
    TWExp.listValue_singleton,
    TWExp.listValue_singleton,
    value_reworded_inv hinputWeight
      outerExpansion innerWord rightWord hword q]

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedBasicSplitFromUniquePrincipal.lean

/-!
# Ordered basic splits from a unique principal occurrence

Transient restart routing only needs the distinguished `basic` recipe to
occur once.  Duplicate nonbasic recipes remain valid strict-tail terms and
need not be ruled out.

This file sharpens the earlier duplicate-free constructor to that exact
inventory condition.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open HACoeff
open BRSpec

/--
The selected packet contains exactly one occurrence of its principal `basic`
recipe.  This permits repeated nonbasic recipes on either side.
-/
def UniqueOccurrence
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) :
    Prop :=
  ∃ beforeBasic afterBasic : List BRecipe,
    packet.recipes = beforeBasic ++ hallPair :: afterBasic ∧
      hallPair ∉ beforeBasic ∧
        hallPair ∉ afterBasic

end PFSubsti.TAPkt

namespace
  PFSubsti.TAPkt.OBSplit

open HACoeff
open BRSpec

/--
An ordered basic split records exactly one occurrence of the principal
`basic` recipe.
-/
def uniqueOccurrence
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : packet.OBSplit) :
    packet.UniqueOccurrence := by
  refine
    ⟨split.beforeBasic, split.afterBasic, split.recipes_eq, ?_, ?_⟩
  · intro hbasic
    exact
      (split.before_strict_tail hallPair hbasic).elim
        (fun h => h left_hall_pair)
        (fun h => h right_degree_pair)
  · intro hbasic
    exact
      (split.after_strict_tail hallPair hbasic).elim
        (fun h => h left_hall_pair)
        (fun h => h right_degree_pair)

end
  PFSubsti.TAPkt.OBSplit

namespace
  PFSubsti.TAPkt.PBRecipea

open HACoeff
open BRSpec

/--
A packet with a principal basic recipe and exactly one occurrence of `basic`
admits an ordered decomposition around that recipe.  Repeated nonbasic tail
recipes are allowed.
-/
noncomputable def ordered_unique_pair
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PBRecipea)
    (hunique : packet.UniqueOccurrence) :
    packet.OBSplit := by
  let beforeBasic := Classical.choose hunique
  let afterBasic := Classical.choose (Classical.choose_spec hunique)
  have hspec :=
    Classical.choose_spec (Classical.choose_spec hunique)
  have hrecipes :
      packet.recipes = beforeBasic ++ hallPair :: afterBasic :=
    hspec.1
  have hbasicNotBefore : hallPair ∉ beforeBasic :=
    hspec.2.1
  have hbasicNotAfter : hallPair ∉ afterBasic :=
    hspec.2.2
  refine
    { beforeBasic := beforeBasic
      afterBasic := afterBasic
      recipes_eq := hrecipes
      before_strict_tail := ?_
      after_strict_tail := ?_ }
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotBefore (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotAfter (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft

end
  PFSubsti.TAPkt.PBRecipea

namespace
  PFSubsti.TAPkt.PBRecipea

open HACoeff
open BRSpec

/--
Duplicate-free principal inventory implies the sharper unique-basic-occurrence
condition.  The converse is deliberately unnecessary: nonbasic recipes may
repeat.
-/
noncomputable def unique_basic_nodup
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PBRecipea)
    (hnodup : packet.recipes.Nodup) :
    packet.UniqueOccurrence := by
  let hsplit := List.mem_iff_append.mp principal.basic_mem
  let beforeBasic := Classical.choose hsplit
  let afterBasic := Classical.choose (Classical.choose_spec hsplit)
  have hrecipes :
      packet.recipes = beforeBasic ++ hallPair :: afterBasic :=
    Classical.choose_spec (Classical.choose_spec hsplit)
  have hnodup' : (beforeBasic ++ hallPair :: afterBasic).Nodup := by
    simpa only [hrecipes] using hnodup
  refine ⟨beforeBasic, afterBasic, hrecipes, ?_, ?_⟩
  · intro hbasic
    exact
      (List.nodup_append.mp hnodup').2.2 hallPair hbasic hallPair (by simp) rfl
  · exact (List.nodup_cons.mp (List.nodup_append.mp hnodup').2.1).1

end
  PFSubsti.TAPkt.PBRecipea

end TCTex
end Towers

-- Merged from OrderedResidualRecollection.lean

/-!
# Recollection of ordered transient rewording residuals

An ordered transient residual is a strict suffix followed by the conjugate of
a strict prefix.  Once both strict tails have been recollected into ordinary
symbolic factors, the existing sharp higher-tail router removes the conjugating
parent wrappers around the prefix.

This file packages that nonterminal composition boundary.  The transient
parent is matched with an ordinary conjugator only through pointwise
evaluation equality, so no invalid attachment of a loose transient carrier is
assumed.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TWExp

/-- The transient view of an ordinary factor on its original word preserves value. -/
@[simp]
lemma value_reword_self
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (q : ℕ) :
    (rewordFactor factor factor.word).value (n := n) q = factor.eval q := by
  rw [value, exponent_rewordFactor]
  rfl

end TWExp

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Recollect an ordered transient rewording residual from independent
recollections of its two strict tails and a sharp route for the conjugated
prefix.
-/
noncomputable def
    recollection_transient_split
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (outerExpansion :
      TWExp H inputWeight)
    (conjugator : SPFactora H inputWeight)
    (hconjugatorWeight :
      conjugator.word.weight PEAddres.weight = lowerWeight)
    (hconjugatorTruncated :
      conjugator.word.weight PEAddres.weight < n)
    (hconjugatorEval :
      ∀ q : ℕ, conjugator.eval (n := n) q = outerExpansion.value q)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (afterRecollection :
      TTRecola
        n (lowerWeight + 1) H
          (split.strictAfterSource hinputWeight outerExpansion innerWord
            rightWord))
    (beforeRecollection :
      TTRecola
        n (lowerWeight + 1) H
          (split.strictBeforeSource hinputWeight outerExpansion
            innerWord rightWord)) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) := by
  let conjugatedBefore :=
    factory.conjugated_recollection_normalizer sharp
      conjugator hconjugatorWeight hconjugatorTruncated
      beforeRecollection.higherSource beforeRecollection.higherSource
      beforeRecollection.higher_source_truncated
      beforeRecollection.higher_weight_least
      (fun _ => rfl)
  exact
    { higherSource :=
        afterRecollection.higherSource ++ conjugatedBefore.higherSource
      higher_source_truncated := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact afterRecollection.higher_source_truncated factor hfactor
        · exact conjugatedBefore.higher_source_truncated factor hfactor
      higher_weight_least := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            afterRecollection.higher_weight_least factor hfactor
        · exact
            conjugatedBefore.higher_least_succ factor
              hfactor
      list_higher_raw := by
        intro q
        rw [SPFactora.listEval_append,
          afterRecollection.list_higher_raw,
          conjugatedBefore.higher_conjugated_raw]
        simp only [SPFactora.conjugatedRawSource,
          SPFactora.listEval_append,
          SPFactora.listEval_cons,
          SPFactora.listEval_nil, mul_one,
          SPFactora.eval_neg,
          beforeRecollection.list_higher_raw,
          hconjugatorEval q]
        rw [
          split.raw_strict_tails
            hinputWeight outerExpansion innerWord rightWord hword q]
        group
    }

/-- Recollect the strict suffix by recursively recollecting each transient carrier. -/
noncomputable def recoll_after_inver
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (factory :
      TTFtry
        d n inputWeight H)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    TTRecola
      n (outerExpansion.word.weight PEAddres.weight + 1) H
        (split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    fun wordExpansion hwordExpansion =>
      (factory.recollectionOrEmpty wordExpansion).weaken
        (Nat.succ_le_of_lt
          (split.outer_after_source
            hinputWeight outerExpansion innerWord rightWord hword
              wordExpansion hwordExpansion))

/-- Recollect the strict prefix by recursively recollecting each transient carrier. -/
noncomputable def recoll_befor_inver
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (factory :
      TTFtry
        d n inputWeight H)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    TTRecola
      n (outerExpansion.word.weight PEAddres.weight + 1) H
        (split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    fun wordExpansion hwordExpansion =>
      (factory.recollectionOrEmpty wordExpansion).weaken
        (Nat.succ_le_of_lt
          (split.outer_before_source
            hinputWeight outerExpansion innerWord rightWord hword
              wordExpansion hwordExpansion))

/--
Specialize ordered residual recollection to the transient view of one ordinary
parent factor.
-/
noncomputable def
    transient_reword_factor
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (afterRecollection :
      TTRecola
        n (lowerWeight + 1) H
          (split.strictAfterSource hinputWeight
            (TWExp.rewordFactor factor
              factor.word)
            innerWord rightWord))
    (beforeRecollection :
      TTRecola
        n (lowerWeight + 1) H
          (split.strictBeforeSource hinputWeight
            (TWExp.rewordFactor factor
              factor.word)
            innerWord rightWord)) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          (TWExp.rewordFactor factor
            factor.word)
          innerWord rightWord) := by
  apply
    split.recollection_transient_split
      hinputWeight factory sharp
        (TWExp.rewordFactor factor
          factor.word)
        factor hfactorWeight hfactorTruncated
  · intro q
    exact
      (TWExp.value_reword_self factor
        q).symm
  · exact hword
  · exact afterRecollection
  · exact beforeRecollection

/--
Recollect the residual of an ordinary parent directly from the recursive
transient singleton factory.
-/
noncomputable def
    recollect_transient_factory
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          (TWExp.rewordFactor factor
            factor.word)
          innerWord rightWord) := by
  apply
    split.transient_reword_factor
      hinputWeight factory sharp factor hfactorWeight hfactorTruncated
        innerWord rightWord hword
  · simpa only [TWExp.rewordFactor,
      hfactorWeight] using
      split.recoll_after_inver transientFactory
        hinputWeight
          (TWExp.rewordFactor factor
            factor.word)
          innerWord rightWord hword
  · simpa only [TWExp.rewordFactor,
      hfactorWeight] using
      split.recoll_befor_inver transientFactory
        hinputWeight
          (TWExp.rewordFactor factor
            factor.word)
          innerWord rightWord hword

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedResidualTerminal.lean

/-!
# Terminal ordered transient rewording residuals

At the next outer-word stratum, every member of the two strict inverse tails
reaches the truncation cutoff.  Their values vanish separately, and the
remaining principal inverse cancels the appended parent semantically.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace OBSplit

/-- At the next parent stratum, the strict suffix evaluates trivially. -/
lemma strict_after_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord) =
      1 := by
  apply
    TWExp.list_value_n
  intro nextExpansion hnext
  have hweight :=
    split.outer_after_source hinputWeight
      outerExpansion innerWord rightWord hword nextExpansion hnext
  omega

/-- At the next parent stratum, the strict prefix evaluates trivially. -/
lemma strict_before_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord) =
      1 := by
  apply
    TWExp.list_value_n
  intro nextExpansion hnext
  have hweight :=
    split.outer_before_source hinputWeight
      outerExpansion innerWord rightWord hword nextExpansion hnext
  omega

/-- At the next parent stratum, both strict inverse tails evaluate trivially. -/
lemma value_strict_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (split.strictInverseSource hinputWeight outerExpansion innerWord
          rightWord) =
      1 := by
  rw [strictInverseSource,
    TWExp.listValue_append,
    split.strict_after_terminal hinputWeight
      outerExpansion innerWord rightWord hword hcutoff q,
    split.strict_before_terminal hinputWeight
      outerExpansion innerWord rightWord hword hcutoff q,
    one_mul]

/--
At the next parent stratum, the explicit ordered residual semantics collapses
to the identity.
-/
lemma inner_split_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    TWExp.listValue (n := n) q
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) =
      1 := by
  rw [
    split.raw_strict_tails
      hinputWeight outerExpansion innerWord rightWord hword q,
    split.strict_after_terminal hinputWeight
      outerExpansion innerWord rightWord hword hcutoff q,
    split.strict_before_terminal hinputWeight
      outerExpansion innerWord rightWord hword hcutoff q]
  group

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedResidualTerminalRecollection.lean

/-!
# Terminal recollection of ordered transient rewording residuals

The two strict inverse tails of an ordered rewording residual vanish
independently at the next outer-word stratum.  This file packages those
terminal facts as transient source recollections, preserving their ordered
composition for later contextual use.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace OBSplit

/-- Recollect the terminal strict suffix to the empty ordinary source. -/
def recoll_after_termi
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1) :
    TTRecola
      n lowerWeight H
        (split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.empty_list_value
    _ fun q =>
      split.strict_after_terminal hinputWeight
        outerExpansion innerWord rightWord hword hcutoff q

/-- Recollect the terminal strict prefix to the empty ordinary source. -/
def recoll_befor_termi
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1) :
    TTRecola
      n lowerWeight H
        (split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.empty_list_value
    _ fun q =>
      split.strict_before_terminal hinputWeight
        outerExpansion innerWord rightWord hword hcutoff q

/-- Recollect both terminal strict tails in their original concatenated order. -/
def source_recol_termi
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1) :
    TTRecola
      n lowerWeight H
        (split.strictInverseSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.append
    (split.recoll_after_termi
      hinputWeight outerExpansion innerWord rightWord hword hcutoff)
    (split.recoll_befor_termi
      hinputWeight outerExpansion innerWord rightWord hword hcutoff)

/--
Recollect the whole explicitly normalized terminal residual to the empty
ordinary source.
-/
def
    recollect_transient_terminal
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight PEAddres.weight + 1) :
    TTRecola
      n lowerWeight H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) :=
  TTRecola.empty_list_value
    _ fun q =>
      split
        |>.inner_split_terminal
          hinputWeight outerExpansion innerWord rightWord hword hcutoff q

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedResidualFactory.lean

/-!
# Factory routing for ordered transient rewording residuals

The nonterminal ordered residual consists of a strict suffix and a conjugated
strict prefix.  Both strict tails delegate to the heavier transient-singleton
collector.  The parent conjugation is available only when the transient outer
carrier can be matched semantically with an ordinary symbolic factor.

This file packages that matched-conjugator input explicitly, dispatches the
next-stratum terminal endpoint without requesting it, and composes the result
with the existing contextual frontier recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
An ordinary symbolic factor whose evaluation agrees with a transient parent
carrier.  The factor is used only to route conjugation through an already
recollected strict higher tail.
-/
structure PMConjug
    {d n inputWeight : ℕ}
    (lowerWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (outerExpansion :
      TWExp H inputWeight) where
  conjugator :
    SPFactora H inputWeight
  conjugator_word_weight :
    conjugator.word.weight PEAddres.weight = lowerWeight
  conjugator_isTruncated :
    conjugator.word.weight PEAddres.weight < n
  conjugator_eval :
    ∀ q : ℕ, conjugator.eval (n := n) q = outerExpansion.value q

namespace PMConjug

/-- The transient view of an ordinary factor is matched by that same factor. -/
def reword_factor_self
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    PMConjug
      (n := n) lowerWeight H
        (TWExp.rewordFactor factor
          factor.word) where
  conjugator := factor
  conjugator_word_weight := hfactorWeight
  conjugator_isTruncated := hfactorTruncated
  conjugator_eval := fun q =>
    (TWExp.value_reword_self factor q).symm

end PMConjug

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Recollect the strict inverse suffix by recursively recollecting its heavier
transient singleton carriers in their original order.
-/
noncomputable def
    after_transient_factory
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight) :
    TTRecola
      n (lowerWeight + 1) H
        (split.strictAfterSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    fun nextExpansion hnext =>
      (transientFactory.recollectionOrEmpty nextExpansion).weaken
        (by
          have hweight :=
            split.outer_after_source
              hinputWeight outerExpansion innerWord rightWord hword
                nextExpansion hnext
          omega)

/--
Recollect the strict inverse prefix by recursively recollecting its heavier
transient singleton carriers in their original order.
-/
noncomputable def
    before_transient_factory
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight) :
    TTRecola
      n (lowerWeight + 1) H
        (split.strictBeforeSource hinputWeight outerExpansion innerWord
          rightWord) :=
  TTRecola.of_singletons _
    fun nextExpansion hnext =>
      (transientFactory.recollectionOrEmpty nextExpansion).weaken
        (by
          have hweight :=
            split.outer_before_source
              hinputWeight outerExpansion innerWord rightWord hword
                nextExpansion hnext
          omega)

/--
Recollect a nonterminal ordered residual from heavier singleton recursion and
one ordinary factor matching the transient parent.
-/
noncomputable def
    recollection_transient_factory
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (matched :
      PMConjug
        (n := n) lowerWeight H outerExpansion)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) :=
  split
    |>.recollection_transient_split
      hinputWeight correctionFactory sharp outerExpansion matched.conjugator
        matched.conjugator_word_weight matched.conjugator_isTruncated
          matched.conjugator_eval innerWord rightWord hword
            (split.after_transient_factory
              hinputWeight transientFactory outerExpansion innerWord rightWord
                hword houterWeight)
            (split.before_transient_factory
              hinputWeight transientFactory outerExpansion innerWord rightWord
                hword houterWeight)

/--
Dispatch an ordered residual to heavier singleton recursion while active, or
erase it at the next parent stratum without requesting a matched conjugator.
-/
noncomputable def
    or_terminal_raw
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (matched :
      lowerWeight + 1 < n →
        PMConjug
          (n := n) lowerWeight H outerExpansion) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) := by
  by_cases hactive : lowerWeight + 1 < n
  · exact
      split
        |>.recollection_transient_factory
          hinputWeight correctionFactory sharp transientFactory outerExpansion
            (matched hactive) innerWord rightWord hword houterWeight
  · exact
      split
        |>.recollect_transient_terminal
          hinputWeight outerExpansion innerWord rightWord hword (by omega)

/--
Compose a recollected temporary packet with the active-or-terminal ordered
residual, yielding a recollection of the original transient frontier.
-/
noncomputable def
    recollection_frontier_reworded
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (matched :
      lowerWeight + 1 < n →
        PMConjug
          (n := n) lowerWeight H outerExpansion)
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            outerExpansion innerWord rightWord)) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  packet.frontier_reworded_residual
    hinputWeight outerExpansion innerWord rightWord packetRecollection
      ((split
        |>.or_terminal_raw
          hinputWeight correctionFactory sharp transientFactory outerExpansion
            innerWord rightWord hword houterWeight matched).weaken
              (Nat.le_succ lowerWeight))

/--
Dispatch the residual of the transient view of an ordinary parent factor.
While active, the parent factor itself supplies the matched conjugator.
-/
noncomputable def
    or_terminal_reword
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          (TWExp.rewordFactor factor
            factor.word)
          innerWord rightWord) :=
  split
    |>.or_terminal_raw
      hinputWeight correctionFactory sharp transientFactory
        (TWExp.rewordFactor factor
          factor.word)
        innerWord rightWord hword hfactorWeight fun hactive =>
          PMConjug.reword_factor_self
            factor hfactorWeight (by omega)

/--
Use an existing first-stage classified-packet recollection and the routed
ordered residual to recollect the transient view of an ordinary parent.
-/
noncomputable def
    frontier_reword_residual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.innerOuterTerms hinputWeight factor
            innerWord rightWord hword)) :
    TTRecol
      n lowerWeight H
        [.frontier
          (TWExp.rewordFactor factor
            factor.word)] := by
  apply
    split.recollection_frontier_reworded
      hinputWeight correctionFactory sharp transientFactory
        (TWExp.rewordFactor factor
          factor.word)
        innerWord rightWord hword hfactorWeight
          (fun hactive =>
            PMConjug.reword_factor_self
              factor hfactorWeight (by omega))
  rw [
    packet
      |>.transient_inner_classified
        hinputWeight factor innerWord rightWord hword]
  exact packetRecollection

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedResidualContextualRecursion.lean

/-!
# Contextual recursion for ordered transient rewording residuals

The ordered residual factory recollects the transient view of an ordinary
parent once its first-stage classified packet has been recollected.  The
contextual well-founded recursion already supplies that packet as a strictly
smaller obligation.  This file packages the direct callback-facing route.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Recollect the transient singleton view of an ordinary parent directly from
the contextual recursive callback for strictly smaller mixed packets.
-/
noncomputable def
    reword_recursive_results
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child
              [.frontier
                (TWExp.rewordFactor factor
                  factor.word)] →
          TTRecol
            n lowerWeight H child) :
    TTRecol
      n lowerWeight H
        [.frontier
          (TWExp.rewordFactor factor
            factor.word)] :=
  split
    |>.frontier_reword_residual
      hinputWeight correctionFactory sharp transientFactory factor
        hfactorWeight innerWord rightWord hword
          (packet.inner_result_reword
            hinputWeight factor innerWord rightWord hword hfactorTruncated
              recursiveResults)

/--
Recollect an arbitrary transient parent from recursive results for the
classified packet rooted at its reworded inner carrier.  The explicit matched
conjugator records the extra semantic input needed while the residual remains
active.
-/
noncomputable def
    reworded_recursive_results
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (hinner :
      innerWord.weight PEAddres.weight < n)
    (matched :
      lowerWeight + 1 < n →
        PMConjug
          (n := n) lowerWeight H outerExpansion)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier (outerExpansion.reword innerWord)] →
          TTRecol
            n lowerWeight H child) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  split.recollection_frontier_reworded
    hinputWeight correctionFactory sharp transientFactory outerExpansion
      innerWord rightWord hword houterWeight matched
        (packet.transient_result_reword
          hinputWeight outerExpansion innerWord rightWord hinner
            recursiveResults)

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedResidualRecursiveFactory.lean

/-!
# Recursive factory bridge for ordered transient rewording residuals

Ordered residual tails need singleton transient recollections at their own
strictly higher physical support bounds.  The local contextual callback alone
retains its parent's requested bound, but the complete contextual recursive
step is polymorphic in that bound.  Rerunning its fixpoint on a singleton
frontier at the singleton's own word weight supplies exactly the older
transient factory interface.

This file packages that bridge and feeds it back into ordinary-parent ordered
residual recursion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TTRecola

/--
Forget that a recollected singleton transient frontier was presented through
the mixed contextual packet API.
-/
def singleton_frontier_recollection
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion :
      TWExp H inputWeight)
    (recollection :
      TTRecol
        n lowerWeight H [.frontier wordExpansion]) :
    TTRecola
      n lowerWeight H [wordExpansion] where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := by
    intro q
    rw [recollection.list_higher_raw]
    simp [TWExp.listValue,
      SOTerm.listValue,
      SOTerm.value]

end TTRecola

namespace TCReca

/--
A support-polymorphic contextual packet resolver supplies the historical
transient-singleton factory by recollecting each singleton frontier at its own
physical Hall-word weight.
-/
noncomputable def toTransientFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (step :
      TCReca
        d n inputWeight H) :
    TTFtry
      d n inputWeight H where
  sourceRecollection wordExpansion _ :=
    TTRecola.singleton_frontier_recollection
      wordExpansion
        (step.sourceRecollection
          (wordExpansion.word.weight PEAddres.weight)
            [.frontier wordExpansion])

end TCReca

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Use one support-polymorphic contextual recursive step for both the temporary
classified packet and every strictly higher ordered residual tail singleton.
-/
noncomputable def
    frontier_reword_recursive
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (step :
      TCReca
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecol
      n lowerWeight H
        [.frontier
          (TWExp.rewordFactor factor
            factor.word)] :=
  split.reword_recursive_results
    hinputWeight correctionFactory sharp step.toTransientFactory factor
      hfactorWeight hfactorTruncated innerWord rightWord hword fun child _ =>
        step.sourceRecollection lowerWeight child

/--
Expose the recursive ordinary-parent route through the transient singleton
source API.
-/
noncomputable def
    recollection_reword_recursive
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (step :
      TCReca
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecola
      n lowerWeight H
        [TWExp.rewordFactor factor
          factor.word] :=
  TTRecola.singleton_frontier_recollection
    _ <|
      split.frontier_reword_recursive
        hinputWeight correctionFactory sharp step factor hfactorWeight
          hfactorTruncated innerWord rightWord hword

/--
Use the support-polymorphic recursive step directly for the classified packet.
Unlike the callback-facing route, this version also covers the terminal
parent stratum without requiring the parent itself to remain truncated.
-/
noncomputable def
    reword_or_terminal
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (step :
      TCReca
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecol
      n lowerWeight H
        [.frontier
          (TWExp.rewordFactor factor
            factor.word)] :=
  split
    |>.frontier_reword_residual
      hinputWeight correctionFactory sharp step.toTransientFactory factor
        hfactorWeight innerWord rightWord hword
          (step.sourceRecollection lowerWeight
            (packet.innerOuterTerms hinputWeight factor
              innerWord rightWord hword))

/--
Expose the terminal-friendly recursive ordinary-parent route through the
transient singleton source API.
-/
noncomputable def
    reword_recursive_terminal
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (step :
      TCReca
        d n inputWeight H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecola
      n lowerWeight H
        [TWExp.rewordFactor factor
          factor.word] :=
  TTRecola.singleton_frontier_recollection
    _ <|
      split
        |>.reword_or_terminal
          hinputWeight correctionFactory sharp step factor hfactorWeight
            innerWord rightWord hword

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedResidualMatchedRecursiveFactory.lean

/-!
# Matched recursive factory bridge for ordered transient residuals

The contextual recursive step supplies both smaller mixed-packet
recollections and the singleton transient factory needed by strict ordered
tails.  For an arbitrary transient parent, active conjugation still requires
an explicit ordinary factor with the same value.  This file packages the
resulting matched-parent route.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Use one support-polymorphic contextual recursive step to recollect an
arbitrary transient parent with an explicitly matched ordinary conjugator.
-/
noncomputable def
    frontier_reworded_recursive
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (step :
      TCReca
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (hinner :
      innerWord.weight PEAddres.weight < n)
    (matched :
      lowerWeight + 1 < n →
        PMConjug
          (n := n) lowerWeight H outerExpansion) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  split
    |>.reworded_recursive_results
      hinputWeight correctionFactory sharp step.toTransientFactory
        outerExpansion innerWord rightWord hword houterWeight hinner matched
          fun child _ => step.sourceRecollection lowerWeight child

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers

-- Merged from OrderedResidualAttachment.lean

/-!
# Attachable transient parents for ordered residual recollection

An attachable transient parent exponent returns to the ordinary symbolic
language as a finite factor list on the same Hall word.  Its exponent need not
be representable by one bounded recipe, so the parent is routed through the
list-level sharp conjugation adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
An ordinary symbolic factor list whose ordered evaluation agrees with a
transient parent carrier.
-/
structure TMConjug
    {d n inputWeight : ℕ}
    (lowerWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (outerExpansion :
      TWExp H inputWeight) where
  conjugators :
    List (SPFactora H inputWeight)
  conjugators_word_weight :
    ∀ conjugator ∈ conjugators,
      conjugator.word.weight PEAddres.weight = lowerWeight
  conjugators_isTruncated :
    SPFactora.IsTruncated n conjugators
  conjugators_eval :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q conjugators =
        outerExpansion.value q

namespace TMConjug

/--
Attach a balanced transient exponent and use its complete ordinary factor
list as the matched parent conjugator.
-/
noncomputable def of_attach
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (outerExpansion :
      TWExp H inputWeight)
    (hattach :
      outerExpansion.exponentWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (houterTruncated :
      outerExpansion.word.weight PEAddres.weight < n) :
    TMConjug
      (n := n) lowerWeight H outerExpansion where
  conjugators := (outerExpansion.toWordExpansion hattach).factors
  conjugators_word_weight := by
    intro conjugator hconjugator
    rw [(outerExpansion.toWordExpansion hattach).of_mem_factors
      hconjugator]
    exact houterWeight
  conjugators_isTruncated := by
    intro conjugator hconjugator
    rw [(outerExpansion.toWordExpansion hattach).of_mem_factors
      hconjugator]
    exact houterTruncated
  conjugators_eval := by
    intro q
    rw [(outerExpansion.toWordExpansion hattach).listEval_factors,
      TWExp.exponent_word_expansion]
    rfl

end TMConjug

namespace PFSubsti.TAPkt
namespace OBSplit

/--
Recollect a nonterminal ordered residual using a matched ordinary parent
factor list.
-/
noncomputable def
    transient_matched_conjugator
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (matched :
      TMConjug
        (n := n) lowerWeight H outerExpansion)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) := by
  let afterRecollection :=
    split.after_transient_factory
      hinputWeight transientFactory outerExpansion innerWord rightWord hword
        houterWeight
  let beforeRecollection :=
    split.before_transient_factory
      hinputWeight transientFactory outerExpansion innerWord rightWord hword
        houterWeight
  let conjugatedBefore :=
    correctionFactory.conjugated_sharp_normalizer
      sharp matched.conjugators beforeRecollection.higherSource
        beforeRecollection.higherSource matched.conjugators_word_weight
          matched.conjugators_isTruncated
            beforeRecollection.higher_source_truncated
              beforeRecollection.higher_weight_least fun _ => rfl
  exact
    { higherSource :=
        afterRecollection.higherSource ++ conjugatedBefore.higherSource
      higher_source_truncated := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact afterRecollection.higher_source_truncated factor hfactor
        · exact conjugatedBefore.higher_source_truncated factor hfactor
      higher_weight_least := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            afterRecollection.higher_weight_least factor hfactor
        · exact
            conjugatedBefore.higher_least_succ factor
              hfactor
      list_higher_raw := by
        intro q
        rw [SPFactora.listEval_append,
          afterRecollection.list_higher_raw,
          conjugatedBefore.list_conjugated_raw,
          SPFactora.conjugated_raw_source,
          beforeRecollection.list_higher_raw,
          matched.conjugators_eval q,
          split.raw_strict_tails
            hinputWeight outerExpansion innerWord rightWord hword q]
        group
    }

/--
Use list-level sharp conjugation while active, or erase the residual at the
next parent stratum without attaching the parent.
-/
noncomputable def
    terminal_matched_conjugator
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (matched :
      lowerWeight + 1 < n →
        TMConjug
          (n := n) lowerWeight H outerExpansion) :
    TTRecola
      n (lowerWeight + 1) H
        (packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) := by
  by_cases hactive : lowerWeight + 1 < n
  · exact
      split
        |>.transient_matched_conjugator
          hinputWeight correctionFactory sharp transientFactory outerExpansion
            (matched hactive) innerWord rightWord hword houterWeight
  · exact
      split
        |>.recollect_transient_terminal
          hinputWeight outerExpansion innerWord rightWord hword (by omega)

/--
Compose a recollected temporary packet with a list-routed ordered residual.
-/
noncomputable def
    reworded_matched_conjugator
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TTFtry
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (matched :
      lowerWeight + 1 < n →
        TMConjug
          (n := n) lowerWeight H outerExpansion)
    (packetRecollection :
      TTRecol
        n lowerWeight H
          (packet.transientInnerTerms hinputWeight
            outerExpansion innerWord rightWord)) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  packet.frontier_reworded_residual
    hinputWeight outerExpansion innerWord rightWord packetRecollection
      ((split
        |>.terminal_matched_conjugator
          hinputWeight correctionFactory sharp transientFactory outerExpansion
            innerWord rightWord hword houterWeight matched).weaken
              (Nat.le_succ lowerWeight))

/--
Recollect an attachable transient parent from one support-polymorphic
recursive step.
-/
noncomputable def
    attachable_reworded_recursive
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet)
    (hinputWeight : 0 < inputWeight)
    (correctionFactory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (step :
      TCReca
        d n inputWeight H)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight PEAddres.weight =
        lowerWeight)
    (hinner :
      innerWord.weight PEAddres.weight < n)
    (hattach :
      lowerWeight + 1 < n →
        outerExpansion.exponentWeight ≤
          outerExpansion.word.weight PEAddres.weight) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  split
    |>.reworded_matched_conjugator
      hinputWeight correctionFactory sharp step.toTransientFactory
        outerExpansion innerWord rightWord hword houterWeight
          (fun hactive =>
            TMConjug.of_attach
              outerExpansion (hattach hactive) houterWeight (by omega))
          (packet.transient_result_reword
            hinputWeight outerExpansion innerWord rightWord hinner
              fun child _ => step.sourceRecollection lowerWeight child)

end OBSplit
end PFSubsti.TAPkt

end TCTex
end Towers
